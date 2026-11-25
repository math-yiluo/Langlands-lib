/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineDisjointSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.AffineFiniteLimits
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficientsInjective
public import WeilConjectures.CategoryTheory.Sites.CechComplexCoefficientsSheaf

/-!
# The Čech criterion for acyclicity on the affine pro-étale site

Let `S` be an affine scheme and `A` an abelian category. We show Cartan's criterion on the affine
pro-étale site `S.AffineProEt`: a sheaf `G` with values in `A` whose Čech complexes
`Č(V' ⟶ V, G)` for the surjections `V' ⟶ V` are exact in positive degrees is acyclic for the
sections functor at the terminal object, i.e. `H^q(S, G) = 0` for `q > 0`.

The key point is that for a short exact sequence `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` of sheaves such that
the first Čech cohomology of `G₁` vanishes for all surjections, the presheaf cokernel of
`G₁ ⟶ G₂` is already a sheaf: it is a sheaf for disjoint finite open covers, since cokernels
commute with finite products, and for single surjections by a diagram chase in the augmented
Čech complexes. Hence `G₂(V) ⟶ G₃(V)` is an epimorphism for every `V`. The criterion then
follows by dimension shifting (`CategoryTheory.Functor.rightAcyclic_of_epi_map_g`), the Čech
complexes of injective sheaves being exact
(`CategoryTheory.Sheaf.exactAt_overCechComplex_of_injective`).

## Main statements

- `AlgebraicGeometry.Scheme.AffineProEt.isSheaf_X₃_of_exactAt_overCechComplex`: the presheaf
  cokernel of a short exact sequence of presheaves whose first two terms are sheaves is a sheaf,
  provided the first Čech cohomology of the first term vanishes for surjections.
- `AlgebraicGeometry.Scheme.AffineProEt.epi_app_g_of_exactAt_overCechComplex`: sections of a
  short exact sequence of sheaves whose first term has vanishing first Čech cohomology are
  right exact.
- `AlgebraicGeometry.Scheme.AffineProEt.rightAcyclic_of_exactAt_overCechComplex` and
  `AlgebraicGeometry.Scheme.AffineProEt.isZero_rightDerived_of_exactAt_overCechComplex`: the Čech
  criterion for acyclicity.

## References

* [Stacks, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public section

universe w v u u'

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.AffineProEt

open Presheaf

variable {S : Scheme.{u}} [IsAffine S] {A : Type u'} [Category.{u + 1} A] [Abelian A]

omit [IsAffine S] in
/-- Let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be an objectwise short exact sequence of presheaves on the
affine pro-étale site such that `P₁` and `P₂` are sheaves. Then `P₃` is a sheaf for every
finite jointly surjective family of open immersions with pairwise disjoint ranges: since
cokernels commute with finite products, `P₃(Y) ⟶ ∏ P₃(U i)` is an isomorphism. -/
lemma isSheafFor_ofArrows_X₃_of_disjoint {T : ShortComplex ((S.AffineProEt)ᵒᵖ ⥤ A)}
    (hT : ∀ X, (T.map ((CategoryTheory.evaluation _ A).obj X)).ShortExact)
    (h₁ : Presheaf.IsSheaf (topology S) T.X₁) (h₂ : Presheaf.IsSheaf (topology S) T.X₂)
    {Y : S.AffineProEt} {ι : Type u} [Finite ι] (U : ι → S.AffineProEt) (j : ∀ i, U i ⟶ Y)
    (hoi : ∀ i, IsOpenImmersion (j i).left)
    (hsurj : ∀ y : Y.left, ∃ i, y ∈ Set.range (j i).left.base)
    (hdisj : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left.base) (Set.range (j k).left.base))
    (a : A) : (Presieve.ofArrows U j).IsSheafFor (T.X₃ ⋙ coyoneda.obj (op a)) := by
  have := Abelian.hasFiniteBiproducts (C := A)
  have e₁ := isIso_piLift_map_of_disjoint ⟨T.X₁, h₁⟩ U j hoi hsurj hdisj
  have e₂ := isIso_piLift_map_of_disjoint ⟨T.X₂, h₂⟩ U j hoi hsurj hdisj
  let φ : T.map ((CategoryTheory.evaluation _ A).obj (op Y)) ⟶
      ShortComplex.mk (Limits.Pi.map fun i ↦ T.f.app (op (U i)))
        (Limits.Pi.map fun i ↦ T.g.app (op (U i))) (by
          ext i
          simp [← NatTrans.comp_app]) :=
    { τ₁ := Pi.lift fun i ↦ T.X₁.map (j i).op
      τ₂ := Pi.lift fun i ↦ T.X₂.map (j i).op
      τ₃ := Pi.lift fun i ↦ T.X₃.map (j i).op
      comm₁₂ := Pi.hom_ext _ _ fun i ↦ by simp
      comm₂₃ := Pi.hom_ext _ _ fun i ↦ by simp }
  have : IsIso φ.τ₁ := e₁
  have : IsIso φ.τ₂ := e₂
  have : Epi (T.map ((CategoryTheory.evaluation _ A).obj (op Y))).g := (hT _).epi_g
  have : Epi (Limits.Pi.map fun i ↦ T.g.app (op (U i))) := by
    have (i : ι) : Epi (T.g.app (op (U i))) := (hT _).epi_g
    exact Pi.map_epi _
  have hφ : IsIso (Pi.lift fun i ↦ T.X₃.map (j i).op :
      T.X₃.obj (op Y) ⟶ ∏ᶜ fun i ↦ T.X₃.obj (op (U i))) :=
    ShortComplex.isIso_τ₃_of_exact φ
      (ShortComplex.exact_mk_piMap (fun i ↦ T.map ((CategoryTheory.evaluation _ A).obj
        (op (U i)))) (fun i ↦ hT _) _)
  rw [Presieve.isSheafFor_arrows_iff]
  intro x _
  refine ⟨Pi.lift x ≫ inv (Pi.lift fun i ↦ T.X₃.map (j i).op), fun i ↦ ?_, fun t ht ↦ ?_⟩
  · rw [comp_coyoneda_obj_map_apply, ← Pi.lift_comp_π (fun i ↦ T.X₃.map (j i).op) i,
      Category.assoc, IsIso.inv_hom_id_assoc, Pi.lift_comp_π]
  · rw [IsIso.eq_comp_inv]
    refine Pi.hom_ext _ _ fun i ↦ ?_
    rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]
    exact ht i

/-- Let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be an objectwise short exact sequence of presheaves on the
affine pro-étale site such that `P₁` and `P₂` are sheaves. If the first Čech cohomology of `P₁`
for a surjection `f` vanishes, then `P₃` is a sheaf for `f`. -/
lemma isSheafFor_singleton_X₃_of_exactAt_overCechComplex
    {T : ShortComplex ((S.AffineProEt)ᵒᵖ ⥤ A)}
    (hT : ∀ X, (T.map ((CategoryTheory.evaluation _ A).obj X)).ShortExact)
    (h₁ : Presheaf.IsSheaf (topology S) T.X₁) (h₂ : Presheaf.IsSheaf (topology S) T.X₂)
    {V V' : S.AffineProEt} (f : V' ⟶ V) (hf : Surjective f.left)
    (hf₁ : ((overCechComplex (CategoryTheory.Over.mk f)).obj T.X₁).ExactAt 1) (a : A) :
    (Presieve.singleton f).IsSheafFor (T.X₃ ⋙ coyoneda.obj (op a)) :=
  isSheafFor_singleton_of_isLimit_overCechAugmentation_mk T.X₃ f
    (isLimitOverCechAugmentationX₃ (CategoryTheory.Over.mk f) hT
      (Sheaf.isLimitOverCechAugmentation ⟨T.X₁, h₁⟩ (CategoryTheory.Over.mk f)
        (generate_singleton_mem_topology f hf))
      (Sheaf.isLimitOverCechAugmentation ⟨T.X₂, h₂⟩ (CategoryTheory.Over.mk f)
        (generate_singleton_mem_topology f hf)) hf₁) a

/-- Let `0 ⟶ P₁ ⟶ P₂ ⟶ P₃ ⟶ 0` be an objectwise short exact sequence of presheaves on the
affine pro-étale site such that `P₁` and `P₂` are sheaves. If the first Čech cohomology of `P₁`
vanishes for all the surjections, then `P₃` is a sheaf. -/
theorem isSheaf_X₃_of_exactAt_overCechComplex {T : ShortComplex ((S.AffineProEt)ᵒᵖ ⥤ A)}
    (hT : ∀ X, (T.map ((CategoryTheory.evaluation _ A).obj X)).ShortExact)
    (h₁ : Presheaf.IsSheaf (topology S) T.X₁) (h₂ : Presheaf.IsSheaf (topology S) T.X₂)
    (h : ∀ {V V' : S.AffineProEt} (f : V' ⟶ V), Surjective f.left →
      ((overCechComplex (CategoryTheory.Over.mk f)).obj T.X₁).ExactAt 1) :
    Presheaf.IsSheaf (topology S) T.X₃ := fun a ↦
  (isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_of_isSheafFor_disjoint S
    (fun U j hoi hsurj hdisj ↦ isSheafFor_ofArrows_X₃_of_disjoint hT h₁ h₂ U j hoi hsurj hdisj a)
    (fun f hf ↦ isSheafFor_singleton_X₃_of_exactAt_overCechComplex hT h₁ h₂ f hf (h f hf) a))

variable [HasSheafify (topology S) A]

/-- **Right exactness of sections.** Let `0 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 0` be a short exact sequence of
sheaves on the affine pro-étale site such that the first Čech cohomology of `G₁` vanishes for
all the surjections. Then `G₂(V) ⟶ G₃(V)` is an epimorphism for every `V`: the presheaf
cokernel of `G₁ ⟶ G₂` is a sheaf (`isSheaf_X₃_of_exactAt_overCechComplex`), hence it is `G₃`. -/
theorem epi_app_g_of_exactAt_overCechComplex {T : ShortComplex (Sheaf (topology S) A)}
    (hT : T.ShortExact)
    (h : ∀ {V V' : S.AffineProEt} (f : V' ⟶ V), Surjective f.left →
      ((overCechComplex (CategoryTheory.Over.mk f)).obj T.X₁.obj).ExactAt 1)
    (V : S.AffineProEt) : Epi (T.g.hom.app (op V)) := by
  have : Mono T.f := hT.mono_f
  have : Epi T.g := hT.epi_g
  have : Mono T.f.hom := (sheafToPresheaf _ A).map_mono T.f
  let T' : ShortComplex ((S.AffineProEt)ᵒᵖ ⥤ A) :=
    ShortComplex.mk T.f.hom (cokernel.π T.f.hom) (cokernel.condition _)
  have hT' : T'.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  let C : Sheaf (topology S) A := ⟨cokernel T.f.hom, isSheaf_X₃_of_exactAt_overCechComplex
    (T := T') hT'.map_evaluation T.X₁.property T.X₂.property h⟩
  let π : T.X₂ ⟶ C := ObjectProperty.homMk (cokernel.π T.f.hom)
  have hfg : T.f.hom ≫ T.g.hom = 0 := congrArg (·.hom) T.zero
  let u : C ⟶ T.X₃ := ObjectProperty.homMk (cokernel.desc T.f.hom T.g.hom hfg)
  have hu : π ≫ u = T.g := Sheaf.hom_ext (cokernel.π_desc _ _ _)
  have : Epi π := (sheafToPresheaf _ A).epi_of_epi_map (inferInstanceAs (Epi (cokernel.π T.f.hom)))
  let v : T.X₃ ⟶ C := hT.gIsCokernel.desc (CokernelCofork.ofπ π
    (Sheaf.hom_ext (cokernel.condition T.f.hom)))
  have hv : T.g ≫ v = π := Cofork.IsColimit.π_desc hT.gIsCokernel
  have : IsIso u := ⟨v, by rw [← cancel_epi π, ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi T.g, ← Category.assoc, hv, hu, Category.comp_id]⟩
  have e : T.g.hom.app (op V) = (cokernel.π T.f.hom).app (op V) ≫
      (sheafToPresheaf _ A ⋙ (CategoryTheory.evaluation _ A).obj (op V)).map u := by
    rw [← hu]
    rfl
  have : Epi ((cokernel.π T.f.hom).app (op V)) := (hT'.map_evaluation (op V)).epi_g
  rw [e]
  infer_instance

variable [HasInjectiveResolutions (Sheaf (topology S) A)] [HasProducts.{u + 1} A]

/-- **The Čech criterion for acyclicity** (Cartan). Let `G` be a sheaf on the affine pro-étale
site of `S` with values in an abelian category, whose Čech complexes `Č(V' ⟶ V, G)` for all the
surjections `V' ⟶ V` are exact in positive degrees. Then `G` is acyclic for the sections at the
terminal object: `H^q(S, G) = 0` for `q > 0`. -/
@[stacks 03F7]
theorem rightAcyclic_of_exactAt_overCechComplex (G : Sheaf (topology S) A)
    (hG : ∀ {V V' : S.AffineProEt} (f : V' ⟶ V), Surjective f.left → ∀ q : ℕ,
      ((overCechComplex (CategoryTheory.Over.mk f)).obj G.obj).ExactAt (q + 1)) :
    (sheafToPresheaf (topology S) A ⋙
      (CategoryTheory.evaluation _ A).obj (op (top S))).rightAcyclic G := by
  refine Functor.rightAcyclic_of_epi_map_g _ (fun G ↦ ∀ {V V' : S.AffineProEt} (f : V' ⟶ V),
      Surjective f.left → ∀ q : ℕ,
        ((overCechComplex (CategoryTheory.Over.mk f)).obj G.obj).ExactAt (q + 1))
    (fun I _ V V' f _ q ↦ Sheaf.exactAt_overCechComplex_of_injective _ I q)
    (fun T hT h₁ h₂ V V' f hf q ↦ ?_)
    (fun T hT h₁ ↦ epi_app_g_of_exactAt_overCechComplex hT (fun f hf ↦ h₁ f hf 0) (top S)) hG
  -- the sections of a short exact sequence whose first term is Čech acyclic are short exact
  have hT' (X : (S.AffineProEt)ᵒᵖ) :
      ((T.map (sheafToPresheaf _ A)).map ((CategoryTheory.evaluation _ A).obj X)).ShortExact := by
    have : Mono T.f := hT.mono_f
    have hm : Mono (T.f.hom.app X) :=
      (sheafToPresheaf _ A ⋙ (CategoryTheory.evaluation _ A).obj X).map_mono T.f
    have he : Epi (T.g.hom.app X) :=
      epi_app_g_of_exactAt_overCechComplex hT (fun f hf ↦ h₁ f hf 0) X.unop
    exact .mk' (hT.exact.map_of_mono_of_preservesKernel
      (sheafToPresheaf _ A ⋙ (CategoryTheory.evaluation _ A).obj X) inferInstance inferInstance)
      hm he
  exact exactAt_overCechComplex_X₃ (S := T.map (sheafToPresheaf _ A)) _ hT' (q + 1)
    (h₂ f hf q) (h₁ f hf (q + 1))

/-- **The Čech criterion for the vanishing of cohomology.** Let `G` be a sheaf on the affine
pro-étale site of `S` whose Čech complexes for all the surjections are exact in positive degrees.
Then the higher derived functors of the sections at the terminal object vanish on `G`. -/
theorem isZero_rightDerived_of_exactAt_overCechComplex (G : Sheaf (topology S) A)
    (hG : ∀ {V V' : S.AffineProEt} (f : V' ⟶ V), Surjective f.left → ∀ q : ℕ,
      ((overCechComplex (CategoryTheory.Over.mk f)).obj G.obj).ExactAt (q + 1)) (q : ℕ) :
    IsZero (((sheafToPresheaf (topology S) A ⋙
      (CategoryTheory.evaluation _ A).obj (op (top S))).rightDerived (q + 1)).obj G) :=
  rightAcyclic_of_exactAt_overCechComplex G hG q

end AlgebraicGeometry.Scheme.AffineProEt
