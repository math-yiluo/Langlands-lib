/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.RingTheory.Etale.Field
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.RingTheory.Etale.Basic
public import WeilConjectures.RingTheory.TensorProduct.Hilbert90

/-!
# Hilbert 90 for the spectrum of a field

For a field `K` the cohomological Picard group `H¹(Spec K_ét, 𝔾ₘ)` vanishes.

## Main definitions

- `AlgebraicGeometry.Scheme.etaleSpec`: `Spec A` as an object of the small étale site of
  `Spec K`, for an étale `K`-algebra `A`.
- `AlgebraicGeometry.Scheme.etaleSpecMap`: the morphism induced by a `K`-algebra map.
- `AlgebraicGeometry.Scheme.gmSheafEtaleSpecEquiv`: the sections of `𝔾ₘ` over `Spec A` are
  the units of `A`.

## Main statements

- `AlgebraicGeometry.Scheme.surjective_app_of_shortExact_gmSheaf`: every `𝔾ₘ`-torsor on
  `Spec K` is trivial, in the form: for `0 → 𝔾ₘ → E → Q → 0` exact, `Γ(E) → Γ(Q)` is
  surjective.
- `AlgebraicGeometry.Scheme.subsingleton_cohomologicalPicardGroup_of_field`: Hilbert 90,
  `H¹(Spec K_ét, 𝔾ₘ) = 0`.

## Implementation details

Rather than deducing the vanishing from `Pic(X) ≃ H¹(X_ét, 𝔾ₘ)`, we prove it directly:

1. `H¹(𝔾ₘ) = Ext¹(ℤ, 𝔾ₘ)` vanishes as soon as for every short exact sequence
   `0 → 𝔾ₘ → E → Q → 0` the global sections of `Q` lift to `E`
   (`CategoryTheory.Sheaf.subsingleton_H_one_of_surjective`).
2. A global section `q` of `Q` lifts locally, hence to a section `e` of `E` over `Spec L` for a
   finite separable extension `L` of `K`
   (`AlgebraicGeometry.Scheme.exists_etaleSpec_field_mem_of_mem_smallEtaleTopology`).
3. The difference `p₁^* e - p₂^* e` of the two pullbacks of `e` to
   `Spec L ×_{Spec K} Spec L = Spec (L ⊗_K L)` is a Čech `1`-cocycle with values in
   `(L ⊗_K L)ˣ`. It is a coboundary by Hilbert 90 for the Amitsur complex
   (`Algebra.TensorProduct.exists_eq_of_cocycle`), so `e` can be corrected by a unit of `L`
   to a section that descends to `Spec K`
   (`AlgebraicGeometry.Scheme.exists_app_eq_of_app_etaleSpec_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

/-- The terminal object `𝟙 : Spec K ⟶ Spec K` of the small étale site of `Spec K`. -/
local notation "𝟙ₑ" => MorphismProperty.Over.mk ⊤ (𝟙 (Spec (CommRingCat.of K)))
  (MorphismProperty.id_mem @AlgebraicGeometry.Etale (Spec (CommRingCat.of K)))

variable (K) in
/-- For an étale `K`-algebra `A`, the spectrum `Spec A` as an object of the small étale site of
`Spec K`. -/
noncomputable def etaleSpec (A : Type u) [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    (Spec (.of K)).Etale :=
  MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap K A)))
    (HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance))

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B]
  [Algebra K C] [Algebra.Etale K A] [Algebra.Etale K B] [Algebra.Etale K C]

/-- The morphism `Spec B ⟶ Spec A` of the small étale site of `Spec K` induced by a morphism
`A →ₐ[K] B` of étale `K`-algebras. -/
noncomputable def etaleSpecMap (φ : A →ₐ[K] B) : etaleSpec K B ⟶ etaleSpec K A :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x)

lemma etaleSpecMap_comp (φ : A →ₐ[K] B) (ψ : B →ₐ[K] C) :
    etaleSpecMap ψ ≫ etaleSpecMap φ = etaleSpecMap (ψ.comp φ) := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The units of `A` are the sections of `𝔾ₘ` over `Spec A`. -/
noncomputable def gmSheafEtaleSpecEquiv (A : Type u) [CommRing A] [Algebra K A]
    [Algebra.Etale K A] :
    (Spec (.of K)).gmSheaf.obj.obj (op (etaleSpec K A)) ≃+ Additive Aˣ :=
  (show _ ≃+ Additive ((Spec (.of A)).presheaf.obj (op ⊤))ˣ from AddEquiv.ulift).trans
    (MulEquiv.toAdditive
    (Units.mapEquiv (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.toMulEquiv))

lemma gmSheafEtaleSpecEquiv_map (φ : A →ₐ[K] B)
    (x : (Spec (.of K)).gmSheaf.obj.obj (op (etaleSpec K A))) :
    gmSheafEtaleSpecEquiv B ((Spec (.of K)).gmSheaf.obj.map (etaleSpecMap φ).op x) =
      Additive.ofMul (Units.map φ.toMonoidHom (gmSheafEtaleSpecEquiv A x).toMul) := by
  apply Additive.toMul.injective
  ext
  have := congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom)) x.down.toMul.1)
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · rfl

/-- Every covering sieve of `Spec K` in the small étale site contains `Spec L` for some finite
separable field extension `L` of `K`. -/
lemma exists_etaleSpec_field_mem_of_mem_smallEtaleTopology (R : Sieve 𝟙ₑ)
    (hR : R ∈ (Spec (.of K)).smallEtaleTopology 𝟙ₑ) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.Etale K L)
      (f : etaleSpec K L ⟶ 𝟙ₑ), R.arrows f := by
  obtain ⟨𝒰, h𝒰, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1 hR
  obtain ⟨j, y, -⟩ := 𝒰.exists_eq (default : Spec (.of K))
  let 𝒱 := (𝒰.X j).affineOpenCover
  obtain ⟨z, -⟩ := 𝒱.covers y
  set k := 𝒱.idx y
  have hc : Etale (𝒱.f k ≫ (𝒰.X j ↘ Spec (.of K))) := by
    have := p j
    infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱.f k ≫ (𝒰.X j ↘ Spec (.of K)))
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @Etale)] at hc
  algebraize [φ.hom]
  have : Nontrivial (𝒱.X k) := (z : PrimeSpectrum (𝒱.X k)).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝒱.X k)
  let := Ideal.Quotient.field m
  have : Module.Finite K (𝒱.X k) := Algebra.FormallyUnramified.finite_of_free K _
  have : Algebra.FormallyEtale K (𝒱.X k ⧸ m) := Algebra.FormallyEtale.of_isSeparable K _
  have : Algebra.Etale K (𝒱.X k ⧸ m) :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  let g : etaleSpec K (𝒱.X k ⧸ m) ⟶ (𝒰.X j).asOverProp _ (p j) :=
    MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk m)) ≫ 𝒱.f k)
      (by
        change _ ≫ (𝒰.X j ↘ Spec (.of K)) = Spec.map _
        rw [Category.assoc, ← hφ, ← Spec.map_comp]
        rfl)
  have hmem : R.arrows ((𝒰.f j).asOverProp _) := hle _ _ (Presieve.ofArrows.mk j)
  exact ⟨_, _, _, _, _, R.downward_closed hmem g⟩

/-- A pair of morphisms `Z ⟶ Spec L` in the small étale site of `Spec K` factors through
`Spec (L ⊗_K L)`, the fibre product `Spec L ×_{Spec K} Spec L`. -/
lemma exists_comp_etaleSpecMap_includeLeft_eq {Z : (Spec (.of K)).Etale}
    (g₁ g₂ : Z ⟶ etaleSpec K A) :
    ∃ h : Z ⟶ etaleSpec K (A ⊗[K] A),
      h ≫ etaleSpecMap Algebra.TensorProduct.includeLeft = g₁ ∧
        h ≫ etaleSpecMap Algebra.TensorProduct.includeRight = g₂ := by
  have w : g₁.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
      g₂.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) :=
    (MorphismProperty.Over.w g₁).trans (MorphismProperty.Over.w g₂).symm
  have hfst : (pullbackSpecIso K A A).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft (R := K) (S := K)
        (A := A) (B := A)).toRingHom) = pullback.fst _ _ :=
    pullbackSpecIso_hom_fst K A A
  have hsnd : (pullbackSpecIso K A A).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := K)
        (A := A) (B := A)).toRingHom) = pullback.snd _ _ :=
    pullbackSpecIso_hom_snd K A A
  refine ⟨MorphismProperty.Over.homMk (pullback.lift _ _ w ≫ (pullbackSpecIso K A A).hom) ?_,
    ?_, ?_⟩
  · have : (etaleSpec K (A ⊗[K] A)).hom = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := A)).toRingHom) ≫
          (etaleSpec K A).hom := by
      change Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
    rw [this, Category.assoc, reassoc_of% hfst, ← Category.assoc, pullback.lift_fst]
    exact MorphismProperty.Over.w g₁
  · apply MorphismProperty.Over.Hom.ext
    change (_ ≫ _) ≫ Spec.map _ = _
    rw [Category.assoc, hfst, pullback.lift_fst]
  · apply MorphismProperty.Over.Hom.ext
    change (_ ≫ _) ≫ Spec.map _ = _
    rw [Category.assoc, hsnd, pullback.lift_snd]

section Descent

variable {E Q : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}}
  (ι : (Spec (.of K)).gmSheaf ⟶ E) (π : E ⟶ Q)

/-- **Gluing a lift along `Spec L → Spec K`.** Let `π : E ⟶ Q` be a morphism of abelian
sheaves on the small étale site of `Spec K`, let `q` be a global section of `Q` and let `e` be a
section of `E` over `Spec L`, for `L` a field étale over `K`, lifting the restriction of `q`. If
the pullbacks of `e` along any two morphisms `Z ⟶ Spec L` agree, then `e` descends to a global
section of `E` lifting `q`. -/
theorem exists_app_eq_of_compatible (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L]
    (f : etaleSpec K L ⟶ 𝟙ₑ) (q : Q.obj.obj (op 𝟙ₑ)) (e : E.obj.obj (op (etaleSpec K L)))
    (he : π.hom.app _ e = Q.obj.map f.op q)
    (hcompat : ∀ {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L),
      E.obj.map g₁.op e = E.obj.map g₂.op e) :
    ∃ x, π.hom.app (op 𝟙ₑ) x = q := by
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ f) ∈ (Spec (.of K)).smallEtaleTopology 𝟙ₑ := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), (default : Spec (.of L)), @Subsingleton.elim (Spec (.of K)) _ _ _⟩
  have hsheaf (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
      Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.singleton f) := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨x, hx, -⟩ := Presieve.isSheafFor_singleton.mp (hsheaf E) e
    (fun g₁ g₂ _ ↦ hcompat g₁ g₂)
  refine ⟨x, ?_⟩
  obtain ⟨y, -, hy⟩ := Presieve.isSheafFor_singleton.mp (hsheaf Q) (Q.obj.map f.op q)
    (fun g₁ g₂ _ ↦ by
      change Q.obj.map g₁.op (Q.obj.map f.op q) = Q.obj.map g₂.op (Q.obj.map f.op q)
      simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        hT.hom_ext (g₁ ≫ f) (g₂ ≫ f)])
  refine (hy _ ?_).trans (hy _ rfl).symm
  change Q.obj.map f.op (π.hom.app _ x) = _
  rw [← NatTrans.naturality_apply]
  have hx' : E.obj.map f.op x = e := hx
  rw [hx', he]

open Algebra.TensorProduct in
/-- **Descent of a lift along `Spec L → Spec K`.** Let `0 → 𝔾ₘ → E → Q` be exact on sections
over every étale `K`-scheme. If a global section `q` of `Q` lifts to a section `e` of `E` over
`Spec L`, for `L` a field étale over `K`, then `q` lifts to a global section of `E`. -/
theorem exists_app_eq_of_app_etaleSpec_eq (hιπ : ι ≫ π = 0)
    (hι : ∀ U, Function.Injective (ι.hom.app U))
    (hexact : ∀ U (x : E.obj.obj U), π.hom.app U x = 0 → ∃ g, ι.hom.app U g = x)
    (L : Type u) [Field L] [Algebra K L] [Algebra.Etale K L] (f : etaleSpec K L ⟶ 𝟙ₑ)
    (q : Q.obj.obj (op 𝟙ₑ)) (e : E.obj.obj (op (etaleSpec K L)))
    (he : π.hom.app _ e = Q.obj.map f.op q) :
    ∃ x, π.hom.app (op 𝟙ₑ) x = q := by
  have hT := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K))
  have hιπ' (U) (g) : π.hom.app U (ι.hom.app U g) = 0 := by
    have := congr_arg (fun φ ↦ φ.hom.app U g) hιπ
    simpa using this
  -- the difference of two pullbacks of `e` is a section of `𝔾ₘ`
  have hπ {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      π.hom.app _ (E.obj.map g₁.op e - E.obj.map g₂.op e) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, hT.hom_ext (g₁ ≫ f) (g₂ ≫ f), sub_self]
  choose c hc using fun (Z : (Spec (.of K)).Etale) (g₁ g₂ : Z ⟶ etaleSpec K L) ↦
    hexact _ _ (hπ g₁ g₂)
  have hc_map {Z Z' : (Spec (.of K)).Etale} (h : Z' ⟶ Z) (g₁ g₂ : Z ⟶ etaleSpec K L) :
      (Spec (.of K)).gmSheaf.obj.map h.op (c Z g₁ g₂) = c Z' (h ≫ g₁) (h ≫ g₂) := by
    apply hι
    rw [NatTrans.naturality_apply, hc, hc, map_sub, ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp, ← op_comp,
      ← op_comp]
  have hc_add {Z : (Spec (.of K)).Etale} (g₁ g₂ g₃ : Z ⟶ etaleSpec K L) :
      c Z g₁ g₃ = c Z g₁ g₂ + c Z g₂ g₃ := by
    apply hι
    rw [map_add, hc, hc, hc]
    abel
  -- the Čech cocycle on `Spec (L ⊗_K L)` and its cocycle identity on `Spec (L ⊗_K L ⊗_K L)`
  let i₁ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeLeft
  let i₂ : etaleSpec K (L ⊗[K] L) ⟶ etaleSpec K L := etaleSpecMap includeRight
  let d₁₂ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) := map (AlgHom.id K L) includeLeft
  let d₁₃ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) := map (AlgHom.id K L) includeRight
  let d₂₃ : L ⊗[K] L →ₐ[K] L ⊗[K] (L ⊗[K] L) := includeRight
  let c₀ := c _ i₁ i₂
  let u : (L ⊗[K] L)ˣ := (gmSheafEtaleSpecEquiv _ c₀).toMul
  have h₁ : etaleSpecMap d₁₂ ≫ i₁ = etaleSpecMap d₁₃ ≫ i₁ := by
    simp only [i₁, etaleSpecMap_comp]
    congr 1
  have h₂ : etaleSpecMap d₁₂ ≫ i₂ = etaleSpecMap d₂₃ ≫ i₁ := by
    simp only [i₁, i₂, etaleSpecMap_comp]
    congr 1
  have h₃ : etaleSpecMap d₁₃ ≫ i₂ = etaleSpecMap d₂₃ ≫ i₂ := by
    simp only [i₂, etaleSpecMap_comp]
    congr 1
  have hcoc : (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₁₃).op c₀ =
      (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₁₂).op c₀ +
        (Spec (.of K)).gmSheaf.obj.map (etaleSpecMap d₂₃).op c₀ := by
    rw [hc_map, hc_map, hc_map, ← h₁, h₂, ← h₃]
    exact hc_add _ _ _
  have hu : d₁₃ (u : L ⊗[K] L) = d₁₂ (u : L ⊗[K] L) * d₂₃ (u : L ⊗[K] L) := by
    have := congr_arg (fun x ↦ ((gmSheafEtaleSpecEquiv _ x).toMul : L ⊗[K] (L ⊗[K] L))) hcoc
    simpa [gmSheafEtaleSpecEquiv_map, u] using this
  obtain ⟨v, hv⟩ := exists_eq_of_cocycle u hu
  -- correct `e` by the unit `v`
  let w := (gmSheafEtaleSpecEquiv (K := K) L).symm (Additive.ofMul v)
  let e' := e + ι.hom.app _ w
  have he' : π.hom.app _ e' = π.hom.app _ e := by simp [e', hιπ']
  have hw : c₀ + (Spec (.of K)).gmSheaf.obj.map i₁.op w -
      (Spec (.of K)).gmSheaf.obj.map i₂.op w = 0 := by
    have hu' : u = Units.map (includeRight : L →ₐ[K] L ⊗[K] L).toMonoidHom v *
        (Units.map (includeLeft : L →ₐ[K] L ⊗[K] L).toMonoidHom v)⁻¹ :=
      Units.ext (by rw [hv]; simp)
    apply (gmSheafEtaleSpecEquiv (L ⊗[K] L)).injective
    rw [map_zero, map_sub, map_add, gmSheafEtaleSpecEquiv_map, gmSheafEtaleSpecEquiv_map]
    apply Additive.toMul.injective
    change u * _ / _ = 1
    rw [hu']
    simp [w]
  have hcompat {Z : (Spec (.of K)).Etale} (g₁ g₂ : Z ⟶ etaleSpec K L) :
      E.obj.map g₁.op e' = E.obj.map g₂.op e' := by
    obtain ⟨h, rfl, rfl⟩ := exists_comp_etaleSpecMap_includeLeft_eq g₁ g₂
    have : E.obj.map i₁.op e' = E.obj.map i₂.op e' := by
      rw [← sub_eq_zero]
      simp only [e', map_add, ← NatTrans.naturality_apply]
      rw [show ∀ a b c d : E.obj.obj (op (etaleSpec K (L ⊗[K] L))),
        a + b - (c + d) = (a - c) + b - d from fun _ _ _ _ ↦ by abel, ← hc, ← map_add,
        ← map_sub, hw, map_zero]
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact congr_arg _ this
  exact exists_app_eq_of_compatible π L f q e' (he'.trans he) hcompat

/-- **Every `𝔾ₘ`-torsor on `Spec K` is trivial.** For a short exact sequence
`0 → 𝔾ₘ → E → Q → 0` of abelian sheaves on the small étale site of the spectrum of a field `K`,
every global section of `Q` lifts to `E`. -/
theorem surjective_app_of_shortExact_gmSheaf (w : ι ≫ π = 0)
    (hS : (ShortComplex.mk ι π w).ShortExact) : Function.Surjective (π.hom.app (op 𝟙ₑ)) := by
  have := hS.mono_f
  have := hS.epi_g
  have (U : (Spec (.of K)).Etaleᵒᵖ) : PreservesLimits
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) :=
    inferInstanceAs (PreservesLimits (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U))
  have hι (U) : Function.Injective (ι.hom.app U) :=
    (AddCommGrpCat.mono_iff_injective _).1
      (((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U).map_mono ι)
  have hexact (U) (x : E.obj.obj U) (hx : π.hom.app U x = 0) : ∃ g, ι.hom.app U g = x :=
    (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      ((sheafSections (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}).obj U)
      hS.mono_f inferInstance) x hx
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  intro q
  obtain ⟨L, _, _, _, f, e, he⟩ := exists_etaleSpec_field_mem_of_mem_smallEtaleTopology _
    (Presheaf.imageSieve_mem (Spec (.of K)).smallEtaleTopology π.hom (U := op 𝟙ₑ) q)
  exact exists_app_eq_of_app_etaleSpec_eq ι π w hι hexact L f q e he

end Descent

/-- **Hilbert 90** for a field: the cohomological Picard group `H¹(Spec K_ét, 𝔾ₘ)` of the
spectrum of a field vanishes. -/
instance subsingleton_cohomologicalPicardGroup_of_field (K : Type u) [Field K] :
    Subsingleton (Spec (.of K)).CohomologicalPicardGroup :=
  Sheaf.subsingleton_H_one_of_surjective _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of K)))
    (fun _ _ ι π w hS ↦ surjective_app_of_shortExact_gmSheaf ι π w hS)

end AlgebraicGeometry.Scheme
