/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.GlobalSections
public import WeilConjectures.CategoryTheory.Sites.CechBaseChange
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# The additive group on the small étale site

The étale sheaf `𝔾ₐ` on a scheme `X` sends an étale `X`-scheme `U` to the additive group of
`Γ(U, 𝒪_U)`. On an affine scheme it has no higher cohomology: every étale covering of an affine
étale `X`-scheme `V = Spec A` is refined by a finite family of affine étale `V`-schemes
`Uₐ = Spec Bₐ`, whose Čech complex with values in `𝔾ₐ` is the Amitsur-type complex
`k ↦ ∏_y B_{y 0} ⊗_A ⋯ ⊗_A B_{y k}`. It is exact in positive degrees because it becomes
contractible after the faithfully flat base change `A → ∏ₐ Bₐ`
(`CategoryTheory.Presheaf.exactAt_cechComplex_of_baseChange`), and the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` concludes.

## Main definitions

- `AlgebraicGeometry.Scheme.gaSheaf`: the sheaf `𝔾ₐ` on the small étale site.

## Main statements

- `AlgebraicGeometry.Scheme.subsingleton_sheafH_gaSheaf_of_isAffine`: `Hᵠ(X_ét, 𝔾ₐ) = 0` for
  `q > 0` and `X` affine.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- The presheaf `𝔾ₐ` on the small étale site of `X`: an étale `X`-scheme `U` is sent to the
additive group of `Γ(U, 𝒪_U)`, lifted to the next universe. -/
noncomputable def gaPresheaf : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  X.etaleStructurePresheaf ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

set_option backward.isDefEq.respectTransparency.types false in
open Pseudofunctor.LocallyDiscreteOpToCat Modules in
/-- The underlying presheaf of sets of `V ↦ Γ(V, 𝒪_V)` is a sheaf on the small étale site:
`a ↦ a ·` identifies it with the étale sheaf `V ↦ End(V^* 𝒪_X)`. -/
theorem isSheaf_etaleStructurePresheaf_comp_forget :
    Presieve.IsSheaf X.smallEtaleTopology
      (X.etaleStructurePresheaf ⋙ CategoryTheory.forget CommRingCat) := by
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.isSheaf_etaleStructurePresheaf)

/-- The presheaf `𝔾ₐ` is a sheaf for the small étale topology. -/
theorem isSheaf_gaPresheaf : Presheaf.IsSheaf X.smallEtaleTopology X.gaPresheaf := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat.{u + 1}),
    isSheaf_iff_isSheaf_of_type]
  exact (Presieve.isSheaf_iff_of_nat_equiv (fun _ ↦ Equiv.ulift.symm) (fun _ _ _ _ ↦ rfl)).1
    X.isSheaf_etaleStructurePresheaf_comp_forget

/-- The sheaf `𝔾ₐ` on the small étale site of `X`: the structure sheaf, as a sheaf of abelian
groups. It is the étale sheaf `𝒪_{X, ét}` attached to the quasi-coherent module `𝒪_X`. -/
noncomputable def gaSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨X.gaPresheaf, X.isSheaf_gaPresheaf⟩

variable {X}

/-- Restriction in `𝔾ₐ` along a map `g` of étale `X`-schemes is pullback of functions along
`g`. -/
lemma gaPresheaf_map_apply {U V : X.Etale} (g : V ⟶ U) (x : X.gaPresheaf.obj (op U)) :
    (X.gaPresheaf.map g.op x).down = g.left.appTop x.down :=
  rfl


/-! ### The Čech complexes of `𝔾ₐ` on affine families -/

section Cech

variable {V : X.Etale}

/-- The ring `Γ(W, 𝒪)` of an object `W` of `Over V`, as a `Γ(V, 𝒪)`-algebra. -/
def OverΓ (W : Over V) : Type u := Γ(W.left.left, ⊤)

instance (W : Over V) : CommRing (OverΓ W) := inferInstanceAs (CommRing Γ(W.left.left, ⊤))

instance (W : Over V) : Algebra Γ(V.left, ⊤) (OverΓ W) := (W.hom.left.appTop).hom.toAlgebra

/-- The pullback `Γ(W', 𝒪) → Γ(W, 𝒪)` along a morphism `W ⟶ W'` of `Over V`, as an algebra
map. -/
noncomputable def overΓMap {W W' : Over V} (f : W ⟶ W') :
    OverΓ W' →ₐ[Γ(V.left, ⊤)] OverΓ W where
  toRingHom := f.left.left.appTop.hom
  commutes' r := by
    change f.left.left.appTop (W'.hom.left.appTop r) = W.hom.left.appTop r
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    congr 3
    exact congrArg (fun g ↦ g.left) (Over.w f)

lemma overΓMap_apply {W W' : Over V} (f : W ⟶ W') (s : OverΓ W') :
    overΓMap f s = f.left.left.appTop s :=
  rfl


lemma overΓMap_comp {W W' W'' : Over V} (f : W ⟶ W') (g : W' ⟶ W'') (s : OverΓ W'') :
    overΓMap (f ≫ g) s = overΓMap f (overΓMap g s) := by
  change (f.left.left ≫ g.left.left).appTop s = _
  rw [Scheme.Hom.comp_appTop]
  rfl

lemma overΓMap_eq_of_eq {W W' : Over V} {f g : W ⟶ W'} (h : f.left.left = g.left.left)
    (s : OverΓ W') : overΓMap f s = overΓMap g s := by
  rw [overΓMap_apply, overΓMap_apply, h]


variable (V) in
/-- The presheaf `W ↦ Γ(W, 𝒪)` of `Γ(V, 𝒪)`-modules on `Over V`. -/
noncomputable def gaModulePresheaf : (Over V)ᵒᵖ ⥤ ModuleCat.{u} Γ(V.left, ⊤) where
  obj W := ModuleCat.of Γ(V.left, ⊤) (OverΓ W.unop)
  map f := ModuleCat.ofHom (overΓMap f.unop).toLinearMap
  map_id W := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    change (𝟙 W.unop.left.left : _ ⟶ _).appTop s = s
    simp
  map_comp f g := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
    exact overΓMap_comp g.unop f.unop s

lemma gaModulePresheaf_map_apply {W W' : Over V} (f : W ⟶ W')
    (s : (gaModulePresheaf V).obj (op W')) :
    (gaModulePresheaf V).map f.op s = overΓMap f s :=
  rfl


/-- The sections of `𝔾ₐ` over `W` are the module `Γ(W, 𝒪)`. -/
noncomputable def gaPresheafAddEquiv (W : Over V) :
    X.gaPresheaf.obj (op W.left) ≃+ (gaModulePresheaf V).obj (op W) :=
  (AddEquiv.ulift : ULift.{u + 1} (OverΓ W) ≃+ OverΓ W)

lemma gaPresheafAddEquiv_naturality {W W' : Over V} (f : W ⟶ W')
    (s : X.gaPresheaf.obj (op W'.left)) :
    gaPresheafAddEquiv W (X.gaPresheaf.map f.left.op s) =
      (gaModulePresheaf V).map f.op (gaPresheafAddEquiv W' s) :=
  rfl

/-- The base change map `Γ(W, 𝒪) ⊗_{Γ(V, 𝒪)} Γ(T, 𝒪) → Γ(W ×_V T, 𝒪)`,
`s ⊗ b ↦ pr₁^* s · pr₂^* b`. -/
noncomputable def gaBaseChange (W T : Over V) :
    OverΓ W ⊗[Γ(V.left, ⊤)] OverΓ T →ₐ[Γ(V.left, ⊤)] OverΓ (W ⨯ T) :=
  Algebra.TensorProduct.productMap (overΓMap prod.fst) (overΓMap prod.snd)

lemma gaBaseChange_tmul (W T : Over V) (s : OverΓ W) (b : OverΓ T) :
    gaBaseChange W T (s ⊗ₜ b) = overΓMap prod.fst s * overΓMap prod.snd b := by
  simp [gaBaseChange]

lemma gaBaseChange_naturality {W W' : Over V} (T : Over V) (f : W ⟶ W')
    (s : OverΓ W') (b : OverΓ T) :
    gaBaseChange W T (overΓMap f s ⊗ₜ b) =
      overΓMap (prod.map f (𝟙 T)) (gaBaseChange W' T (s ⊗ₜ b)) := by
  rw [gaBaseChange_tmul, gaBaseChange_tmul, map_mul, ← overΓMap_comp, ← overΓMap_comp,
    ← overΓMap_comp]
  congr 1
  · exact congrArg (overΓMap · s) (prod.map_fst f (𝟙 T)).symm
  · exact congrArg (overΓMap · b) ((prod.map_snd f (𝟙 T)).trans (Category.comp_id _)).symm

/-- A binary product in `Over V` of étale `X`-schemes is a fibre product of the underlying
schemes over `V`. -/
lemma isPullback_prod_left_left (W T : Over V) :
    IsPullback (prod.fst : W ⨯ T ⟶ W).left.left (prod.snd : W ⨯ T ⟶ T).left.left
      W.hom.left T.hom.left := by
  have h : IsPullback (prod.fst : W ⨯ T ⟶ W).left (prod.snd : W ⨯ T ⟶ T).left W.hom T.hom :=
    IsPullback.of_iso_pullback ⟨by rw [Over.w, Over.w]⟩ (Over.prodLeftIsoPullback W T)
      (Over.prodLeftIsoPullback_hom_fst W T) (Over.prodLeftIsoPullback_hom_snd W T)
  exact h.map (Etale.forget X ⋙ Over.forget X)

/-- The base change map `Γ(W, 𝒪) ⊗_{Γ(V, 𝒪)} Γ(T, 𝒪) → Γ(W ×_V T, 𝒪)` is bijective for affine
`V`, `W` and `T`. -/
lemma bijective_gaBaseChange (W T : Over V) [IsAffine V.left] [IsAffine W.left.left]
    [IsAffine T.left.left] : Function.Bijective (gaBaseChange W T) := by
  have h := (isPushout_appTop_of_isPullback (isPullback_prod_left_left W T)).flip
  let : Algebra Γ(V.left, ⊤) Γ(W.left.left, ⊤) := inferInstanceAs (Algebra _ (OverΓ W))
  let : Algebra Γ(V.left, ⊤) Γ(T.left.left, ⊤) := inferInstanceAs (Algebra _ (OverΓ T))
  let e := h.tensorEquiv rfl rfl
  have he : ∀ t : OverΓ W ⊗[Γ(V.left, ⊤)] OverΓ T, gaBaseChange W T t = e t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s b =>
      rw [gaBaseChange_tmul]
      exact (h.tensorEquiv_tmul rfl rfl s b).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : (gaBaseChange W T : OverΓ W ⊗[Γ(V.left, ⊤)] OverΓ T → OverΓ (W ⨯ T)) = e :=
    funext he
  rw [this]
  exact e.bijective

/-- A finite product in `Over V` of étale `X`-schemes with affine underlying schemes has affine
underlying scheme, if `V` has. -/
lemma isAffine_piObj [IsAffine V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, IsAffine (U j).left.left) : IsAffine (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦ IsAffine A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B := by
    have : IsAffine A.left.left := h
    have : IsIso e.inv.left.left :=
      inferInstanceAs (IsIso ((Over.forget V ⋙ Etale.forget X ⋙ Over.forget X).map e.inv))
    exact IsAffine.of_isIso e.inv.left.left
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) (inferInstanceAs (IsAffine V.left))⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    have : IsAffine (h.diag.obj ⟨.left⟩).left.left := h.prop_diag_obj ⟨.left⟩
    have : IsAffine (h.diag.obj ⟨.right⟩).left.left := h.prop_diag_obj ⟨.right⟩
    exact IsAffine.of_isPullback (isPullback_prod_left_left _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

/-- The members of the Čech nerve of a family of étale `X`-schemes with affine underlying
schemes over an affine `V` have affine underlying schemes. -/
lemma isAffine_cechNerveObj [IsAffine V.left] {ι : Type*} (U : ι → Over V)
    (hU : ∀ a, IsAffine (U a).left.left) {k : ℕ} (y : Fin (k + 1) → ι) :
    IsAffine (Presheaf.cechNerveObj U y).left.left :=
  isAffine_piObj _ fun l ↦ hU (y l)

lemma etale_hom_left {A B : X.Etale} (f : A ⟶ B) : Etale f.left :=
  MorphismProperty.of_postcomp @Etale f.left B.hom B.prop (by simp [A.prop])

/-- For a finite jointly surjective family of étale morphisms `Uₐ ⟶ V` of affine schemes,
`∏ₐ Γ(Uₐ, 𝒪)` is faithfully flat over `Γ(V, 𝒪)`. -/
lemma faithfullyFlat_pi_overΓ [IsAffine V.left] {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ a, IsAffine (U a).left.left)
    (hsurj : ⋃ a, Set.range (U a).hom.left = Set.univ) :
    Module.FaithfullyFlat Γ(V.left, ⊤) (∀ a, OverΓ (U a)) := by
  have hflat (a : Fin n) : Module.Flat Γ(V.left, ⊤) (OverΓ (U a)) := by
    have := etale_hom_left (U a).hom
    exact (U a).hom.left.flat_appTop
  have : Module.Flat Γ(V.left, ⊤) (∀ a, OverΓ (U a)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype Γ(V.left, ⊤) (Fin n)
      fun a ↦ OverΓ (U a)).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun P ↦ ?_
  have hP : V.left.isoSpec.inv P ∈ ⋃ a, Set.range (U a).hom.left := by
    rw [hsurj]
    trivial
  obtain ⟨a, u, hu⟩ := Set.mem_iUnion.1 hP
  let Q := (U a).left.left.isoSpec.hom u
  have hQ : PrimeSpectrum.comap (U a).hom.left.appTop.hom Q = P := by
    have h := congrArg (fun f ↦ f u) (Scheme.isoSpec_hom_naturality (U a).hom.left)
    simp only [Scheme.Hom.comp_apply, hu] at h
    have e : V.left.isoSpec.hom (V.left.isoSpec.inv P) = P := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [e] at h
    exact h
  refine ⟨⟨Ideal.comap (Pi.evalRingHom (fun a ↦ OverΓ (U a)) a) Q.asIdeal, inferInstance⟩, ?_⟩
  ext1
  change Ideal.comap _ (Ideal.comap _ _) = _
  rw [Ideal.comap_comap]
  exact congrArg PrimeSpectrum.asIdeal hQ

/-- **Čech complexes of `𝔾ₐ` on affine families are exact.** Let `V` be an étale `X`-scheme
with affine underlying scheme and `U` a finite covering family of `V` whose Čech nerve consists
of affine schemes. Then the Čech complex of `𝔾ₐ` on `U` is exact in positive degrees. -/
theorem exactAt_cechComplex_gaPresheaf [IsAffine V.left] {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), IsAffine (Presheaf.cechNerveObj U y).left.left)
    (hcov : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V)
    (q : ℕ) : ((Presheaf.cechComplex U).obj X.gaPresheaf).ExactAt (q + 1) := by
  have hUa (a : Fin n) : IsAffine (U a).left.left := by
    have := hU 0 (fun _ ↦ a)
    have : IsIso (Pi.π (fun _ : Fin 1 ↦ U a) 0).left.left := by
      have h : Pi.π (fun _ : Fin 1 ↦ U a) 0 = (productUniqueIso _).hom :=
        (productUniqueIso_hom _).symm
      rw [h]
      exact inferInstanceAs
        (IsIso ((Over.forget V ⋙ Etale.forget X ⋙ Over.forget X).map (productUniqueIso _).hom))
    exact IsAffine.of_isIso (inv (Pi.π (fun _ : Fin 1 ↦ U a) 0).left.left)
  have hsurj := (ofArrows_mem_smallEtaleTopology_iff (fun a ↦ (U a).hom)).1 hcov
  have := faithfullyFlat_pi_overΓ U hUa hsurj
  exact Presheaf.exactAt_cechComplex_of_baseChange U (gaModulePresheaf V) X.gaPresheaf
    (fun y ↦ gaPresheafAddEquiv _) (fun y θ s ↦ gaPresheafAddEquiv_naturality _ s)
    (fun a ↦ OverΓ (U a))
    (fun a W ↦ (gaBaseChange W (U a)).toAddMonoidHom)
    (fun a W W' f s b ↦ gaBaseChange_naturality (U a) f s b)
    (fun a k y ↦ by
      have := hU k y
      exact bijective_gaBaseChange _ _) q

end Cech

/-- **`𝔾ₐ` is acyclic on affine schemes.** For an affine scheme `X` and `q > 0`,
`Hᵠ(X_ét, 𝔾ₐ) = 0`. Every étale covering of an affine étale `X`-scheme is refined by a finite
family of affine étale schemes, whose Čech nerve consists of affine schemes, and on such
families the Čech complex of `𝔾ₐ` is exact in positive degrees
(`AlgebraicGeometry.Scheme.exactAt_cechComplex_gaPresheaf`); the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` concludes. -/
theorem subsingleton_sheafH_gaSheaf_of_isAffine (X : Scheme.{u}) [IsAffine X] (q : ℕ) :
    Subsingleton (Sheaf.H X.gaSheaf (q + 1)) := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let B : X.Etale → Prop := fun W ↦ IsAffine W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
        (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    have : IsAffine V.left := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
    exact ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ isAffine_cechNerveObj _ hU y, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    (inferInstanceAs (IsAffine X)) hcov X.gaSheaf
    (fun V hV n U hU hUJ q ↦
      have : IsAffine V.left := hV
      exactAt_cechComplex_gaPresheaf U hU hUJ q) q

end AlgebraicGeometry.Scheme
