/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Tor amplitude is tested on the residue field

Let `C` be a closed braided monoidal Grothendieck abelian category with functorial flat
resolutions, linear over a commutative ring `R` compatibly with the tensor product, and let
`ϖ ∈ R` be nilpotent. Put `κ = 𝟙 / ϖ` (the cokernel of `ϖ` on the unit). Assume that tensoring
with an object killed by `ϖ` preserves monomorphisms between objects killed by `ϖ`: this is
the flatness of all modules over the field `R / ϖ` when `C` is a category of sheaves of
`R`-modules and `R / ϖ` is a field.

Then an object `K` of the derived category `D(C)` has Tor amplitude in `[a, b]` exactly when
`K ⊗ᴸ κ` has homology concentrated in `[a, b]`
(`DerivedCategory.torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor`).

For `F` killed by `ϖ`, represent `K` by a K-flat complex `P`: then `K ⊗ᴸ F` is `P ⊗ F`, which is
`(P ⊗ κ) ⊗ F` because `κ ⊗ F ≅ F`, and tensoring with `F` preserves the exactness of the
complex `P ⊗ κ` of objects killed by `ϖ`
(`ShortComplex.Exact.map_tensorRight_of_smul_eq_zero`). A general `F` has the finite
filtration by the `ϖ^s F`, whose graded pieces are killed by `ϖ`.

This is the categorical core of blueprint `lemma-bounds-finite-reductions--2`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]
  {R : Type*} [CommRing R] [Linear R C] [MonoidalLinear R C]

omit [Abelian C] [MonoidalPreadditive C] [Linear R C] [MonoidalLinear R C] in
/-- Tensoring on the right with an object preserves finite colimits in a closed braided
monoidal category: it is isomorphic, through the braiding, to tensoring on the left, which is a
left adjoint. -/
lemma preservesFiniteColimits_tensorRight (F : C) : PreservesFiniteColimits (tensorRight F) :=
  preservesFiniteColimits_of_natIso (F := tensorLeft F)
    (NatIso.ofComponents (fun Y ↦ β_ F Y) (by intros; simp))

omit [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [MonoidalLinear R C] in
/-- The image of a morphism into an object killed by `r` is killed by `r`. -/
lemma smul_id_image_eq_zero (r : R) {X Y : C} (g : X ⟶ Y) (hY : r • 𝟙 Y = 0) :
    r • 𝟙 (image g) = 0 := by
  have h : factorThruImage g ≫ (r • 𝟙 (image g)) ≫ image.ι g = 0 := by
    rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, image.fac, ← Category.comp_id g,
      ← Linear.comp_smul, hY, comp_zero]
  refine (cancel_mono (image.ι g)).1 ((cancel_epi (factorThruImage g)).1 ?_)
  rw [zero_comp, comp_zero]
  exact h

omit [MonoidalLinear R C] in
/-- **Exactness of `- ⊗ F` on objects killed by `r`.** Let `F` be killed by `r`, and assume that
`- ⊗ F` preserves monomorphisms between objects killed by `r`. Then `- ⊗ F` preserves the
exactness of a short complex `S` of objects killed by `r`.

Factor `S.g` through its image `I`, which is killed by `r`. The short complex
`S.X₁ ⟶ S.X₂ ⟶ I` is right exact, and `- ⊗ F` is right exact; and `I ⊗ F ⟶ S.X₃ ⊗ F` is a
monomorphism. -/
lemma ShortComplex.Exact.map_tensorRight_of_smul_eq_zero (r : R) {F : C}
    (hmono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], r • 𝟙 X = 0 → r • 𝟙 Y = 0 →
      Mono (f ▷ F))
    {S : ShortComplex C} (hS : S.Exact) (h₃ : r • 𝟙 S.X₃ = 0) :
    (S.map (tensorRight F)).Exact := by
  have := preservesFiniteColimits_tensorRight F
  let S' : ShortComplex C := ShortComplex.mk S.f (factorThruImage S.g)
    ((cancel_mono (image.ι S.g)).1 (by simp))
  let φ : S' ⟶ S := { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := image.ι S.g }
  have hS' : S'.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 hS
  have hS'F : (S'.map (tensorRight F)).Exact :=
    hS'.map_of_epi_of_preservesCokernel _ (inferInstanceAs (Epi (factorThruImage S.g)))
      inferInstance
  let ψ := (tensorRight F).mapShortComplex.map φ
  have : IsIso ψ.τ₁ := inferInstanceAs (IsIso ((tensorRight F).map (𝟙 _)))
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso ((tensorRight F).map (𝟙 _)))
  have : Mono ψ.τ₃ := hmono (image.ι S.g) (smul_id_image_eq_zero r S.g h₃) h₃
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).1 hS'F

omit [MonoidalLinear R C] in
/-- **Exactness of `- ⊗ F` on complexes of objects killed by `r`.** In the situation of
`CategoryTheory.ShortComplex.Exact.map_tensorRight_of_smul_eq_zero`, tensoring with `F`
preserves the exactness in a given degree of a complex of objects killed by `r`. -/
lemma HomologicalComplex.ExactAt.map_tensorRight_of_smul_eq_zero (r : R) {F : C}
    (hmono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], r • 𝟙 X = 0 → r • 𝟙 Y = 0 →
      Mono (f ▷ F))
    {P : CochainComplex C ℤ} (hP : ∀ n, r • 𝟙 (P.X n) = 0) {i : ℤ} (h : P.ExactAt i) :
    (((tensorRight F).mapHomologicalComplex _).obj P).ExactAt i :=
  ShortComplex.Exact.map_tensorRight_of_smul_eq_zero r hmono h (hP _)

omit [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [MonoidalLinear R C] in
/-- An object isomorphic to the cokernel of `r` on the unit is killed by `r`. -/
lemma smul_id_eq_zero_of_iso_cokernel (r : R) {κ : C} (eκ : κ ≅ cokernel (r • 𝟙 (𝟙_ C))) :
    r • 𝟙 κ = 0 := by
  have : r • 𝟙 (cokernel (r • 𝟙 (𝟙_ C))) = 0 := by
    refine (cancel_epi (cokernel.π (r • 𝟙 (𝟙_ C)))).1 ?_
    rw [comp_zero, Linear.comp_smul, Category.comp_id, ← Category.id_comp (cokernel.π _),
      ← Linear.smul_comp, cokernel.condition]
  calc r • 𝟙 κ = eκ.hom ≫ (r • 𝟙 _) ≫ eκ.inv := by simp
    _ = 0 := by rw [this]; simp

/-- If `κ` is the cokernel of `r` on the unit, then `κ ⊗ F ≅ F` for every object `F` killed by
`r`: tensoring is right exact, so `κ ⊗ F` is the cokernel of `r` on `𝟙 ⊗ F ≅ F`, which is
zero. -/
noncomputable def tensorIsoOfSmulEqZero (r : R) {κ : C} (eκ : κ ≅ cokernel (r • 𝟙 (𝟙_ C)))
    {F : C} (hF : r • 𝟙 F = 0) : κ ⊗ F ≅ F :=
  have := preservesFiniteColimits_tensorRight F
  have h : (tensorRight F).map (r • 𝟙 (𝟙_ C)) = 0 := by
    change (r • 𝟙 (𝟙_ C)) ▷ F = 0
    rw [MonoidalLinear.smul_whiskerRight, id_whiskerRight, ← MonoidalCategory.whiskerLeft_id,
      ← MonoidalLinear.whiskerLeft_smul, hF, MonoidalPreadditive.whiskerLeft_zero]
  (tensorRight F).mapIso eκ ≪≫ PreservesCokernel.iso (tensorRight F) _ ≪≫
    cokernelIsoOfEq h ≪≫ cokernelZeroIsoTarget ≪≫ λ_ F

end CategoryTheory

namespace DerivedCategory

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C]
  {R : Type*} [CommRing R] [Linear R C] [MonoidalLinear R C]

variable [IsGrothendieckAbelian.{v} C] [HasDerivedCategory.{v} C]
  [Abelian.HasFunctorialFlatResolution C]

/-- **The residue test for objects killed by `r`.** Let `κ` and `F` be killed by `r`, with
`κ ⊗ F ≅ F`, and assume that tensoring with `F` preserves monomorphisms between objects killed
by `r`. If `K ⊗ᴸ κ` has homology concentrated in `[a, b]`, so has `K ⊗ᴸ F`.

Represent `K` by a K-flat complex `P` of flat objects. Then `K ⊗ᴸ F` is `P ⊗ F ≅ (P ⊗ κ) ⊗ F`,
and `P ⊗ κ`, which computes `K ⊗ᴸ κ`, is a complex of objects killed by `r`, exact outside
`[a, b]`; tensoring with `F` preserves this exactness
(`CategoryTheory.HomologicalComplex.ExactAt.map_tensorRight_of_smul_eq_zero`). -/
lemma homologyConcentratedIn_tensor_singleFunctor_of_smul_eq_zero (r : R) {κ F : C}
    (hκ : r • 𝟙 κ = 0) (e : κ ⊗ F ≅ F)
    (hmono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], r • 𝟙 X = 0 → r • 𝟙 Y = 0 →
      Mono (f ▷ F))
    {a b : ℤ} {K : DerivedCategory C}
    (hK : homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj κ)) :
    homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj F) := by
  obtain ⟨P, π, hπ, -, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage K)
  let eP : Q.obj P ≅ K := asIso (Q.map π) ≪≫ Q.objObjPreimageIso K
  let Pκ := ((tensorRight κ).mapHomologicalComplex (.up ℤ)).obj P
  have hPκ : ∀ n, r • 𝟙 (Pκ.X n) = 0 := fun n ↦ by
    change r • 𝟙 (P.X n ⊗ κ) = 0
    rw [← MonoidalCategory.whiskerLeft_id, ← MonoidalLinear.whiskerLeft_smul, hκ,
      MonoidalPreadditive.whiskerLeft_zero]
  have h₁ : homologyConcentratedIn a b (Q.obj Pκ) :=
    (homologyConcentratedIn a b).prop_of_iso
      (whiskerRightIso eP.symm _ ≪≫ QObjTensorSingleFunctorObjIso P hP κ) hK
  rw [homologyConcentratedIn_iff, ← DerivedCategory.IsGE, ← DerivedCategory.IsLE,
    isGE_Q_obj_iff, isLE_Q_obj_iff, CochainComplex.isGE_iff, CochainComplex.isLE_iff] at h₁
  let e' : ((tensorRight κ).mapHomologicalComplex (.up ℤ) ⋙
      (tensorRight F).mapHomologicalComplex (.up ℤ)).obj P ≅
      ((tensorRight F).mapHomologicalComplex (.up ℤ)).obj P :=
    (Functor.mapHomologicalComplexCompIso (NatIso.ofComponents (F := tensorRight κ ⋙ tensorRight F)
      (G := tensorRight F)
      (fun X ↦ α_ X κ F ≪≫ whiskerLeftIso X e) (fun f ↦ by simp [whisker_exchange])) _).app P
  refine (homologyConcentratedIn a b).prop_of_iso
    (Q.mapIso e' ≪≫ (QObjTensorSingleFunctorObjIso P hP F).symm ≪≫ whiskerRightIso eP _) ?_
  let G := ((tensorRight F).mapHomologicalComplex (.up ℤ)).obj Pκ
  have : CochainComplex.IsGE G a := (CochainComplex.isGE_iff G a).2 fun i hi ↦
    HomologicalComplex.ExactAt.map_tensorRight_of_smul_eq_zero r hmono hPκ (h₁.1 i hi)
  have : CochainComplex.IsLE G b := (CochainComplex.isLE_iff G b).2 fun i hi ↦
    HomologicalComplex.ExactAt.map_tensorRight_of_smul_eq_zero r hmono hPκ (h₁.2 i hi)
  exact ⟨inferInstanceAs ((Q.obj G).IsGE a), inferInstanceAs ((Q.obj G).IsLE b)⟩

omit [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [MonoidalLinear R C] [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
/-- An object killed by `r ^ (m + 1)` is an extension of an object killed by `r` (the cokernel
of the image of `r`) by an object killed by `r ^ m` (the image of `r`). -/
lemma exists_shortExact_of_smul_pow_succ_eq_zero (r : R) {m : ℕ} {F : C}
    (hF : r ^ (m + 1) • 𝟙 F = 0) :
    ∃ (S : ShortComplex C) (_ : S.ShortExact) (_ : S.X₂ = F), r ^ m • 𝟙 S.X₁ = 0 ∧
      r • 𝟙 S.X₃ = 0 := by
  let φ := r • 𝟙 F
  refine ⟨ShortComplex.mk (image.ι φ) (cokernel.π (image.ι φ)) (cokernel.condition _),
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }, rfl, ?_, ?_⟩
  · refine (cancel_mono (image.ι φ)).1 ((cancel_epi (factorThruImage φ)).1 ?_)
    rw [zero_comp, comp_zero, Linear.smul_comp, Category.id_comp, Linear.comp_smul, image.fac]
    simp only [φ, smul_smul, ← pow_succ, hF]
  · change r • 𝟙 (cokernel (image.ι φ)) = 0
    refine (cancel_epi (cokernel.π (image.ι φ))).1 ?_
    have h : φ ≫ cokernel.π (image.ι φ) = 0 := by
      rw [← image.fac_assoc, cokernel.condition, comp_zero]
    rw [comp_zero, Linear.comp_smul, Category.comp_id, ← Category.id_comp (cokernel.π _),
      ← Linear.smul_comp]
    exact h

/-- Blueprint `lemma-bounds-finite-reductions--2`: The residue test on the pro-étale site (the
categorical statement).

Let `r ∈ R` be nilpotent and `κ ≅ 𝟙 / r` the cokernel of `r` on the unit, and assume that
tensoring with an object killed by `r` preserves monomorphisms between objects killed by `r`
(for sheaves of `R`-modules with `R / r` a field: every module over the field `R / r` is flat).
Then `K ∈ D(C)` has Tor amplitude in `[a, b]` if and only if `K ⊗ᴸ κ` has homology concentrated
in `[a, b]`.

One direction is the definition of Tor amplitude. Conversely, for `F` killed by `r` this is
`DerivedCategory.homologyConcentratedIn_tensor_singleFunctor_of_smul_eq_zero`, since
`κ ⊗ F ≅ F` (`CategoryTheory.tensorIsoOfSmulEqZero`); a general `F` is killed by some power
`r ^ m`, and the short exact sequences `0 ⟶ r F ⟶ F ⟶ F / r F ⟶ 0`
(`DerivedCategory.exists_shortExact_of_smul_pow_succ_eq_zero`) give distinguished triangles
`K ⊗ᴸ r F ⟶ K ⊗ᴸ F ⟶ K ⊗ᴸ F / r F ⟶` whose outer terms have homology in `[a, b]` by
induction on `m`. -/
theorem torAmplitudeIn_iff_homologyConcentratedIn_tensor_singleFunctor (r : R)
    (hr : IsNilpotent r) {κ : C} (eκ : κ ≅ cokernel (r • 𝟙 (𝟙_ C)))
    (hmono : ∀ F : C, r • 𝟙 F = 0 → ∀ {X Y : C} (f : X ⟶ Y) [Mono f], r • 𝟙 X = 0 →
      r • 𝟙 Y = 0 → Mono (f ▷ F))
    (a b : ℤ) (K : DerivedCategory C) :
    torAmplitudeIn C a b K ↔ homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj κ) := by
  refine ⟨fun hK ↦ hK κ, fun hK F ↦ ?_⟩
  obtain ⟨n, hn⟩ := hr
  have key : ∀ (m : ℕ) (F : C), r ^ m • 𝟙 F = 0 →
      homologyConcentratedIn a b (K ⊗ (singleFunctor C 0).obj F) := by
    intro m
    induction m with
    | zero =>
      intro F hF
      rw [pow_zero, one_smul] at hF
      have hZ : IsZero (K ⊗ (singleFunctor C 0).obj F) :=
        MonoidalCategory.isZero_tensorObj_of_isZero_right K
          ((singleFunctor C 0).map_isZero ((IsZero.iff_id_eq_zero F).2 hF))
      exact ⟨TStructure.t.isGE_of_isZero hZ a, TStructure.t.isLE_of_isZero hZ b⟩
    | succ m ih =>
      intro F hF
      obtain ⟨S, hS, rfl, h₁, h₃⟩ := exists_shortExact_of_smul_pow_succ_eq_zero r hF
      have hT := ((curriedTensor (DerivedCategory C)).obj K).map_distinguished _
        hS.singleTriangle_distinguished
      have hT₁ := ih _ h₁
      have hT₃ := homologyConcentratedIn_tensor_singleFunctor_of_smul_eq_zero r
        (smul_id_eq_zero_of_iso_cokernel r eκ) (tensorIsoOfSmulEqZero r eκ h₃) (hmono _ h₃) hK
      exact ⟨TStructure.t.isGE₂ _ hT a hT₁.1 hT₃.1, TStructure.t.isLE₂ _ hT b hT₁.2 hT₃.2⟩
  exact key n F (by rw [hn, zero_smul])

end DerivedCategory
