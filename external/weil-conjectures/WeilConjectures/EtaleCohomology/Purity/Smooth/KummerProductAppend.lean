/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.LeftUnitorShift
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ShiftTateObjectAssoc
public import WeilConjectures.Mathlib.Data.Fin.Tuple.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc

/-!
# Products of Kummer boundaries of concatenated tuples

The iterated cup product with supports of Kummer boundaries
(`AlgebraicGeometry.Etale.kummerBoundaryProduct`) of a concatenated tuple `(f, g)` is the cup
product with supports (`AlgebraicGeometry.Etale.cupWithSupportsTateObject`) of the products of
`f` and of `g`:

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a) ∪ ∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b) = (∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a)) ∪ (∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b))`.

The proof is an induction on the length of `f`, from the associativity and the unit law of the
cup product with supports with Tate coefficients. These in turn come from the associativity and
unit law of the product of supports (`WeilConjectures.SixFunctors.Etale.Derived.SupportsAssoc`),
the coassociativity of the diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U`, and the corresponding laws for the
identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`).

## Implementation notes

The left unit law of `AlgebraicGeometry.Etale.shiftTateObjectAddIso`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso_zero_left`) is proved from
`HasTateTwist.twistObjectAddIso_zero_left` and the compatibility of the left unitor of the derived
tensor product with shifts (`DerivedCategory.leftUnitor_commShift_app`). Its associativity
(`AlgebraicGeometry.Etale.ShiftTateObjectAddIsoAssoc`) is a *hypothesis* of the associativity
statements below: it follows from `HasTateTwist.twistObjectAddIso_assoc` together with the
compatibility of the associator of the derived tensor product with the commutation of `⊗ᴸ` with
shifts, which is not available in the library.

## Main statements

- `AlgebraicGeometry.Etale.shiftTateObjectAddIso_zero_left`
- `AlgebraicGeometry.Etale.constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom`
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject_assoc`
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject_kummerBoundaryProduct_zero`
- `AlgebraicGeometry.Etale.kummerBoundaryProduct_append`
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- `V(s ∪ t) = V(s) ∩ V(t)`. -/
lemma Scheme.range_zeroLocusSubschemeι_union {X : Scheme.{u}} (s t : Set Γ(X, ⊤)) :
    Set.range (X.zeroLocusSubschemeι (s ∪ t)).base =
      Set.range (X.zeroLocusSubschemeι s).base ∩ Set.range (X.zeroLocusSubschemeι t).base := by
  simp only [range_zeroLocusSubschemeι]
  ext x
  simp only [Scheme.mem_zeroLocus_iff, Set.mem_union, Set.mem_inter_iff, or_imp, forall_and]

namespace Etale

section Shift

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The left unitor of the derived tensor product commutes with the shifts
(`DerivedCategory.leftUnitor_commShift_app`). -/
lemma derivedTensorLeftUnitor_commShift (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (n : ℤ) :
    (((derivedTensor A X).obj (𝟙_ _)).commShiftIso n).hom.app K ≫
        (derivedTensorLeftUnitor A X K).hom⟦n⟧' = (derivedTensorLeftUnitor A X (K⟦n⟧)).hom :=
  DerivedCategory.leftUnitor_commShift_app _ K n

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- `K⟦b⟧⟦0⟧ ≅ K⟦b + 0⟧` is the identification `K⟦b⟧⟦0⟧ ≅ K⟦b⟧`. -/
lemma shiftFunctorAdd'_add_zero_inv_app_eq (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (b c : ℤ) (h : b + 0 = c) :
    (shiftFunctorAdd' _ b 0 c h).inv.app K =
      (shiftFunctorZero _ ℤ).hom.app (K⟦b⟧) ≫ eqToHom (by rw [← h, add_zero]; rfl) := by
  obtain rfl : c = b := by omega
  simp [shiftFunctorAdd'_add_zero]

/-- The identification `K⟦a⟧ ⊗ M⟦b⟧ ≅ (K ⊗ M)⟦a + b⟧`
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`)
for `a = 0` is the commutation of `K ⊗ -` with the shift by `b`. -/
lemma derivedTensorHom_shiftFunctorZero'_inv_comp_derivedTensorShiftIso_hom
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a b : ℤ) (ha : a = 0) :
    derivedTensorHom A ((shiftFunctorZero' _ a ha).inv.app K) (𝟙 (M⟦b⟧)) ≫
        (derivedTensorShiftIso A K M a b).hom =
      (((derivedTensor A X).obj K).commShiftIso b).hom.app M ≫
        eqToHom (by rw [ha, zero_add]; rfl) := by
  subst ha
  simp only [derivedTensorShiftIso, derivedTensorHom, shiftFunctorZero', eqToIso_refl,
    Iso.refl_trans, Iso.trans_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Iso.symm_hom,
    Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app,
    shiftFunctorAdd'_add_zero_inv_app_eq, CategoryTheory.Functor.map_id, Category.comp_id,
    Functor.flip_obj_map, Category.assoc]
  rw [← NatTrans.comp_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    ← (shiftFunctorZero _ ℤ).inv.naturality_assoc]
  simp

end Shift

/-- Shifting a morphism across an equation of shift amounts. -/
@[reassoc]
lemma eqToHom_comp_shift_map_of_eq {D : Type*} [Category D] [HasShift D ℤ] {K L : D}
    (f : K ⟶ L) {c c' : ℤ} (h : c = c') :
    (eqToHom (by rw [h]) : K⟦c⟧ ⟶ K⟦c'⟧) ≫ f⟦c'⟧' = f⟦c⟧' ≫ eqToHom (by rw [h]) := by
  subst h
  simp

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

variable (U : Scheme.{u}) [HasInvertibleExponent Λ U]

/-- The *associativity* of the identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`) on `U`, for the twists `a, b, c`:

```
(Λ(a)[2a] ⊗ Λ(b)[2b]) ⊗ Λ(c)[2c] ───α───▶ Λ(a)[2a] ⊗ (Λ(b)[2b] ⊗ Λ(c)[2c])
          │                                          │
          ▼                                          ▼
Λ(a + b)[2(a + b)] ⊗ Λ(c)[2c]               Λ(a)[2a] ⊗ Λ(b + c)[2(b + c)]
          │                                          │
          ▼                                          ▼
   Λ((a + b) + c)[…] ═══════════════════════ Λ(a + (b + c))[…]
```

It follows from `HasTateTwist.twistObjectAddIso_assoc` and the compatibility of the associator of
the derived tensor product with shifts. -/
def ShiftTateObjectAddIsoAssoc (a b c : ℤ) : Prop :=
  derivedTensorHom (ModuleCat.{u + 1} Λ) (shiftTateObjectAddIso Λ U a b).hom
      (𝟙 ((tateObject Λ U c)⟦2 * c⟧)) ≫ (shiftTateObjectAddIso Λ U (a + b) c).hom =
    (derivedTensorAssociator _ U _ _ _).hom ≫
      derivedTensorHom _ (𝟙 ((tateObject Λ U a)⟦2 * a⟧)) (shiftTateObjectAddIso Λ U b c).hom ≫
        (shiftTateObjectAddIso Λ U a (b + c)).hom ≫ eqToHom (by rw [add_assoc])

omit [Finite Λ] in
/-- The identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` are associative
(`AlgebraicGeometry.Etale.ShiftTateObjectAddIsoAssoc`). -/
theorem shiftTateObjectAddIsoAssoc (a b c : ℤ) : ShiftTateObjectAddIsoAssoc Λ U a b c :=
  shiftTateObjectAddIso_hom_assoc Λ U a b c

omit [Finite Λ] in
/-- The *left unit law* of the identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.shiftTateObjectAddIso`) on `U`: through `Λ_U ≅ Λ_U(0)[0]`, the
identification `Λ(0)[0] ⊗ Λ(m)[2m] ≅ Λ(m)[2m]` is the left unitor. This is
`HasTateTwist.twistObjectAddIso_zero_left` together with the compatibility of the left unitor of
the derived tensor product with shifts (`DerivedCategory.leftUnitor_commShift_app`). -/
theorem shiftTateObjectAddIso_zero_left (m : ℤ) :
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U ((tateObject Λ U m)⟦2 * m⟧)).inv ≫
      derivedTensorHom _ ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) (𝟙 _) ≫
        (shiftTateObjectAddIso Λ U 0 m).hom =
    eqToHom (by rw [zero_add]) := by
  set Z := HasTateTwist.twistObjectZeroIso (Λ := Λ) U
  have hz := HasTateTwist.twistObjectAddIso_zero_left (Λ := Λ) U m
  have hadd : (HasTateTwist.twistObjectAddIso U 0 m).hom =
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map Z.hom).app (HasTateTwist.twistObject U m) ≫
        (derivedTensorLeftUnitor _ U _).hom ≫ eqToHom (by rw [zero_add]) := by
    rw [reassoc_of% hz, eqToHom_trans, eqToHom_refl, Category.comp_id]
  have hc : (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj
      (HasTateTwist.twistObject U 0)).commShiftIso
      (2 * m)).hom.app (tateObject Λ U m) ≫
        (((derivedTensor (ModuleCat.{u + 1} Λ) U).map Z.hom).app
          (HasTateTwist.twistObject U m))⟦2 * m⟧' =
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map Z.hom).app ((tateObject Λ U m)⟦2 * m⟧) ≫
        (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).commShiftIso
          (2 * m)).hom.app (tateObject Λ U m) :=
    NatTrans.shift_app_comm _ _ _
  have hl : (((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).commShiftIso
      (2 * m)).hom.app (tateObject Λ U m) ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U
          (HasTateTwist.twistObject U m)).hom⟦2 * m⟧' =
      (derivedTensorLeftUnitor _ U ((tateObject Λ U m)⟦2 * m⟧)).hom :=
    derivedTensorLeftUnitor_commShift (A := ModuleCat.{u + 1} Λ) (X := U) _ (2 * m)
  have hZ (K : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      derivedTensorHom (ModuleCat.{u + 1} Λ) Z.inv (𝟙 K) ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).map Z.hom).app K = 𝟙 _ := by
    have : ((derivedTensor (ModuleCat.{u + 1} Λ) U).map Z.hom).app K =
        derivedTensorHom _ Z.hom (𝟙 K) := by
      simp [derivedTensorHom]
    rw [this, derivedTensorHom_comp, Iso.inv_hom_id, Category.comp_id, derivedTensorHom_id]
  have e : derivedTensorHom (ModuleCat.{u + 1} Λ) (Z.inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _)
          (𝟙 ((tateObject Λ U m)⟦2 * m⟧)) =
      derivedTensorHom _ Z.inv (𝟙 _) ≫
        derivedTensorHom _ ((shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) (𝟙 _) := by
    rw [derivedTensorHom_comp, Category.comp_id]
  rw [e]
  simp only [shiftTateObjectAddIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Category.assoc]
  erw [reassoc_of% derivedTensorHom_shiftFunctorZero'_inv_comp_derivedTensorShiftIso_hom]
  rw [eqToHom_comp_shift_map_of_eq_assoc _ (show 2 * m = 2 * 0 + 2 * m by ring), hadd,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  erw [reassoc_of% hc]
  rw [reassoc_of% hZ]
  erw [reassoc_of% hl]
  simp [eqToHom_map]

omit [Finite Λ] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` (`AlgebraicGeometry.Etale.constantComplexDiagonal`) is a
section of the left unitor: by the unit law `HasTateTwist.twistObjectAddIso_zero_left`. -/
lemma constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom :
    constantComplexDiagonal Λ U ≫ (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).hom =
      𝟙 _ := by
  have hz := HasTateTwist.twistObjectAddIso_zero_left (Λ := Λ) U 0
  have hn : ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).map
      (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom ≫
        (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U _).hom =
      (derivedTensorLeftUnitor _ U _).hom ≫ (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom := by
    have := derivedTensorHom_id_comp_derivedTensorLeftUnitor_hom (A := ModuleCat.{u + 1} Λ)
      (X := U) (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).hom
    simp only [derivedTensorHom, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at this
    exact this
  simp only [constantComplexDiagonal, Category.assoc]
  rw [hn, reassoc_of% hz, Iso.inv_hom_id_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id]

omit [Finite Λ] in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` is coassociative. -/
lemma constantComplexDiagonal_coassoc :
    constantComplexDiagonal Λ U ≫
        derivedTensorHom _ (constantComplexDiagonal Λ U) (𝟙 (constantComplex Λ U)) ≫
          (derivedTensorAssociator (ModuleCat.{u + 1} Λ) U _ _ _).hom =
      constantComplexDiagonal Λ U ≫
        derivedTensorHom _ (𝟙 (constantComplex Λ U)) (constantComplexDiagonal Λ U) :=
  coassoc_of_comp_derivedTensorLeftUnitor_hom (constantComplexDiagonal Λ U)
    (constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom Λ U)

variable {U}

section Cup

variable {Z₁ Z₂ Z₃ Z₁₂ Z₂₃ Z : Scheme.{u}}

/-- **Associativity of the cup product with supports with Tate coefficients**, given the
associativity of `AlgebraicGeometry.Etale.shiftTateObjectAddIso`:
`(α ∪ β) ∪ γ = α ∪ (β ∪ γ)` in `H^{2(m₁ + m₂ + m₃)}_{Z₁ ∩ Z₂ ∩ Z₃}(U, Λ(m₁ + m₂ + m₃))`. -/
theorem cupWithSupportsTateObject_assoc (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i₃ : Z₃ ⟶ U)
    (i₁₂ : Z₁₂ ⟶ U) (i₂₃ : Z₂₃ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i₃]
    [IsClosedImmersion i₁₂] [IsClosedImmersion i₂₃] [IsClosedImmersion i]
    (h₁₂ : Set.range i₁₂.base = Set.range i₁.base ∩ Set.range i₂.base)
    (h₂₃ : Set.range i₂₃.base = Set.range i₂.base ∩ Set.range i₃.base)
    (h : Set.range i.base = Set.range i₁₂.base ∩ Set.range i₃.base)
    (h' : Set.range i.base = Set.range i₁.base ∩ Set.range i₂₃.base) {m₁ m₂ m₃ : ℤ}
    (hμ : ShiftTateObjectAddIsoAssoc Λ U m₁ m₂ m₃)
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m₁)⟦2 * m₁⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m₂)⟦2 * m₂⟧)))
    (γ : constantComplex Λ U ⟶ (R(i₃)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₃)^![Λ]).obj ((tateObject Λ U m₃)⟦2 * m₃⟧))) :
    cupWithSupportsTateObject Λ i₁₂ i₃ i h (cupWithSupportsTateObject Λ i₁ i₂ i₁₂ h₁₂ α β) γ =
      cupWithSupportsTateObject Λ i₁ i₂₃ i h' α (cupWithSupportsTateObject Λ i₂ i₃ i₂₃ h₂₃ β γ) ≫
        eqToHom (by rw [add_assoc]) := by
  unfold ShiftTateObjectAddIsoAssoc at hμ
  have e₁ := cupWithSupports_comp_map Λ i₁₂ i₃ i h
    (constantComplexDiagonal Λ U)
    (cupWithSupports _ i₁ i₂ i₁₂ h₁₂ (constantComplexDiagonal Λ U) α β) γ
    (shiftTateObjectAddIso Λ U m₁ m₂).hom (𝟙 _)
  have e₂ := cupWithSupports_comp_map Λ i₁ i₂₃ i h'
    (constantComplexDiagonal Λ U) α
    (cupWithSupports _ i₂ i₃ i₂₃ h₂₃ (constantComplexDiagonal Λ U) β γ)
    (𝟙 _) (shiftTateObjectAddIso Λ U m₂ m₃).hom
  have e₃ := cupWithSupports_assoc Λ i₁ i₂ i₃ i₁₂ i₂₃ i h₁₂ h₂₃ h h'
    (constantComplexDiagonal Λ U) (constantComplexDiagonal_coassoc Λ U) α β γ
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at e₁ e₂
  simp only [cupWithSupportsTateObject]
  rw [← e₁, ← e₂, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hμ, ← e₃]
  simp only [Functor.map_comp, Category.assoc, eqToHom_map]

/-- Changing the closed subscheme `V(s)` carrying a cup product to an equal one `V(t)`. -/
lemma cupWithSupportsTateObject_zeroLocusSubschemeι_congr (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] {s t : Set Γ(U, ⊤)} (hst : s = t)
    (h : Set.range (U.zeroLocusSubschemeι s).base = Set.range i₁.base ∩ Set.range i₂.base)
    (h' : Set.range (U.zeroLocusSubschemeι t).base = Set.range i₁.base ∩ Set.range i₂.base)
    {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    cupWithSupportsTateObject Λ i₁ i₂ (U.zeroLocusSubschemeι s) h α β =
      cupWithSupportsTateObject Λ i₁ i₂ (U.zeroLocusSubschemeι t) h' α β ≫
        eqToHom (by subst hst; rfl) := by
  subst hst
  simp

/-- Moving an identification of twists out of the left factor of a cup product. -/
lemma cupWithSupportsTateObject_eqToHom_left (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) {m₁ m₁' m' : ℤ}
    (hm : m₁ = m₁')
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m₁)⟦2 * m₁⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    cupWithSupportsTateObject Λ i₁ i₂ i h (m := m₁') (α ≫ eqToHom (by rw [hm])) β =
      cupWithSupportsTateObject Λ i₁ i₂ i h α β ≫ eqToHom (by rw [hm]) := by
  subst hm
  simp

/-- Moving an identification of twists out of the right factor of a cup product. -/
lemma cupWithSupportsTateObject_eqToHom_right (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) {m m₂ m₂' : ℤ}
    (hm : m₂ = m₂')
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m₂)⟦2 * m₂⟧))) :
    cupWithSupportsTateObject Λ i₁ i₂ i h (m' := m₂') α (β ≫ eqToHom (by rw [hm])) =
      cupWithSupportsTateObject Λ i₁ i₂ i h α β ≫ eqToHom (by rw [hm]) := by
  subst hm
  simp

end Cup

section Product

/-- **The unit law.** The cup product with the empty product of Kummer boundaries (the unit class
supported everywhere) is the identity. -/
theorem cupWithSupportsTateObject_kummerBoundaryProduct_zero {Z : Scheme.{u}}
    (f : Fin 0 → Γ(U, ⊤)) (i : Z ⟶ U) [IsClosedImmersion i]
    (h : Set.range i.base =
      Set.range (U.zeroLocusSubschemeι (Set.range f)).base ∩ Set.range i.base) {m : ℤ}
    (β : constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧))) :
    cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι (Set.range f)) i i h
        (kummerBoundaryProduct Λ f) β =
      β ≫ eqToHom (by rw [Nat.cast_zero, zero_add]) := by
  have hunit :
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U ((tateObject Λ U m)⟦2 * m⟧)).inv ≫
      derivedTensorHom _ ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _) (𝟙 _) ≫
        (shiftTateObjectAddIso Λ U ((0 : ℕ) : ℤ) m).hom =
      eqToHom (by rw [Nat.cast_zero, zero_add]) :=
    shiftTateObjectAddIso_zero_left Λ U m
  rw [kummerBoundaryProduct, cupWithSupportsTateObject,
    cupWithSupports_liftCounitOfRangeEqUniv Λ _ i _ h
      (constantComplexDiagonal Λ U) (constantComplexDiagonal_comp_derivedTensorLeftUnitor_hom Λ U),
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp, Category.assoc, hunit]
  simp only [eqToHom_map]

/-- The product of Kummer boundaries of `(x, f₁, …, f_n)` is `∂κ(x) ∪ (∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n))`. -/
lemma kummerBoundaryProduct_cons {n : ℕ} (x : Γ(U, ⊤)) (f : Fin n → Γ(U, ⊤)) :
    kummerBoundaryProduct Λ (Fin.cons x f : Fin (n + 1) → Γ(U, ⊤)) =
      cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι {x})
          (U.zeroLocusSubschemeι (Set.range f))
          (U.zeroLocusSubschemeι (Set.range (Fin.cons x f : Fin (n + 1) → Γ(U, ⊤))))
          (by rw [Fin.range_cons, range_zeroLocusSubschemeι_insert]) (m := 1)
          (shiftSupportedClass Λ _ 2 (kummerBoundary Λ x))
          (kummerBoundaryProduct Λ f) ≫
        eqToHom (by rw [Nat.cast_succ, add_comm (1 : ℤ)]) := by
  rw [kummerBoundaryProduct]
  rfl

/-- Transport of a product of Kummer boundaries along a reindexing `Fin n ≃ Fin m`. -/
lemma kummerBoundaryProduct_eq_comp_eqToHom {n m : ℕ} (h : n = m) (f : Fin n → Γ(U, ⊤))
    (g : Fin m → Γ(U, ⊤)) (hfg : ∀ i, f i = g (Fin.cast h i)) :
    kummerBoundaryProduct Λ g = kummerBoundaryProduct Λ f ≫ eqToHom (by
      subst h
      obtain rfl : f = g := funext fun i ↦ by simpa using hfg i
      rfl) := by
  subst h
  obtain rfl : f = g := funext fun i ↦ by simpa using hfg i
  simp

/-- **Products of Kummer boundaries of concatenated tuples.** For `f = (f₁, …, f_a)` and
`g = (g₁, …, g_b)`,

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a) ∪ ∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b) = (∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_a)) ∪ (∂κ(g₁) ∪ ⋯ ∪ ∂κ(g_b))`

in `H^{2(a + b)}_{V(f, g)}(U, Λ(a + b))`, given the associativity of the
identifications `Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]`
(`AlgebraicGeometry.Etale.ShiftTateObjectAddIsoAssoc`). -/
theorem kummerBoundaryProduct_append :
    ∀ {a b : ℕ} (f : Fin a → Γ(U, ⊤)) (g : Fin b → Γ(U, ⊤)),
      kummerBoundaryProduct Λ (Fin.append f g) =
        cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι (Set.range f))
            (U.zeroLocusSubschemeι (Set.range g))
            (U.zeroLocusSubschemeι (Set.range (Fin.append f g)))
            (by rw [Fin.range_append, Scheme.range_zeroLocusSubschemeι_union])
            (kummerBoundaryProduct Λ f) (kummerBoundaryProduct Λ g) ≫
          eqToHom (by rw [Nat.cast_add]) := by
  intro a
  induction a with
  | zero =>
    intro b f g
    have hs : Set.range (Fin.append f g) = Set.range g := by
      rw [Fin.range_append, Set.range_eq_empty f, Set.empty_union]
    rw [kummerBoundaryProduct_eq_comp_eqToHom Λ (Nat.zero_add b).symm g (Fin.append f g)
        (fun i ↦ by rw [Fin.append_left_nil f g rfl]; simp),
      cupWithSupportsTateObject_zeroLocusSubschemeι_congr Λ _ _ hs _
        (by rw [Set.range_eq_empty f, range_zeroLocusSubschemeι_empty, Set.univ_inter]),
      cupWithSupportsTateObject_kummerBoundaryProduct_zero Λ f _ _]
    simp only [Category.assoc, eqToHom_trans]
  | succ a ih =>
    intro b f g
    obtain ⟨x, f', rfl⟩ : ∃ x f', f = Fin.cons x f' :=
      ⟨f 0, Fin.tail f, (Fin.cons_self_tail f).symm⟩
    have hs : Set.range (Fin.cons x (Fin.append f' g) : Fin (a + b + 1) → Γ(U, ⊤)) =
        Set.range (Fin.append (Fin.cons x f' : Fin (a + 1) → Γ(U, ⊤)) g) := by
      rw [Fin.range_cons, Fin.range_append, Fin.range_append, Fin.range_cons,
        Set.insert_union]
    rw [kummerBoundaryProduct_eq_comp_eqToHom Λ (Nat.add_right_comm a b 1)
        (Fin.cons x (Fin.append f' g)) (Fin.append (Fin.cons x f') g)
        (fun i ↦ by rw [Fin.append_cons]; simp),
      kummerBoundaryProduct_cons Λ x (Fin.append f' g), ih f' g,
      cupWithSupportsTateObject_eqToHom_right Λ _ _ _ _ (Nat.cast_add a b).symm,
      cupWithSupportsTateObject_zeroLocusSubschemeι_congr Λ _ _ hs _
        (by rw [← hs, Fin.range_cons, range_zeroLocusSubschemeι_insert]),
      kummerBoundaryProduct_cons Λ x f',
      cupWithSupportsTateObject_eqToHom_left Λ _ _ _ _ (by push_cast; ring),
      cupWithSupportsTateObject_assoc Λ _ _ _ _
        (U.zeroLocusSubschemeι (Set.range (Fin.append f' g)))
        _ _ (by rw [Fin.range_append, Scheme.range_zeroLocusSubschemeι_union]) _
        (by rw [← hs, Fin.range_cons, range_zeroLocusSubschemeι_insert])
        (shiftTateObjectAddIsoAssoc Λ U _ _ _)]
    simp only [Category.assoc, eqToHom_trans]

end Product

end Etale

end AlgebraicGeometry
