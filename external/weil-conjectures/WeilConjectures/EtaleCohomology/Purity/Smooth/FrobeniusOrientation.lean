/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CanonicalPurityBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalBaseChangeFinal
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.EtaleCohomology.TateTwist.FrobeniusNormalization
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil

/-!
# Frobenius equivariance of the smooth orientation of a geometric fibre

Let `X₀` be a smooth separated scheme of finite type and relative dimension `d` over a finite
field `k₀ = 𝔽_q`, `a : X ⟶ Spec k̄` its geometric fibre, `σ` the geometric Frobenius of `Spec k̄`
and `g` the geometric Galois Frobenius of `X`, so that `g ≫ a = a ≫ σ` is cartesian
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius`). The dualizing complex
`ω = Ra^! Λ` carries the exceptional Weil datum of the square
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`), and the canonical orientation
`θ : ω ≅ Λ_X(d)[2d]` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) identifies it with
the Tate datum, on which geometric Frobenius acts by `q⁻ᵈ` (`definition-weil-structure--1`,
`AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum`). Over `k̄` the twist is trivial, so
this can be written without Tate twists: there is an isomorphism `o : Λ_X[2d] ≅ ω` which is a
morphism of Weil objects from the canonical datum of `Λ_X[2d]` to `q^d` times the exceptional
datum (`AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism`).

The input is the compatibility of the canonical orientation with base change
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`), the case `K = Λ` of the
compatibility of the canonical purity map with base change
(`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`, blueprint
`proposition-compatibility-purity-base-change` of the smooth purity chapter).

## Main statements

- `AlgebraicGeometry.Etale.exists_iso_dualizingComplex_isWeilMorphism`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section TateSection

variable {Λ : Type (u + 1)} [CommRing Λ] [HasTateTwist Λ] {X Y Z : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ Z] (m : ℤ)

/-- The pullback `H⁰(Y, Λ(m)) ⟶ H⁰(X, Λ(m))` of global sections of a Tate twist along
`φ : X ⟶ Y`: `x ↦ ε⁻¹ ≫ Lφ^* x ≫ τ_φ`, for the canonical `ε : Lφ^* Λ_Y ≅ Λ_X` and the
identification `τ_φ : Lφ^* Λ_Y(m) ≅ Λ_X(m)` of the Tate twist datum. For an endomorphism it is
the Frobenius operator of the Tate datum (`AlgebraicGeometry.Etale.tateWeilDatum`). -/
noncomputable def tateSectionPullback (φ : X ⟶ Y) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y m) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ X) ⟶ tateObject Λ X m) where
  toFun x := (leftDerivedUpperStarUnitIso _ φ).inv ≫ (L((φ)^*[ModuleCat.{u + 1} Λ])).map x ≫
    (leftDerivedUpperStarTateObjectIso φ m).hom
  map_add' x y := by
    rw [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c x := by
    dsimp only [RingHom.id_apply]
    rw [Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

lemma tateSectionPullback_apply (φ : X ⟶ Y) (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ _) :
    tateSectionPullback m φ x = (leftDerivedUpperStarUnitIso _ φ).inv ≫
      (L((φ)^*[ModuleCat.{u + 1} Λ])).map x ≫ (leftDerivedUpperStarTateObjectIso φ m).hom :=
  rfl

/-- The Frobenius operator of the Tate datum is the pullback of sections. -/
lemma frobeniusOperator_tateWeilDatum_eq_tateSectionPullback (h : Y ⟶ Y)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y m) :
    frobeniusOperator h (tateWeilDatum Λ h m).hom x = tateSectionPullback m h x :=
  rfl

/-- The pullback of sections of a Tate twist is compatible with composition. -/
lemma tateSectionPullback_comp (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    (x : 𝟙_ (DerivedCategoryModule Λ Z) ⟶ tateObject Λ Z m) :
    tateSectionPullback m (φ ≫ ψ) x = tateSectionPullback m φ (tateSectionPullback m ψ x) := by
  have hu := leftDerivedUpperStarComp_hom_app_unit (ModuleCat.{u + 1} Λ) φ ψ (φ ≫ ψ) rfl
  rw [← leftDerivedUpperStarUnitIso_hom_eq_η, ← leftDerivedUpperStarUnitIso_hom_eq_η,
    ← leftDerivedUpperStarUnitIso_hom_eq_η] at hu
  have hτ := HasTateTwist.leftDerivedUpperStarTwistObjectIso_comp (Λ := Λ) φ ψ m
  have hn := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) φ ψ).hom.naturality
    (x : 𝟙_ _ ⟶ HasTateTwist.twistObject Z m)
  simp only [Functor.comp_map] at hn
  rw [tateSectionPullback_apply, tateSectionPullback_apply, tateSectionPullback_apply,
    leftDerivedUpperStarTateObjectIso, leftDerivedUpperStarTateObjectIso,
    leftDerivedUpperStarTateObjectIso, hτ]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  have hu' : (leftDerivedUpperStarUnitIso _ (φ ≫ ψ)).inv ≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) φ ψ).hom.app (𝟙_ _) =
        (leftDerivedUpperStarUnitIso _ φ).inv ≫
          (L((φ)^*[ModuleCat.{u + 1} Λ])).map (leftDerivedUpperStarUnitIso _ ψ).inv := by
    rw [Iso.inv_comp_eq, ← hu]
    simp
  erw [reassoc_of% hn]
  rw [reassoc_of% hu']

end TateSection

section LeftUnitor

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}}

/-- Let `w : Λ_Y ⟶ T` and `w' : Λ_X ⟶ T'` be compatible, up to a scalar `c`, with a morphism
`τ : Lg^* T ⟶ T'`. Then so are `w ≫ λ⁻¹ : Λ_Y ⟶ Λ_Y ⊗ᴸ T` and `w' ≫ λ⁻¹ : Λ_X ⟶ Λ_X ⊗ᴸ T'`, for
the morphism `Lg^*(Λ_Y ⊗ᴸ T) ≅ Lg^* Λ_Y ⊗ᴸ Lg^* T ⟶ Λ_X ⊗ᴸ T'` induced by `τ` and the canonical
`Lg^* Λ_Y ≅ Λ_X`. -/
lemma leftDerivedUpperStar_map_comp_leftUnitor_inv (g : X ⟶ Y)
    {T : DerivedCategoryModule Λ Y} {T' : DerivedCategoryModule Λ X}
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T') {w : 𝟙_ _ ⟶ T} {w' : 𝟙_ _ ⟶ T'} (c : Λ)
    (h : (L((g)^*[ModuleCat.{u + 1} Λ])).map w ≫ τ =
      c • ((leftDerivedUpperStarUnitIso _ g).hom ≫ w')) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map (w ≫ (derivedTensorLeftUnitor _ _ T).inv) ≫
        (leftDerivedUpperStarTensorIso _ g _ _).hom ≫
          ((derivedTensor _ _).obj _).map τ ≫
            ((derivedTensor _ _).map (leftDerivedUpperStarUnitIso _ g).hom).app _ =
      c • ((leftDerivedUpperStarUnitIso _ g).hom ≫ w' ≫ (derivedTensorLeftUnitor _ _ T').inv) := by
  have hl : (leftDerivedUpperStarTensorIso _ g (𝟙_ _) T).hom ≫
      ((derivedTensor _ _).map (leftDerivedUpperStarUnitIso _ g).hom).app _ ≫
        (derivedTensorLeftUnitor _ _ _).hom =
      (L((g)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorLeftUnitor _ _ _).hom :=
    leftDerivedUpperStarTensorComparison_leftUnitor_hom (ModuleCat.{u + 1} Λ) g T
  have hl' : (L((g)^*[ModuleCat.{u + 1} Λ])).map (derivedTensorLeftUnitor _ _ T).inv ≫
      (leftDerivedUpperStarTensorIso _ g (𝟙_ _) _).hom ≫
        ((derivedTensor _ _).map (leftDerivedUpperStarUnitIso _ g).hom).app _ =
      (derivedTensorLeftUnitor _ _ _).inv := by
    rw [← cancel_mono (derivedTensorLeftUnitor _ _ _).hom, Category.assoc, Category.assoc, hl,
      Iso.inv_hom_id, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hx := ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
    (leftDerivedUpperStarUnitIso _ g).hom).naturality τ
  have hnat := ((derivedTensorLeftUnitorNatIso (ModuleCat.{u + 1} Λ) X).inv.naturality τ).symm
  dsimp only [derivedTensorLeftUnitorNatIso, NatIso.ofComponents_inv_app, Functor.id_map] at hnat
  rw [Functor.map_comp, Category.assoc, hx, reassoc_of% hl', hnat, reassoc_of% h,
    Linear.smul_comp]
  simp only [Category.assoc]

end LeftUnitor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ : Scheme.{u}} (f : X₀ ⟶ Spec (.of k₀)) (d : ℕ)
  [SmoothOfRelativeDimension d f] [IsSeparated f] [QuasiCompact f]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k₀)))]
  [HasInvertibleExponent Λ f.geometricFiber]
  [HasCompactification f.geometricFiberToAlgebraicClosure]

set_option maxHeartbeats 400000 in
-- the final `exact` unfolds the twist-and-shift of the geometric fibre
/-- Frobenius equivariance of the smooth orientation of the geometric fibre
`a : X ⟶ Spec k̄` of a smooth separated `𝔽_q`-scheme of finite type and relative dimension `d`,
in untwisted form: there is an isomorphism `o : Λ_X[2d] ≅ ω = Ra^! Λ_{k̄}` such that

`Lg^*(o) ≫ q^d • φ^! = φ_{Λ_X}[2d] ≫ o`,

where `φ_{Λ_X}` is the canonical datum `Lg^* Λ_X ≅ Λ_X` and `φ^!` is the exceptional datum
`Lg^* Ra^! Λ ⟶ Ra^! Lσ^* Λ ≅ Ra^! Λ` of the square
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`).

It is the canonical orientation `θ : ω ≅ Λ_X(d)[2d]` composed with a trivialization
`Λ_X ≅ Λ_X(d)` pulled back from `k̄`: by the base change compatibility of `θ`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`, blueprint
`proposition-compatibility-purity-base-change`) the exceptional datum corresponds to the Tate datum,
and on the pulled back trivialization the Tate datum is `q⁻ᵈ` times the canonical datum
(`definition-weil-structure--1`, `AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum`).
Equivalently, geometric Frobenius acts by `q^d` on the compactly supported cohomology
`H^{2d}_c(X, Λ)` through the trace. -/
theorem exists_iso_dualizingComplex_isWeilMorphism :
    ∃ o : (𝟙_ (DerivedCategoryModule Λ f.geometricFiber))⟦(2 * d : ℤ)⟧ ≅
        dualizingComplex Λ f.geometricFiberToAlgebraicClosure,
      IsWeilMorphism f.geometricGaloisFrobenius.asIso.hom
        (shiftWeilDatum f.geometricGaloisFrobenius.asIso.hom
          (leftDerivedUpperStarUnitIso _ f.geometricGaloisFrobenius.asIso.hom).hom (2 * d))
        (((Nat.card k₀ : Λ) ^ d) •
          upperShriekMateWeilDatum (Λ := Λ) f.isPullback_geometricGaloisFrobenius
            (leftDerivedUpperStarUnitIso _ (specGeometricFrobenius k₀).asIso.hom).hom)
        o.hom := by
  have : NeZero (ringChar Λ) := ⟨CharP.char_ne_zero_of_finite Λ (ringChar Λ)⟩
  set a := f.geometricFiberToAlgebraicClosure
  set g := f.geometricGaloisFrobenius.asIso.hom
  set σ := (specGeometricFrobenius k₀).asIso.hom
  have sq : IsPullback g a a σ := f.isPullback_geometricGaloisFrobenius
  have : SmoothOfRelativeDimension d a :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.snd _ _))
  have : IsSeparated a := inferInstanceAs (IsSeparated (Limits.pullback.snd _ _))
  have : QuasiCompact a := inferInstanceAs (QuasiCompact (Limits.pullback.snd _ _))
  have : Smooth a := SmoothOfRelativeDimension.smooth d a
  have : LocallyOfFiniteType a := inferInstance
  have : IsNoetherian f.geometricFiber := isNoetherian_of_locallyOfFiniteType a
  have hbc :=
    dualizingComplexTwistShiftIso_baseChange_of_isIso_of_isNoetherian Λ sq d (𝟙 _) (𝟙 _)
  set θ := dualizingComplexTwistShiftIso Λ a d (𝟙 (Spec (.of (AlgebraicClosure k₀))))
  -- the exceptional datum corresponds to the Tate datum under `θ`
  have hθ : (L((g)^*[ModuleCat.{u + 1} Λ])).map θ.inv ≫
      upperShriekMateWeilDatum (Λ := Λ) f.isPullback_geometricGaloisFrobenius
        (leftDerivedUpperStarUnitIso _ σ).hom =
      (leftDerivedUpperStarTwistShiftIso Λ g d (constantComplex Λ _)).hom ≫
        (twistShift Λ _ d).map (leftDerivedUpperStarUnitIso _ g).hom ≫ θ.inv := by
    rw [← cancel_mono θ.hom]
    simp only [upperShriekMateWeilDatum, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [hbc]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  obtain ⟨v⟩ := nonempty_tateObject_iso_unit Λ (AlgebraicClosure k₀) (d : ℤ)
  -- the trivialization `Λ_X ≅ Λ_X(d)` pulled back from `k̄`
  let w : 𝟙_ (DerivedCategoryModule Λ f.geometricFiber) ≅ tateObject Λ f.geometricFiber d :=
    (leftDerivedUpperStarUnitIso _ a).symm ≪≫ (L((a)^*[ModuleCat.{u + 1} Λ])).mapIso v.symm ≪≫
      leftDerivedUpperStarTateObjectIso a d
  have hw : w.hom = tateSectionPullback (d : ℤ) a v.inv := rfl
  -- geometric Frobenius acts on `w` by `q⁻ᵈ`
  set c : Λ := (((isUnit_natCard_of_hasInvertibleExponent Λ k₀).unit⁻¹ ^ (d : ℤ) : Λˣ) : Λ)
  have hc : ((Nat.card k₀ : Λ) ^ d) * c = 1 := by
    simp only [c, zpow_natCast, Units.val_pow_eq_pow_val, ← mul_pow, IsUnit.mul_val_inv,
      one_pow]
  have hτ : (L((g)^*[ModuleCat.{u + 1} Λ])).map w.hom ≫
      (leftDerivedUpperStarTateObjectIso g d).hom =
        c • ((leftDerivedUpperStarUnitIso _ g).hom ≫ w.hom) := by
    have h1 : tateSectionPullback (d : ℤ) g w.hom = c • w.hom := by
      rw [hw, ← tateSectionPullback_comp, sq.w, tateSectionPullback_comp,
        ← frobeniusOperator_tateWeilDatum_eq_tateSectionPullback,
        frobeniusOperator_tateWeilDatum, map_smul]
    rw [tateSectionPullback_apply] at h1
    rw [← Linear.comp_smul, ← h1, Iso.hom_inv_id_assoc]
  let o := (shiftFunctor _ (2 * d : ℤ)).mapIso (w ≪≫ (derivedTensorLeftUnitor _ _ _).symm) ≪≫
    θ.symm
  refine ⟨o, ?_⟩
  -- the twist-free form of the Tate datum on `Λ_X ≅ Λ_X(d) ≅ Λ_X ⊗ᴸ Λ_X(d)`
  have hI : (Nat.card k₀ ^ d) • ((L((g)^*[ModuleCat.{u + 1} Λ])).map
      (w.hom ≫ (derivedTensorLeftUnitor _ _ _).inv) ≫
        (leftDerivedUpperStarTensorIso _ g _ _).hom ≫
          ((derivedTensor _ _).obj _).map (leftDerivedUpperStarTateObjectIso g d).hom ≫
            ((derivedTensor _ _).map (leftDerivedUpperStarUnitIso _ g).hom).app _) =
      (leftDerivedUpperStarUnitIso _ g).hom ≫ w.hom ≫ (derivedTensorLeftUnitor _ _ _).inv := by
    rw [leftDerivedUpperStar_map_comp_leftUnitor_inv g _ c hτ, ← Nat.cast_smul_eq_nsmul Λ,
      smul_smul, Nat.cast_pow, hc, one_smul]
  have ho : o.hom = (w.hom ≫ (derivedTensorLeftUnitor _ _ _).inv)⟦(2 * d : ℤ)⟧' ≫ θ.inv := rfl
  have hI' := congrArg (fun t ↦
    ((L((g)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * d : ℤ)).hom.app (𝟙_ _) ≫
      t⟦(2 * d : ℤ)⟧' ≫ θ.inv) hI
  simp only [Functor.map_nsmul, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Functor.map_comp, Category.assoc] at hI'
  unfold IsWeilMorphism shiftWeilDatum
  rw [ho, Functor.map_comp, Category.assoc]
  simp only [Linear.comp_smul]
  rw [hθ, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  simp only [leftDerivedUpperStarTwistShiftIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  erw [Functor.commShiftIso_hom_naturality_assoc]
  simp only [twistShift, tateTwist, Functor.comp_map, Functor.flip_obj_map, Functor.map_comp,
    Category.assoc] at hI' ⊢
  exact hI'

end AlgebraicGeometry.Etale
