/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Basic
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.EtaleCohomology.TateTwist.FrobeniusScalar
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass.TwistPullback
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-!
# Geometric Frobenius acts on `Λ(r)` by `q^{-r}`

Let `k` be a finite field with `q` elements, `k̄` an algebraic closure, `Y = Spec k̄` and
`h : Y ⟶ Y` the geometric Frobenius (`AlgebraicGeometry.specGeometricFrobenius`), the spectrum of
the inverse `γ` of `z ↦ z ^ q`. For a commutative ring `Λ` of characteristic `n ≠ 0` invertible on
`Y`, this file shows that the Frobenius operator of the Tate datum
`τ_r : Lh^* Λ_Y(r) ≅ Λ_Y(r)` (`AlgebraicGeometry.Etale.tateWeilDatum`) of the genuine Tate twist
(`AlgebraicGeometry.Etale.hasTateTwist`) is the multiplication by `q^{-r}`
(`AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum`): this is the twist normalization of
`prose-10-21`.

By `WeilConjectures.EtaleCohomology.TateTwist.FrobeniusScalar` the Frobenius operator on
`H⁰(Y, Λ(r))` is the multiplication by `c_1 ^ r` for a unit `c_1`, and it remains to show
`c_1 = q⁻¹`. Through `Λ(1) ≅ (μₙ ⊗ Λ)[0]` and `Λ ≅ (ℤ ⊗ Λ)[0]`, both compatible with the derived
pullbacks, the Frobenius operator on `Λ(1)` becomes "pull back along `h`" on the morphisms of
sheaves `ℤ ⟶ μₙ`. A global `n`-th root of unity `ζ` gives such a morphism `1 ↦ ζ`
(`AlgebraicGeometry.Etale.tateClassOfRootOfUnity`), and its pullback is `1 ↦ h^♯ ζ`; for `ζ`
primitive, `h^♯ ζ = γ(ζ) = ζ ^ c` with `c q ≡ 1 (mod n)`, so the operator is the multiplication by
`c = q⁻¹` in `Λ`.

## Main definitions

- `AlgebraicGeometry.Scheme.constantSheafIntToConstantZMod`: the reduction `ℤ ⟶ ℤ/n` of constant
  sheaves.
- `AlgebraicGeometry.Etale.tateClassOfRootOfUnity`: the class in `H⁰(X, Λ(1))` of an `n`-th root of
  unity.

## Main statements

- `AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum_tateClassOfRootOfUnity`: an
  endomorphism `h` with `h^♯ ζ = ζ ^ c` acts on the class of `ζ` by `c`.
- `AlgebraicGeometry.Etale.frobeniusOperator_tateWeilDatum`: geometric Frobenius acts on
  `H⁰(Spec k̄, Λ(r))` by `q^{-r}`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

namespace Scheme

variable {X Y : Scheme.{u}} (n : ℕ)

variable (X) in
/-- The reduction `ℤ ⟶ ℤ/n` of constant étale sheaves. -/
noncomputable def constantSheafIntToConstantZMod : X.constantSheafInt ⟶ X.constantZMod n :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.uliftIntToZMod.{u + 1} n)

/-- The morphism `ℤ ⟶ μₙ`, `1 ↦ ζ ^ c`, is `c` times the morphism `1 ↦ ζ`. -/
lemma constantSheafIntToConstantZMod_comp_constantZModToRootsOfUnitySheaf_pow (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ n = 1) (c : ℕ) (hζc : (ζ ^ c) ^ n = 1) :
    X.constantSheafIntToConstantZMod n ≫ X.constantZModToRootsOfUnitySheaf n (ζ ^ c) hζc =
      c • (X.constantSheafIntToConstantZMod n ≫ X.constantZModToRootsOfUnitySheaf n ζ hζ) := by
  refine equalizer.hom_ext ?_
  rw [Category.assoc, Preadditive.nsmul_comp, Category.assoc]
  erw [kernel.lift_ι, kernel.lift_ι]
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  apply (adj.homEquiv _ _).injective
  rw [constantSheafIntToConstantZMod, Adjunction.homEquiv_naturality_left,
    adj.homEquiv_unit (f := c • _), Functor.map_nsmul, Preadditive.comp_nsmul,
    ← adj.homEquiv_unit, Adjunction.homEquiv_naturality_left,
    constantSheafAdj_homEquiv_constantZModToGmSheaf,
    constantSheafAdj_homEquiv_constantZModToGmSheaf]
  apply AddCommGrpCat.hom_ext_uliftInt
  have h₂ : c • (ULift.up ((1 : ℕ) : ZMod n) : ULift.{u + 1} (ZMod n)) =
      ULift.up ((c : ℕ) : ZMod n) :=
    ULift.ext (by simp)
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_nsmul, AddMonoidHom.nsmul_apply,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddCommGrpCat.uliftIntToZMod_apply_one, ← map_nsmul, h₂, zmodToGmSections_natCast,
    zmodToGmSections_natCast, pow_one]

/-- **Pulling back the morphism `1 ↦ ζ` of sheaves `ℤ ⟶ μₙ`.** For an endomorphism `g` of `X`
with `g^♯ ζ = ζ ^ c`, the pullback of `ℤ ⟶ μₙ`, `1 ↦ ζ`, along `g`, followed by the comparison
`g^* μₙ ⟶ μₙ`, is `c` times `1 ↦ ζ`, through `g^* ℤ ≅ ℤ`. -/
lemma upperStar_map_constantZModToRootsOfUnitySheaf_comp_eq_nsmul [NeZero n] (g : X ⟶ X)
    (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ n = 1) (c : ℕ) (hc : Units.map g.appTop.hom.toMonoidHom ζ = ζ ^ c) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).map
        (X.constantSheafIntToConstantZMod n ≫ X.constantZModToRootsOfUnitySheaf n ζ hζ) ≫
        upperStarRootsOfUnitySheafToRootsOfUnitySheaf n g =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app _ ≫
        (c • (X.constantSheafIntToConstantZMod n ≫ X.constantZModToRootsOfUnitySheaf n ζ hζ)) := by
  have hθ : ∀ (ζ' : Γ(X, ⊤)ˣ) (hζ' : ζ' ^ n = 1) (hζc : (ζ ^ c) ^ n = 1), ζ' = ζ ^ c →
      X.constantZModToRootsOfUnitySheaf n ζ' hζ' =
        X.constantZModToRootsOfUnitySheaf n (ζ ^ c) hζc := by
    rintro _ _ _ rfl
    rfl
  have hζc : (ζ ^ c) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hnat := (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.naturality
    (AddCommGrpCat.uliftIntToZMod.{u + 1} n)
  rw [Functor.map_comp, Category.assoc, upperStar_map_constantZModToRootsOfUnitySheaf_comp,
    hθ _ _ hζc hc, ← constantSheafIntToConstantZMod_comp_constantZModToRootsOfUnitySheaf_pow n ζ hζ
      c hζc, constantSheafIntToConstantZMod, ← Category.assoc, ← Category.assoc]
  exact hnat =≫ _

end Scheme

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- The morphism `ℤ ⊗ Λ ⟶ μₙ ⊗ Λ` of étale sheaves of `Λ`-modules given by an `n`-th root of unity
`ζ`, `n` the characteristic of `Λ`: the extension of scalars of `1 ↦ ζ`. -/
noncomputable def extendScalarsRootOfUnity (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ ringChar Λ = 1) :
    (extendScalars Λ X).obj X.constantSheafInt ⟶
      (extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ)) :=
  (extendScalars Λ X).map
    (X.constantSheafIntToConstantZMod _ ≫ X.constantZModToRootsOfUnitySheaf _ ζ hζ)

/-- The class `[ζ] ∈ H⁰(X, Λ(1)) = Hom(Λ_X, Λ_X(1))` of an `n`-th root of unity `ζ`, `n` the
characteristic of `Λ`:
```
           ≅                    1 ↦ ζ                       ≅
  Λ_X ─────────▶ (ℤ ⊗ Λ)[0] ──────────────▶ (μₙ ⊗ Λ)[0] ─────────▶ Λ_X(1)
```
through the identifications
`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsInt` and
`AlgebraicGeometry.Etale.tateTwistObjectOneIso`. -/
noncomputable def tateClassOfRootOfUnity (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ ringChar Λ = 1) :
    𝟙_ (DerivedCategoryModule Λ X) ⟶ tateObject Λ X 1 :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map (extendScalarsRootOfUnity Λ ζ hζ) ≫
      (tateTwistObjectOneIso X Λ).inv

omit [HasInvertibleExponent Λ X] in
/-- The pullback of the extension of scalars of `1 ↦ ζ` along an endomorphism `g` with
`g^♯ ζ = ζ ^ c`, followed by the comparison `g^*(μₙ ⊗ Λ) ⟶ μₙ ⊗ Λ`, is `c` times the extension of
scalars of `1 ↦ ζ`, through `g^*(ℤ ⊗ Λ) ≅ ℤ ⊗ Λ`. -/
lemma upperStar_map_extendScalarsRootOfUnity (g : X ⟶ X) (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ ringChar Λ = 1) (c : ℕ) (hc : Units.map g.appTop.hom.toMonoidHom ζ = ζ ^ c) :
    (g)^*[ModuleCat.{u + 1} Λ].map (extendScalarsRootOfUnity Λ ζ hζ) ≫
        (upperStarExtendScalarsIso Λ g).hom.app (X.rootsOfUnitySheaf (ringChar Λ)) ≫
          (extendScalars Λ X).map
            (upperStarRootsOfUnitySheafToRootsOfUnitySheaf (ringChar Λ) g) =
      ((upperStarExtendScalarsIso Λ g).hom.app X.constantSheafInt ≫
        (extendScalars Λ X).map
          ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app _)) ≫
        (c • extendScalarsRootOfUnity Λ ζ hζ) := by
  have hnat := (upperStarExtendScalarsIso Λ g).hom.naturality
    (X.constantSheafIntToConstantZMod _ ≫ X.constantZModToRootsOfUnitySheaf _ ζ hζ)
  simp only [Functor.comp_map] at hnat
  rw [extendScalarsRootOfUnity, reassoc_of% hnat, ← Functor.map_comp,
    upperStar_map_constantZModToRootsOfUnitySheaf_comp_eq_nsmul _ g ζ hζ c hc, Functor.map_comp,
    Functor.map_nsmul, Category.assoc]

/-- **An endomorphism `h` with `h^♯ ζ = ζ ^ c` acts on the class of `ζ` by `c`**: the Frobenius
operator of the Tate datum `τ_1 : Lh^* Λ(1) ≅ Λ(1)` sends the class `[ζ] ∈ H⁰(X, Λ(1))` of an
`n`-th root of unity (`AlgebraicGeometry.Etale.tateClassOfRootOfUnity`) to `c • [ζ]`. -/
theorem frobeniusOperator_tateWeilDatum_tateClassOfRootOfUnity (h : X ⟶ X) (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ ringChar Λ = 1) (c : ℕ) (hc : Units.map h.appTop.hom.toMonoidHom ζ = ζ ^ c) :
    frobeniusOperator h (tateWeilDatum Λ h 1).hom (tateClassOfRootOfUnity Λ ζ hζ) =
      (c : Λ) • tateClassOfRootOfUnity Λ ζ hζ := by
  have hT := leftDerivedUpperStar_map_tateTwistObjectOneIso Λ h
  have hE := leftDerivedUpperStar_map_constantComplexIsoSingleFunctorExtendScalarsInt Λ h
  have hσ := (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) h).hom.naturality
    (extendScalarsRootOfUnity Λ ζ hζ)
  have hS := congrArg (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0).map (upperStar_map_extendScalarsRootOfUnity Λ h ζ hζ c hc)
  have hη : (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) h).hom =
      (leftDerivedUpperStarConstantComplexIso Λ h).hom :=
    leftDerivedUpperStarUnitIso_hom_eq_η h
  have hτ : (tateWeilDatum Λ h 1).hom = (leftDerivedUpperStarTateTwistObjectIso Λ h 1).hom := rfl
  simp only [Functor.comp_map] at hσ
  simp only [Functor.map_comp, Functor.map_nsmul, Category.assoc] at hS hE
  rw [frobeniusOperator_apply, hτ, ← cancel_mono (tateTwistObjectOneIso X Λ).hom, Category.assoc,
    Category.assoc, ← hT, tateClassOfRootOfUnity]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc, Linear.smul_comp,
    Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% hσ, hS]
  simp only [Preadditive.comp_nsmul]
  rw [reassoc_of% hE, ← hη, Iso.inv_hom_id_assoc, Nat.cast_smul_eq_nsmul]

omit [NeZero (ringChar Λ)] [HasInvertibleExponent Λ X] in
/-- Extension of scalars of `1 ↦ ζ` is an epimorphism when `θ_ζ : ℤ/n ⟶ μₙ` is an isomorphism:
`ℤ ⟶ ℤ/n` is surjective, and the constant sheaf functor and extension of scalars are left
adjoints. -/
lemma epi_extendScalarsRootOfUnity (ζ : Γ(X, ⊤)ˣ) (hζ : ζ ^ ringChar Λ = 1)
    [IsIso (X.constantZModToRootsOfUnitySheaf _ ζ hζ)] :
    Epi (extendScalarsRootOfUnity Λ ζ hζ) := by
  have : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).isLeftAdjoint
  have : Epi (AddCommGrpCat.uliftIntToZMod.{u + 1} (ringChar Λ)) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro x
    obtain ⟨a, ha⟩ := ZMod.castHom_surjective (dvd_zero (ringChar Λ)) x.down
    exact ⟨ULift.up a, ULift.ext ha⟩
  dsimp only [extendScalarsRootOfUnity, constantSheafIntToConstantZMod]
  infer_instance

/-- The class `[ζ] ∈ H⁰(X, Λ(1))` of an `n`-th root of unity `ζ` for which `θ_ζ : ℤ/n ⟶ μₙ` is an
isomorphism is not torsion, `X` being connected and `Λ(1) ≅ Λ`. -/
lemma eq_zero_of_smul_tateClassOfRootOfUnity_eq_zero [ConnectedSpace X] (ζ : Γ(X, ⊤)ˣ)
    (hζ : ζ ^ ringChar Λ = 1) [IsIso (X.constantZModToRootsOfUnitySheaf _ ζ hζ)]
    (e : tateObject Λ X 1 ≅ 𝟙_ (DerivedCategoryModule Λ X)) {b : Λ}
    (hb : b • tateClassOfRootOfUnity Λ ζ hζ = 0) : b = 0 := by
  have := epi_extendScalarsRootOfUnity Λ ζ hζ
  refine eq_zero_of_smul_id_eq_zero_of_iso_unit ((tateTwistObjectOneIso X Λ).symm ≪≫ e) ?_
  have hS : b • 𝟙 ((extendScalars Λ X).obj (X.rootsOfUnitySheaf (ringChar Λ))) = 0 := by
    rw [← cancel_epi (extendScalarsRootOfUnity Λ ζ hζ), Linear.comp_smul, Category.comp_id,
      comp_zero]
    apply (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      0).map_injective
    rw [Functor.map_smul, Functor.map_zero, ← cancel_epi
      (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom, ← cancel_mono
      (tateTwistObjectOneIso X Λ).inv, comp_zero, zero_comp, Linear.comp_smul, Linear.smul_comp,
      Category.assoc]
    rw [tateClassOfRootOfUnity] at hb
    exact hb
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul, hS, Functor.map_zero]

end Etale

namespace Etale

variable (k : Type u) [Field k] [Fintype k]

/-- The geometric Frobenius `γ` of `k̄` over the finite field `k`, the inverse of `z ↦ z ^ q`,
acts on a primitive `n`-th root of unity `ζ` by `γ(ζ) = ζ ^ c` with `c q ≡ 1 (mod n)`. -/
theorem exists_geometricFrobeniusAlgEquivOfAlgebraic_eq_pow {n : ℕ} [NeZero n]
    {ζ : AlgebraicClosure k} (hζ : IsPrimitiveRoot ζ n) :
    ∃ c : ℕ, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) ζ = ζ ^ c ∧
      c * Fintype.card k ≡ 1 [MOD n] := by
  have hF : IsPrimitiveRoot (ζ ^ Fintype.card k) n :=
    hζ.map_of_injective (f := FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k))
      (FiniteField.frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)).injective
  obtain ⟨c, -, hc⟩ := hF.eq_pow_of_pow_eq_one hζ.pow_eq_one
  refine ⟨c, ?_, ?_⟩
  · rw [FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv, AlgEquiv.aut_inv,
      AlgEquiv.symm_apply_eq]
    refine hc.symm.trans ?_
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← pow_mul, mul_comm, pow_mul]
  · rw [hζ.eq_orderOf]
    refine (hζ.isOfFinOrder (NeZero.ne n)).pow_eq_pow_iff_modEq.1 ?_
    rw [mul_comm, pow_mul, hc, pow_one]

end Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [NeZero (ringChar Λ)] (k : Type u) [Field k] [Finite k]
  [HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure k)))]

/-- The geometric Frobenius of `k̄` over `k` acts on `H⁰(Spec k̄, Λ(1))` by `q⁻¹`: its Frobenius
scalar `c_1` (`AlgebraicGeometry.Etale.tateFrobeniusScalar`) satisfies `c_1 q = 1`. -/
theorem tateFrobeniusScalar_specGeometricFrobenius_mul_natCard :
    tateFrobeniusScalar Λ (specGeometricFrobenius k).asIso.hom 1 * (Nat.card k : Λ) = 1 := by
  let := Fintype.ofFinite k
  have hn : IsUnit ((ringChar Λ : ℕ) : AlgebraicClosure k) := by
    simpa using (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ)
      (Spec (.of (AlgebraicClosure k)))).map (Scheme.ΓSpecIso (.of (AlgebraicClosure k))).hom.hom
  have : NeZero ((ringChar Λ : ℕ) : AlgebraicClosure k) := ⟨hn.ne_zero⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure k) (ringChar Λ)
  obtain ⟨c, hγ, hcq⟩ := exists_geometricFrobeniusAlgEquivOfAlgebraic_eq_pow k hζ₀
  let u₀ := (hζ₀.isUnit (NeZero.ne _)).unit
  have hu₀ : u₀ ^ ringChar Λ = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hζ₀.pow_eq_one, Units.val_one])
  let ζ : Γ(Spec (.of (AlgebraicClosure k)), ⊤)ˣ :=
    Units.map (Scheme.ΓSpecIso (.of (AlgebraicClosure k))).inv.hom.toMonoidHom u₀
  have hζ : ζ ^ ringChar Λ = 1 := by rw [← map_pow, hu₀, map_one]
  have hc : Units.map (specGeometricFrobenius k).asIso.hom.appTop.hom.toMonoidHom ζ = ζ ^ c := by
    have key := congrArg (fun φ ↦ φ.hom ζ₀) (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k
        (AlgebraicClosure k)).toRingEquiv.toRingHom))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
    ext
    simp only [ζ, u₀, Units.coe_map, Units.val_pow_eq_pow_val, IsUnit.unit_spec,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, specGeometricFrobenius_hom]
    rw [← key, ← map_pow]
    exact congrArg _ hγ
  have : IsIso ((Spec (.of (AlgebraicClosure k))).constantZModToRootsOfUnitySheaf _ ζ hζ) :=
    (Spec (.of (AlgebraicClosure k))).isIso_constantZModToRootsOfUnitySheaf (ringChar Λ) (𝟙 _)
      hζ₀ ζ hζ (by simp [ζ, u₀])
  obtain ⟨e⟩ := nonempty_tateObject_iso_unit Λ (AlgebraicClosure k) 1
  rw [tateFrobeniusScalar_eq_of_frobeniusOperator_eq_smul Λ _ (tateClassOfRootOfUnity Λ ζ hζ)
    (fun _ hb ↦ eq_zero_of_smul_tateClassOfRootOfUnity_eq_zero Λ ζ hζ e hb)
    (frobeniusOperator_tateWeilDatum_tateClassOfRootOfUnity Λ _ ζ hζ c hc),
    ← Nat.cast_mul, Nat.card_eq_fintype_card, ← Nat.cast_one]
  exact (CharP.natCast_eq_natCast Λ (ringChar Λ)).2 hcq

/-- The cardinality `q` of `k` is a unit of `Λ`. -/
theorem isUnit_natCard_of_hasInvertibleExponent : IsUnit (Nat.card k : Λ) :=
  isUnit_iff_exists_inv'.2 ⟨_, tateFrobeniusScalar_specGeometricFrobenius_mul_natCard Λ k⟩

/-- Blueprint `definition-weil-structure--1`: Strict Weil data and the Tate datum.

The Tate datum `τ_r : Lg^* Λ(r) ≅ Λ(r)` (`AlgebraicGeometry.Etale.tateWeilDatum`) of the Tate
twist, for `g` the geometric Frobenius of `Spec k̄` over the finite field `k` with `q` elements, is
normalized as in `prose-10-21`: geometric Frobenius acts on
`H⁰(Spec k̄, Λ(r))` by `q^{-r}` (hence by `q^r` on `Λ(-r)`). Here `Λ` is a commutative ring of
characteristic `n ≠ 0` invertible on `Spec k̄`, so that `q` is a unit of `Λ`
(`AlgebraicGeometry.Etale.isUnit_natCard_of_hasInvertibleExponent`). -/
theorem frobeniusOperator_tateWeilDatum (r : ℤ)
    (x : 𝟙_ (DerivedCategoryModule Λ (Spec (.of (AlgebraicClosure k)))) ⟶
      tateObject Λ (Spec (.of (AlgebraicClosure k))) r) :
    frobeniusOperator (specGeometricFrobenius k).asIso.hom (tateWeilDatum Λ _ r).hom x =
      (((isUnit_natCard_of_hasInvertibleExponent Λ k).unit⁻¹ ^ r : Λˣ) : Λ) • x := by
  have hu : tateFrobeniusUnit Λ (specGeometricFrobenius k).asIso.hom =
      (isUnit_natCard_of_hasInvertibleExponent Λ k).unit⁻¹ := by
    refine Units.ext ?_
    rw [val_tateFrobeniusUnit, Units.inv_eq_of_mul_eq_one_left]
    rw [IsUnit.unit_spec]
    exact tateFrobeniusScalar_specGeometricFrobenius_mul_natCard Λ k
  rw [frobeniusOperator_tateWeilDatum_eq_zpow_smul, hu]

end Etale

end AlgebraicGeometry
