/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrobeniusDatum
public import WeilConjectures.EtaleCohomology.Purity.Smooth.WeilDatum
public import WeilConjectures.SixFunctors.Etale.Derived.VerdierDualWeil

/-!
# Weil equivariance of smooth purity and of the smooth trace

Let `f : X ⟶ Y` be smooth of relative dimension `d`, and let `g_X`, `g_Y` be endomorphisms of `X`
and `Y` forming a cartesian square `g_X ≫ f = f ≫ g_Y` (in the blueprint, the geometric-Galois
Frobenii of `sec-Weil-complexes`). A Weil datum `φ_K : Lg_Y^* K ⟶ K` induces
data on the source and on the target of the smooth purity map `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K`
(`definition-weil-structure--1`: `AlgebraicGeometry.Etale.smoothPurityWeilDatum` and
`AlgebraicGeometry.Etale.upperShriekWeilDatum`, constructed in
`WeilConjectures.EtaleCohomology.Purity.Smooth.WeilDatum`), and on compactly supported direct
images (`prose-10-20`). This file proves that purity, the exceptional counit
and the smooth trace are morphisms of Weil objects
(`proposition-purity-trace-commute-frobenius`), that the same holds for the scheme-Frobenius
forms of the data (`proposition-purity-trace-commute-frobenius`), and that these equivariances
are transported by every functor commuting with the Frobenius pullbacks
(`prop-pur-weil-equivariance-compatibilities`).

## Main definitions

- `AlgebraicGeometry.Etale.compactSupportWeilTransport`,
  `AlgebraicGeometry.Etale.schemeFrobeniusWeilDatum` (`prose-10-20`).
- `AlgebraicGeometry.Etale.smoothCoefficientTrace` (`definition-trace-map`).

## Main statements

- `AlgebraicGeometry.Etale.isWeilMorphism_smoothPurityIso_hom`,
  `AlgebraicGeometry.Etale.isWeilMorphism_counit`,
  `AlgebraicGeometry.Etale.isWeilMorphism_smoothCoefficientTrace`
  (`proposition-purity-trace-commute-frobenius`).
- `AlgebraicGeometry.Etale.PurityFrobeniusDatum.isWeilMorphism_schemeFrobenius_smoothPurityIso_hom`
  and its companions (`proposition-purity-trace-commute-frobenius`).
- `AlgebraicGeometry.Etale.isWeilEquivariant_map_smoothPurityIso_hom` and its companions
  (`prop-pur-weil-equivariance-compatibilities`).

## Implementation notes

The library constructs the smooth purity map `γ_{f,K}` from an identification `θ` of the
dualizing complex and a natural tensor formula `Φ` (`AlgebraicGeometry.Etale.smoothPurityIso`),
which are arguments here. The purity square is proved for arbitrary `θ` and `Φ`. The counit and
trace squares use, as in the blueprint, that the smooth pullback exchange of
`proposition-compatibility-purity-base-change--1` is the exceptional base change, i.e. the mate of
the compact-support base change (`AlgebraicGeometry.Etale.upperShriekBaseChangeMap`); this is the
base-change compatibility of purity of `proposition-exceptional-inverse-image-smooth-morphism` (c)
for the canonical purity map, which is not constructed in the library, so it is a hypothesis `hcoh`.
For arbitrary `θ` and `Φ` it can fail: a natural automorphism of `Rf^!` that does not commute with
`Lg^*` (for instance `±1` on two components of `X` swapped by `g`) changes `Φ` without changing
anything else.

The comparisons `κ` between scheme-Frobenius and geometric-Galois pullbacks are those of the
purity Frobenius datum (`AlgebraicGeometry.Etale.PurityFrobeniusDatum`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Naturality

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X : Scheme.{u}}

/-- The twist reassociation `M(m)[2m] ≅ M ⊗ Λ_X(m)[2m]` is natural in `M`. -/
@[reassoc]
lemma twistShiftObjIso_hom_naturality (m : ℤ) {M M' : DerivedCategoryModule Λ X}
    (v : M ⟶ M') :
    (twistShift Λ X m).map v ≫ (twistShiftObjIso Λ X m M').hom =
      (twistShiftObjIso Λ X m M).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map v).app
          ((twistShift Λ X m).obj (constantComplex Λ X)) := by
  have h := (derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ) (tateObject Λ X m)
    (2 * m)).inv.naturality v
  dsimp [derivedTensorRightShiftIso, derivedTensorRight] at h
  simp only [twistShiftObjIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    Category.assoc]
  erw [reassoc_of% h]
  rw [NatTrans.naturality]

end Naturality

section Purity

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [HasCompactification f]
  [HasInvertibleExponent Λ X]
  (θ : dualizingComplex Λ f ≅ (twistShift Λ X d).obj (constantComplex Λ X))
  (Φ : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (dualizingComplex Λ f) ≅
    R(f)^![Λ])

omit [HasInvertibleExponent Λ X] in
/-- The smooth purity map `γ_{f,K}` built from a tensor formula `Φ` natural in `K` is natural
in `K`. -/
lemma smoothPurityIso_hom_naturality {K K' : DerivedCategoryModule Λ Y} (v : K ⟶ K') :
    (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map v) ≫
        (smoothPurityIso Λ f K' θ (Φ.app K')).hom =
      (smoothPurityIso Λ f K θ (Φ.app K)).hom ≫ (R(f)^![Λ]).map v := by
  have h := Φ.hom.naturality v
  dsimp at h
  simp only [smoothPurityIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom,
    Category.assoc]
  rw [twistShiftObjIso_hom_naturality_assoc, ← NatTrans.naturality_assoc]
  erw [h]

variable {gX : X ⟶ X} {gY : Y ⟶ Y}

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Weil equivariance of purity and
trace, the purity square.

For a cartesian square `g_X ≫ f = f ≫ g_Y` and a Weil datum `φ_K` on `K`, the smooth purity map
`γ_{f,K} : Lf^* K(d)[2d] ⟶ Rf^! K` is a morphism of Weil objects for the data `φ^pur_{f,K}` and
`φ^!_{f,K}` of `definition-weil-structure--1`:
```
Lg_X^* Lf^* K(d)[2d] ──Lg_X^* γ──▶ Lg_X^* Rf^! K
        │ φ^pur                        │ φ^!
        ▼                              ▼
   Lf^* K(d)[2d] ─────────γ──────────▶ Rf^! K
```
-/
theorem isWeilMorphism_smoothPurityIso_hom (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    IsWeilMorphism gX (smoothPurityWeilDatum Λ d f sq.toCommSq φK)
      (upperShriekWeilDatum Λ f sq φK θ (Φ.app K) (Φ.app _))
      (smoothPurityIso Λ f K θ (Φ.app K)).hom := by
  unfold IsWeilMorphism smoothPurityWeilDatum upperShriekWeilDatum
  rw [reassoc_of% (leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom Λ f sq K θ (Φ.app K)
    θ (Φ.app _)), ← smoothPurityIso_hom_naturality, Category.assoc]

/-- Blueprint `definition-trace-map`: the coefficient-valued smooth trace
`Tr^sm_{f,K} : Rf_!(Lf^* K(d)[2d]) ──Rf_! γ──▶ Rf_! Rf^! K ──counit──▶ K`. -/
noncomputable def smoothCoefficientTrace (K : DerivedCategoryModule Λ Y)
    (φ : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex Λ f) ≅
      (rightDerivedUpperShriek Λ f).obj K) :
    (R(f)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶ K :=
  (R(f)_![ModuleCat.{u + 1} Λ]).map (smoothPurityIso Λ f K θ φ).hom ≫
    (rightDerivedUpperShriekAdjunction Λ f).counit.app K

variable [QuasiCompact f]

variable {Λ f} in
/-- Blueprint `prose-10-20`: Compact-support transport of a Weil datum.

For a cartesian square `g_X ≫ f = f ≫ g_Y` and a Weil datum `φ_M : Lg_X^* M ⟶ M`, the datum
```
Lg_Y^* Rf_! M ──Ex_!──▶ Rf_! Lg_X^* M ──Rf_! φ_M──▶ Rf_! M
```
on `Rf_! M`, through the compact-support base change of the square
(`AlgebraicGeometry.Etale.lowerShriekWeilDatum`). Its scheme-Frobenius form is
`AlgebraicGeometry.Etale.schemeFrobeniusWeilDatum`. -/
noncomputable abbrev compactSupportWeilTransport (sq : IsPullback gX f f gY)
    {M : DerivedCategoryModule Λ X} (φM : (L((gX)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M) :
    (L((gY)^*[ModuleCat.{u + 1} Λ])).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj M) ⟶
      (R(f)_![ModuleCat.{u + 1} Λ]).obj M :=
  lowerShriekWeilDatum sq φM

/-- Under the base-change compatibility `hcoh` of purity, the datum `φ^!_{f,K}` of
`definition-weil-structure--1` is the exceptional transport of `φ_K`
(`AlgebraicGeometry.Etale.upperShriekMateWeilDatum`). -/
lemma upperShriekWeilDatum_eq (sq : IsPullback gX f f gY) {K : DerivedCategoryModule Λ Y}
    (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (hcoh : (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ sq).app K) :
    upperShriekWeilDatum Λ f sq φK θ (Φ.app K) (Φ.app _) =
      upperShriekMateWeilDatum sq φK := by
  rw [upperShriekWeilDatum, upperShriekMateWeilDatum, hcoh]

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Weil equivariance of purity and
trace, the counit square.

If the smooth pullback exchange of the square is the exceptional base change `hcoh` (the
base-change compatibility of purity, `proposition-exceptional-inverse-image-smooth-morphism` (c)),
then the exceptional counit `Rf_! Rf^! K ⟶ K` is a morphism of Weil objects from the compact-support
transport of `φ^!_{f,K}` to `φ_K`. -/
theorem isWeilMorphism_counit (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (hcoh : (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ sq).app K) :
    IsWeilMorphism gY
      (compactSupportWeilTransport sq (upperShriekWeilDatum Λ f sq φK θ (Φ.app K) (Φ.app _))) φK
      ((rightDerivedUpperShriekAdjunction Λ f).counit.app K) := by
  rw [upperShriekWeilDatum_eq Λ f θ Φ sq φK hcoh]
  exact isWeilMorphism_counit_upperShriekMateWeilDatum Λ sq φK

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Weil equivariance of purity and
trace, the trace square.

Under the base-change compatibility `hcoh` of purity, the smooth trace
`Tr^sm_{f,K} : Rf_!(Lf^* K(d)[2d]) ⟶ K` is a morphism of Weil objects from the compact-support
transport of `φ^pur_{f,K}` to `φ_K`: it is the composite of the purity square, pushed forward
along `Rf_!`, with the counit square. -/
theorem isWeilMorphism_smoothCoefficientTrace (sq : IsPullback gX f f gY)
    {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (hcoh : (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ sq).app K) :
    IsWeilMorphism gY
      (compactSupportWeilTransport sq (smoothPurityWeilDatum Λ d f sq.toCommSq φK)) φK
      (smoothCoefficientTrace Λ f θ K (Φ.app K)) :=
  ((isWeilMorphism_smoothPurityIso_hom Λ f θ Φ sq φK).rightDerivedLowerShriek_map sq).comp
    (isWeilMorphism_counit Λ f θ Φ sq φK hcoh)

end Purity

section SchemeFrobenius

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {F g : X ⟶ X}

/-- Blueprint `prose-10-20`: Compact-support transport of a Weil datum,
the scheme-Frobenius form.

The scheme-Frobenius form `u_N = φ_N ∘ κ_N : LΦ^* N ⟶ N` of a Weil datum `φ_N : Lg^* N ⟶ N`,
for a comparison `κ : LΦ^* ⟶ Lg^*` of the pullbacks along the scheme Frobenius `Φ` and the
geometric-Galois automorphism `g` (in the blueprint, `κ_X` or `κ_Y` of the purity Frobenius
datum `AlgebraicGeometry.Etale.PurityFrobeniusDatum`). -/
noncomputable def schemeFrobeniusWeilDatum
    (κ : L((F)^*[ModuleCat.{u + 1} Λ]) ⟶ L((g)^*[ModuleCat.{u + 1} Λ]))
    {N : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N) :
    (L((F)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N :=
  κ.app N ≫ φ

/-- A morphism of Weil objects for the geometric-Galois data is one for their scheme-Frobenius
forms (`AlgebraicGeometry.Etale.schemeFrobeniusWeilDatum`): precomposing the vertical maps of
an equivariance square with `κ` preserves its commutativity. -/
lemma IsWeilMorphism.schemeFrobeniusWeilDatum
    (κ : L((F)^*[ModuleCat.{u + 1} Λ]) ⟶ L((g)^*[ModuleCat.{u + 1} Λ]))
    {M N : DerivedCategoryModule Λ X} {φM : (L((g)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ M}
    {φN : (L((g)^*[ModuleCat.{u + 1} Λ])).obj N ⟶ N} {v : M ⟶ N}
    (hv : IsWeilMorphism g φM φN v) :
    IsWeilMorphism F (schemeFrobeniusWeilDatum κ φM) (schemeFrobeniusWeilDatum κ φN) v := by
  unfold IsWeilMorphism Etale.schemeFrobeniusWeilDatum at *
  rw [← Category.assoc, κ.naturality, Category.assoc, hv, Category.assoc]

end SchemeFrobenius

namespace PurityFrobeniusDatum

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {k₀ : Type u} [Field k₀]
  [Finite k₀] {X₀ Y₀ : Scheme.{u}} {aX : X₀ ⟶ Spec (.of k₀)} {aY : Y₀ ⟶ Spec (.of k₀)}
  {f₀ : X₀ ⟶ Y₀} {hf₀ : f₀ ≫ aY = aX} (D : PurityFrobeniusDatum Λ f₀ hf₀) {d : ℕ}
  [HasCompactification (Hom.geometricFiberMap f₀ hf₀)]
  [HasInvertibleExponent Λ aX.geometricFiber]
  (θ : dualizingComplex Λ (Hom.geometricFiberMap f₀ hf₀) ≅
    (twistShift Λ aX.geometricFiber d).obj (constantComplex Λ aX.geometricFiber))
  (Φ : L((Hom.geometricFiberMap f₀ hf₀)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) aX.geometricFiber).flip.obj
        (dualizingComplex Λ (Hom.geometricFiberMap f₀ hf₀)) ≅
    R(Hom.geometricFiberMap f₀ hf₀)^![Λ])
  {K : DerivedCategoryModule Λ aY.geometricFiber}
  (φK : (L((aY.geometricGaloisFrobenius.asIso.hom)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Scheme-Frobenius forms of Weil
equivariance, the purity square.

Precomposing the data `φ^pur_{f,K}` and `φ^!_{f,K}` with the comparison `κ_X` of the purity
Frobenius datum, the smooth purity map is a morphism of Weil objects for the scheme Frobenius
`Φ_X`. -/
theorem isWeilMorphism_schemeFrobenius_smoothPurityIso_hom :
    IsWeilMorphism D.schemeFrobeniusX
      (schemeFrobeniusWeilDatum D.κX.hom
        (smoothPurityWeilDatum Λ d (Hom.geometricFiberMap f₀ hf₀)
          (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀).toCommSq φK))
      (schemeFrobeniusWeilDatum D.κX.hom (upperShriekWeilDatum Λ _
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀) φK θ (Φ.app K)
        (Φ.app _)))
      (smoothPurityIso Λ (Hom.geometricFiberMap f₀ hf₀) K θ (Φ.app K)).hom :=
  (isWeilMorphism_smoothPurityIso_hom Λ _ θ Φ _ φK).schemeFrobeniusWeilDatum D.κX.hom

variable [QuasiCompact (Hom.geometricFiberMap f₀ hf₀)]

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Scheme-Frobenius forms of Weil
equivariance, the counit square.

Under the base-change compatibility `hcoh` of purity, precomposing with the comparison `κ_Y`,
the exceptional counit is a morphism of Weil objects for the scheme Frobenius `Φ_Y`. -/
theorem isWeilMorphism_schemeFrobenius_counit
    (hcoh : (smoothPullbackExchange Λ (Hom.geometricFiberMap f₀ hf₀)
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀) K θ (Φ.app K) θ
        (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)).app K) :
    IsWeilMorphism D.schemeFrobeniusY
      (schemeFrobeniusWeilDatum D.κY.hom (compactSupportWeilTransport
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)
        (upperShriekWeilDatum Λ _
          (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀) φK θ (Φ.app K)
          (Φ.app _))))
      (schemeFrobeniusWeilDatum D.κY.hom φK)
      ((rightDerivedUpperShriekAdjunction Λ
        (Hom.geometricFiberMap f₀ hf₀)).counit.app K) :=
  (isWeilMorphism_counit Λ _ θ Φ _ φK hcoh).schemeFrobeniusWeilDatum D.κY.hom

/-- Blueprint `proposition-purity-trace-commute-frobenius`: Scheme-Frobenius forms of Weil
equivariance, the trace square.

Under the base-change compatibility `hcoh` of purity, precomposing with the comparison `κ_Y`,
the smooth trace is a morphism of Weil objects for the scheme Frobenius `Φ_Y`. -/
theorem isWeilMorphism_schemeFrobenius_smoothCoefficientTrace
    (hcoh : (smoothPullbackExchange Λ (Hom.geometricFiberMap f₀ hf₀)
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀) K θ (Φ.app K) θ
        (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)).app K) :
    IsWeilMorphism D.schemeFrobeniusY
      (schemeFrobeniusWeilDatum D.κY.hom (compactSupportWeilTransport
        (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀)
        (smoothPurityWeilDatum Λ d (Hom.geometricFiberMap f₀ hf₀)
          (Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap f₀ hf₀).toCommSq φK)))
      (schemeFrobeniusWeilDatum D.κY.hom φK)
      (smoothCoefficientTrace Λ _ θ K (Φ.app K)) :=
  (isWeilMorphism_smoothCoefficientTrace Λ _ θ Φ _ φK hcoh).schemeFrobeniusWeilDatum D.κY.hom

end PurityFrobeniusDatum

section Compatibilities

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [HasCompactification f]
  [HasInvertibleExponent Λ X]
  (θ : dualizingComplex Λ f ≅ (twistShift Λ X d).obj (constantComplex Λ X))
  (Φ : L((f)^*[ModuleCat.{u + 1} Λ]) ⋙
      (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (dualizingComplex Λ f) ≅
    R(f)^![Λ])
  {gX : X ⟶ X} {gY : Y ⟶ Y} (sq : IsPullback gX f f gY)
  {K : DerivedCategoryModule Λ Y} (φK : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)

/-- Blueprint `prop-pur-weil-equivariance-compatibilities`: Compatibilities of Weil
equivariance, the purity square.

The purity square is transported by every functor `T : D(X_ét, Λ) ⥤ 𝒟` commuting with the
Frobenius pullbacks, `c : Lg_X^* ⋙ T ≅ T ⋙ G'` — a finite reduction or scalar extension of the
coefficients, or a pullback along a Frobenius-compatible base change: `T γ_{f,K}` is a morphism
of Weil objects for the transported data. -/
theorem isWeilEquivariant_map_smoothPurityIso_hom {𝒟 : Type*} [Category* 𝒟] {G' : 𝒟 ⥤ 𝒟}
    (T : DerivedCategoryModule Λ X ⥤ 𝒟) (c : L((gX)^*[ModuleCat.{u + 1} Λ]) ⋙ T ≅ T ⋙ G') :
    IsWeilEquivariant G' (transportWeilDatum T c (smoothPurityWeilDatum Λ d f sq.toCommSq φK))
      (transportWeilDatum T c (upperShriekWeilDatum Λ f sq φK θ (Φ.app K) (Φ.app _)))
      (T.map (smoothPurityIso Λ f K θ (Φ.app K)).hom) :=
  IsWeilEquivariant.map T c (isWeilMorphism_smoothPurityIso_hom Λ f θ Φ sq φK)

variable [QuasiCompact f]

/-- Blueprint `prop-pur-weil-equivariance-compatibilities`: Compatibilities of Weil
equivariance, the counit square.

Under the base-change compatibility `hcoh` of purity, the counit square is transported by every
functor `T : D(Y_ét, Λ) ⥤ 𝒟` commuting with the Frobenius pullbacks. -/
theorem isWeilEquivariant_map_counit {𝒟 : Type*} [Category* 𝒟] {G' : 𝒟 ⥤ 𝒟}
    (T : DerivedCategoryModule Λ Y ⥤ 𝒟) (c : L((gY)^*[ModuleCat.{u + 1} Λ]) ⋙ T ≅ T ⋙ G')
    (hcoh : (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ sq).app K) :
    IsWeilEquivariant G'
      (transportWeilDatum T c
        (compactSupportWeilTransport sq (upperShriekWeilDatum Λ f sq φK θ (Φ.app K) (Φ.app _))))
      (transportWeilDatum T c φK)
      (T.map ((rightDerivedUpperShriekAdjunction Λ f).counit.app K)) :=
  IsWeilEquivariant.map T c (isWeilMorphism_counit Λ f θ Φ sq φK hcoh)

/-- Blueprint `prop-pur-weil-equivariance-compatibilities`: Compatibilities of Weil
equivariance, the trace square.

Under the base-change compatibility `hcoh` of purity, the trace square is transported by every
functor `T : D(Y_ét, Λ) ⥤ 𝒟` commuting with the Frobenius pullbacks. -/
theorem isWeilEquivariant_map_smoothCoefficientTrace {𝒟 : Type*} [Category* 𝒟] {G' : 𝒟 ⥤ 𝒟}
    (T : DerivedCategoryModule Λ Y ⥤ 𝒟) (c : L((gY)^*[ModuleCat.{u + 1} Λ]) ⋙ T ≅ T ⋙ G')
    (hcoh : (smoothPullbackExchange Λ f sq K θ (Φ.app K) θ (Φ.app _)).hom =
      (upperShriekBaseChangeMap Λ sq).app K) :
    IsWeilEquivariant G'
      (transportWeilDatum T c
        (compactSupportWeilTransport sq (smoothPurityWeilDatum Λ d f sq.toCommSq φK)))
      (transportWeilDatum T c φK) (T.map (smoothCoefficientTrace Λ f θ K (Φ.app K))) :=
  IsWeilEquivariant.map T c (isWeilMorphism_smoothCoefficientTrace Λ f θ Φ sq φK hcoh)

end Compatibilities

end Etale

end AlgebraicGeometry
