# Cohomology of a complex identified with a derived complex

Author: Worker 1119.

This helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement` relates a cochain complex `K` to
the right derived functors of an additive functor `F : C ⥤ D` (with `C` having enough
injectives) once `K` has been identified, in the derived category of `D`, with the derived
complex `DerivedPlus.derivedComplex F` of an object. It contains no `sorry` and no new axioms.

## Declarations

- `DerivedPlus.homologyIsoOfIsoDerivedComplex F α n`: for
  `α : Q.obj K ≅ Plus.ι.obj ((derivedComplex F).obj A)` and `n : ℕ`, the isomorphism
  `K.homology n ≅ (F.rightDerived n).obj A`. It is the composite of the inverse of
  `DerivedCategory.homologyFunctorFactors`, the derived-category homology of `α`, and the
  Library's `DerivedPlus.homologyIso F (injectiveResolution A) n`, equivalently
  the component of `DerivedPlus.homologyNatIso F n`. This construction is
  reused from `Langlands.Cohomology.DerivedPlus`.
- `homologyMap_comp_homologyIsoOfDerivedIso`: given a chain map `ψ : K ⟶ K'`, a morphism
  `u : A ⟶ B` and identifications `α`, `β` with
  `Q.map ψ ≫ β.hom = α.hom ≫ Plus.ι.map ((derivedComplex F).map u)`, the square
  `homologyMap ψ n ≫ (DerivedPlus.homologyIsoOfIsoDerivedComplex F β n).hom =
  (DerivedPlus.homologyIsoOfIsoDerivedComplex F α n).hom ≫ (F.rightDerived n).map u` commutes. The proof composes
  the naturality of `homologyFunctorFactors` in `ψ`, the image of the hypothesis under the
  derived-category homology functor, and the naturality of `homologyNatIso F n` in `u`. These
  are chained with explicit `Eq.trans` steps, because the objects `K.homology n` and
  `(homologyFunctor _ _ n).obj K` agree only up to definitional unfolding.
- `isZero_homology_of_derivedIso`: such a `K` has zero cohomology in negative degrees, by
  `DerivedPlus.isZero_homology_of_neg` transported along the same isomorphisms.
- `isIso_iff_of_comm`: in a commutative square whose vertical maps are isomorphisms, one
  horizontal map is an isomorphism exactly when the other is.
- `detectsZero_of_comm`: for module maps `u₁, u₂` out of `A` and `u₁', u₂'` out of `A'`,
  intertwined by an injective `e : A ⟶ A'` and maps `e₁, e₂` of the targets
  (`u₁ ≫ e₁ = e ≫ u₁'`, `u₂ ≫ e₂ = e ≫ u₂'`): if `u₁'` and `u₂'` jointly detect zero, that is
  `u₁' c = 0` and `u₂' c = 0` force `c = 0`, then so do `u₁` and `u₂`.
- `isIso_rightDerived_zero_map_iff`: for a left exact additive `G`, `(G.rightDerived 0).map u`
  is an isomorphism exactly when `G.map u` is (Mathlib's `rightDerivedZeroIsoSelf` with
  `NatIso.isIso_map_iff`).

## Provenance

Internal lemmas, not taken from the literature. They translate between the derived-category
compatibility squares of `RestrictionPerfectModelsStatement` and the cohomology-level
statements of `FibreH0RestrictionSpreadStatement` in the proof of Stacks tag 0BF2 (see
`FibreFrameLiftingStatement.md`).
