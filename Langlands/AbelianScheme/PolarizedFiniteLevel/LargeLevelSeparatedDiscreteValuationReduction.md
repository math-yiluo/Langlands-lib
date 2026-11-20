# Separatedness of the moduli scheme from discrete valuative uniqueness of data

The module
`Langlands.AbelianScheme.PolarizedFiniteLevel.LargeLevelSeparatedDiscreteValuationReduction`
contains two proved declarations. Neither has external hypotheses beyond its
displayed arguments. Both use only the standard axioms.

## 1. The noetherian valuative criterion for separatedness

`Langlands.AlgebraicGeometry.isSeparated_of_discreteValuativeUniqueness`
(universe `u`). Let `S` be a locally noetherian scheme and `f : X ⟶ S` a morphism
locally of finite type. Assume that for every valuative commutative square
`sq : ValuativeCommSq f` (Mathlib) whose ring `sq.R` is a discrete valuation
ring, the lifts of `sq.commSq` form a subsingleton. Then `f` is separated.

This is the implication (3) ⇒ (1) of Stacks Lemma 32.15.2 (Tag 0207), registered
snapshot `stacks-noetherian-valuative-criterion-2026-11-19` (content SHA-256
`9866a5bc72a396ef3c13a5341fd9a1d6b487894a8232d31aae3d6d1257fed566`, file
`0207.html`):

> Let S be a locally Noetherian scheme. Let f : X → S be a morphism of schemes.
> Assume f is locally of finite type. The following are equivalent: (1) The
> morphism f is separated. […] (3) For all diagrams (32.15.1.1) with A a
> discrete valuation ring there is at most one dotted arrow.

### The Lean proof

The Lean proof differs from the Stacks proof. It shows that the diagonal
`Δ = pullback.diagonal f` is a closed immersion.

1. `X` is locally noetherian (`LocallyOfFiniteType.isLocallyNoetherian`). The
   diagonal is locally of finite type.
2. The diagonal satisfies discrete valuative existence, in the sense of the
   Library's `DiscreteValuativeCriterion.Existence` (module
   `Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesStatement`).
   Take a valuative square for `Δ` with `R` a discrete valuation ring, with top
   map `i₁ : Spec K ⟶ X` and bottom map `i₂ : Spec R ⟶ X ×_S X`. Then `i₂ ≫ fst`
   and `i₂ ≫ snd` are two lifts of one valuative square for `f`. By hypothesis
   they are equal, so `i₂ ≫ fst` is a lift for the square of `Δ`. The equation
   `(i₂ ≫ fst) ≫ Δ = i₂` is checked on both projections of the pullback.
3. The Library theorem `DiscreteValuativeCriterion.Existence.specializingMap`
   (module `Langlands.AlgebraicGeometry.Picard.DiscreteValuativeClosedIrreducibleImagesProof`)
   applies to `Δ : X ⟶ X ×_S X`. It needs the target `X ×_S X` to be locally
   noetherian. Mathlib infers this: `X` is locally noetherian by step 1, and
   either projection `X ×_S X ⟶ X` is locally of finite type, as a base change
   of `f`. The theorem shows that `Δ` is specializing. Mathlib's
   `isClosedMap_iff_specializingMap` makes `Δ` a closed map. It needs `Δ` quasi-compact. That holds because `X` is locally noetherian,
   hence a quasi-separated space (Mathlib instance
   `IsLocallyNoetherian.quasiSeparatedSpace`), so `f` is quasi-separated.
4. The diagonal is an immersion, hence a preimmersion. A preimmersion with
   closed range is a closed immersion (`IsClosedImmersion.of_isPreimmersion`).

## 2. The reduction

`Langlands.AbelianScheme.PolarizedFiniteLevel.largeLevelSeparated_of_datumUniqueness`
is a proved definition of type

`LargeLevelFiniteTypeStatement → DiscreteValuationDatumUniquenessStatement.{0} →
LargeLevelSeparatedStatement`.

It is an internal derivation and makes no external mathematical claim beyond
those of its two premises and the criterion of Section 1.

### The proof

Fix `P`, `g`, `d` with `0 < g` and `0 < d`. The bound `N` is the bound given by
`LargeLevelFiniteTypeStatement`. Let `n ≥ N` with `3 ≤ n`, and let
`X : LevelBase n` represent the moduli functor through `e`. Write
`π = X.toLocalizationSpec : X.obj ⟶ Spec ℤ[1/n]`.

1. `LargeLevelFiniteTypeStatement` shows that `π` is locally of finite type. The
   base `Spec ℤ[1/n]` is noetherian. So the criterion of Section 1 applies to
   `π`. Separatedness alone needs only the local finite type part of that
   premise.
2. Take a valuative square for `π` with `R` a discrete valuation ring and
   fraction field `K`, and two lifts `l₁ l₂ : Spec R ⟶ X.obj`. The bottom map
   `Spec R ⟶ Spec ℤ[1/n]` makes `n` a unit in `Γ(Spec R)`, in `Γ(Spec K)` and in
   `R`. So `Spec R` and `Spec K` are level bases `T` and `T_K`, and
   `ι : Spec K ⟶ Spec R` is a morphism `T_K ⟶ T` of level bases.
3. Through `e`, each lift `lᵢ` gives a class in `Moduli P (Spec R) g d n`. Choose
   representatives `a₁ a₂ : Datum P (Spec R) g d n`. Naturality of `e` and the
   lift equation `ι ≫ lᵢ = i₁` show that the pullbacks `aᵢ.pullback ι` have the
   same class over `Spec K`. So they are `Isomorphic`.
4. `DiscreteValuationDatumUniquenessStatement.{0}` (with `IsUnit (n : R)` from
   step 2) shows that `a₁` and `a₂` are `Isomorphic`. Hence the two classes over
   `Spec R` are equal.
5. The component of `e` at `T` is injective, since it is an isomorphism. So the
   two lifts are equal as morphisms of level bases, hence as scheme morphisms.
   The two lift structures are then equal.

## Role

With `largeLevelAmple_of_quasiFiniteProjective` and
`largeLevelQuasiProjectivity_of_ample`, this definition reduces the separatedness
input of the target `LargeLevelQuasiProjectivityStatement` to the moduli
statement `DiscreteValuationDatumUniquenessStatement` and to
`LargeLevelFiniteTypeStatement`, which is already an input of the same chain.
`DiscreteValuationDatumUniquenessStatement` says that restriction to the generic
fibre is injective on isomorphism classes of polarized full-level data over a
discrete valuation ring in which the level is invertible. It is not the Néron
mapping property (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2 Definition 1).
For abelian schemes that property (loc. cit., Proposition 8) is one input from
which the statement can be derived.
