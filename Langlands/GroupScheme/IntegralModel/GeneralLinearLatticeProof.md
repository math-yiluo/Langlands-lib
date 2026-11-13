# Proof: the general linear integral model on a full lattice

This module proves the Library statement
`Langlands.GroupScheme.GeneralLinearLatticeIntegralModelStatement`, at an arbitrary
universe `u`. The statement is in
`Langlands.GroupScheme.IntegralModel.GeneralLinearLattice`. The theorem is

`Langlands.GroupScheme.generalLinearLatticeIntegralModel :
  GeneralLinearLatticeIntegralModelStatement.{u}`.

Its axioms are only `propext`, `Classical.choice` and `Quot.sound`. The proof
uses the helper module `Langlands.GroupScheme.IntegralModel.GeneralLinearStandardPoints`,
which computes the integral points of the standard model.

The statement isolates the `GL(L)` paragraph of Kaletha–Prasad, *Bruhat–Tits
Theory: A New Approach* (2023), Proposition 8.3.1 (PDF p. 327, printed p. 296).
That paragraph uses the smooth group scheme `GL(L)` without proof. The proof
below is the usual construction: `GL(L)` is `GL_n` over `R` written in a basis
of `L`.

## Outline

Let `R` be a discrete valuation ring with fraction field `K`. Let
`Λ ⊆ Fin n → K` be a full lattice (`Submodule.IsLattice K Λ`).

1. Choose an `R`-basis `b` of `Λ` indexed by `Fin n`. Let `B ∈ GL_n(K)` be the
   matrix whose `j`-th column is `b j`.
2. The model is the standard group `GL_{n,R}`. Its generic identification is
   the standard one followed by the inner automorphism of `GL_{n,K}` given by
   conjugation by `B`.
3. The integral points of this model are the `g` with `B⁻¹ g B ∈ GL_n(R)`.
   That is exactly the condition that `g` and `g⁻¹` both carry `Λ` into `Λ`.

## The basis and the lattice matrix (section `Lattice`)

These results assume only a commutative ring `R`, a field `K` with
`IsFractionRing R K`, a submodule `Λ` with `[Submodule.IsLattice K Λ]` and a
basis `b : Module.Basis (Fin n) R Λ`.

- `GeneralLinear.latticeCoordEquiv b` is the `K`-linear automorphism
  `(b.extendOfIsLattice K).equivFun.symm` of `Fin n → K`. It sends `c` to
  `∑ j, c j • b j` (`latticeCoordEquiv_apply`) and the standard basis vector
  `Pi.single j 1` to `b j` (`latticeCoordEquiv_single`). Mathlib's
  `Module.Basis.extendOfIsLattice` turns the `R`-basis of `Λ` into a `K`-basis
  of `Fin n → K`.
- `GeneralLinear.mem_lattice_iff`: `v ∈ Λ` holds exactly when
  `v = latticeCoordEquiv b (algebraMap R K ∘ c)` for some `c : Fin n → R`.
  Forward: take `c = b.repr ⟨v, hv⟩` and use `b.sum_repr`. Backward: the sum
  of `R`-multiples of the `b j` lies in `Λ`.
- `GeneralLinear.latticeMatrix b : GL (Fin n) K` has value
  `LinearMap.toMatrix'` of `latticeCoordEquiv b` and inverse the matrix of its
  inverse map. Its columns are therefore the vectors `b j`.
  `latticeMatrix_mulVec` and `latticeMatrix_inv_mulVec` state that
  multiplying by the matrix, or by its inverse, applies `latticeCoordEquiv b`,
  or its inverse.
- `GeneralLinear.forall_mulVec_mem_iff`: for any matrix `A` over `K`,
  `∀ v ∈ Λ, A *ᵥ v ∈ Λ` holds exactly when `B⁻¹ * A * B` equals
  `C.map (algebraMap R K)` for some `C` over `R`.
  - Forward: for each `j`, `A *ᵥ b j ∈ Λ`. So `A *ᵥ b j` has integral
    coordinates `c j` (by `mem_lattice_iff`; the family is chosen with
    `choose`). The `j`-th column of `B⁻¹ A B` is
    `B⁻¹ *ᵥ (A *ᵥ (B *ᵥ Pi.single j 1))`, which is `algebraMap R K ∘ c j`.
    Take `C i j = c j i`.
  - Backward: write `v = B *ᵥ (algebraMap R K ∘ c)`. Then
    `A *ᵥ v = B *ᵥ ((B⁻¹ A B) *ᵥ (algebraMap R K ∘ c))`, which is
    `B *ᵥ (algebraMap R K ∘ (C *ᵥ c))` by `RingHom.map_mulVec`. So it lies in
    `Λ`.
- `GeneralLinear.mem_range_map_iff_exists_map` (section `MatrixAlgebra`): an
  `X ∈ GL_n(K)` lies in the range of
  `Matrix.GeneralLinearGroup.map (algebraMap R K)` exactly when `X` and `X⁻¹`
  both come from matrices over `R`. For the backward direction, if
  `C ↦ X` and `D ↦ X⁻¹`, then `C * D = 1` and `D * C = 1`. This follows by
  injectivity of the entrywise map: `algebraMap R K` is injective by
  `IsFractionRing.injective`. So `⟨C, D, _, _⟩ ∈ GL_n(R)` maps to `X`.
- `GeneralLinear.stabilizesLattice_iff` (adds `[IsDomain R]`, which the
  predicate's definition carries):
  `GeneralLinear.StabilizesLattice Λ g` holds exactly when
  `(latticeMatrix b)⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g * latticeMatrix b`
  lies in the range of `Matrix.GeneralLinearGroup.map (algebraMap R K)`. Apply
  `forall_mulVec_mem_iff` to both clauses of `StabilizesLattice`. Its second
  clause uses the matrix inverse of the matrix of `g`. Mathlib's
  `Matrix.coe_units_inv` identifies this with the matrix of the inverse in
  `GL_n(K)`. The inverse of `B⁻¹ g B` is `B⁻¹ g⁻¹ B` (by `group`). Now
  `mem_range_map_iff_exists_map` gives the claim.

## The model and its generic identification (section `ConjugatedModel`)

Here `R` is an integral domain with fraction field `K`, and `B` is any element
of `Langlands.GeneralLinear n K`.

- `GeneralLinear.conjugatedStandardIntegralModel R K B` is an actual
  `IntegralModel R K (GeneralLinear.groupScheme (Fin n) (CommRingCat.of K))`.
  Its `group`, `affine`, `flat` and `finiteType` fields are those of the
  Library's `GeneralLinear.standardIntegralModel R K (Fin n)`. So the group is
  the Library's `GeneralLinear.groupScheme (Fin n) (CommRingCat.of R)`. Its
  `genericIso` is the composite
  `(standardIntegralModel R K (Fin n)).genericIso ≪≫ G.innerIso p`, where:
  - `G` is `GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)`;
  - `p` is the rational point `(rationalPointsEquiv n (CommRingCat.of K)).symm B`;
  - the standard generic identification is `GeneralLinear.baseChangeIso`;
  - `GroupScheme.innerIso` (Library module
    `Langlands.GroupScheme.InnerAutomorphism`) is the group-scheme automorphism
    acting on points by conjugation by `p`.
- `GeneralLinear.conjugatedStandardIntegralModel_isSmooth`: the model is
  smooth. Its group is `GeneralLinear.groupScheme (Fin n) (CommRingCat.of R)`,
  and the Library theorem `GeneralLinear.smoothStatement (Fin n) (CommRingCat.of R)`
  gives smoothness. This is the same proof term as the Library's
  `standardIntegralModel_isSmooth`.
- `GeneralLinear.conjugatedStandardIntegralModelIso` is an
  `IntegralModel.Iso` from the standard model to the conjugated model over
  `G.innerIso p`. Its underlying group isomorphism is the identity. The
  compatibility square holds because the base change of the identity is the
  identity.
- The imported `Langlands.GroupScheme.rationalPoints_map_innerIso` from
  `GroupScheme.Rational.ParabolicPointConjugation` identifies the rational-point
  map of an inner automorphism with conjugation. Evaluating it gives
  `rationalPoints.map (G.innerIso p).hom h = p * h * p⁻¹`; the proof uses this
  existing declaration directly.
- `GeneralLinear.mem_conjugatedStandardIntegralModel_integralPoints_iff`: the
  exact integral-point formula of the conjugated model. A rational point `g`
  lies in `(conjugatedStandardIntegralModel R K B).integralPoints` exactly when
  `B⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g * B` lies in the range of
  `Matrix.GeneralLinearGroup.map (algebraMap R K)`. The Library theorem
  `IntegralModel.Iso.map_integralPoints`, applied to
  `conjugatedStandardIntegralModelIso`, says that the conjugated model's
  integral points are the image of the standard model's integral points under
  `rationalPoints.map (G.innerIso p).hom`, that is, under `h ↦ p h p⁻¹`. The
  helper `GeneralLinear.mem_standardIntegralModel_integralPoints_iff` says
  that `h` is an integral point of the standard model exactly when its matrix
  comes from `GL_n(R)`. Since `rationalPointsEquiv` is multiplicative and sends
  `p` to `B`, `g = p h p⁻¹` with `h` integral is equivalent to
  `B⁻¹ g B ∈ GL_n(R)`. In the backward direction take `h = p⁻¹ g p`.

## The main theorem

`generalLinearLatticeIntegralModel` introduces `R`, `K`, `n`, `Λ` and the
lattice hypothesis, and registers that hypothesis as an instance. Mathlib's
`Submodule.IsLattice.finrank_of_pi` gives `Module.finrank R Λ = n`. Instance
search supplies `Module.Free R Λ` and `Module.Finite R Λ` from Mathlib's
lattice instances (`Submodule.IsLattice.free`, using that a discrete valuation
ring is a principal ideal domain, and `Submodule.IsLattice.finite`). So
`Module.finBasisOfFinrankEq` gives a basis `b : Module.Basis (Fin n) R Λ`.

The witness is `conjugatedStandardIntegralModel R K (latticeMatrix b)`. Its
smoothness is `conjugatedStandardIntegralModel_isSmooth`. For every `g`, the
statement's equivalence is
`mem_conjugatedStandardIntegralModel_integralPoints_iff` followed by
`stabilizesLattice_iff b`. Both sides become the same condition
`(latticeMatrix b)⁻¹ * rationalPointsEquiv n (CommRingCat.of K) g * latticeMatrix b`
lies in the range of `Matrix.GeneralLinearGroup.map (algebraMap R K)`.

## Scope

The model and its formula use only the chosen basis `b`. Independence of the
basis is neither needed nor proved, and neither is uniqueness of the model. The
discrete valuation ring hypothesis is used only to make `Λ` free of rank `n`.
Everything else holds over any integral domain with its fraction field. The
proof changes no Library file. It adds the helper module
`IntegralModel/GeneralLinearStandardPoints` and this module.
