# Upper bound for the split rank of Cayley automorphism group schemes

Let `c : CayleyDatum K` over a field `K`, in any characteristic, and let
`iH : H ⟶ GL₈` satisfy `c.IsAutomorphismRepresentation iH`. This module
proves `splitRank H ≤ 2`. A closed split torus `𝔾ₘ^I → H` defines a
weight grading of the algebra by `ℤ^I` whose degrees generate `ℤ^I`, so
`Grading.card_le_two` (module
`Langlands.GroupScheme.Composition.CayleyGrading`) gives `|I| ≤ 2`.

## Change of coefficients

- `map_mulVec_comp`: `M.map ψ *ᵥ (ψ ∘ v) = ψ ∘ (M *ᵥ v)` for a ring map
  `ψ`.
- `multiplicationOver_comp`: the extended multiplication
  `c.multiplicationOver` commutes with a further ring map `ψ`. Also
  `unitOver_eq`, `unitOver_comp`, and `multiplicationOver_algebraMap`,
  which handles vectors with coefficients in `K`.
- `IsAutomorphismMatrix.of_map`: if the image of `g` under an injective
  ring map `ψ : A → B` is an automorphism matrix over `B` (for `ψ ∘ φ`),
  then `g` is an automorphism matrix over `A` (for `φ`).

## Homogeneous monomials

- `algebraMap_addMonoidAlgebra`: `K → K[M]` sends `r` to `single 0 r`.
- `multiplicationOver_single`: in `K[M]`, the extended product of the
  monomial vectors `single a ∘ x` and `single b ∘ y` is
  `single (a + b) ∘ (xy)`.

## The weight grading

Fix a morphism `j : splitTorus (Spec K) I ⟶ H` with `I` finite. The
Library module `Langlands.GroupScheme.Torus.RingRepresentationWeights`
provides the universal matrix of `iH ∘ j` over `K[ℤ^I]`
(`universalMatrix iH I j`), its coefficient matrices `weight iH I j m`
(orthogonal idempotents summing to `1`), and the finite set
`weightSupport iH I j`.

- `isAutomorphismMatrix_universalMatrix`: the universal matrix is an
  automorphism matrix over `K[ℤ^I]`. The universal torus point composed
  with `j` and `iH` lies in the range of `iH`. By the all-test
  hypothesis `hrep.2`, its matrix over the sections of `Spec K[ℤ^I]`
  is an automorphism matrix. We then transport it along the injective
  inverse of `Corepresented.affineSectionsIso` with `of_map`.
- `coeff_universalMatrix_mulVec`: the coefficient at `n` of the universal
  matrix applied to a constant vector `v` is `weight n *ᵥ v`.
- `universalMatrix_mulVec_of_weight`: a vector `x` of weight `a` (that is,
  `weight a *ᵥ x = x`) is sent to the monomial vector `single a ∘ x`.
- `weightGrading hrep I j : c.Grading (I → ℤ)`. Its projections are the
  weight matrices and its support is `weightSupport`. The unit has
  degree `0`: take the coefficient at `0` of the identity
  `g 1 = 1` for the universal matrix. Products are homogeneous: apply
  the automorphism identity `g(xy) = (gx)(gy)` to vectors `x`, `y` of
  weights `a`, `b`. The right side is `single (a + b) ∘ (xy)` by
  `multiplicationOver_single`. Comparing coefficients at `a + b` gives
  `weight (a + b) *ᵥ xy = xy`.
- `card_le_two_of_isClosedSubgroup`: if `j` is a closed subgroup, then
  `Fintype.card I ≤ 2`. The underlying morphism of `j ≫ iH` is a
  composite of closed immersions (`hj` and `hrep.1`), hence a
  monomorphism. So the Library theorem `closure_weights_eq_top` says that
  the nonzero weights generate `ℤ^I`, and `Grading.card_le_two` applies.

## Main result

**`splitRank_le_two (hrep) : splitRank H ≤ 2`.** The Library's
`splitRank H` is the supremum of `Nat.card I` over finite `I` and
closed-subgroup morphisms `splitTorus (Spec K) I ⟶ H`. Each term is at
most `2` by `card_le_two_of_isClosedSubgroup`.

## Provenance

This is internal, derived content. The bound reflects the fact that the
automorphism group of a Cayley algebra is a form of `G₂`, of absolute
rank two (Knus, Merkurjev, Rost and Tignol, *The Book of Involutions*,
Section 33.C and Theorem 25.14, as cited in the target statement's
Markdown). The proof here does not use that identification. It uses
only the weight decomposition from the Library, the all-test
automorphism hypothesis, and the combinatorial rank bound of
`CayleyGrading`.
