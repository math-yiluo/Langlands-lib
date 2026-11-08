# Weights of a highest-weight representation at the first fundamental weight of a path

This module is an internal prerequisite for the even type `A` case of the
quasi-split Steinberg quotient task (Steinberg 1965, §9.10–9.19). Steinberg
computes in the standard representation of `SL_{2m+1}`. For an actual group
scheme with a split pinning, the analogue of that representation is a
highest-weight representation whose highest weight is the fundamental weight at
the end vertex of a path component of type `A_L` of the Dynkin diagram. The
module determines its torus weights and their multiplicities. The weights are
the `L + 1` path weights `ε_j = lam - (α_0 + ⋯ + α_{j-1})`, each with a
one-dimensional weight space. So the representation space is the direct sum
of these lines and has dimension `L + 1`. The module also fixes a basis
adapted to these lines.

## Setting

All declarations are in the namespace `Langlands.GroupScheme.SplitPinning`.
`k : Type u` is an arbitrary field, `G` an actual affine group scheme over
`Spec k`, and `p : SplitPinning G` a supplied split pinning. `ρ` is an actual
`MatrixRepresentation G n` on a finite type `n` with decidable equality, and
`lam : characterLattice p.torus`. The type `β : Fin L → p.base.support` is a
family of simple roots. The path notions `IsPathComponent`,
`IsPathFundamental` and `pathWeight` come from
`Langlands.LinearAlgebra.RootDatumPathWeights`, applied to `p.rootDatum` and
`p.base`. `p.IsHighestWeight ρ lam` and `p.representationWeightSpace` are the
Library's highest-weight package and actual torus weight spaces
(`Rational.FundamentalRepresentations`). No algebraic closedness, characteristic
restriction or simple connectedness is assumed. The existence of such
representations is not addressed. The module takes `ρ` and `hρ` as hypotheses.

## Results

- `nonempty_simpleReflectionRepresentative`: every simple root `a` has a
  `p.SimpleReflectionRepresentative a`. Its point, torus automorphism and
  normalizing and reflection equations are the witnesses that the pinning's
  root-datum field `p.isRootDatum` supplies for `a`.
- `finrank_representationWeightSpace_simpleReflection`: for every actual
  representation, the weight spaces at `μ` and at
  `p.rootDatum.reflection a μ` have equal dimension. This applies the
  published `SimpleReflectionRepresentative.finrank_representationWeightSpace_reflection`
  to the representative above.
- `iSupIndep_representationWeightSpace`: the actual weight spaces of any
  representation are independent. This is the published
  `MatrixRepresentation.characterSpace_iSupIndep` of the restriction to the
  torus, reindexed by the character-lattice equivalence.
- `isPathFundamental_of_isFundamentalWeight`: if `hβ : IsPathComponent β` and
  `p.IsFundamentalWeight (β 0) lam`, then `IsPathFundamental β lam`. Injectivity
  of `β` converts the Kronecker delta at `β 0` into the path form.
  `FundamentalRepresentation.isPathFundamental` applies this to the highest
  weight of a supplied `F : p.FundamentalRepresentation (β 0)`.

The remaining results assume `hρ : p.IsHighestWeight ρ lam`,
`hβ : IsPathComponent β` and `hlam : IsPathFundamental β lam`.

- `exists_eq_pathWeight_of_isHighestWeight`: every `μ` with
  `p.representationWeightSpace ρ μ ≠ ⊥` equals `pathWeight β lam j` for some
  `j ≤ L`.
- `finrank_pathWeightSpace`: for `j ≤ L`, the weight space at
  `pathWeight β lam j` has dimension `1`.
- `representationWeightSpace_ne_bot_iff`: a weight space is nonzero exactly at
  the path weights.
- `isInternal_pathWeightSpace`: the family
  `j : Fin (L + 1) ↦ p.representationWeightSpace ρ (pathWeight β lam j)` is an
  internal direct sum decomposition (`DirectSum.IsInternal`) of `n → k`.
- `pathWeightBasis` (definition): a basis of `n → k` indexed by `Fin (L + 1)`.
  It is the collected basis of this decomposition from chosen bases of the
  one-dimensional summands (`Module.finBasisOfFinrankEq`), reindexed by a
  private equivalence `(Σ j : Fin (L + 1), Fin 1) ≃ Fin (L + 1)`. The basis
  vectors are choices. Only the lines they span are canonical.
  `pathWeightBasis_mem` states that the `j`-th vector lies in the weight space
  of `pathWeight β lam j`.
- `card_eq_of_isHighestWeight`: `Fintype.card n = L + 1`.

## Proof as implemented

Let `S` be the set of weights `μ` with nonzero weight space. Weight
multiplicities are invariant under simple reflections, so `S` is stable under
them. The last field of `IsHighestWeight` says that `lam - μ` lies in
`p.positiveRootMonoid` for `μ ∈ S`. This is the additive closure of the simple
roots, which is exactly the hypothesis of
`RootDatumPathWeights.exists_eq_pathWeight`. That theorem shows `S` consists
of path weights. The dimension one statement is proved by induction on `j`.
For `j = 0` it is the one-dimensional highest weight space of
`IsHighestWeight`. Then `ε_{j+1} = s_{β j} ε_j` (`reflection_pathWeight_self`)
and multiplicities are reflection invariant. For the direct sum, the weight spaces are independent, and
the path weights are distinct (`pathWeight_injOn`), so the path weight spaces
are independent. Their supremum contains every weight space, since all other
weight spaces are zero. By `iSup_representationWeightSpace_eq_top` it is
therefore everything, and Mathlib's
`DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top` applies. The
dimension count compares the cardinality of the collected basis with
`finrank k (n → k) = Fintype.card n`.

## Scope

The module computes weights only. It does not show that ρ is trivial on the
root subgroups of other components. It gives no matrices for root
subgroups or reflection representatives in `pathWeightBasis`, constructs no
fundamental representation, and makes no statement about class functions.
These are later even type `A` obligations of the host task.
