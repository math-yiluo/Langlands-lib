# Actual normalized induction and unramified trace coefficients

This internal derived adapter combines the existing actual normalized induction,
published normalized-induction admissibility, compact-quotient induction, finite trace
coefficients, and compact-subgroup unramified-character results. It introduces no
additional assertion from the original literature.

Let `G` be a locally compact nonarchimedean group, and let
`h : IsSemidirectDecomposition P M U` be an actual subgroup decomposition. The
unipotent subgroup `U` is assumed closed and the canonical Levi projection
`h.projection : P →* M` continuous. Coefficient representations are actual
`SmoothRep ℂ M` objects with all-open-subgroup admissibility. Group and
coefficient-carrier universes are independent.

The coefficient and distribution constructions further assume that `G` is
Hausdorff, has its Borel measurable structure, and carries a left-invariant
measure `μ` finite on compact sets. The actual canonical quotient
`Induction.LeftQuotient P` is compact. The coefficient construction, evaluation
formula and continuity theorem also require `P` closed. Total disconnectedness
is derived from the Hausdorff nonarchimedean assumptions using Mathlib's
instance; it is not a separate retained premise.

## Admissibility and the twist identity

`IsSemidirectDecomposition.isOpenMap_projection` only needs `G` to be a
topological group. The actual inclusion of `M` into `P` is continuous and is a
right inverse of the projection by `h.projection_levi`. Hence the continuous
projection is a quotient map and, being a group homomorphism, is open.

The published `inducingRepresentation_isAdmissible` and
`normalizedInductionFunctor_obj_isAdmissible` from
`RationalInductionDualityReduction` supply the admissibility of the actual
normalized inflation and, for a compact quotient, the actual normalized
functor value. Their fixed-vector proof uses the continuous canonical Levi
inclusion and the open kernel of the closed half-modulus character. These
results require no Hausdorff, Borel, measure or closed-`P` hypothesis.

`inducingRepresentation_twist` pulls an actual smooth Levi character through
the canonical projection. The pullback character commutes with the fixed
half-modulus scalar by commutativity of complex scalar multiplication. The
result is equality of representations on the identical coefficient carrier,
with the positive character convention used throughout the Library.

## One coefficient function before all unramified parameters

For an admissible Levi object `A` and a test function `f`,
`normalizedInductionTwistCoefficients h hU hproj μ hP A hA f : P →₀ ℂ`
applies `Induction.compactQuotientTwistCoefficients` to the actual normalized
inflation. It chooses one finitely supported function before any character or
norm family is supplied.

Let `ν : I → (M →* ℝ≥0ˣ)` be a family of positive norm characters, with an
independent index universe. The parameter group is the actual
`Plancherel.unramifiedCharacters ν`: continuous complex characters trivial on
the common norm kernel. Its topology below is inherited from the compact-open
topology on continuous monoid homomorphisms.

`normalizedUnramifiedInductionDistribution` is the genuine distribution
character of the actual normalized functor applied to `A` twisted by such a
parameter. The parameter's kernel is open by the existing unramified-character
smoothness theorem. Admissibility of the twisted Levi object follows from
admissibility of `A`; the preceding compact-quotient theorem then supplies the
required admissibility of its actual normalized induction. The definition
requires neither continuity of the norm family nor closedness of `P`.

When every `ν i` is continuous,
`normalizedUnramifiedInductionDistribution_eval` computes its value on `f` as

`∑ p ∈ c.support, c p * (χ.val (h.projection p) : ℂ)`,

where `c` is the single coefficient function defined above. The proof uses
`inducingRepresentation_twist` and explicit equality transport, including the
dependent admissibility proof. The existing unramified pullback theorem shows
that every compact subgroup of `P` lies in the pullback character's kernel.
The genuine compact-quotient distribution formula then gives the evaluation.
No character or induced-admissibility choice enters the definition of `c`.

## Continuity and dense extension

`continuous_normalizedUnramifiedInductionDistribution` fixes `f`, rewrites its
actual distribution value using that same finite coefficient function, and
uses continuity of evaluation on the actual compact-open character space,
continuity of `ℂˣ → ℂ`, and continuity of finite sums. It asserts scalar
continuity for every test function, without choosing a topology on the space of
distributions.

`normalizedUnramifiedInductionDistribution_eq_of_dense` allows a second actual
decomposition `Q = M N`, with closed `N`, continuous canonical projection,
closed `Q` and compact actual quotient. The second admissible Levi object has
an independent carrier universe. Both families use the same Levi and positive
norm family. Equality of their actual distributions on an explicitly supplied
dense subset extends to every unramified parameter. For each test function the
preceding continuity theorem makes the equality locus closed; it contains the
closure of the supplied subset, hence every parameter.

The dense subset and equality on it remain explicit inputs. No generic
irreducibility, same-Levi comparison, finite-length admissibility, reductive
rational-point realization or exact-K0 conclusion is asserted. The full
`RationalInducedK0WeylConjugacyStatement` remains a separate proof obligation.
