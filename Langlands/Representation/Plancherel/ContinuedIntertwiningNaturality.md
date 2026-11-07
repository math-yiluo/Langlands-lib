# Representative transport for rational intertwiner continuations

This module constructs transport of common-denominator continuation data by
fixed linear maps and proves preservation of an inducing-representative square
under two independently chosen continuations. The final result concerns the
actual canonical normalized induction spaces. This is derived content toward
Waldspurger, *La formule de Plancherel pour les groupes p-adiques*, IV.1,
printed pp.276–277 (PDF pp.42–43), especially the representative-isomorphism
diagram on p.277.

## Fixed linear maps and the common-denominator convention

For a topological group `H` and a family of norm characters, let
`A : Ω → V →ₗ[ℂ] W`, where the four complex module carriers used below may
have independent universes. `RationalOperatorContinuationData Ω A` consists
of a global polynomial operator numerator and one regular denominator,
nonzero at every point of `Ω`, clearing the whole family. The denominator
is chosen before quantifying over input vectors; individual input vectors
may have different finite polynomial expansions.

For fixed maps `S : V' →ₗ[ℂ] V` and `T : W →ₗ[ℂ] W'`,
`RationalOperatorContinuationData.map` sends continuation data `p` to data
for `χ ↦ T ∘ A(χ) ∘ S`. It retains the exact denominator and composes the
global numerator on both sides. Polynomiality follows from the existing
precomposition and postcomposition lemmas. The clearing identity follows
by linearity. No injectivity, surjectivity, topology on the module
carriers, or finite dimensionality is required.

`map_regularRegion` identifies the regular regions definitionally.
`map_continuedOperator` identifies the new continued operator with
`T ∘ p.continuedOperator(χ) ∘ S` on that region, by moving the reciprocal
denominator through the fixed linear maps.

## Propagating a square on actual rational characters

`rationalOperatorContinuationData_natural` compares two independently supplied
continuations `p` and `q`, for families `A : Ω → V →ₗ[ℂ] W` and
`B : Λ → V' →ₗ[ℂ] W'`. The parameters here are the actual unramified
characters defined from all rational norm characters of a connected
reductive group scheme `L` over an arbitrary nonarchimedean local field.
A topology on its rational points and continuity `hp` of
`rationalValuationImageProjection L` are explicit hypotheses.

For fixed linear maps `S : V →ₗ[ℂ] V'` and `T : W →ₗ[ℂ] W'`, assume

`B(χ) ∘ S = T ∘ A(χ)`

on a specified nonempty ambient open set `D` contained in both `Ω` and `Λ`.
The theorem gives the same equation for the continued operators at every
point of `p.regularRegion ∩ q.regularRegion`. Neither the original regions
nor the denominators need agree, and the original regions need not be open.
Because both data clear their respective original families, the whole set
`D` is contained in both regular regions.

The proof restricts the rational continued families to that intersection,
precomposes the second with `S`, and postcomposes the first with `T`.
Recovery of the original families supplies their equality on `D`.
The published `rationalUnramifiedOperator_eq_of_eqOn_isOpen` then supplies
equality on the full intersection. This route uses the existing
open-set uniqueness for actual rational characters.

## Actual normalized induction and compact conjugation

The compact-square comparison uses a locally compact nonarchimedean
topological group `G` and two semidirect decompositions `Pᵢ = M Uᵢ`
with common literal Levi subgroup `M`. Both parabolics and radicals are
closed, the imported `IsUnimodularModulus Uᵢ hUᵢ` hypotheses hold,
and both Levi projections are continuous. A common compact open subgroup
`K` satisfies the displayed `G = Pᵢ K` factorizations. A continuous family
of norm characters on `M` defines the unramified twists.

Let `A` and `B` be canonical complex `SmoothRep` objects of `M` and
`φ : A.representation.Equiv B.representation`. These inducing objects
have independent carrier universes. Write `Iᵢ,χ(φ)` for the actual
`inducedMap` of `twistEquiv χ φ` and `Cᵢ(φ)` for
`compactInductionPictureEquiv hᵢ K φ`. The latter map is independent
of `χ` because its compact carrier is fixed.

`compactIntertwiningOperator_natural_iff` proves that the actual square

`JB ∘ I₀,χ(φ) = I₁,χ(φ) ∘ JA`

is equivalent to the compact square

`compact(JB) ∘ C₀(φ) = C₁(φ) ∘ compact(JA)`.

These equalities are stated pointwise for all input vectors. The forward
direction is the published compact naturality lemma. For the reverse
direction, the proof evaluates the compact square at the compact
restriction of an actual induced vector, uses inverse naturality and
equivalence cancellation, and then uses injectivity of the target
restriction equivalence. Thus compact conjugation reflects the actual
square as well as preserving it.

For the final continuation theorems, `L` is as above and
`e : GroupScheme.rationalPoints L ≃ₜ* M` identifies its rational points
with the literal Levi. Continuity of every rational norm character is
also displayed. Parameters on `L` are transported to `M` through the
existing unramified-character homeomorphism. The field, ambient-group,
and both inducing-carrier universes are independent. There is no
characteristic, splitness, admissibility, finite-length or irreducibility
restriction.

The original families `JA` on `Ω` and `JB` on `Λ` consist of actual
ambient `G` intertwiners from the `P₀` induction to the `P₁` induction.
The inputs `p` and `q` are continuation data for their exact compact
conjugations. The hypothesis `hnat` supplies the original actual square
on one common nonempty ambient open `D ⊆ Ω ∩ Λ`. This compatibility and
the existence of the continuation data are substantive supplied inputs.

`continuedCompactIntertwiner_natural` first sends that original square
to the compact carriers using the published compact naturality lemma.
It applies `rationalOperatorContinuationData_natural` with the fixed
maps `C₀(φ)` and `C₁(φ)`, then evaluates the resulting linear-map equality.
This proves the compact square on the full common regular locus.

`continuedInductionIntertwiner_natural` proves the actual square for the
two `continuedInductionIntertwiner` constructions on that same locus.
It applies the reverse implication of the compact-square equivalence.
The two exact `continuedInductionIntertwiner_compact` identities identify
the compact conjugations with `p.continuedOperator` and
`q.continuedOperator`; composing these identities with the preceding
compact naturality result finishes the proof. The existing normalized
restriction and extension maps are used throughout.

## Source correspondence and remaining obligations

On printed p.276 the source introduces fixed compact carriers for
unramified inductions. On p.277 it requires the family to commute with
every inducing-representative isomorphism, defines polynomial and rational
operator families by compact conjugation, and describes continuation on
the denominator's nonzero locus. The implemented results combine these
requirements with the existing algebraic uniqueness theorem. The fixed
linear-map construction, the allowance of separate original regions and
denominators, and the proof on actual character parameters are derived
implementation results. The source starts with admissible inducing
representations and orbit-indexed families; it does not state this
more general algebraic helper.

The theorem handles any supplied `φ` at the same character parameter.
It does not identify different character parameters giving isomorphic
twists or descend a family through a stabilizer or an orbit quotient.
It also does not prove the original representative square for a
standard integral, construct its rationality data, compare algebraic
`B`-families, or realize the displayed geometric and topology hypotheses
for every ambient reductive rational-point group.

Standard-integral convergence and rationality, generic irreducibility,
orbit descent, parabolic independence, opposite-composition scalars,
global `j` and `mu`, and the main Plancherel results remain obligations
of the larger program. The naturality theorem alone discharges none
of those analytic or representation-theoretic prerequisites.
