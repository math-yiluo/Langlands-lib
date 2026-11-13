# Renard II.2.5: the stalk of a nondegenerate test module

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, printed pp.40–41 / PDF pp.46–47,
registered as `renard-2026-representations-groupes-reductifs-padiques`.
The passage follows the proof of the equivalence theorem and precedes the
Example about the regular module. This pair constructs the literal annihilator
submodule and states the stalk descriptions. It does not prove those descriptions.

Let `X` be a t.d. space in Renard's sense: Hausdorff with a compact-open
neighborhood basis, represented by `Langlands.Topology.IsLocallyProfinite X`.
Let `M` be an additive commutative group with its specified original nonunital
action of the pointwise test algebra `PointwiseTestAlgebra.Carrier X`, and let
`hM` assert nondegeneracy. Complex scalars on `M` are the published canonical
`ProjectorVectorSheaf.originalModule hM`; no pre-existing compatible complex
action is assumed.

`annihilatorSubmodule hX hM x` has exactly the carrier

`{m | ∃ f : PointwiseTestAlgebra.Carrier X, f x ≠ 0 ∧ f • m = 0}`.

Here `f` is a compactly supported locally constant test, and `f • m` is the
original action. The subspace is not defined as the kernel of a germ map.
Its intrinsic closure proofs use a compact-open indicator containing `x` as
the zero witness; the product of two witness tests as the witness for a sum;
commutativity and associativity of the original test action; and the published
commutation of that action with canonical complex scalars. `mem_annihilatorSubmodule`
records the exact membership predicate.

`SameProjectorGerm hX x m n` is the printed equivalence relation: there exists a
compact-open neighborhood `U` of `x` on which the original projectors of `m`
and `n` agree. `AnnihilatorDescription` states that membership in `M(x)` is
equivalent to this relation with zero. It retains independent space and module
universes `u` and `v`.

`BasisStalkComparison` states an additive equivalence from `M/M(x)` to the
published `rawStalk (ProjectorBasisSheaf.rawPresheaf hX M) x`. This is the
actual abelian-group colimit of the compact-open neighborhood restriction
diagram, whose values are the original ranges `χ_U M`. The existing
`BasisStalk` construction lifts values to universe `max u v` before forming
the colimit. Compatibility with `rawGerm` of `χ_U m` is required for every
compact-open neighborhood `U`, every membership proof, and every original
vector `m`. Thus the target is a genuine stalk, not a newly named quotient,
and its characterization does not depend on a chosen neighborhood.

For the published all-open vector sheaf, `originalGerm` is the complex-linear
composition of `ProjectorVectorSheaf.originalSection ⊤` with Mathlib's actual
global germ map. `GermSurjective`, `GermKernel`, and `GermEquality` state,
respectively, surjectivity, equality of its kernel with the literal
annihilator submodule, and the printed compact-open criterion for equality of
germs. `VectorStalkComparison` states a complex-linear equivalence
`M/M(x) ≃ₗ[ℂ] ℳ_x` that sends the quotient class of each `m` to `originalGerm m`.
These clauses use the existing `ProjectorVectorSheaf.presheaf`, whose sheaf
condition is already proved.

Mathlib's all-open `Γgerm` API ties the hom universe of the target category
to the space universe. Consequently the all-open vector-stalk clauses use
`X : Type u`, `M : Type u`, and `ModuleCat.{u} ℂ`; they do not restrict `u`
to zero. The independent-universe basis-colimit clause above retains the
source's arbitrary original-module universe. No finite-dimensionality,
compactness of `X`, countability, or continuity of a linear functional is
assumed.

`ProjectorStalkDescription.{u,v}` aggregates the independent-universe
annihilator and basis-colimit clauses and the all-open vector-stalk clauses.
It is a `Prop`-valued statement for a separate proof task. The all-open kernel,
surjectivity, and linear-equivalence formulations make explicit the linear
content of Renard's quotient identification. This passage is distinct from
the later printed p.42 / PDF p.48 Remark, whose quotient starts with compact
sections of an arbitrary sheaf and uses the span of tests vanishing at `x`.
