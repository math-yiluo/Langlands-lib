# Canonical Harris lattices and reductions over all ordered compact levels

Author: Worker 57.

This internal construction assembles the independently constructed canonical
Harris lattices and their original power reductions over all compact open
levels ordered by inclusion. It retains each actual level subgroup and its
original coefficient action. Level inclusions compose, every original
exponent reduction is natural in the level, and the resulting squares form
a functor into varying-group equivariant diagrams.

## Exact inputs and level category

The generic subgroup construction is in
`Langlands.Shimura.CompactOpenLevel`. Fix `G : Type u` with a group and a
topological space. The existing `CompactOpenLevel.Ordered G`, imported from
`LevelColimit`, is the type of actual compact open levels with the preorder
induced by their subgroup inclusions. Thus an arrow `U → V` supplies exactly
`U.subgroup ≤ V.subgroup`. Its category has at most one arrow with fixed
endpoints. The existing transporter category on `CompactOpenLevel G` has
additional right-translation arrows; this construction uses the ordered
category throughout.

`orderedSubgroupFunctor G` is the functor to `GrpCat` whose vertex is the
actual group `U.subgroup` and whose map at `f : U → V` is
`Subgroup.inclusion (leOfHom f)`. Group-homomorphism extensionality proves
its identity and composition laws by reflexivity. The `obj` and `map`
lemmas identify those exact objects and maps. This generic group diagram
asserts no additional continuity result and requires no topological-group
axiom on `G`.

All remaining declarations are in `Langlands.Shimura.Coefficients`.
The arithmetic data share one universe `u` and consist of a ring `A` with
an algebra structure over `ℚ` and `Module.Finite ℚ A`, a number field `L`,
a finite-dimensional `L`-module `W`, an algebra involution
`σ : AlgebraInvolution ℚ A`, an algebraic representation
`ρ : (σ.baseChange L).AlgebraicRepresentation W`, and a rational finite
place `p`. Put

\[
 G=\sigma.\mathrm{FiniteAdelicPoints},\qquad
 R=\operatorname{HarrisCoefficientIntegers}(L,p).
\]

The group, topology, coefficient ring, ambient tensor coefficient module and
original coefficient actions are the existing constructions for these data.
No lattice, comparison map, desired action compatibility or functor is supplied
as output data. The construction does not require a central-simple or CM
specialization of this generic algebra-with-involution input.

For an actual compact open level `U`, write `Λ_U` for the existing
`harrisLattice ρ p U`. It is the original full canonical lattice in
`(L ⊗[ℚ] FiniteCompletion ℚ p) ⊗[L] W`. The imported lattice-inclusion
construction proves `Λ_U ≤ Λ_V` when `U.subgroup ≤ V.subgroup`: its local
orbit-span generators at `U` are among those at `V`, the product lattice
inclusions hold componentwise, and the fixed integral coefficient splitting
pulls them back to these full lattices. Consequently all level comparisons
below concern these actual independently constructed canonical lattices in
the same original tensor module.

## Actual lattices and their level actions

`harrisLatticeLevelFunctor` is the functor

\[
 \operatorname{CompactOpenLevel.Ordered}(G)
    \longrightarrow R\text{-Mod},\qquad U\longmapsto\Lambda_U.
\]

Its map at `f : U → V` is the original ambient linear inclusion
`harrisLatticeInclusion ρ p V U (leOfHom f)`. The argument order of the
existing inclusion is target level followed by source level. Linear-map
extensionality proves the functor identity and composition laws by
reflexivity: every composite keeps the same ambient vector. Its `obj` and
`map` lemmas normalize precisely these vertices and maps.

`harrisLatticeLevelDiagram` equips this functor with the original action
`(harrisLatticeAction ρ p U).ρ` of the actual subgroup `U.subgroup` at each
vertex. It is an `EquivariantDiagram` over `orderedSubgroupFunctor G`.
Its compatibility field is the already constructed
`harrisLatticeActionInclusion.comm` for the actual inclusion `U ≤ V`.
Thus for `g ∈ U`, inclusion intertwines the original `g` action on `Λ_U`
with the original action of its same-element inclusion in `V` on `Λ_V`.

## Full exponent system over the level diagram

Fix any `m : ℕ`, and put
`I = harrisCoefficientScalarIdeal L p m`, the span of the natural scalar
`m` in the full ring `R`. For `k : ℕᵒᵖ`, define

\[
 M_{U,k}=\Lambda_U/(I^{k.unop}\,\Lambda_U).
\]

Here the precise Lean submodule is `I ^ k.unop • ⊤` in `Λ_U`.
The scalar ring remains `R` at every exponent.

`harrisTorsionLevelDiagram m k` has underlying functor exactly
`harrisLatticeLevelFunctor ⋙ AdicSystem.powerReduction I k.unop`.
Its action at `U` is the original
`((harrisTorsionSystem ρ p U m).obj k).ρ`.
Its compatibility field is the existing reduced action inclusion's
`comm` field. Consequently its vertices, level maps and actions are exactly
the original coefficient reductions, actual included-vector maps and
original subgroup actions.

The entry definition `harrisTorsionLevelSystem m` constructs

\[
 \mathbb N^{op}\longrightarrow
 \operatorname{EquivariantDiagram}
   (\operatorname{orderedSubgroupFunctor}(G),R\text{-Mod}).
\]

Its value at `k` is the diagram just described. For `f : i → j` in
`ℕᵒᵖ`, its component at `U` is exactly the underlying map of
`(harrisTorsionSystem ρ p U m).map f`. Naturality in a level inclusion
follows by applying `congrArg Action.Hom.hom` to the original naturality
square of `harrisTorsionSystemInclusion` and reversing the equality.
Its equivariance field is the original reduction's `comm` field.
Extensionality first for equivariant-diagram morphisms and then for natural
transformations reduces the exponent functor identity and composition laws
to the corresponding laws of the original torsion system at each `U`.

The `obj_obj`, `level_map`, `action` and `exponent_map` lemmas identify the
original modules, included-vector maps, subgroup actions and exponent
reductions by reflexivity. In particular, no object is replaced by an
unspecified isomorphic coefficient module.

Write `j_k(h) : M_{U,k} → M_{V,k}` for the level map at `h : U → V`, and
write `r_U(f) : M_{U,i} → M_{U,j}` for the original exponent reduction.
The `square` theorem is naturality of the constructed exponent map and gives

\[
 j_i(h)\,;\,r_V(f)=r_U(f)\,;\,j_j(h).
\]

This holds simultaneously for every actual level inclusion and exponent
arrow. The `level_map_mk` theorem is the original representative formula

\[
 j_k(h)([x])=[\operatorname{harrisLatticeInclusion}(h)(x)].
\]

Both quotient classes use the same ambient tensor vector, in the respective
actual lattices.

## Concrete composition of the original reduced inclusions

For `T ≤ V ≤ U`, `harrisTorsionSystemInclusion_comp` proves equality of the
underlying `R`-linear coefficient maps at every exponent:

\[
 j_{T,V,k}\,;\,j_{V,U,k}=j_{T,U,k}.
\]

`harrisTorsionSystemInclusion_refl` identifies the original reduced inclusion
from a level to itself with the identity. These theorems concern the named
original maps, after forgetting the differently indexed subgroup actions;
the varying-group equivariance is retained by the diagram above. Their
proofs use module-morphism extensionality and quotient surjectivity to reduce
to an original lattice representative, where both sides are reflexively the
same included vector. These are concrete specializations of the composition
and identity behavior assembled into the level diagrams.

Every natural scalar `m`, including zero, and every exponent, including zero,
is admitted. No finiteness, injectivity or invertibility of a reduced level
map is asserted by this construction.

## Provenance and remaining scope

This is an internal deduction from the direct imports
`Coefficients.HarrisLatticeLevelInclusion`, `LevelColimit` and
`CategoryTheory.EquivariantDiagram`. They provide the actual canonical
lattices and reduced inclusion maps, the existing ordered compact-level
category, and the varying-group diagram category. The new subgroup and
lattice functors use actual inclusions and prove their laws by
extensionality. The original lattice and torsion inclusion compatibility
fields construct the equivariant diagrams. Original torsion naturality and
functor laws assemble the whole exponent functor, and quotient induction
proves the final named-map normalizations. No additional external-source
assertion is introduced.

The construction supplies arithmetic coherence across ordered compact-level
inclusions and exponent reductions. Transport through the original CM
inverse-unop level actions, further descended geometric coarse-refinement
coherence, Hecke transporter compatibility, and rational adic lattice
independence are separate obligations. The exact representability,
arithmetic-existence, source-comparison and canonical-model obligations of
the containing task also remain explicit or unfinished. This focused
construction does not complete that task.
