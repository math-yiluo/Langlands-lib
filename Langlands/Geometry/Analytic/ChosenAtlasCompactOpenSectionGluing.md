# Coefficients and finite simultaneous stabilizers of actual sheaf glue

## Provenance and hypotheses

This is an internal construction by Worker 56. It uses the actual
continuous discrete section action of
`ChosenAtlasCompactOpenSectionAction`, the whole arbitrary-sieve glue of
`ChosenAtlasLocallyConstantGluingAction`, and the actual coefficient
natural transformation of `OriginalDomainLocallyConstantLocalization`.
Finite intersections of open subgroups and finite unions of compact sets
supply the remaining topological constructions. No new result is
attributed to external literature.

The geometric input is a group action `X` in the category of full chosen
bounded affinoid atlas presentations over a complete ultrametric normed
field. The original group topology makes `G` a topological group, and
`hX` asserts exactly joint continuity of the original point action
`(g,x) ↦ (X.ρ g).baseMap x`. Group elements act on domains by the actual
base homeomorphisms of `X.ρAut g` and on functions by actual inverse
precomposition. Coefficient types are arbitrary, with no action,
topology or nonemptiness premise. The field, point, chart-index,
coefficient, group and finite-family index universes are independent.

## Actual coefficient morphisms

`CompactOpenOriginalDomainSection.map φ` postcomposes the entire section
with any coefficient function `φ`, retaining the actual domain and its
compactness and openness proofs. Its identity and composition equations
are equalities of whole pairs, obtained from the published underlying
pair equations. `compactOpen_smul_map` proves equivariance for the
actual group operators through whole-pair extensionality and the
original transport/postcomposition equation.

`compactOpenCoefficientMap` is an actual morphism between the previously
constructed `ContAction` objects. Its underlying continuous function is
exactly this coefficient postcomposition. Continuity follows from the
discrete source topology, and the proved group equation gives
its equivariance. `compactOpenCoefficientFunctor` packages these objects
and morphisms into a functor from all coefficient types and functions to
continuous actions. Its identity and composition proofs reduce to the
whole-pair coefficient laws; the group topology is unchanged.

## Constructed common open stabilizers

`compactOpenSectionOpenStabilizer` packages the entire stabilizer of a
compact-open section pair as an open subgroup, using the predecessor's
proved ambient openness. For a finite family of complete pairs `s i`
and a prescribed open subgroup `U`, `finiteSectionOpenStabilizer`
constructs

`U ∩ ⋂ i, Stab_G(s i)`.

`mem_finiteSectionOpenStabilizer` characterizes membership exactly by
membership in `U` and fixedness of every whole local pair.
`finiteSectionOpenStabilizer_le` proves refinement of `U`.
`finiteSectionOpenStabilizer_map_le` proves that this original subgroup
is contained in the corresponding subgroup for every coefficient-mapped
family: equivariance sends each fixed original pair to a fixed mapped
pair. The construction includes the empty finite family; then there are
no local fixedness conditions and the subgroup is `U`.

## Arbitrary covering sieves and a finite selected subcover

The gluing input consists of an original-chart domain `S`, an arbitrary
sieve `R` on it, the full locally constant family `p` on every member of
`R`, its matching condition and the full original-domain covering
condition `IsCovering R`. In addition, choose a finite indexed family of
actual domains `T i`, original inclusions `f i : T i ⟶ S` that belong to
`R`, and proofs that each actual subset `T i` is compact and open. The
selected domains cover the target by the literal equality

`⋃ i, (T i : Set X.V.space) = (S : Set X.V.space)`.

This is finite subcover data within the original sieve. It neither
replaces that sieve by the selected members nor weakens its matching or
covering condition. It is an additional hypothesis; the module does not
assert existence of such a compact-open subcover for every domain.

`finiteSieveLocalSections` retains the selected original function
`p (f i) (hf i)` together with its entire actual domain `T i`.
`finiteSieveGlue` retains the actual previously constructed arbitrary-sieve
glue together with `S`. Its compactness proof is the finite union of the
selected compact subsets, and its openness proof is the union of the
selected open subsets, both rewritten through the displayed cover
equality. Thus target compactness and openness are derived, not supplied
as separate premises. `finiteSieveGlue_map` proves equality of the entire
mapped glue pair with the actual glue pair for the full
coefficient-mapped matching family. This uses the original whole-pair
glue coefficient equation and wrapper extensionality.

## Fixedness derived from the selected local pairs

`finiteSieveGlueOpenStabilizer` is exactly the common open subgroup
constructed from `U` and the finite selected local section pairs. It does
not include or assume the global glue's stabilizer as an input.

`finiteSieveGlue_fixed` proves that every element of this subgroup fixes
the actual entire glue pair. The implemented proof first takes domain
projections of the selected pair fixedness equations. Each literal
image domain is therefore its original `T i`. Images commute with
unions, so their cover equality gives invariance of the entire actual
target `S`.

To prove equality of the functions, take any target point and choose a
selected local member containing it. Its pair fixedness places the group
element in that member's full setwise stabilizer. The predecessor's
fixed-domain action comparison extracts equality of the complete
locally constant function with its inverse precomposition. The original
sheaf glue recovers the selected local function at both the point and
its inverse translate. These two recovery equations and local fixedness
prove equality of the global values. Whole-pair extensionality then
combines this equality with the derived target-domain invariance.

`finiteSieveGlueOpenStabilizer_le` states the result as containment of
the constructed common local subgroup in the entire global glue
stabilizer. The common subgroup already lies in `U` and fixes every
selected local pair. The global fixedness conclusion is proved from
their actual values and cover, rather than assumed or obtained by
intersecting with the global stabilizer.

## Scope and empty cases

The finite selected family can be empty only when its cover equality
forces the target subset to be empty. The proof then needs no target
point and has no coefficient default. Empty coefficient types and empty
sieves are retained whenever the given matching-family and covering data
exist.

This module treats locally constant functions and compact-open original
chart domains of a fixed chosen atlas. It does not assert compact-open
subcovers for arbitrary compact or distinguished domains, construct
general smooth equivariant sheaves, all analytic or etale sites, or the
Harris tower. Its result is a concrete common open subgroup for the
actual local sections and their actual sheaf glue in the stated local
class, with functorial continuous coefficient morphisms.
