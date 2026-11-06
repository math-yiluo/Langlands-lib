# Original Harris coefficients on actual smaller coarse CM levels

This internal construction fixes the original stable lattice at a small CM level
`U`, an inclusion `hVU : V.obj.subgroup ≤ U.obj.subgroup`, and the original full
Harris coefficient reductions. It constructs their actual kernel levels over
`V`, their residual quotient diagram, and the coefficient diagram obtained by
restricting the original action. No new lattice is chosen at `V`.

## Inputs and conventions

The namespace is
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. The arithmetic types are in
universe zero. The inputs retain:

- A totally real number field `E`, a totally complex CM number field `F`, and
  a quadratic `E`-algebra structure on `F`.
- A ring `A` with compatible `E`, `F` and rational algebra structures, including
  the `E/F/A`, rational/`E/A` and rational/`F/A` scalar towers, a finite rational
  module structure, and `D : CentralSimpleUnitaryData E F A n`.
- A number field `K`, a finite-dimensional `K`-module `W`, and the algebraic
  representation `ρ` of `D.rationalInvolution.baseChange K` on `W`.
- A rational finite place `p`, actual small CM levels `U`, `V`, and their specified
  subgroup inclusion `hVU`.

The definitions use the full product ring `R = HarrisCoefficientIntegers K p`
and the original `harrisLatticeAction` at
`CompactOpenLevel.inverseOpposite U.obj`. They keep all coefficient places above
`p` and all original lattice reductions. The integer `m` is nonzero whenever
kernel levels and their finite quotients are used. Exponents run through
`ℕᵒᵖ`, including zero.

The acting CM level groups are subgroups of the opposite finite adelic point
group. Their action on the original lattice is transported through
`CompactOpenLevel.inverseOppositeEquiv U.obj`; the construction does not replace
this inverse-unop convention. The inclusion of `V` into `U` is not required to
be normal.

## Restricted action and actual kernel levels

Write `U_k = cmHarrisCoefficientLevel D ρ p U m hm k` and let `M_k` denote the
original full integral coefficient module at exponent `k`.
`cmHarrisCoarseTorsionSystem` is literally the original `cmHarrisTorsionSystem`
followed by `Action.res` along `Subgroup.inclusion hVU`. Its kernel theorem
identifies its exponent-`k` kernel with the inverse image of
`cmHarrisCongruenceKernel D ρ p U m k` under that subgroup inclusion.

`cmHarrisCoarseCoefficientLevel` is the existing identity-Hecke intersection
`smallCMCommonLevel D V U_k`, as an actual `SmallCMLevel D`. Denote it by `T_k`.
The specified inclusion proof is an explicit parameter of this definition; this
also lets the normality instance recover the same inclusion from the level
expression. The underlying level is the stated intersection.
The subgroup, inclusion and kernel lemmas prove

\[
|T_k|=|V|\cap |U_k|,\qquad |T_k|\le |V|,\qquad |T_k|\le |U_k|,
\]

and

\[
|T_k|\operatorname{.subgroupOf}|V|
 =\operatorname{comap}(V\hookrightarrow U)(\ker(U\curvearrowright M_k))
 =\ker(V\curvearrowright M_k).
\]

Here `|T|` means the actual ambient subgroup of the level, rather than its
underlying topological space. The equality with the restricted action kernel is
`cmHarrisCoarseCoefficientLevel_eq_ker`.
`cmHarrisCoarseCoefficientLevel_normal` derives normality in `V` from the comap
of the original normal kernel. Thus normality of `V` in `U` is not an input.

`cmHarrisCoarseCoefficientLevel_antitone` proves that larger exponents give
smaller ambient subgroups. `cmHarrisCoarseCoefficientLevels` uses those
inclusions as the morphisms of a functor `ℕᵒᵖ ⥤ SmallCMLevel D`. Its identities
and compositions follow from the original identity-transporter inclusion laws.

`cmHarrisCoarseCoefficientLevelProjection` projects this tower to the constant
level `V`. `cmHarrisCoarseCoefficientLevelComparison` maps it to the original
kernel tower at `U`. Both are natural transformations with actual inclusion
components. The projection comparison theorem proves, at every exponent,

\[
(T_k\longrightarrow U_k)\,;\,(U_k\longrightarrow U)
 = (T_k\longrightarrow V)\,;\,(V\longrightarrow U).
\]

These are equalities in the genuine small CM level category, before passing to
schemes. Its morphisms retain the original transporter elements.

## Residual quotients and their embeddings

`cmHarrisCoarseCoefficientGroups` is the functor of actual residual groups

\[
H_k=V/(T_k\operatorname{.subgroupOf}V).
\]

Its exponent transitions are the existing `smallCMResidualQuotientMap` for the
proved kernel-level inclusions. They retain every representative `g ∈ V` and
are surjective. Their identity and composition laws are proved by the original
quotient-map laws. Every `H_k` is finite by `smallCMResidualGroup_finite` for
compact/open CM levels.

`cmHarrisCoarseCoefficientGroupInclusion` uses
`QuotientGroup.quotientMapSubgroupOfOfLe` to construct

\[
\iota_k:H_k\longrightarrow G_k=U/(U_k\operatorname{.subgroupOf}U),
\qquad [g]\longmapsto [g].
\]

The representative in the target is `Subgroup.inclusion hVU g`.
Its injectivity proof reduces to representatives: if its image is the identity,
then `g` belongs to `U_k`; since `g` already belongs to `V`, it belongs to the
actual intersection `T_k`. This proves an embedding; no surjectivity of this
map is asserted.

`cmHarrisCoarseCoefficientGroupMap` assembles these homomorphisms into a natural
transformation to the original `cmHarrisCoefficientGroups`. Its naturality
proof reduces both routes to the same original representative. Thus, for every
exponent arrow `f : i ⟶ j`,

\[
\iota_j\circ H(f)=G(f)\circ\iota_i.
\]

## Full coefficient diagram on the restricted groups

`cmHarrisCoarseCoefficientDiagram` is an
`EquivariantDiagram (cmHarrisCoarseCoefficientGroups …) (ModuleCat R)`.
Its underlying coefficient functor is definitionally the original
`cmHarrisCoefficientDiagram … U … .obj`, so both its modules and all their
reduction maps are unchanged. Its action at `k` is the original residual action
composed with the constructed `ι_k`.

The equivariance field is proved from the displayed group naturality equation
and the original coefficient diagram's equivariance. In particular, no new
commuting-square premise is supplied. `cmHarrisCoarseCoefficientActionIso` is
the identity isomorphism between this action and the original action restricted
through `ι_k`; these two action objects are definitionally equal.

`cmHarrisCoarseCoefficientDiagram_action` states that evaluating the residual
action on `[g]`, for `g ∈ V`, gives exactly the restricted original torsion
action on `g`. On an original lattice representative `x`, the more explicit
`cmHarrisCoarseCoefficientDiagram_action_mk` gives

\[
[g]\,[x]=\bigl[\rho_L(\operatorname{inverseOppositeEquiv}_U(g))x\bigr],
\]

where `g` is first included into `U` and `ρ_L` is the original stable-lattice
action. Each coefficient transition sends the class of `x` to the class of the
same `x` at the smaller exponent. All coefficient transitions remain surjective
and every coefficient module has a finite carrier; the proofs use the original
full-lattice reduction results.

## Provenance and scope

This pair is an internal composition of the published
`HarrisTaylorCMCoefficientCommonRefinement` and `HarrisTaylorCMCoefficientDiagram`
modules, together with Mathlib's subgroup and quotient constructions imported
through them. The former constructs the actual identity-Hecke intersection
level and its subgroup equality. The latter supplies the original full lattice
system, its actual coefficient kernels and level tower, residual quotients,
coefficient actions and reduction maps. Kernel comap, intersection monotonicity,
original inclusion functoriality and quotient induction prove all the new laws.
It makes no new claim translated from an external source.

This is the arithmetic prerequisite for comparison on named intersection covers
when the coarse level changes from `U` to `V`. It does not yet construct the
scheme torsors over `S(V)`, their maps to pullbacks of covers over `S(U)`, or
associated-sheaf comparisons on those covers. It does not identify this lattice
with a separately chosen lattice at `V`, prove base/lattice independence, or
construct an independent all-level adelic coefficient system. The geometric
existence and source-specialization obligations of the containing task remain.
