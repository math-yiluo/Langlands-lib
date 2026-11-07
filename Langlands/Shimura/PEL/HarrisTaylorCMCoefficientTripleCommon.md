# Three original canonical coefficient systems on actual common CM kernels

Author: Worker 57.

For actual small CM levels `T ≤ V ≤ U`, this internal construction puts the
three original canonical coefficient systems on one finite residual quotient
diagram inside `T`. It retains the original coefficient modules, inverse-unop
actions, exponent reductions and included-vector maps. The resulting two-arrow
chain has composite exactly the original direct `T`-to-`U` coefficient map.

All declarations are in
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`, in universe zero.

## Exact inputs and original coefficient systems

The arithmetic inputs are number fields `E` and `F`, with `E` totally real,
`F` totally complex and CM, an `E`-algebra structure on `F`, and
`IsQuadraticExtension E F`. The ring `A` has compatible `E`, `F` and rational
algebra structures and the scalar towers `E → F → A`, `ℚ → E → A` and
`ℚ → F → A`. Fix `n : ℕ`,
`D : CentralSimpleUnitaryData E F A n`, and `Module.Finite ℚ A`.

The coefficient inputs are a number field `K`, a finite-dimensional
`K`-module `W`, an algebraic representation
`ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`,
and a rational finite place `p`. Write
`R = HarrisCoefficientIntegers K p`. The original small CM levels
`U V T : SmallCMLevel D` retain their compact open opposite-group subgroups
and sufficiently-small certificates. The only new level premises are

```text
hVU : V.obj.subgroup ≤ U.obj.subgroup
hTV : T.obj.subgroup ≤ V.obj.subgroup.
```

Write `hTU = hTV.trans hVU`. Fix a natural scalar `m` and `hm : m ≠ 0`.
The nonzero premise is used by the existing actual compact open coefficient
kernel levels and finite residual quotients. Every exponent, including zero,
is retained. Some subgroup lemmas explicitly omit the unused `IsCMField F`
and `IsScalarTower E F A` classes.

For `X = T,V,U`, let `Λ_X` denote the original full Harris lattice at
`CompactOpenLevel.inverseOpposite X.obj`, and put
`I = harrisCoefficientScalarIdeal K p m`. The three underlying coefficient
modules at `k : ℕᵒᵖ` are

\[
 M_{X,k}=\Lambda_X/(I^{k.unop}\,\Lambda_X).
\]

Here the exact submodule is `I ^ k.unop • ⊤`, and the scalar ring remains
`R`. All three full exponent functors and their maps are the original ones:

- The own system is `cmHarrisTorsionSystem D ρ p T m`.
- The middle system is
  `cmHarrisCoarseTorsionSystem D ρ p V T hTV m`, the original `V` system
  restricted to the original subgroup `T`.
- The upper system is
  `cmHarrisCoarseTorsionSystem D ρ p U T hTU m`, the original `U` system
  restricted to that same subgroup `T`.

Thus all three actions have domain `T.obj.subgroup`. Each retains its
original inverse-unop transport to the ordinary finite-adelic group.
No action, lattice, desired coefficient map or normality of `T` in `V` or
`U` is supplied as an additional input.

## Literal common kernels and finite residual groups

For an ordinary exponent `k : ℕ`, write `X_k` for the original
`cmHarrisCoefficientLevel` at `X`. The existing coarse coefficient levels
have subgroups `T ∩ V_k` and `T ∩ U_k`. The existing direct pair comparison
level has subgroup `T_k ∩ (T ∩ U_k)`.

`cmHarrisTripleCommonLevel` takes the actual `smallCMCommonLevel` of that
direct pair level and the middle coarse coefficient level. Its subgroup is
literally

\[
 L_k=\bigl(T_k\cap(T\cap U_k)\bigr)\cap(T\cap V_k).
\]

The `subgroup` theorem identifies this precise parenthesized intersection.
The `le_pair`, `le_middle`, `le_own`, `le_upper` and `le` theorems give its
actual containments in the direct comparison level, middle kernel, own
kernel, upper kernel and `T`, respectively. They use the two intersection
projections and the previously constructed coefficient-level inclusions.

`cmHarrisTripleCommonLevel_subgroupOf` identifies the subgroup inside `T`
exactly with

\[
 \bigl(\ker\rho_{T,k}\cap\ker(\rho_{U,k}|_T)\bigr)
       \cap\ker(\rho_{V,k}|_T).
\]

The proof unfolds the literal subgroup intersection, then rewrites by the
existing direct pair kernel identity and middle coarse kernel identity.
The `normal` instance rewrites to this same intersection of kernels and
uses their normality. The `antitone` theorem follows by `inf_le_inf` from
the antitonicity of the original pair and middle coefficient levels.

The `le_lowerPair` theorem also puts `L_k` inside the original `T`-to-`V`
pair comparison level. The `le_upperPair` theorem puts it inside the
original `V`-to-`U` pair comparison level. The latter combines the
containments in the middle and upper coefficient kernels with `T ≤ V`,
then uses the original coarse-level subgroup formula. These are actual
subgroup containments, available for subsequent geometric tower maps.

`cmHarrisTripleCommonLevels` assembles the levels into a functor
`ℕᵒᵖ ⥤ SmallCMLevel D`. An exponent arrow is sent to the original
`smallCMInclusion` given by the proved antitonicity. The identity and
composition fields are the original inclusion identity and transitivity
laws.

`cmHarrisTripleCommonGroups` is the functor with vertices

\[
 Q_k=T/\bigl(L_{k.unop}.\operatorname{subgroupOf}(T)\bigr).
\]

Its arrows are the original `smallCMResidualQuotientMap` maps induced by
the common-kernel inclusions. They keep the same representative in `T`.
The existing quotient-map identity and composition laws prove the functor
laws. `cmHarrisTripleCommonGroups_finite` applies the original finite
residual-group theorem to these actual compact open subgroups.

## Three unchanged coefficient diagrams on the common quotients

`cmHarrisTripleOwnGroupMap`, `cmHarrisTripleMiddleGroupMap` and
`cmHarrisTripleUpperGroupMap` are natural group maps from `Q` to the
original own, middle and upper residual-group diagrams. Their components
are the quotient maps supplied by `L_k ≤ T_k`,
`L_k ≤ T ∩ V_k` and `L_k ≤ T ∩ U_k`. Quotient induction proves naturality:
both sides retain the same original representative.

The corresponding definitions
`cmHarrisTripleOwnCoefficients`, `cmHarrisTripleMiddleCoefficients` and
`cmHarrisTripleUpperCoefficients` are objects of

```text
EquivariantDiagram Q (ModuleCat R).
```

Each `.obj` is the complete underlying original coefficient functor,
including every exponent reduction. Its residual action is the original
residual action composed with the corresponding natural group map.
Quotient induction reduces transition equivariance to the original own,
middle or upper torsion-system transition's `comm` field. Thus changing
to the common residual quotient changes neither coefficient modules nor
their original actions and exponent maps.

## Actual coefficient chain and its direct composite

`cmHarrisTripleLowerCoefficientInclusion` is the morphism from the own
diagram to the middle diagram. Its underlying natural transformation is
the original `cmHarrisTorsionSystemInclusion` for `T ≤ V`, followed by
forgetting the `T` action.

`cmHarrisTripleUpperCoefficientInclusion` is the morphism from the middle
diagram to the upper diagram. Its underlying transformation is the
original inclusion for `V ≤ U`, first restricted along the actual subgroup
inclusion `T → V`, then with the `T` action forgotten.

`cmHarrisTripleDirectCoefficientInclusion` is the original direct
`T ≤ U` transformation with its `T` action forgotten. Equivariance of
each of these three maps is proved by quotient induction from the
corresponding original inclusion's `comm` field; the upper map applies
that field to `Subgroup.inclusion hTV g`.

`cmHarrisTripleCoefficientInclusion_comp` proves the equality of
equivariant-diagram morphisms

\[
 j_{T,V}\,;\,(j_{V,U}|_T)=j_{T,U}.
\]

Extensionality reduces it first to underlying natural transformations,
then to each exponent component. The concrete original
`cmHarrisTorsionSystemInclusion_comp` theorem gives exactly that component
equality.

The entry definition `cmHarrisTripleCoefficientChain` packages the two
maps as

```text
ComposableArrows (EquivariantDiagram Q (ModuleCat R)) 2.
```

It is constructed by `ComposableArrows.mk₂`, so it contains all three
full exponent diagrams and both actual arrows. The `lower` and `upper`
normalizations identify its `map' 0 1` and `map' 1 2` with the two original
inclusions by reflexivity. The `hom` theorem identifies the full chain's
composite with the direct original inclusion using the proved composition
equality.

`cmHarrisTripleDirectCoefficientInclusion_mk` gives the exact original
representative formula: the class of `x ∈ Λ_T` is sent to the class of
`harrisLatticeInclusion` from `Λ_T` into `Λ_U`, with
`CompactOpenLevel.inverseOpposite_mono hTU`. This retains the same ambient
coefficient vector in the two canonical lattices.

The direct, lower and upper `transition` theorems state the exponent
naturality square for every arrow `f : i → j` in `ℕᵒᵖ`. For each of the
three maps, reduction at the source followed by inclusion at `j` equals
inclusion at `i` followed by reduction at the target. These theorems are
the naturality fields of the actual underlying transformations, with the
entire original reduction systems retained.

## Provenance and scope

This is an internal deduction from
`HarrisTaylorCMCoefficientLevelSystem` and its imported actual CM kernel,
residual quotient, action and lattice-comparison constructions, together
with Mathlib's `ComposableArrows.Basic`. Literal intersections construct
the levels; the original kernel identities prove normality; existing
inclusion and quotient laws construct the diagrams; quotient induction
supplies their compatibility fields. The named original CM inclusion
composition law proves the chain's exact composite. No new assertion
from external literature or desired comparison output is assumed.

This unit constructs the arithmetic common-cover input for three nested
levels. Geometric torsors, associated sheaf systems on these common
covers and comparison with the separate pulled systems are subsequent
constructions. Reduced coefficient maps are not claimed to be injective
or invertible; equality of the lattices, rational adic independence and
Hecke compatibility are not established here. The containing task's
representability, arithmetic existence, source-comparison and
canonical-model obligations remain. This unit does not complete that task.
