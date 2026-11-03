# Finite-length and irreducible consequences on the actual rational points

Author: Worker 379. The six propositions in
`Langlands.Aubert.General.RationalPointFamily` restate the generic targets of
`SharpConsequenceStatements` (Aubert's Corollaire 3.9 and its finite-length
specialization) for the actual group of rational points of a connected
reductive group and its actual standard subgroup families. They are
proposition definitions only: no target is proved here.

## Setting

The group setting is that of `RationalSupportCategoryTargets.md`. The
statements quantify over every nonarchimedean local field `k`, connected
reductive `G` (`hG`), actual maximal split torus `i` (`hi`) and generic
cocharacter `ν` (`hν`). The ambient group is `RationalPoint k G.X` with
`pointTopology` and explicit local compactness, nonarchimedean and Hausdorff
premises. The families are literally `parabolic i ν`, `levi i ν` and
`unipotent i ν` at `rootSet i ν I`, and the finite enumeration of
`SimpleRoot i ν` is `simpleRelativeRootFintype`. No split, quasisplit or
characteristic-zero restriction is imposed, and the empty simple-root set is
allowed. Every statement quantifies over every linear order on
`SimpleRoot i ν`; it only chooses the exterior coordinates of the complex.

`E#` is the actual terminal cokernel of the normalized complex at degree
`|S| - |I|`, that is `StandardComplex.sharpObject` with the actual families
substituted. It is the same object as `rationalSharpObject` of
`RationalStandardComplex`. Representations have carriers in
`Type (max (u + 1) v)`, the carrier universe of `E#`, so `E`, `E#` and `(E#)#`
lie in one category and one Grothendieck group. The generic targets are
instantiated at `.{u, u, max (u + 1) v}`.

## Derived generic arguments

| Generic argument | Actual value |
| --- | --- |
| `h` | `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν` |
| `hclosed` | explicit closedness premise `hU` of the radicals |
| `hδ` | `standardUnipotent_isUnimodular i ν hU hUc` |
| `hP`, `hU` | `standardParabolic_monotone i ν hOrder hG hi hν`, `standardUnipotent_antitone i ν hOrder hG hi hν` |
| `hM` | explicit closedness premise `hM` of the Levis |
| `hL` | `isSemidirectDecomposition_in_levi i ν hInter hG hi hν` |
| `IsAssociate` | `rootAssociation i ν hN hZ` |

So unimodularity is derived from the compact-limit premise `hUc`, and the
order of the families from `StandardParabolicOrderStatement`; neither is a free
field. `rootAssociation` and its pairing with Levi conjugation are explained in
`RationalSupportCategoryTargets.md`.

Each definition keeps only the inputs its generic target uses. All six keep
`hStandard`, `hOrder`, `hRoots`, `hU` and `hUc`. All but
`RationalSharpFiniteLengthStatement` also keep `hInter` and `hM`, which enter
through the support category or the cuspidal series. Only the class formula,
support retention and cuspidal-series statements use `IsAssociate` and keep
`hN` and `hZ`. No statement uses `StandardParabolicEndpointsStatement`.
Omitting an unused premise only strengthens the statement.

## Targets

| Declaration | Generic target | Source |
| --- | --- | --- |
| `RationalSharpFiniteLengthStatement` | `SharpFiniteLengthTarget` | needed for Corollaire 3.9 (a), Aubert (1995), p. 2189 |
| `RationalSharpClassFormulaStatement` | `SharpClassFormulaTarget` | Corollaire 3.9 (a), p. 2189; erratum, p. 4690 |
| `RationalSharpSupportRetentionStatement` | `SharpSupportRetentionTarget` | derived: needed to iterate `#` on `Alg({I})` (erratum, pp. 4687 and 4690) |
| `RationalSharpIrreducibleStatement` | `SharpIrreducibleTarget` | Corollaire 3.9 (b), p. 2189 |
| `RationalSharpCuspidalSeriesStatement` | `SharpCuspidalSeriesTarget` | derived: used in the proof of Corollaire 3.9 (c), p. 2189 |
| `RationalSharpInvolutionStatement` | `SharpInvolutionTarget` | Corollaire 3.9 (c), p. 2189 |

With these substitutions the statements say the following, for the actual
support category `Alg({I})` and the actual cuspidal series `𝔈(I)` of the
rational points:

- finite length of `E` implies finite length of `E#`;
- for a finite-length `E ∈ Alg({I})` with `E#` of finite length,
  `D_G([E]) = (-1)^{|I|} [E#]` in the exact finite-length Grothendieck group,
  where `D_G` is Aubert's unadjusted operator `alternatingOperator` on the
  actual families;
- `E ∈ Alg({I})` implies `E# ∈ Alg({I})`;
- `E ∈ 𝔈(I)` implies that `E#` is irreducible;
- `E ∈ 𝔈(I)` implies `E# ∈ 𝔈(I')` for some `I'` and some actual point `n`
  with `rootAssociation i ν hN hZ I I' n` and `L_{I'} = n L_I n⁻¹`;
- `E ∈ 𝔈(I)` implies `(E#)# ≅ E`, both cokernels taken at degree `|S| - |I|`.

In the class formula the finite-length preservation
`hfl : ∀ J, ParabolicFiniteLength (h J) (hclosed J)` used to build `D_G` stays
universally quantified inside the generic target. `ParabolicFiniteLength` is a
proposition, so `D_G` does not depend on the proof chosen. One such proof is
`standardParabolicFiniteLength` of `RationalAlternatingOperator`, from its own
named premises; this statement does not commit to that route. The full reading
of the generic targets and the extension of (a) from `𝔈(I)` to `Alg({I})` are
in `SharpConsequenceStatements.md`.

## Provenance

This is a derived specialization: the mathematical content is that of Aubert's
Corollaire 3.9 and the erratum's description of `E#`. The derivation pins the
generic parameters to the actual families and the named structural inputs
above. The structural, closedness and topological premises remain
intermediate obligations, to be discharged or matched to the parent's
external structural ledger. No representation-theoretic statement is moved
into them. Aubert's Proposition 3.2 is not used.
