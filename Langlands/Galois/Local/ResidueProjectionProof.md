# The residue projection of a separable closure: proof of the statement

`Langlands.Galois.Local.ResidueProjectionProof` proves the proposition
`ResidueProjectionExactness` of `Galois/Local/ResidueProjectionStatement.lean`: for every
nonarchimedean local field `K`, of either characteristic, and every separable closure `Ω`
of `K`, the integers, residue field, residue homomorphism and inertia subgroup of `Ω`
defined in `Galois/Local/AbsoluteDefinitions.lean` have the twenty-two properties of
`ResidueProjectionProperties K Ω`. Each clause is a theorem of its own, in the files by
subject listed below or in the Library; this file assembles them.

## Statements

**`residueProjectionProperties`.** For `K` and `Ω` as in the statement,
`ResidueProjectionProperties K Ω` holds:

```lean
theorem Langlands.LocalGalois.residueProjectionProperties
    (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] :
    ResidueProjectionProperties K Ω
```

**`residueProjectionExactness`.** The statement itself, with the two independent universe
parameters of the statement:

```lean
theorem Langlands.LocalGalois.residueProjectionExactness.{uK, uΩ} :
    ResidueProjectionExactness.{uK, uΩ}
```

## The clauses and their theorems

`G = Ω ≃ₐ[K] Ω`, `ρ = SepClosed.absoluteResidueHom K Ω`, `I = SepClosed.absoluteInertia K Ω`,
`B = SepClosed.closureIntegers K Ω`. All names are in `Langlands.LocalGalois`.

| # | Clause | Theorem | File |
| --- | --- | --- | --- |
| 1 | the topology of `localNormedField K` is that of `K` | `localNormedField_topology` | `AbsoluteDefinitions` |
| 2 | `Finite 𝓀[K]` | Mathlib instance `IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation` | `Mathlib/NumberTheory/LocalField/Basic.lean` |
| 3 | `closureValuation K Ω` extends the valuation of `K` | instance `SepClosed.closureValuation_extends` | `AbsoluteDefinitions` |
| 4 | the unit ball of the norm is `𝒪[K]` | `localNormedField_integer` | `AbsoluteDefinitions` |
| 5 | integral over `𝒪[K]` iff in `B` | `SepClosed.isIntegral_iff_mem_closureIntegers` | `ResidueProjectionIntegers` |
| 6 | the valuation is `G`-invariant | `SepClosed.closureValuation_algEquiv_apply` | `ResidueProjectionIntegers` |
| 7 | the residue field of `B` is an algebraic closure of `𝓀[K]` | `SepClosed.residueAlgebra_isAlgClosure` | `ResidueProjectionResidueField` |
| 8 | the comparison is compatible with reduction from `𝒪[K]` | `SepClosed.residueClosureEquiv_residue_integerMap` | `ResidueProjectionResidueField` |
| 9 | `ρ σ` acts on residues as `σ` | `SepClosed.absoluteResidueHom_residue` | `ResidueProjectionInertia` |
| 10 | `ρ` is continuous | `SepClosed.absoluteResidueHom_continuous` | `AbsoluteProof` |
| 11 | `ρ` is surjective | `SepClosed.absoluteResidueHom_surjective` (with Mathlib's `IsSepClosure.isGalois`) | `AbsoluteProof` |
| 12 | `ρ` is open | `SepClosed.isOpenMap_absoluteResidueHom` | `ResidueProjectionInertia` |
| 13 | `ker ρ = I` | `SepClosed.absoluteResidueHom_ker` | `AbsoluteProof` |
| 14 | `σ ∈ I` iff trivial on residues | `SepClosed.mem_absoluteInertia_iff` | `ResidueProjectionInertia` |
| 15 | `I` is the preimage of Mathlib's inertia subgroup | `SepClosed.absoluteInertia_eq_comap_decompositionHom` | `ResidueProjectionInertia` |
| 16 | `I` is normal | instance `SepClosed.absoluteInertia_normal` | `AbsoluteDefinitions` |
| 17 | `I` is closed | `SepClosed.isClosed_absoluteInertia` | `ResidueProjectionInertia` |
| 18 | `I` is compact | instance `SepClosed.compactSpace_absoluteInertia` | `ResidueProjectionInertia` |
| 19 | `I` is totally disconnected | `SepClosed.totallyDisconnectedSpace_absoluteInertia` | `ResidueProjectionInertia` |
| 20 | `I` is Hausdorff | `SepClosed.t2Space_absoluteInertia` | `ResidueProjectionInertia` |
| 21 | `G/I ≃ₜ* Field.absoluteGaloisGroup 𝓀[K]` through `ρ` | `SepClosed.absoluteResidueQuotientEquiv` and `SepClosed.absoluteResidueQuotientEquiv_apply` | `ResidueProjectionQuotient` |
| 22 | reduction commutes with restriction to normal `E` | `SepClosed.absoluteResidueHom_restrictNormal` | `ResidueProjectionInertia` |

The files named without a directory are in `Langlands/Galois/Local/`.

## Proof

The body of `ResidueProjectionProperties K Ω` begins with
`haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`; after its first clause it installs
`localNormedField K` and its ultrametric and completeness certificates with `letI`. The
proof follows the same order: it adds `IsSepClosed Ω` and `Algebra.IsAlgebraic K Ω` (from
`Algebra.IsSeparable.isAlgebraic`) as local hypotheses, proves the first clause by
`localNormedField_topology K`, installs the same three instances, and gives the remaining
twenty-one clauses by the theorems of the table. The theorems of the subject files are
stated with local instances whose values are `localNormedField K` and its certificates,
and with `IsSepClosure.sep_closed K` for `IsSepClosed Ω`, so they match the clauses up to
unfolding of those reducible local instances and proof irrelevance.
`residueProjectionExactness` applies `residueProjectionProperties` to every `K` and `Ω`.

The proof uses no hypothesis on the characteristic of `K`. Where the characteristic-zero
proof of `LocalResidueProperties` (`Galois/Local/AbsoluteProof.lean`) used `CharZero K` to
make `AlgebraicClosure K` Galois over `K`, the separable closure is Galois over `K` by
Mathlib's `IsSepClosure.isGalois`; where it used algebraic closedness of
`AlgebraicClosure K` to make the residue field algebraically closed, the Library's
`SepClosed.residue_isAlgClosure` uses that the residue field of a separably closed valued
field is separably closed and that the finite residue field of `K` is perfect.

## Declarations, in order

1. `residueProjectionProperties` (theorem).
2. `residueProjectionExactness` (theorem).

## Literature

The mathematical content is that of the subject files; their pages cite the sources:
the extension of the valuation and the integers (`ResidueProjectionIntegers.md`: Neukirch,
*Algebraic Number Theory*, II (4.8), pp. 131–132; Serre, *Local Fields*, II §2, Proposition 3
and Corollaries 2–3, pp. 28–29); the residue field (`ResidueProjectionResidueField.md`:
Neukirch II (7.5), p. 154, and II §9, p. 173; Serre III §5, Corollary 1, pp. 54–55, and
V §4, Lemma 7, p. 89); inertia and the residue homomorphism
(`ResidueProjectionInertia.md`: Serre I §7, Propositions 20 and 22, pp. 21–23; Neukirch II
(9.3), p. 168, and (9.9), p. 172; Cassels–Fröhlich, ch. I §7, Theorem 2, pp. 27–28); the
quotient (`ResidueProjectionQuotient.md`: Serre III §5, Corollary 1, pp. 54–55; Neukirch II
(9.9)–(9.11), pp. 172–173; Cassels–Fröhlich, ch. I §7, Corollary 2 and the Application,
p. 28). For the finiteness of the residue field (clause 2): Serre, *Local Fields*, II §1,
Proposition 1, printed p. 27 (a field complete under a discrete valuation is locally
compact exactly when its residue field is finite); file
`/srv/central-library/Serre--Local Fields--1979.pdf`. The sources treat finite extensions,
or the maximal unramified extension, of a complete discretely valued field; the statement
proved here is the derived statement for a separable closure, with the Library's
objects.
