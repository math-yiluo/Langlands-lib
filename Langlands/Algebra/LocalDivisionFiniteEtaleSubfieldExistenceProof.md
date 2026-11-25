# An actual embedded field with finite étale integer ring: proof

Lean module: `Langlands.Algebra.LocalDivisionFiniteEtaleSubfieldExistenceProof`,
namespace `Langlands.CentralDivision`.

## Statement

```
theorem Langlands.CentralDivision.localDivisionFiniteEtaleSubfieldExistence :
    LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u}
```

The type is exactly the published proposition
`Langlands.CentralDivision.LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u}`
of the module `Langlands.Algebra.LocalDivisionFiniteEtaleSubfieldExistenceStatement`,
at an arbitrary universe `u`, with no further hypothesis. Unfolded, it reads:

```
∀ (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D],
  ∃ b : (localReducedNormValuation K D).integer,
    let E := residueGeneratorSubalgebra K D (b : D)
    letI : Field E := residueGeneratorField K D (b : D)
    let ι := E.val
    letI := localDivisionSubfieldIntegerAlgebra K D ι
    Function.Surjective (localDivisionSubfieldResidueMap K D ι) ∧
      FiniteDimensional K E ∧
      Module.Finite 𝒪[K] (localDivisionSubfieldValuation K D ι).integer ∧
      Algebra.Etale 𝒪[K] (localDivisionSubfieldValuation K D ι).integer ∧
      Module.finrank K E = CentralSimple.reducedDegree K D
```

In words: for every nonarchimedean local field `K` and every
finite-dimensional central division `K`-algebra `D`, of any characteristic,
there is an integral element `b` of `D` whose singleton adjoin `E` is a field
with residue map onto the residue field of `D`, finite-dimensional over `K` of
dimension the reduced degree of `D`, whose valuation ring is finite and étale
over `𝒪[K]`.

## Proof

The Lean proof is the single application

```
localDivisionFiniteEtaleSubfieldExistence_of_fullResidueEtale
  localDivisionFullResidueSubfieldEtale.{u, u}
```

of `localDivisionFiniteEtaleSubfieldExistence_of_fullResidueEtale` (module
`Algebra.LocalDivisionFiniteEtaleSubfieldExistenceStatement`), which derives
the statement from `LocalDivisionFullResidueSubfieldEtaleStatement.{u, u}`, to
`localDivisionFullResidueSubfieldEtale` (module
`Algebra.LocalDivisionFullResidueSubfieldEtaleProof`) at the universes
`u, u`, proved without hypotheses: for every subfield `L` of `D`, finite over
`K` of reduced degree and with full residue field, the valuation ring of `L`
is étale over `𝒪[K]`. The second universe parameter, that of `L`, is set to
`u` because the reduction applies it to a subalgebra of `D`.

Inside the reduction, the witness `b` is that of
`exists_localDivision_fullResidue_reducedDegree_cyclic_subfield`, finiteness
of the integer ring is `localDivisionSubfieldInteger_finite`, and étaleness is
the premise; see the page of
`Algebra.LocalDivisionFiniteEtaleSubfieldExistenceStatement`. The statement is
not modified and no hypothesis is added.

## Declarations

- `Langlands.CentralDivision.localDivisionFiniteEtaleSubfieldExistence :
  LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u}`.

## Literature

The statement's page records an internal deduction and cites no source. The
étaleness input is the classical comparison of J.-P. Serre, *Local Fields*
(1979), Chapter I, §6: Proposition 15 with Corollaries 1 and 2, printed p. 18
(a monic polynomial with irreducible reduction presents the integral closure,
and separable reduction gives an unramified extension), and Proposition 16,
printed pp. 18–19 (the converse for an integral closure whose residue field is
a simple extension of the full degree), as cited on the page of
`Algebra.LocalDivisionFullResidueSubfieldEtaleStatement`.
