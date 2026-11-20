# An actual embedded field with finite étale integer ring

`Langlands.CentralDivision.LocalDivisionFiniteEtaleSubfieldExistenceStatement`
is the existence proposition for every nonarchimedean local field `K` with
its given valuative relation and compatible topology, and every
finite-dimensional central division `K`-algebra `D`. The carriers have a
common arbitrary universe. The characteristic is unrestricted.

The witness is an original integral element
`b : (localReducedNormValuation K D).integer`. Write
`E = residueGeneratorSubalgebra K D (b : D)` for its actual singleton adjoin
with field structure `residueGeneratorField K D (b : D)`, `ι = E.val` for
the inclusion, and `w = localDivisionSubfieldValuation K D ι` for the
restricted valuation. The proposition gives all of the following.

- The original `localDivisionSubfieldResidueMap K D ι` is surjective.
- `E` is finite-dimensional over `K`.
- `w.integer` satisfies `Module.Finite 𝒪[K] w.integer` and
  `Algebra.Etale 𝒪[K] w.integer` with `localDivisionSubfieldIntegerAlgebra K D ι`.
- `Module.finrank K E = CentralSimple.reducedDegree K D`.

The proved implication
`localDivisionFiniteEtaleSubfieldExistence_of_fullResidueEtale` applies
`LocalDivisionFullResidueSubfieldEtaleStatement` to the witness of
`exists_localDivision_fullResidue_reducedDegree_cyclic_subfield` in
`LocalDivisionReducedDegree`. It uses that witness's original embedding,
residue surjectivity and reduced degree.
`FiniteDimensional.finiteDimensional_subalgebra` supplies finite dimension
from `D`. `localDivisionSubfieldInteger_finite` proves the module finiteness
conjunct over the original scalar action. This implication is an internal
deduction from the named declarations. Integral étaleness and the unconditional
finite étale existence proposition remain proof targets.

## Formal-module consumer

A consumer importing this pair and `Langlands.Geometry.FormalGroup.SpecialModule`
can pass the four conjuncts to `IsUnramifiedSubfieldOfReducedDegree` on the
same `ι`. Both algebra structures come from the same
`localDivisionSubfieldBaseIntegerMap K D ι` via `RingHom.toAlgebra`.
In namespace `Langlands.FormalGroup.LocalDivision`, with `ValuativeRel` and
`Langlands.CentralDivision` open and `K` and `D` as above, the comparison is

```lean
example (h : LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u}) :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      IsUnramifiedSubfieldOfReducedDegree K D (residueGeneratorSubalgebra K D (b : D)).val := by
  obtain ⟨b, _, hdim, hfinite, hetale, hdegree⟩ := h K D
  exact ⟨b, hdim, hfinite, hetale, hdegree⟩
```
