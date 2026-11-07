# Original cyclic full-residue subfields of reduced degree

Let `K` be an actual nonarchimedean local field and `D` a finite-dimensional
central division `K`-algebra. Both types lie in an arbitrary common universe.
There is no restriction on characteristic. All valuations, residue quotients,
scalar maps, and subalgebras below are the existing constructions on the
original objects.

The theorem `localDivisionResidue_finrank_eq_reducedDegree` proves

```text
[DivisionValuation.Residue (localReducedNormValuation K D) : 𝓀[K]]
  = CentralSimple.reducedDegree K D.
```

The residue field and its base-residue algebra structure are precisely
`localDivisionResidueField` and `localDivisionResidueAlgebra`. This is the
dimension of the actual strict-ideal quotient over the original base residue
field, with the previously proved finiteness.

For the upper bound, `DivisionReducedCharpoly` proves that the minimal
polynomial of an original division element has degree at most the reduced
degree. The existing full-residue field construction has degree equal to the
actual residue extension degree, so that bound applies to it. For the lower
bound, choose that same existing full-residue field and apply
`reducedDegree_le_localDivisionSubfield_finrank` from `LocalDivisionDegree`.
The latter theorem uses finite valuation-layer approximation, the finite
original integer lattice, Nakayama's lemma, and the original scalar-tower
dimension identity. Antisymmetry gives the displayed equality.

The theorem `exists_localDivision_fullResidue_reducedDegree_cyclic_subfield`
then takes the witness from
`exists_localDivision_fullResidue_cyclic_subfield`. Its original integral
generator `b` is separable over `K`. The original singleton-adjoin subalgebra
`residueGeneratorSubalgebra K D (b : D)`, equipped with
`residueGeneratorField`, has surjective actual residue map, is Galois over
`K`, and has cyclic group of `K`-automorphisms. Its degree over `K` is exactly
the reduced degree, by the residue-degree equality just proved. No new
subfield or altered embedding replaces the original witness.

The definition `localDivisionCyclicReducedDegreeGenerator` chooses one such
original integral generator. The theorem with suffix `_spec` records all five
properties together: separability, residue surjectivity, the exact degree,
the Galois property, and cyclicity of the actual automorphism group.

This is an internal deduction from the named imported constructions and
their proved dimension bounds. The reduced-characteristic-polynomial bound
is due to Worker 1360; the lattice, lower bound, cyclic-subfield construction,
and this assembly are due to Worker 1757. This unit does not prove
arbitrary-element movement, local SK1, or the full local Kneser–Tits theorem.
