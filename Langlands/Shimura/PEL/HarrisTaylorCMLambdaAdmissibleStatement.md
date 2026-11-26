# Admissibility and Galois continuity of CM λ-adic tower cohomology

## Sources

Michael Harris and Richard Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), III.2, printed pp. 94–97 (PDF pp. 102–105).
The construction of the lisse sheaf from an algebraic representation and
the compatible level maps is on pp. 94–96. The colimit and invariants
comparison are on p. 96, and the admissibility and Galois continuity
assertion is on p. 97. Registered ID
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Michael Harris, *Galois properties of cohomological automorphic forms on
GL(n)* (1999), §3, printed pp. 306–307, and §§4–5, pp. 311–313, uses a
coefficient representation rational over a number field and cohomology
with the corresponding lisse system at a coefficient prime. Registered
ID `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
Theorem 5.7 then considers Galois representations on the isotypic
cohomology. The tower admissibility assertion here uses Harris–Taylor
III.2. Harris's Proposition 4.10 uses equivariance for the prime-to-`ℓ,p`
levels in the comparison with analytic spaces.

## Lean proposition

`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel.CMHarrisLambdaTowerAdmissibleContinuousStatement`
uses the actual `cmHarrisLambdaTowerCohomology` of the Library's CM
unitary similitude Shimura tower. As in the construction module
[HarrisTaylorCMLambdaTower](HarrisTaylorCMLambdaTower.md), it takes
Harris signature charts, the indicated geometric construction and
representability premises, and the rigidity premise at each small
level. It assumes that the central simple algebra `A` is a division
algebra. Coefficients are a general finite-dimensional algebraic
representation `ρ` defined over a number field `K`, at a place `l`
of `K` above the given rational place and in any degree `degree`. The
module topology on a finite-dimensional space over `FiniteCompletion K l.1`
is the `λ`-adic topology. This coefficient field is a finite extension
of `ℚ_ℓ` in the Library's Harris model. Harris–Taylor III.2 uses
algebraically closed `ℓ`-adic coefficients.

The conclusions are as follows.

- `CMHarrisLambdaTowerFixedVectorComparison` asserts that the actual
  colimit leg from any small level is injective and has image the
  fixed-vector submodule for that level. This compares finite-level
  cohomology with the tower through the map defined by change of level.
- `Langlands.IsAdmissible` asserts smoothness and finite generation
  over `K_λ` of the fixed vectors of every open subgroup of the
  finite-adelic group. The Library uses all open subgroups in the
  admissibility condition. Finiteness for arbitrary open subgroups
  follows from the compact open case by containment in the fixed
  space of a smaller compact open subgroup.
- `HasContinuousOrbits` asserts continuity of the Galois action on
  the actual fixed vectors for every compact open subgroup `J`. The
  action is `fixedVectorsActionFunctor` applied to the tower, with
  the Krull topology on the Galois group. The spaces are finite
  dimensional by admissibility, so continuous orbit maps give a
  continuous finite-dimensional Galois representation.

A proof requires the fixed-vector comparison from finite-level
étale descent and the finite-dimensionality and Galois continuity
of the finite-level cohomology. Small levels are cofinal in the
compact open subgroups used to test admissibility and continuity.
These requirements are proof obligations, while the only inputs to
the proposition's cohomology objects are their stated construction
premises. The statement has no split-place comparison or banality
condition.
