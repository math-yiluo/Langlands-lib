# Nondegeneracy of the rational prime-adic polarization Weil pairing

Authors: Worker 989, Worker 970.

`Langlands.AbelianScheme.primeRationalPolarizationWeilNondegeneracy` proves exactly
`Langlands.AbelianScheme.PrimeRationalPolarizationWeilNondegeneracyStatement`, from
`Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyStatement`,
unchanged and with no extra hypotheses.

The statement concerns the existing `primeRationalWeilAlongHomBilinearMap`, pulled
back in its second variable by an actual relative polarization `lam` of an abelian
scheme `A` over a quasi-separated base `S`. It is evaluated on the rational
prime-adic Tate module `GroupScheme.Tate.PrimeAdic.Rational A.toGrp (Over.mk s) p`
at a geometric point `s : Spec K ⟶ S`, where `K` is algebraically closed and
`(p : K) ≠ 0`. The conclusion is Mathlib's `LinearMap.Nondegenerate`, so both
radicals vanish. The statement keeps `RelativeFiniteWeilTransitionStatement` and the
other dual-constructor propositions as explicit inputs of the proposition. The proof
assumes no finite nondegeneracy or alternation.

## Implemented proof

The theorem is a term proof that composes four published Library theorems.

1. `fieldDualKernelCharacterBijective`
   (module `Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveProof`)
   proves `FieldDualKernelCharacterBijectiveStatement`. Let `f : A ⟶ B` be an
   isogeny of abelian schemes over a field `k`, and let `T` be a test `k`-scheme.
   Then the normalized point map `dualKernelPointCharacter` is bijective, from the
   points of the kernel of the dual homomorphism to the Cartier characters of `ker f`.
2. `geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective`
   (module `Langlands.AbelianScheme.Tate.WeilFiniteGeometricNondegeneracyFromField`)
   is applied to the proof from step 1. The result is
   `GeometricFiniteWeilNondegeneracyStatement`. Let `s : Spec K ⟶ S` be a geometric
   point with `K` algebraically closed and `(n : K) ≠ 0`. Then the finite-level Weil
   pairing `finiteWeilLevelBilinearMap ... n (Over.mk s)` between the `n`-torsion
   points of `A` and of its dual has trivial left and right kernels.
3. `algClosedPointDivisibility`
   (module `Langlands.AbelianScheme.AlgClosedPointDivisibility`) proves
   `AlgClosedPointDivisibilityStatement`. Let `B` be an abelian scheme over `S`, and
   let `s : Spec K ⟶ S` be a geometric point with `K` algebraically closed and
   `(m : K) ≠ 0`. Then every point `y : Over.mk s ⟶ B.X` has the form `x ^ m`.
4. `primeRationalPolarizationWeilNondegeneracyReduction`
   (module `Langlands.AbelianScheme.Tate.WeilPrimeRationalPolarizationNondegeneracyReduction`)
   proves `PrimeRationalPolarizationWeilNondegeneracyReductionStatement`. This is the
   implication from the statements of steps 2 and 3 to the target. The levels
   `p ^ n` give left and right separation of the integral prime-adic pairing. The
   polarization isogeny then gives integral and rational nondegeneracy of the pulled-back
   pairing, as described in that module's Markdown.

So the proof is
`primeRationalPolarizationWeilNondegeneracyReduction
  (geometricFiniteWeilNondegeneracy_of_fieldDualKernelCharacterBijective
    fieldDualKernelCharacterBijective)
  algClosedPointDivisibility`.
The module defines nothing new. The theorem's axioms are the standard `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance and scope

This proof is a derived assembly of published Library results. The mathematical
outline follows Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`:

- Chapter VII, Theorem (7.5), printed p.100 / PDF p.104: the kernel of the dual
  isogeny is the Cartier dual of the kernel (step 1).
- Chapter XI, Definition (11.11) and its following discussion, printed pp.162–163 /
  PDF pp.166–167: the finite Weil pairing and its perfectness (step 2).
- Chapter XI, (11.23), printed p.168 / PDF p.172, and Chapter X, Corollary (10.7),
  printed p.144 / PDF p.148: passage to Tate modules, and rational invertibility of
  an isogeny (step 4).

The result is limited to the target. It claims no integral perfectness for a
nonprincipal polarization, no statement at the characteristic prime, no
nondegeneracy on arbitrary test schemes, and no adelic or full rational nondegeneracy.
