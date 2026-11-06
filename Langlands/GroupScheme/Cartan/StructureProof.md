# Smooth connected nilpotent structure of Cartan subgroups

Author: Worker 1588.

`Langlands.GroupScheme.cartanStructure` proves the unchanged
`Langlands.GroupScheme.CartanStructureStatement.{u}`. For every field
`k : Type u`, every smooth connected affine group scheme `G` over `k`,
and every actual Cartan embedding `i : C → G`, its conclusion is

```text
Smooth C.X.hom ∧ ConnectedSpace C.X.left ∧ IsNilpotentGroupScheme C.
```

Here `IsCartanSubgroup i` specifies a closed representative of the
all-test centralizer of an actual maximal torus. It does not assume
smoothness, connectedness, or nilpotence of `C`.
`IsNilpotentGroupScheme C` means that the abstract group of points of
`C` over the specified algebraic closure of `k` is nilpotent.
There is no additional outer premise. The theorem retains arbitrary
universe, characteristic, finite and imperfect fields, and nonsplit
witnessing tori.

## Implemented proof

The proof composes three published results.

1. `maximalTorusConjugacy`, from
   `Absolute.MaximalTorusConjugacyProof`, proves the exact
   `MaximalTorusConjugacyStatement.{u}`. It applies the Borel reduction
   with the unconditional Borel and arbitrary-field solvable
   maximal-torus conjugacy proofs.
2. `finiteFieldGeometricMaximalTorus_of_maximalTorusConjugacy`, from
   `Torus.FiniteFieldGeometricAssembly`, takes that theorem as its explicit
   argument. It yields `FiniteFieldGeometricMaximalTorusStatement.{u}`.
   Over a finite field, independent existence supplies a geometric
   maximal torus. Field-isomorphism transport, conjugacy and Lang's
   theorem produce a conjugate with Frobenius-invariant all-test range.
   Splitting and Frobenius descent recover an actual original-field
   inclusion, maximal both there and after algebraic-closure extension.
3. `cartanStructure_of_finiteFieldGeometricMaximalTorus`, from
   `Cartan.StructureReduction`, takes this finite-field conclusion and
   returns exactly the target statement.

The last reduction supplies all six inputs to
`noTorusStructuralReduction`: the finite-field result just obtained,
`nilpotentCentralTorusStatement`,
`algClosedTrivialMaximalTorusUnipotent`,
`Lie.semisimpleCentralizerSmooth`,
`Lie.semisimpleCentralizerSpanning` and
`semisimpleIsogenyReduction`. Its finite-field branch uses geometric
maximal-torus existence and the algebraically closed criterion. Its
infinite-field branch uses induction on Lie dimension, an isogeny
reduction and semisimple-element centralizers. Thus the exact
no-torus unipotence proposition is derived with every structural premise
supplied.

The resulting `cartanStructure_of_noTorusUnipotent` uses the actual
central maximal-torus quotient of `C`. This quotient is smooth connected
affine and receives only trivial torus homomorphisms, so the derived
no-torus theorem makes it unipotent. Its central kernel gives a uniform
nilpotence bound on the points of `C` over every relative scheme test;
the geometric-point adapter gives `IsNilpotentGroupScheme C`.
`IsCartanSubgroup.smooth_connected` supplies the first two conjuncts.

The finite-field construction and the supplied conjugacy proof do not
use the no-torus unipotence result, general forward preservation of
maximal tori under field extension, or Cartan generation. In particular,
the argument does not assume that the initially given rational maximal
torus stays maximal after extension. The final module adds only this
proof and leaves the target statement and its imports unchanged.

## Source and provenance

The target is the structural assertion of J. S. Milne, *Algebraic Groups*
(2017), Proposition 17.44, printed pp.364–365 / one-based PDF pp.380–381,
with the Cartan convention of Definition 17.43. The registered original
source is `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The complete registered 2017 errata snapshot dated 2026-11-02 contains
no correction to this proposition.

Milne's proof invokes smoothness of torus centralizers (13.10),
connectedness (17.38), and nilpotence (17.28), using the central
maximal-torus criterion (17.23). The implemented proof instead composes
the Library results described above. Its provenance is this internal
composition; no new external structural assertion is introduced.
The conjugacy and dense-open union conclusions also appearing in
Proposition 17.44 are outside `CartanStructureStatement`.
