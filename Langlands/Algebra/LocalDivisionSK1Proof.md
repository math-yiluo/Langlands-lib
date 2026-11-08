# Local SK1: the reduced-norm kernel is the commutator subgroup

`Langlands.CentralDivision.localSK1 : LocalSK1Statement.{u}` proves the Library
proposition `Langlands.CentralDivision.LocalSK1Statement` from
`Langlands.Algebra.LocalDivisionSK1Statement`, unchanged, at an arbitrary
universe `u` and with no restriction on the characteristic. For every
nonarchimedean local field `F : Type u` (`Field F`, `ValuativeRel F`,
`TopologicalSpace F`, `IsNonarchimedeanLocalField F`) and every
finite-dimensional central division `F`-algebra `D : Type u`, the kernel of the
canonical reduced norm on the original units,

```text
((Langlands.CentralSimple.reducedNormUnits F D F).comp
  (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)).ker,
```

equals `commutator Dˣ`. No hypothesis is added: the subfield, the residue
degree and the movement of units are all constructed or proved inside the
proof.

## Implemented proof

The proof combines four results; the kernel above is by definition the
kernel of `Langlands.BinaryElementary.Reduced.coefficientNorm F D`.

1. **A cyclic full-residue subfield.** `exists_localDivision_fullResidue_cyclic_subfield F D`
   (module `Langlands.Algebra.LocalDivisionSubfieldCyclic`) gives an integral
   element `b` of `D` whose generated subalgebra
   `E = residueGeneratorSubalgebra F D b` (a field) has surjective residue map
   `localDivisionSubfieldResidueMap F D E.val`, satisfies
   `Module.finrank F E = finrank` of the residue algebra of `D` over the
   residue field of `F`, and is Galois over `F` with cyclic automorphism group.
2. **Residue degree equals reduced degree.** `localResidueDegree :
   LocalResidueDegreeStatement.{u}` (module
   `Langlands.Algebra.LocalDivisionResidueDegreeProof`) says that this residue
   degree equals `reducedDegree F D`. Composing with step 1 gives
   `Module.finrank F E = reducedDegree F D`.
3. **Movement of valuation-one units.** `localDivision_move_unit F D E.val hsurj
   (localResidueDegree F D) a ha` (module
   `Langlands.Algebra.LocalDivisionUnitMovement`, Tits' Lemma 3.2 in this
   setting) shows that every unit `a : Dˣ` with
   `localReducedNormValuation F D a = 1` admits `c ∈ commutator Dˣ` with
   `c * a` in the image of `Eˣ`. It uses the surjective residue map of step 1
   and the residue-degree equality of step 2.
4. **The kernel reduction.** `ker_coefficientNorm_eq_commutator_of_unit_movement`
   (module `Langlands.Algebra.LocalDivisionSK1Reduction`) concludes
   `(coefficientNorm F D).ker = commutator Dˣ` from the embedding `E.val`, the
   degree equality of step 2 and the movement of step 3. A unit of reduced norm
   one has valuation one; a commutator moves it into `E`, where the product
   still has reduced norm one; since `E` is cyclic of degree `reducedDegree F D`,
   reduced-norm-one elements of `E` are commutators (Library
   `range_inf_ker_coefficientNorm_eq_range_inf_commutator`, via cyclic
   Hilbert 90); and commutators lie in the kernel because `Fˣ` is commutative.

The Lean proof introduces `F` and `D`, obtains `b` from step 1, records the
field structure `residueGeneratorField F D b` on `E`, forms the degree equality
from steps 1 and 2, and applies step 4 with the movement function of step 3.

## Source

This follows the route of Jacques Tits, *Groupes de Whitehead de groupes
algébriques simples sur un corps*, Séminaire Bourbaki, exposé 505 (1977):
Section 3.1 (unramified maximal subfield with residue field the full residue
algebra, cyclic over the base), Lemma 3.2 (moving an element by a commutator
into such a subfield) and Proposition 3.3 (an element of reduced norm one is
then a commutator), printed pages 227–228. Tits states triviality of `SK1`
over local fields with finite residue field in Section 1.2, printed page 221.
The equality of the kernel with the commutator subgroup is the quotient-free
form of `SK1(D) = 1`.
