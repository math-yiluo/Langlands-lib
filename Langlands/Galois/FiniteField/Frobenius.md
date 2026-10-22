# Frobenius for a finite field

This file defines arithmetic and geometric Frobenius for an arbitrary finite
field `k : Type u`. It uses Mathlib's actual algebraic closure and
`Field.absoluteGaloisGroup k`, including the Krull topology already defined on
that group. It does not postulate a procyclic group or an equivalence with
profinite integers.

`closureAction` unfolds the absolute Galois group to its automorphism action on
the specified algebraic closure. It is the identity continuous group equivalence,
not a transport to a different closure.

Write `q = Nat.card k`. The definition `arithmetic k K`, for an algebraic field
extension `K/k` in an independent universe, is Mathlib's
`FiniteField.frobeniusAlgEquivOfAlgebraic`. Its underlying function is
`x ↦ x ^ q`. The implementation chooses a `Fintype` from `Finite k`;
`Fintype.card_eq_nat_card` identifies its cardinality with `q`. The definition
`geometric k K` is the inverse automorphism. `arithmeticFrobenius` and
`geometricFrobenius` specialize these constructions to the algebraic closure.

For every finite-dimensional intermediate field `L` of that closure,
`finiteRestriction L` is the continuous restriction homomorphism from the actual
absolute Galois group to `Gal(L/k)`. Its construction uses the fact that a finite
extension of a finite field is a finite field and hence Galois.
Mathlib's `InfiniteGalois.restrictNormalHom_continuous` proves continuity for the
Krull topologies. No choice of Frobenius lift or additional topology is imposed.

The intended comparison maps geometric Frobenius to the canonical image of
`+1` in `Langlands.Weil.ProfiniteIntegers`. Therefore arithmetic Frobenius maps
to the image of `-1`. This reverses the arithmetic generator used in Serre's
finite-field example; it is an explicit normalization, not a change to the
cardinality-power formula. This definition file alone does not prove the
comparison or the generation and order laws.

## Sources and existing support

* Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
  Graduate Texts in Mathematics 67, Springer, 1979, Chapter XIII, section 2,
  printed pages 190–191, especially the definition of a quasi-finite field and
  Example (a) on page 191. Serre uses arithmetic Frobenius `x ↦ x^q`.
  Retained source: `serre-1979-local-fields`, SHA256
  `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
* Guy Henniart, “Une preuve simple des conjectures de Langlands pour GL(n) sur
  un corps p-adique”, *Inventiones mathematicae* 139 (2000), 439–455, section
  1.1, page 439, for the geometric Frobenius reciprocity convention motivating
  the sign chosen here. Retained source: `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

At Mathlib revision `5ed2965256430c3649e86755f9576b54eca72435`,
`FieldTheory/Finite/Basic.lean` already constructs Frobenius on algebraic
extensions and proves its order and generation for finite extensions.
`FieldTheory/Finite/GaloisField.lean` supplies the finite-field Galois instance.
`FieldTheory/Finite/Extension.lean` constructs extensions of every positive
degree. `FieldTheory/Galois/Profinite.lean` identifies a Galois group with its
finite Galois restriction limit and supplies the continuity used here.
Those results do not themselves identify the actual absolute Galois group with
the specific profinite-integer object used by the Weil construction.

The algebraic-extension definition has independent universes `u` and `v`.
The absolute Galois specialization keeps `k : Type u` arbitrary. No resizing,
replacement closure, or unproved closure transport occurs in this file.
