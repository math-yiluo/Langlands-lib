# Finite étale affine-space classification and the Picard reduction

This module states the classification input for the characteristic-zero affine-space
case of Task 7538 and proves its implication to the published Picard target.
The classification is a `Prop`-valued definition; this module does not prove it.

## Classification statement

`Langlands.Algebra.AffineSpaceFiniteEtaleClassificationStatement.{u}` says that,
for every field `k : Type u` of characteristic zero, every natural number `n`,
and every module-finite étale algebra `A : Type u` over `MvPolynomial (Fin n) k`,
there exist a natural number `m` and fields `K i : Type u`, indexed by `Fin m`,
with `k`-algebra structures and `Module.Finite k (K i)`, together with a
nonempty type of algebra equivalences

```text
A ≃ₐ[MvPolynomial (Fin n) k] (∀ i : Fin m, MvPolynomial (Fin n) (K i)).
```

The polynomial-ring algebra structures on the factors are the canonical ones
induced by `algebraMap k (K i)`, using `MvPolynomial.algebraMvPolynomial`;
the product has the pointwise algebra structure. Thus the equivalence preserves
the original affine-space coordinates, as well as the ring operations.
In characteristic zero the finite field extensions are automatically separable.

No connectedness, domain, nonzero-ring or faithfulness hypothesis is imposed on
`A`. The empty product (`m = 0`) includes the zero ring, and `n = 0` is allowed.
All fields and algebras are in the same arbitrary universe `u`.

## Provenance and remaining obligation

This is an internal prerequisite statement, isolated from the standard proof
route recorded in the published
`Langlands/Algebra/AffineSpaceFiniteEtalePicardStatement.md` and the Task 7538
contract. It is stronger than the final Picard conclusion. It is not attributed
as a separately stated theorem to Conrad's Remark 7.2.13.

A proof of this prerequisite must supply the actual algebra equivalence:
geometric simple connectivity of affine space over an algebraically closed field
of characteristic zero, descent to finite extension fields over `k`, and the
finite decomposition into components are still mathematical obligations.
None of those results is assumed as an axiom or asserted to have been proved
by this module. The finite field extension condition is part of the
classification, although the Picard reduction only uses that each `K i` is a field.

## Implemented proofs

`subsingleton_pic_pi_of_finite` proves that a finite product of commutative
rings with trivial Picard groups has trivial Picard group. It equips each
factor with the algebra structure given by projection from the product.
The resulting structure map from the product to the product of the factors
is the identity and hence bijective. The published
`subsingleton_pic_of_bijective_algebraMap_pi` then gives the conclusion.
This proof also applies to the empty product.

`subsingleton_pic_pi_mvPolynomial` applies this result to polynomial rings
over fields. Mathlib supplies unique factorization for these rings and hence
the instance giving trivial Picard group for a domain with gcds.

`affineSpaceFiniteEtalePicardTrivialStatement_of_classification` is a conditional
proof of the unchanged published
`Langlands.Algebra.AffineSpaceFiniteEtalePicardTrivialStatement.{u}`.
It applies the classification premise to each finite étale algebra `A`,
uses the preceding theorem on the resulting product, and transfers Picard
triviality along the underlying ring equivalence with the published
`subsingleton_pic_of_ringEquiv`. This theorem does not discharge the
classification premise, so the unconditional Picard target remains open.
