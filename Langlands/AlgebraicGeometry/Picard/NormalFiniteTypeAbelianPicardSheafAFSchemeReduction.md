# The normal-base Picard statement from ampleness and the projective case

Authors: Worker 3570.

## Result

`Langlands.AlgebraicGeometry.Picard.normalFiniteTypeAbelianPicardSheafAFScheme_of_ample`
is a theorem with the universe parameter `u`:

```lean
theorem normalFiniteTypeAbelianPicardSheafAFScheme_of_ample
    (ample : NormalFiniteTypeAbelianAmpleExistenceStatement.{u})
    (projective : AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}) :
    NormalFiniteTypeAbelianPicardSheafAFSchemeStatement.{u}
```

All three propositions are in the namespace
`Langlands.AlgebraicGeometry.Picard` and quantify over the same rings: every
integrally closed domain `R : Type u` of finite type over `ℤ`, and every Library
abelian scheme `A` over `Spec R`.

- `NormalFiniteTypeAbelianAmpleExistenceStatement` says that `A.X.left` has an
  ample line bundle.
- `AmpleNormalFiniteTypeAbelianPicardSheafAFSchemeStatement` says that, if
  `A.X.left` has an ample line bundle, then the Picard class sheaf
  `RelativePicard.classSheafPresheaf A.X.hom` is represented by some
  `P : Over (Spec R)` such that every finite set of points of `P.left` lies in
  one affine open.
- `NormalFiniteTypeAbelianPicardSheafAFSchemeStatement` is the same conclusion
  without the ampleness premise.

The theorem is conditional: it proves the third proposition from the first two
and proves neither of them.

## Proof

For given `R` with its instances and `A`, the proof applies `projective R A` to
the ample line bundle supplied by `ample R A`. The term is
`fun R _ _ _ _ A => projective R A (ample R A)`; no other argument is needed.

## Provenance and use

This is an internal assembly lemma. It records the split of the normal-base
step in Deligne's proof of Faltings–Chai, *Degeneration of Abelian Varieties*,
Chapter I, Theorem 1.9 (printed pp.6–7), into global projectivity of `A` and
the Picard scheme of a projective abelian scheme, as described in the Markdown
of the two premise statements. It lets the proof of
`FiniteTypeAbelianPicardSheafSchemeStatement` planned in task
`de799868-75c2-4835-b620-f024e5969aa8` obtain its normal-base input from
proofs of the two premises.
