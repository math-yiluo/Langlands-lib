# Finite-Galois descent of affine character evaluations

Authors: Worker 706 and Worker 1366. Worker 706 supplied the complete five-module
proof draft. Worker 1366 checked it against the public statement, added the
exact-target theorem wrapper and completed the companion explanations.
This is derived internal mathematics using existing Library and Mathlib
constructions; no external-source proof correspondence is claimed.

The theorem `Langlands.GroupScheme.affineCharacterFiniteGaloisDescent.{u}`
proves exactly the public
`Langlands.GroupScheme.AffineCharacterFiniteGaloisDescentStatement.{u}`.
Both fields lie in an arbitrary universe `u`. The extension `K/k` is
Galois and may have infinite degree. The group scheme `G/k` is arbitrary
affine, including noncommutative groups and groups whose coordinate
algebras are not finitely generated. There is no added finite-type,
smoothness, connectedness, reductivity or splitting hypothesis.

## Conclusion

For each actual character `ψ` of `GaloisPointComparison.baseChanged k K G`,
one finite Galois intermediate field `L` and one actual character of
`GaloisPointComparison.baseChanged k L G` work for every base-field
rational point `g`. Their values satisfy the exact equality in `K`

```text
algebraMap L K (rationalCharacterEval ψL (rationalExtend k L G g))
  = rationalCharacterEval ψ (rationalExtend k K G g),
```

where both unit values are coerced to their underlying field elements.
The field and character are chosen before `g`. The conclusion is agreement
on extensions of base-field rational points; it does not assert a full
base-change equality of group-scheme morphisms.

## Implemented proof

The [tensor tools](AffineCharacterFiniteGaloisTools.md) first descend an
arbitrary tensor to a finite Galois coefficient field by tensor induction.
Applying this to the universal character unit and its inverse, and taking
the supremum of their two fields, gives a unit over a common finite Galois
field. Injectivity of the tensor coefficient embedding reflects the
inverse equation. This step uses no finite generation of `Coord G`.

The [universal values](AffineCharacterFiniteGaloisValues.md) evaluate the
actual ambient character at the universal point over `K ⊗[k] Coord G`.
Naturality shows that every character value is the image of this unit
under the tensor evaluation map attached to the point.

The [reconstruction module](AffineCharacterFiniteGaloisReconstruction.md)
evaluates the descended unit on every test algebra over the finite field.
After extending such an algebra `B` to `K ⊗[L] B`, these values agree with
the original character. Injectivity of `B → K ⊗[L] B` therefore reflects
the identity and multiplication laws. The values are natural in the test
algebra. The [natural-value construction](AffineCharacterNaturalValues.md)
uses the existing corepresented Yoneda map and its actual group-scheme
isomorphisms to reconstruct a character over `L`. Its value theorem
recovers the descended model on every affine test algebra.

In this entry module, `tensorEval_field_compare` proves that direct tensor
evaluation commutes with `L → K`, by tensor extensionality and naturality
of point coordinates. `modelValue_field_compare` applies that equality to
the descended unit and uses its image equality to identify the result
with the ambient character value.

`finiteCharacter_rationalEval` now uses the existing
`valueE_baseChangeCoeffEquiv` comparisons for actual rational character
evaluation. The reconstructed character's value formula rewrites the
finite-field side to `modelValue`; `modelValue_field_compare` compares
it in `K`. The two resulting ambient points coincide by
`baseChangeCoeffEquiv_rationalExtend` and the composition law for actual
affine point maps.

`exists_finiteGalois_character` applies `exists_tensorEmbed_unit` to the
universal tensor value, constructs `finiteCharacter` and uses this
all-point comparison. The final exact-target theorem introduces precisely
the public statement's fields, instances, affine group and character,
then applies that quantified theorem. The public statement and all of
its imported Lean and Markdown files are used unchanged.
