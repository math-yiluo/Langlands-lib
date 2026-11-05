# Finite-Galois fields of definition for affine characters

Authors: Worker 1366 and Worker 706. Worker 706 supplied the proposition and
its design; this module preserves that source.

`Langlands.GroupScheme.AffineCharacterFiniteGaloisDescentStatement.{u}` is a
proposition definition. This module states the proposition and supplies no
proof of it. Its provenance is a derived internal finite-coefficient descent
argument, explained below.

## Quantifiers and conclusion

The universe `u` is arbitrary. Both `k K : Type u` are fields, with the
specified extension structure `Algebra k K` and `IsGalois k K`. In Mathlib,
this means an algebraic, separable, normal extension; its degree need not be
finite. The group `G` is any actual
`GroupScheme (Spec (CommRingCat.of k))` with `IsAffine G.X.left`, so its
underlying scheme is affine. There is no finite-type, reductive, smooth,
connected or splitting hypothesis on `G`. Commutativity of `G` is also
unnecessary.

For every character
`ψ : rationalCharacters (GaloisPointComparison.baseChanged k K G)`,
the proposition requests an intermediate field
`E : FiniteGaloisIntermediateField k K` and a character
`ψE : rationalCharacters (GaloisPointComparison.baseChanged k E G)`.
The existing Mathlib structure makes `E` an intermediate field
`k ⊆ E ⊆ K`, finite-dimensional and Galois over `k`. Its inherited field
and algebra structures are the ones used in the displayed Lean statement.
The choices of `E` and `ψE` may depend on `k`, `K`, `G` and `ψ`, but precede
the universal quantifier over points.

For every `g : rationalPoints G`, the conclusion is the equality in `K`

```text
algebraMap E K (ψE(g extended from k to E))
  = ψ(g extended from k to K).
```

Both evaluations initially lie in field units. The explicit coercions
`: E` and `: K` in Lean take their underlying field elements, and
`algebraMap E K` includes the first element into `K`. The same field `E`
and character `ψE` work simultaneously for all base-field rational points.

## Actual characters, base change and point extension

The imported
[rational-character module](Characters.md) defines `rationalCharacters H`
as the additive form of the group-scheme homomorphisms
`H ⟶ (Gm _).toGrp`. Thus `ψ` and `ψE` are algebraic characters of the
actual base-changed groups. They are not supplied functions on rational
points. `rationalPoints G` is the existing group of sections of `G` over
`Spec k`, and `rationalCharacterEval` evaluates a character on such a
section using the existing multiplicative-group units equivalence and
`Γ(Spec k) ≅ k`.

For `L = E` or `K`, the imported
[rational-point comparison module](../GaloisPointRational.md) defines
`GaloisPointComparison.baseMap k L` as
`Spec.map (CommRingCat.ofHom (algebraMap k L))`. Its
`baseChanged k L G` is the actual `GroupScheme.baseChange` along this
scheme morphism. `GaloisPointComparison.rationalExtend k L G` sends
sections over `Spec k` to sections of this pullback over `Spec L`.
The existing theorem `rationalExtend_fst` identifies its composite with
the pullback projection as `baseMap k L ≫ g.left`.

The asserted equality is only on the images of base-field points under
these extension maps. It does not assert equality on all `K`-points or
all test schemes, or identify `ψ` with the scalar extension of `ψE` as a
group-scheme morphism. A full field-of-definition theorem would imply
this evaluation statement, but is a stronger assertion.

## Derived provenance and proof boundary

Write `A = O(G)`. Affineness identifies the coordinate algebra after
extension with `K ⊗[k] A`. A morphism from this affine scheme to `Gm`
is determined by the image of the Laurent coordinate and its inverse:
a coordinate-ring unit and its inverse. Each of these two elements is
a finite sum of tensors, even when `A` is not finitely generated.
Consequently only finitely many coefficients from `K` are needed to
write them.

The expected descent argument takes the finite Galois normal closure
inside `K` of the field generated over `k` by those coefficients.
Algebraicity and separability give finiteness, and normality of `K/k`
keeps this closure inside `K`. Over the resulting `E`, the same tensor
expressions define a unit: their inverse identities reflect through
the injective scalar extension from `E` to `K`. The character's
multiplication law likewise reflects through the injective coefficient
map on the tensor algebra for `G × G`; its identity law reflects over
the fields. This would construct a character over `E` whose scalar
extension is the original one, and hence give the requested equality
on extended `k`-points.

This is the internal mathematical rationale for the target, not an
implemented Lean proof. The existing
[coordinate-unit module](CharacterUnits.md) provides the character
unit, its injectivity and its group-like comultiplication law; it does
not by itself prove this descent statement. Results descending maps
from a diagonalizable group to a finite-type target do not supply the
present arbitrary-affine-source target. The separate proof successor
must establish the finite-coefficient descent and its compatibility
with the actual maps used here.
