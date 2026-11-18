# Quasi-affine morphisms of schemes

Worker 912, Task 7281. This module defines the predicate
`Langlands.AlgebraicGeometry.IsQuasiAffineOver`. Here `f : X ⟶ S` is a
morphism of schemes in an arbitrary universe `u`. The predicate is the
Prop-valued condition

    ∀ V : S.affineOpens, (f ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine

So for every affine open `V` of `S`, the open subscheme `f⁻¹(V)` of `X` is
a quasi-affine scheme. No hypothesis is imposed on `X`, `S` or `f`.

## Source

This is the Stacks Project, Morphisms of Schemes, Definition 29.13.1
(Tag 01SK): "A morphism of schemes f : X → S is called quasi-affine if the
inverse image of every affine open of S is a quasi-affine scheme." We read
it in the registered snapshot `stacks-quasi-affine-01P6-01SK-01SM`
(file `tag-01SK.html`, folder SHA-256
`09cd1ef04e7401bbe97bcbd9f08be73182e811f7204017f6fd6320b978986eeb`).

Quasi-affine schemes are Mathlib's `AlgebraicGeometry.Scheme.IsQuasiAffine`,
with its own quasi-compactness convention. Mathlib defines it as a
quasi-compact scheme (`CompactSpace X`) whose canonical morphism
`X.toSpecΓ : X ⟶ Spec Γ(X, ⊤)` is an immersion. Mathlib tags this class with
Stacks, Properties of Schemes, Definition 28.19.1 (Tag 01P6), which is in
the same snapshot (`tag-01P6.html`). Tag 01P6 asks for a quasi-compact
scheme isomorphic to an open subscheme of an affine scheme. The two
conventions agree. Mathlib's docstring notes that the immersion
`X ⟶ Spec Γ(X, ⊤)` is then an open immersion, so `X` is isomorphic to an
open subscheme of an affine scheme. Conversely, the canonical morphism of a
quasi-affine scheme to the spectrum of its global sections is a
quasi-compact open immersion. The proof of Morphisms, Lemma 29.13.3
(Tag 01SM, `tag-01SM.html`) uses this, citing Properties, Lemma 28.19.4.
Following the task, the Lean predicate uses Mathlib's class directly and
does not reprove this comparison.

The name matches the local `let IsQuasiAffineOver` binding in the published
statement `Langlands.GroupScheme.RelativeMultiplicativeTypeQuotientStatement`.
That binding is defined on objects `Y : Over S`. Its body is the same
condition for the structure morphism `Y.hom`. The descent statements about this
predicate are in
[RelativeQuasiAffineDescentStatement](RelativeQuasiAffineDescentStatement.md).
