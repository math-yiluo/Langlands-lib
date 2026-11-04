# Actual affine scheme scalar extension in global sections

This internal comparison supports the pure-dimensional fibre condition in
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed pp. 5–6, Theorem 3.4(2). The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The construction is derived from the affine scheme/global-section
equivalence and the universal property of actual scheme pullbacks.

For any morphism f from an affine scheme X to Spec R,
`affineStructureMap` is the actual ring map R → Γ(X, ⊤), obtained by
composing the inverse of the canonical global-section isomorphism for
Spec R with f's map on global sections. The algebra structure used in
every tensor product is induced by this map. The lemma
`isoSpec_hom_affineStructureMap` proves compatibility of X's canonical
isomorphism with the original f.
`affineStructureMap_finiteType` proves that this map is of finite
type when f is locally of finite type; affineness makes the
global-section finite-generation conclusion valid.

For any commutative R-algebra B, `affinePullbackTensorIso` constructs
an isomorphism from the actual pullback X ×[Spec R] Spec B to
Spec(Γ(X, ⊤) tensor_R B). It uses the isomorphism of pullbacks induced
by X ≅ Spec Γ(X, ⊤), followed by Mathlib's `pullbackSpecIso`.
Both projection identities are proved.

`hasPureDimension_affinePullback_iff` then identifies pure dimension
of the actual pullback with pure ring dimension of the actual tensor
algebra. It uses invariance under scheme isomorphism and the published
componentwise spectrum comparison. The condition concerns every
irreducible component, equivalently every minimal-prime quotient.

These constructions permit arbitrary commutative R and B, zero rings,
nilpotents and zero divisors, with no finite-type, flatness or field
hypothesis. All schemes and rings are in a common universe because the
actual Scheme category and pullback have that universe. This unit does
not assert invariance of pure dimension under scalar extension;
the finite-type field theorem, nonaffine locality, constructibility
and filtered fibre descent remain separate obligations.
