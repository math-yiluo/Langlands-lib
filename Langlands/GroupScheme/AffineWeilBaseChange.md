# Base change of actual affine Weil restriction

This derived construction is in the namespace
`Langlands.GroupScheme.AffineWeil.BaseChange`.
Let `A`, `B`, and `C` be commutative rings in an arbitrary common universe `u`,
with specified `A`-algebra structures on `B` and `C`. For the group-scheme
comparison, assume that `B` is a finite projective `A`-module and that `G`
is an affine group scheme locally of finite type over `Spec B`.
There is no reducedness, separability, field, or flatness assumption on `C`.
Write `D = C ⊗[A] B`, with its canonical `C`-algebra structure and its
`B`-algebra structure through the right tensor factor.

The definition `iso` is an isomorphism of actual group schemes over `Spec C`
between:

- `source A B C G`, the scheme-theoretic base change of
  `AffineWeil.groupScheme A B G` along `Spec C → Spec A`;
- `target A B C G`, the actual affine Weil restriction along `C → D` of
  `factor A B C G`, the scheme-theoretic base change of `G` along
  `Spec D → Spec B`.

Thus arbitrary base change commutes with this finite-projective affine
restriction. These are the existing pullback and corepresented group-scheme
constructions, with their original group laws.

For a `C`-algebra test object `R`, `tensorEquiv` is the `B`-algebra
isomorphism
`D ⊗[C] R ≃ₐ[B] B ⊗[A] R` given by
`(c ⊗ b) ⊗ r ↦ b ⊗ (c*r)`.
Its construction composes tensor commutativity, cancellation of the base
change, and tensor commutativity again. The proof of `commutes'` checks
explicitly that this retains the original right-factor `B`-action.
`tensorEquiv_naturality` proves compatibility with every `C`-algebra map of
test objects by tensor induction.

Both actual group schemes have naturally the point group
`G(B ⊗[A] R)`. On the source this is the existing
`baseChangeTensorPointsEquiv`. On the target, `targetPointsEquiv` first uses
the actual affine Weil point equivalence, then the inverse point equivalence
for the coefficient base change, and finally `tensorEquiv`.
`factorTensorPointsEquiv_left` identifies the latter map with the original
pullback projection preceded by the spectrum map of `tensorEquiv`.
The tensor naturality calculation proves
`factorTensorPointsEquiv_naturality` and `targetPointsEquiv_naturality`.
Consequently `pointEquiv` is a natural multiplicative equivalence on all
affine test algebras. `affinePointIso` packages it as a natural isomorphism
of group-valued affine point functors, and the existing affine comparison
theorem reconstructs `iso`. `iso_hom_points` records its exact point formula.

Now let `f : G ⟶ H`, where `H` is also affine and locally of finite type
over `Spec B`. `factorMap` is the actual coefficient base change of `f`;
`sourceMap` is the actual base change of the restricted map; and `targetMap`
is the restriction of `factorMap`. The point comparison commutes with these
maps. Its proof uses the pullback projection formula for inverse
base-change points and the existing affine Weil map formula. Applying
affine-point faithfulness yields `iso_naturality`:
`(iso G).hom ≫ targetMap f = sourceMap f ≫ (iso H).hom`.

The definition `kernelIso` gives an isomorphism

`kernel (sourceMap f) ≅
  AffineWeil.groupScheme C D (kernel (factorMap f))`.

Here both kernels are the existing scheme-theoretic pullback kernels.
First, `kernelSquareIso` applies to the commuting square just proved.
Then `AffineWeil.kernelIso` identifies the kernel of the restricted map
with restriction of the kernel. The kernel over `D` is affine and locally
of finite type because `G_D` is affine and locally of finite type and
`H_D` is separated. The local instances establish these facts before
forming its actual restriction.
`kernelIso_hom_inclusion` proves that this composite respects inclusion:
its homomorphism followed by the restriction of the coefficient-kernel
inclusion is the original kernel inclusion followed by `(iso G).hom`.
Thus the comparison identifies the actual subgroup and its map into the
source.

The provenance is the explicit tensor calculation and the existing actual
point, affine comparison, and kernel APIs. The construction supports the
restriction-of-scalars step of Kaletha–Prasad, *Bruhat–Tits theory: a new
approach* (2023), Proposition C.5.1, printed pp.703–704 / PDF pp.734–735,
and the special-fibre kernel calculation motivated by Lemma C.5.3, printed
p.705 / PDF p.736. It is a derived general comparison, rather than a literal
restatement of either result. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.

This file does not assert smoothness, connectedness or unipotence of these
kernels. Their computation over the base-changed coefficient algebra and
the identification of arbitrary supplied root-depth models remain inputs
to the eventual C.5.3 proof. No host KP Proposition 8.4.15 kernel theorem is
used.
