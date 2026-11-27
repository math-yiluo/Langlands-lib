# Smooth proper pointed lifts of abelian schemes across elementary Artinian extensions

`Langlands.AbelianScheme.AbelianSmoothArtinianLiftingStatement.{u}` is a proposition
definition. This file states it and does not prove it.

## The statement

Let \(\varphi\colon R'\to R\) be a surjection of commutative local Artinian rings in the
universe `u`, with \(R'\) a \(\mathbf Q\)-algebra (`[Algebra ℚ R']`), and assume that the
maximal ideal of \(R'\) annihilates \(I=\ker\varphi\)
(`IsLocalRing.maximalIdeal R' * RingHom.ker φ = ⊥`). Put
`t := Spec.map (CommRingCat.ofHom φ) : Spec R ⟶ Spec R'`.

For every abelian scheme `B : AbelianScheme (Spec R)` the proposition asserts that there
are

- a scheme `X` with a morphism `p : X ⟶ Spec R'` that is smooth and proper;
- a section `s : Spec R' ⟶ X` of `p` (`s ≫ p = 𝟙 _`);
- an isomorphism of schemes `e₀ : B.X.left ≅ pullback p t` over `Spec R`, that is,
  `e₀.hom ≫ pullback.snd p t = B.X.hom`,

such that `e₀` carries the identity section of `B` to the section induced by `s`: the
identity section `η[B.X].left`, followed by `e₀.hom` and the projection
`pullback.fst p t` to `X`, equals `t ≫ s`.

Only the underlying pointed scheme of `B` is lifted. No group law on `X` is asserted.
The conclusion has exactly the form of the hypothesis of
`Langlands.AbelianScheme.PointedAbelianArtinianLiftingStatement`, with `B` in the role
of the abelian scheme over the thinner ring. The module
`Langlands.AbelianScheme.AbelianArtinianLiftingReduction` proves that the two
propositions together imply
`Langlands.AbelianScheme.AbelianArtinianLiftingStatement`.

## Source comparison

The source is Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura
varieties*, Harvard thesis revised 14 March 2021, registered as
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`. Printed page numbers
are the PDF page numbers minus 28.

- Definition 2.1.2.1 (printed p. 114) defines, for a square-zero closed immersion
  \(S\hookrightarrow\tilde S\) and a smooth \(S\)-scheme \(X\), the set
  \(\mathrm{Lift}(X;S\hookrightarrow\tilde S)\) of isomorphism classes of pairs
  \((\tilde X,\phi)\) with \(\tilde X\to\tilde S\) smooth and
  \(\phi\colon\tilde X\times_{\tilde S}S\simeq X\) over \(S\). Here
  \(S=\operatorname{Spec}R\), \(\tilde S=\operatorname{Spec}R'\) and \(X=B\). The ideal
  \(I\) has square zero because it lies in the maximal ideal of \(R'\), which
  annihilates it. The proposition asserts that this set is nonempty: a nonempty set of
  isomorphism classes supplies a representative pair \((\tilde X,\phi)\), and the
  isomorphism `e₀` is the inverse of its \(\phi\).
- Definition 2.2.1.1 (printed p. 142) calls such a surjection small. Lan's
  Proposition 2.2.4.1 (proof on printed pp. 152–154) shows that the obstruction
  \(o(A;\tilde R\twoheadrightarrow R)\in H^2(A_0,\mathrm{Der}_{A_0/S_0})\otimes_k I\)
  to \(\mathrm{Lift}(A;\tilde R\twoheadrightarrow R)\) vanishes for an abelian scheme
  \(A\) over \(R\), where \(A_0\) is its special fibre; by Proposition 2.1.2.2
  (printed p. 114) the set of lifts is then nonempty. Proposition 2.2.2.3 (printed
  p. 144) uses such a lift, together with the identity section, to lift \(A\) as an
  abelian scheme.
- A lift is proper over \(\tilde S\): its reduction \(B\) is proper and the closed
  immersion of the reduction into the lift is a homeomorphism. A section `s` exists by
  smoothness, lifting the identity section of \(B\) across the square-zero thickening;
  this is the "automatic existence of identity sections by smoothness" invoked in the
  proof of Proposition 2.2.2.3 (printed p. 145). The proposition asks for properness and
  for this section explicitly, because the pointed lifting statement uses them.

Lan works over a complete local base with a fixed residue field of the finite-type
convention of his §2.2.1 (printed p. 140). The proposition here ranges over all local
Artinian \(\mathbf Q\)-algebras \(R'\), with arbitrary residue fields of characteristic
zero.
