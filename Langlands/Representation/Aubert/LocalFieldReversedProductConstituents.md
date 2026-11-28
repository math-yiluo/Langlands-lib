# Constituent matching for reversed all-field normalized induction

`Langlands.Aubert.LocalFieldGraded.sameFactors_reverseProduct` concerns a
nonarchimedean local field in the sense of `AllFieldBZ.LocalFieldPackage`,
of characteristic zero or positive characteristic, with its topological data.
Let `D` be an ordered block shape of positive total rank `n`, and let `A` be
a family of irreducible smooth factors indexed by its blocks. The theorem
states that the actual normalized product of `A` along `D` and the normalized
product along the reversed shape `D.reverse`, with the factors in reverse
order, have the same Jordan–Hölder factors with multiplicities
(`HaveSameJordanHolderFactors`).

Zelevinsky 1980, Theorem 1.9, printed p. 174, proves a binary identity: if
`π₁` and `π₂` are representations of `GL_k` and `GL_l` of finite length, then
`π₁ × π₂` and `π₂ × π₁` have the same composition factors. The theorem here
is an ordered-block analogue of that identity. It reverses any number of
blocks, but its factors must be irreducible. Zelevinsky's proof uses the
automorphism `s(g) = s_n (ᵗg)⁻¹ s_n⁻¹` of `GL_n`. Its Lemma (a) gives
`s(π₁ × π₂) ≅ s(π₂) × s(π₁)`. Its Lemma (b) states that, for `π` of finite
length, the twist `s(π)` and the smooth contragredient `π̃` have the same
composition factors. For irreducible `π` this is the theorem of Gelfand and
Kazhdan. The concluding calculation goes from `π₁ × π₂` to the contragredient
of `s(π₁ × π₂)` by Lemma (b) and reverses the factors by Lemma (a). It then
moves the contragredient onto the factors by §1.1(d), printed p. 170, and
reaches `π₂ × π₁` by Lemma (b) again.

The Lean proof combines the same ingredients in a different orientation.
Write `θ` for the inverse-transpose automorphism `g ↦ (ᵗg)⁻¹` of `GL_n`
(`GeneralLinear.inverseTranspose`, with no conjugation by a Weyl element),
`X` for the original product and `Y` for the reversed product. The pullback
of `X` along `θ` is equivalent to the smooth dual of `Y`. The smooth dual of
`Y` has the same composition factors as the pullback of `Y` along `θ`. The
common pullback along `θ` is then removed. In detail:

1. `Langlands.AllFieldBZ.Parabolic.productDualReversal` identifies the
   pullback of `X` along `θ` with the smooth contragredient of `Y`. That
   equivalence uses upper-to-opposite transport, order reversal,
   Gelfand–Kazhdan on the inducing blocks and the identification of the
   smooth dual of a normalized product with the product of the duals
   (`Langlands.AllFieldBZ.Classification.CuspidalProductContragredient.nonempty_contragredient_productEquiv`).
2. `Langlands.AllFieldBZ.Classification.irreducibleProductFiniteLength`
   gives `Y` finite length, so it has a composition series with irreducible
   graded pieces.
3. The private lemma `sameFactors_dual_inverseTranspose` takes the
   annihilator filtration `dualSeries` on the smooth dual. By `dualSeries_graded`, its graded
   pieces are the smooth duals of the composition factors of `Y`, in reverse
   order. Each composition factor is irreducible and, by the cuspidal
   embedding `Langlands.AllFieldBZ.CuspidalSupport.cuspidalEmbedding`,
   admissible. `Langlands.AllFieldBZ.Parabolic.nonempty_inverseTranspose_contragredient`
   (the Gelfand–Kazhdan theorem) identifies its dual with its pullback along
   `θ`. So the smooth dual of `Y` and the pullback of `Y` along `θ` have the
   same Jordan–Hölder factors, matched by reversing the indices.
4. Transporting along the equivalence of step 1 shows that the pullbacks of
   `X` and `Y` along `θ` have the same factors.
   `Langlands.Classification.TwoFactorCommutativity.haveSameJordanHolderFactors_of_comp`
   removes the pullback along the group automorphism `θ`.

- `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`,
  §1.9 (theorem, Lemma (a)–(b) and concluding calculation), printed p. 174;
  §1.1(d), printed p. 170.
