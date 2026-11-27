# Inverse transpose and the dual of reversed normalized induction

`Langlands.AllFieldBZ.Parabolic.productDualReversal` proves
`Langlands.AllFieldBZ.Parabolic.ProductDualReversalStatement` for every
nonarchimedean local field, with independent field and representation universes.
Write \(I_B(A)\) for normalized induction of the ordered family \(A\) from
the standard upper block parabolic and set \(\theta(g)=(g^{-1})^{\mathsf T}\)
in each rank. The proof composes three intertwiners of smooth representations.

1. `inverseTransposeProductReversalEquiv` transports the pullback \(\theta^* I_B(A)\)
   through the opposite parabolic to \(I_{B^{\mathrm{rev}}}(\theta^* A^{\mathrm{rev}})\).
2. The admissibility clause of `cuspidalEmbedding` supplies admissibility for
   each irreducible smooth factor. The helper
   `nonempty_inverseTranspose_contragredient` writes the positive block rank as
   \(m+1\) and packages the linear equivalence and intertwining identity from
   `Langlands.LocalField.gelfandKazhdanContragredient` as a `Representation.Equiv`.
   Applying `normalizedProductInducedEquiv` to these equivalences gives an intertwiner to
   \(I_{B^{\mathrm{rev}}}((A^{\mathrm{rev}})^\vee)\).
3. The inverse of `nonempty_contragredient_productEquiv`, applied to the reversed
   admissible family, identifies this product of smooth duals with
   \(I_{B^{\mathrm{rev}}}(A^{\mathrm{rev}})^\vee\).

At rank zero the block family is empty, so the blockwise constructions have
empty domain and the same composition applies.

The block equivalence uses the inverse-transpose form of the Gelfand–Kazhdan
theorem in Bernstein and Zelevinsky (1976), §§7.1–7.3, printed pp. 57–58
(`bernstein-zelevinsky-1976-representations-gln`, SHA-256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`).
Conjugation by the signed antidiagonal matrix in the source is inner, and the
action of that matrix intertwines the two forms. Zelevinsky (1980), §1.1(d)
and the lemma in §1.9, printed pp. 170 and 174, use the induction duality and
the block reversal in this argument (`zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`).
