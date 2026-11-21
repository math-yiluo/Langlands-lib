# The free operator action on the adelic tensor

The complexified archimedean Lie algebra acts by adding the actions of its
actual place projections on the corresponding tensor slots. The proof checks
that different slots commute, so the bracket of the two sums is the sum of
the brackets at each slot. Each place inclusion acts in its own slot.

`tensorCompactAction` transports the given compact element to the product
of its real and complex compact coordinates and tensors the corresponding
endomorphisms. Finite adelic translations act on the grouped finite factor.
`tensorFreeAction` extends these translations and the universal enveloping
action of `tensorLieAction` along the free algebra. The theorem
`tensorFreeAction_hasActions` verifies the finite, compact and complexified
Lie generator formulas in `HasActions`.

The construction uses the actual finite and archimedean components in the
tensor of Langlands (1979), Lemma 1, printed p. 203 (Corvallis I PDF p. 198),
and in Getz–Hahn (2024), Theorem 10.7.5, printed p. 288 (PDF p. 300).
