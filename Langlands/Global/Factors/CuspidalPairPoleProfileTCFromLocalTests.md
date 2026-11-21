# Completed pole profiles from ordinary local tests over totally complex fields

`CuspidalPairPoleProfileTCFromLocalTestsStatement` gives a certified completed
Euler product and its simple pole profile for each pair of split-centre-trivial
cuspidal realizations over a totally complex number field. The inputs include
their actual spectral presentations with irreducible admissible finite
components, a certified finite pair factor choice and the complex-place
parameters. Both the field and the presentation carrier retain their own
universe. The local analytic premises are equal-rank ordinary complex normalized
continuation, complex normalized generation and the specified actual Whittaker
slice ranges. The additive character is unitary and nontrivial, and it is
trivial on the diagonal field. The completion is holomorphic off zero and one.
At each of those points it has a simple pole exactly for equal-rank
contragredient pairs.

In equal rank the proof uses pointwise generation to form a covering family of
actual partial integrals. It obtains a conjugate residue test by ordinary
continuation, taking a common finite set which also contains the exceptional
places and the finite support of the adelic character. Since the continuation
only needs the covering and residue witnesses, any covering test selected at
zero supplies the family member. The equal-rank gluing theorem gives the
completed product and the criterion for poles at zero and one.

In unequal rank the proof chooses complex local tests for opposite additive
characters, realizes their products on the cuspidal tensors, and uses the
canonical finite additive characters and self-dual measures to complete the
normalized partial tests. The unequal gluing theorem gives the certified
product with no poles. For the opposite rank order, symmetry of the archimedean
and finite factors gives the same certified product. The real-place product is
empty, so the archimedean factor is exactly the complex-place product.

This is an internal reduction of the continuation and pole data used in
cuspidal constituent recovery. The ordinary global integrals and equal-rank
residue argument are in J. W. Cogdell, *Analytic Theory of L-Functions for GL(n)*
(2004), §2.3, printed pp. 208–211 (PDF pp. 211–214), and §§4.1–4.2, printed
pp. 219–222 (PDF pp. 222–225). Registered source
`cogdell-2004-analytic-theory-gln`, SHA-256
`8117f145869274324b12344dc83fa3289e3bd27c515b8d0d4a0211cd64174944`.
The local continuation and generation inputs concern H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), Theorems 2.1, 2.3, 2.6 and
2.7, author PDF pp. 6–10. Registered source
`jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.
