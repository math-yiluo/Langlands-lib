# Joint admissibility of generated automorphic realizations

`Langlands.Automorphic.generatedFormAdmissibility` proves
`GeneratedFormAdmissibilityStatement.{u}` for every number field in
universe `u`, every rank and every automorphic form. It applies
`generatedFormAdmissibility_of_harishChandraFiniteness` to
`harishChandraFiniteness` at the same universe.
[Target statement](AutomorphicAdmissibilityStatement.md)

The reduction uses the finite-dimensional span of the central translates
of the compact orbit of the generating form. Its annihilator is an ideal
of finite codimension that is stable under compact conjugation. The
subspace annihilated by this ideal is stable under finite adelic
translations, compact translations and the archimedean enveloping algebra,
so it contains the generated realization. For each open finite adelic
subgroup and each standard compact representation on `Fin m → ℂ`,
postcomposition with the inclusion into automorphic forms embeds the
generated multiplicity space into the corresponding multiplicity space
annihilated by that ideal.
[Reduction proof](GeneratedFormAdmissibilityReduction.md)

`harishChandraFiniteness` gives finite dimension for the latter space.
Its proof uses induction on rank with maximal-block constant terms.
Cuspidal finiteness bounds the kernel and the two lower-rank families of
Levi slices bound the image.
[Finiteness proof](HarishChandraFinitenessProof.md)

This application formalizes the deduction from §4.3 (i), printed p. 195
(PDF p. 190), used in Proposition 4.5 (1) ⇒ (4), printed p. 196
(PDF p. 191), of Borel and Jacquet, *Automorphic forms and automorphic
representations*, Corvallis Part I (1979). The reduction obtains the
common ideal from the compact and central finiteness conditions of
§4.2 (b)–(c), printed p. 195 (PDF p. 190). The finiteness input adapts
the constant-term induction in Harish-Chandra, *Automorphic forms on
semisimple Lie groups* (1968), Chapter I, §6, Lemmas 17–18 and the
proof of Theorem 1, printed pp. 17–20 (PDF pp. 27–30).
