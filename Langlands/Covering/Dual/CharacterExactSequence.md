# Algebraic complex characters of a short exact sequence

Gan and Gao, *The Langlands–Weissman program for Brylinski–Deligne
extensions*, Astérisque 398 (2018), §5.2, (5.1)–(5.2), printed pp. 214–215
(PDF pp. 232–233), dualize an abelian group extension by applying
\(\operatorname{Hom}_{\mathbf Z}(-,\mathbf C^\times)\). The module
`Langlands.Covering.Dual.CharacterExactSequence` constructs this dual sequence
for arbitrary abelian groups \(B,E,D\) in a supplied short exact sequence
\(1\to B\xrightarrow{i}E\xrightarrow{p}D\to 1\).

`Character G` is the group of homomorphisms \(G\to\mathbf C^\times\) with
pointwise multiplication. `precompose f` sends \(\chi\) to \(\chi\circ f\).
Consequently `dualExtension` has inclusion \(\psi\mapsto\psi\circ p\) and
projection \(\chi\mapsto\chi\circ i\). In (5.1), \(D\) is the modified
cocharacter quotient, so the left endpoint of the dual sequence is its
algebraic complex character group.

The `GroupExtension` fields certify exactness. Surjectivity of \(p\) makes
precomposition with \(p\) injective. A character pulled back from \(D\) is
trivial on \(i(B)\). Conversely a character trivial there kills
\(\ker p=i(B)\), so `MonoidHom.liftOfSurjective` descends it through \(p\).
Surjectivity of restriction follows from
`Langlands.Topology.exists_complex_character_extension` applied to the
injective map \(i\).

The retained source has literature ID `gan-gao-2018-langlands-weissman-program`
and SHA-256 `fabbe056bdec2a5d57a22a0d3ad275640d0343c3f71092a7df427f7ebaebe892`.
