# Proof of exact absolute generation for a nonmultipliable relative root

`Langlands.GroupScheme.relativeRootGroupExactGeneration` proves
[`RelativeRootGroupExactGenerationStatement`](RelativeRootGroupExactGenerationStatement.md)
at an arbitrary universe. The data are those of the statement: a connected
reductive \(G\) over a field \(k\), a maximal \(k\)-split torus \(S\), a
maximal torus \(T\) containing \(S\) through \(f\), an arbitrary extension
\(K/k\) over which \(T\) splits, and a relative root \(a\) with \(2a\) not a
relative root.

The proof reduces the statement to the positive-multiple generation theorem
`relativeRootGroupAbsoluteGeneration`
([statement](RelativeRootGroupAbsoluteGenerationStatement.md)), applied to the
same tori, the same extension \(K\) and the same root \(a\). That theorem
gives two clauses for the absolute roots \(\beta\) of \((G_K, T_K)\) whose
restriction to \(S_K\) is \(n a_K\) for some natural number \(n > 0\).

**Containment.** A root \(\beta\) with \(\beta|_{S_K} = a_K\) has this form
with \(n = 1\). The first clause of the positive-multiple theorem therefore
places its root group \(U_\beta\) inside the base change of
`RelativeRoot.subgroup i a`.

**Minimality.** Let \(h : H \to G_K\) be a closed subgroup whose range
contains \(U_\beta\) for every root \(\beta\) restricting exactly to \(a_K\).
By the second clause of the positive-multiple theorem it suffices to show
that every root \(\beta\) with \(\beta|_{S_K} = n a_K\), \(n > 0\), restricts
exactly to \(a_K\). Three published results give this.

1. `IsSplitTorus.nsmul_ne_zero`: the character lattice of the split torus
   \(S\) is torsion free, so \(n a \neq 0\) because \(a \neq 0\).
2. `relativeRootAbsoluteRestriction`: a nonzero character of \(S\) whose base
   change is the restriction of an absolute root of \((G_K, T_K)\) is a
   relative root. Since base change of characters is additive,
   \(\beta|_{S_K} = \beta \circ f_K = n a_K = (n a)_K\), so \(n a\) is a
   relative root.
3. `relativeRootSystem` supplies the relative root system of \(S\), and
   `HasRelativeRootSystem.eq_one_of_nsmul_mem_of_two_not_mem` states that
   when \(a\) and \(n a\) are relative roots and \(2a\) is not, \(n = 1\).

Hence \(\beta|_{S_K} = a_K\), so \(U_\beta\) lies in the range of \(h\) by
hypothesis. The second clause then gives the subgroup-functor inequality
\((U_{(a)})_K \le \operatorname{range} h\) on every test scheme over \(K\).

The two affineness instances required by the statement come from
`IsConnectedReductive.isAffineHom` and base change of an affine morphism;
the mono instance on the split torus inclusion comes from the maximal split
torus hypothesis. The theorem depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
