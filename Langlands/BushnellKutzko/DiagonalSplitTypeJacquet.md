# Jacquet nonvanishing for a split type of level \((x,x)\) in \(\mathrm{GL}_n(F)\)

This module transports `SplitBlockData.not_le_relations_blockUnipotent`
(`DiagonalSplitTypeRefinement`) from \(\mathrm{Aut}_F(F^n)\) to the
matrix group. This is Bushnell–Kutzko (8.2.5)(iv) for split types of
level \((x,x)\), \(x>0\).

## General lemmas

- `relations_comp_mulEquiv`: for a group isomorphism \(e:H\to G\), the
  coinvariant relations of \(\rho\circ e\) for \(N\le H\) are those of
  \(\rho\) for \(e(N)\).
- `not_mem_relations_ker`: let \(\rho\) be a smooth representation of a
  topological group, \(K\) a compact subgroup and \(\vartheta\) a
  character of \(K\) with open kernel. Then a nonzero
  \(\vartheta\)-isotypic vector is not a coinvariant relation of
  \(\ker\vartheta\). The \(\vartheta^{-1}\)-twisted average over \(K\),
  `Jacquet.Localization.characterAverage`, fixes the vector
  (`Compact.averageMap_id`) and kills the relations of
  \(\ker\vartheta\) (`characterAverage_relation`). This replaces the
  integrals over compact subgroups of \(U\) in BK93, printed p. 281.

## The main theorem

`diagonalSplitType_jacquet_nonvanishing`. Let \(\pi\) be an admissible
smooth representation of \(\mathrm{GL}_n(F)\). Let \((K,\rho)\) be a pair
with \(K\) compact and open, satisfying `IsDiagonalPositiveSplitType`
after transport by `glRepresentationToAut`. If \(\pi\) contains
\(\rho\) (`ContainsType`), then for some `BlockShape` \(B\) with proper
parabolic and some \(g\), the coinvariants of \(\pi\) by
`B.conjugateUnipotent g` are nonzero. Irreducibility is not used.

The proof:

1. Unfold the split type. It gives \([\mathfrak A,n,n-1,b]\) split
   fundamental with \(n>0\) and \(\gcd(n,e)=1\), and an isomorphism of
   the pair with \((U^n(\mathfrak A),\psi_b)\). The base ring
   \(\mathfrak o_F\) is Henselian because it is \(\mathfrak p_F\)-adically
   complete, so `nonempty_splitBlockData` supplies block data.
2. The isomorphism makes \(\rho(k)\) the scalar \(\vartheta(k)\), where
   \(\vartheta\) is \(\psi_b\) composed with the identification of \(K\)
   with \(U^n(\mathfrak A)\). A nonzero intertwiner from \(\rho\) to
   \(\pi\) gives a nonzero \(\vartheta\)-isotypic vector \(v_0\). The
   \(\vartheta\)-isotypic subspace for \(K\) equals the
   \(\psi_b\)-isotypic subspace of the transported representation
   \(\pi'=\pi\circ\mathrm{toLin}^{-1}\) of \(\mathrm{Aut}_F(F^n)\).
3. Smoothness of \(\rho\) at a vector with nonzero image gives an open
   subgroup of \(K\) in \(\ker\vartheta\). Its image is open in
   \(\mathrm{GL}_n(F)\) and fixes the isotypic subspace. Admissibility
   makes that subspace finite-dimensional.
4. The relations of \(\pi'\) for \(\ker\psi_b\) are those of \(\pi\) for a
   subgroup of \(\ker\vartheta\) (`relations_comp_mulEquiv`), so
   `not_mem_relations_ker` shows that \(v_0\) is not one of them. This
   is the starting hypothesis of the refinement theorem, which then
   gives a vector outside the relations of \(1+e_1Ae_2\).
5. `exists_blockShape_conjugateUnipotent_le` (`IdempotentBlockShape`)
   gives \(B\) and \(g\) with `B.conjugateUnipotent g` inside the image of
   \(1+e_1Ae_2\). Relations only shrink for a smaller group, so
   `Jacquet.not_subsingleton_of_not_le_relations` concludes.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.5)(iv), printed pp. 276–277, and
printed pp. 280–284; the pair is (8.1.1), printed p. 266.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
