# The refinement for a split type of level \((x,x)\) in \(\mathrm{Aut}_F(V)\)

This module proves the refinement step of Bushnell–Kutzko (8.2.5)(iv)
for the split types of level \((x,x)\), \(x>0\). In the source this is
the case \(E=F\), \(\mathfrak B=\mathfrak A\), \(m=n\), \(s=\mathrm{id}\)
of printed pp. 275–284. The pair is \((U^n(\mathfrak A),\psi_b)\) for a
split fundamental stratum \([\mathfrak A,n,n-1,b]\) with
\(\gcd(n,e(\mathfrak A))=1\) (`IsDiagonalPositiveSplitType`). All results
concern an arbitrary representation of \(\mathrm{Aut}_F(V)\), with no
topology. The matrix group is treated in `DiagonalSplitTypeJacquet`.

Throughout the lattice and character sections, \(F\) is a
nonarchimedean local field and \(\psi_F\) is an additive character of
\(F\) that is trivial on \(\mathfrak p_F\) and nontrivial on
\(\mathfrak o_F\) (`IsBKAdditiveCharacter`). This is the conductor
convention of BK93, printed pp. 19–20, under which additive duality
(1.1.4) holds. We write \(\psi_A=\psi_F\circ\operatorname{tr}\)
(`traceCharacter ψF`).

## Block unipotent subgroups

For \(e_1,e_2\in A=\mathrm{End}_F(V)\) with \(e_2e_1=0\) and an additive
subgroup \(P\) of \(A\), `blockUnipotent e₁ e₂ h₂₁ P` is the group of
units \(u\) with \(u-1=e_1(u-1)e_2\in P\). For \(x=e_1xe_2\) and
\(x'=e_1x'e_2\) one has \(xx'=0\), so \(u\mapsto u-1\) is additive on
this group and its elements commute (`blockUnipotent_commute`). These
two facts use only \(e_2e_1=0\).

When \(e_1,e_2\) are complementary idempotents (\(e_1+e_2=1\),
\(e_1e_2=e_2e_1=0\)), they are the projections of a decomposition
\(V=V_1\oplus V_2\) with \(V_i=e_iV\). Then \(x=e_1xe_2\) exactly when
\(x\in e_1Ae_2=\mathrm{Hom}_F(V_2,V_1)=A_{12}\). With \(P=A\) the group is
then the unipotent radical \(U=1+A_{12}\) of BK93 (8.2.1), and with
\(P=\mathfrak P^j\) it is the group \(M_j=1+\mathfrak P^j\cap A_{12}\) of
printed p. 281. Without idempotency these identifications can fail.
For example, \(e_1=2E_{11}\) and \(e_2=E_{22}\) in \(M_2(\mathbb Q_3)\)
satisfy \(e_2e_1=0\), but \(1+E_{12}\) is not in the group. The block
data of `SplitStratumBlocks` supply complementary idempotents, and
these are the only ones used below. `blockUnit` is the unit
\(1+e_1ye_2\) with inverse \(1-e_1ye_2\); it lies in the group when
\(e_1,e_2\) are idempotent (`blockUnit_mem`).

## Lattice facts over a local field

- `finite_layerQuotient`: \(\mathfrak P^i/\mathfrak P^j\) is finite for
  \(i\le j\). The proof repeats that of the private lemma
  `finite_endFiltrationQuotient` of `AdditiveDualityProof`.
- `mem_unitFiltration_of_sub_one_mem`: for \(m\ge1\), a unit \(g\) with
  \(g-1\in\mathfrak P^m\) lies in \(U^m(\mathfrak A)\).
  `conj_mem_unitFiltration`: a unit with \(g,g^{-1}\in\mathfrak A\)
  normalizes \(U^m(\mathfrak A)\).
- `traceCharacter_eq_one`: \(\psi_F(\operatorname{tr}x)=1\) for
  \(x\in\mathfrak P\), since \(\operatorname{tr}x\in\mathfrak p_F\) and
  \(\psi_F\) is trivial on \(\mathfrak p_F\).
- `blockCharacter`: for \(e_1,e_2,w\in\mathfrak A\), the character
  \(y\mapsto\psi_A(e_1ye_2w)\) of \(\mathfrak P^0/\mathfrak P^1\).
  `blockCharacter_eq_zero_iff` shows that it is trivial exactly when
  \(e_2we_1\in\mathfrak P\). One direction is the trace bound. For the
  other, \(\psi_A(e_2we_1y)=\psi_A(e_1ye_2w)\), and additive duality
  (`additiveDuality`, BK93 (1.1.4)) identifies the dual of
  \(\mathfrak P^0\) with \(\mathfrak P^1\). Both directions use
  `IsBKAdditiveCharacter`. Without the conductor condition the
  equivalence fails: for the trivial character every such \(\Phi\) is
  trivial.

## The shift element

For block data \(D\) (`SplitBlockData`, from `SplitStratumBlocks`),
`SplitBlockData.shift` is the unit \(z=\zeta+e_2\) with inverse
\(\zeta'+e_2\). This is the element \(\zeta\) of BK93 (8.2.9). It
commutes with \(b\).

- `shift_conj_block`: on \(e_1Ae_2\), conjugation by \(z\) is left
  multiplication by \(\zeta\). Hence \(zM_{j-1}z^{-1}\subseteq M_j\). The
  source has equality, from (8.2.10).
- `shift_conj_mem_iff`: for \(x\in\mathfrak P^m\),
  \((\zeta+e_2)x(\zeta'+e_2)\in\mathfrak P^m\) if and only if
  \(e_2xe_1\in\mathfrak P^{m+1}\). Expanding the product, only the term
  \(e_2x\zeta'\) can leave \(\mathfrak P^m\), and \(e_2x\zeta'\zeta=e_2xe_1\).

## Characters

`characterSubspace ρ K ϑ` is the \(\vartheta\)-isotypic subspace of
\(\rho\) for a character \(\vartheta\) of a subgroup \(K\). `conjEndo`
is conjugation by an element normalizing \(K\). For \(y\in\mathfrak A\),
`conjChar` is the character \(k\mapsto\vartheta(gkg^{-1})\) of
\(U^m(\mathfrak A)\) with \(g=1+e_1ye_2\). Let
\(\vartheta(k)=\psi_A(b(k-1))\) and write \(k=1+x\).
`conjChar_mul` computes
\[
\vartheta(gkg^{-1})\,\psi_A\bigl(e_1ye_2(bx-xb)\bigr)=\vartheta(k).
\]
This follows from \(g^{-1}bg=b+(bY-Yb)\) for \(Y=e_1ye_2\), since
\(YbY=0\).

`theta_shift_conj`: if \(k\) and \(zkz^{-1}\) both lie in
\(U^n(\mathfrak A)\), then \(\vartheta(zkz^{-1})=\vartheta(k)\), because
\(z\) commutes with \(b\).

`shift_conj_mem_unitFiltration_iff`: for \(k=1+x\in U^n(\mathfrak A)\),
\(zkz^{-1}\in U^n(\mathfrak A)\) if and only if
\(e_2(bx-xb)e_1\in\mathfrak P\). By `shift_conj_mem_iff` the first
condition says \(x_{21}=e_2xe_1\in\mathfrak P^{n+1}\). Since \(b\)
commutes with the idempotents, \(e_2(bx-xb)e_1=bx_{21}-x_{21}b\). This
lies in \(\mathfrak P\) when \(x_{21}\in\mathfrak P^{n+1}\). Conversely,
graded injectivity on the \((2,1)\)-block (`SplitBlockData.inj₂₁`, from
(8.2.4)(ii)) gives \(x_{21}\in\mathfrak P^{n+1}\) when
\(bx_{21}-x_{21}b\in\mathfrak P\).

## The main theorem

`SplitBlockData.not_le_relations_blockUnipotent`. Let \(F\) and
\(\psi_F\) be as above, with `IsBKAdditiveCharacter ψF`. Let \(S\) be a
stratum over \(\mathfrak o_F\) with \(n=m\ge1\), \(b\in\mathfrak P^{-n}\)
and block data \(D\). Let \(\vartheta\) be a character of
\(U^n(\mathfrak A)\) with \(\vartheta(g)=\psi_A(b(g-1))\). Let \(\rho\) be a representation of
\(\mathrm{Aut}_F(V)\) whose \(\vartheta\)-isotypic subspace \(P\) is
finite-dimensional and not contained in the relations of
\(\ker\vartheta\). Then \(P\) is not contained in the relations of
\(U=1+e_1Ae_2\).

The proof applies `Jacquet.not_le_relations_of_refinement` to the
family \(M_j\), which is antitone and covers \(U\)
(`SplitObstruction.exists_mem_endFiltration`).

- Start, \(j_0=n\): \(M_n\subseteq U^n(\mathfrak A)\) and
  \(\vartheta(u)=\psi_F(\operatorname{tr}(be_1(u-1)e_2))=1\) there, since
  \(e_2be_1=be_2e_1=0\). So \(M_n\subseteq\ker\vartheta\).
- Step from \(M_j\) to \(M_{j-1}\). Take \(v_1\in P\) not a relation of
  \(M_j\) and put \(v_2=\rho(z^{-1})v_1\). By
  \(zM_{j-1}z^{-1}\subseteq M_j\) and `Jacquet.apply_mem_relations`,
  \(v_2\) is not a relation of \(M_{j-1}\), as on printed p. 283. Let
  \(\mathcal K=K\cap z^{-1}Kz\) with \(K=U^n(\mathfrak A)\). By
  `theta_shift_conj`, \(\mathcal K\) acts on \(v_2\) through
  \(\vartheta\). The group \(\mathcal K\) contains \(U^{n+1}(\mathfrak A)\),
  so \(K/\mathcal K\) is finite (`finite_layerQuotient` and
  `LatticeChain.unitFiltrationToQuotient`). The family indexed by
  \(Z=\mathfrak P^0/\mathfrak P^1\) is \(g_q=1+e_1y_qe_2\) and
  \(\chi_q=\) `conjChar` of \(y_q\), with \(y_q\) a representative of
  \(q\). Then:
  - \(\chi_q(k)^{-1}=\Phi_k(q)\,\vartheta(k)^{-1}\), where \(\Phi_k\) is
    the `blockCharacter` of \(w=bx-xb\);
  - by `blockCharacter_eq_zero_iff` and
    `shift_conj_mem_unitFiltration_iff`, \(\Phi_k\) is trivial exactly
    when \(k\in\mathcal K\);
  - the sum of a character of the finite group \(Z\) is \(|Z|\) or \(0\)
    (`AddChar.sum_eq_ite`), which gives the orthogonality relation;
  - \(g_q\) lies in \(U\), which is commutative, so it normalizes
    \(M_{j-1}\);
  - \(\rho(g_q)\) carries \(\chi_q\)-isotypic vectors to
    \(\vartheta\)-isotypic ones.

  `Jacquet.exists_isotypic_not_mem_relations` then gives a vector of
  \(P\) that is not a relation of \(M_{j-1}\).

The source passes from the group \(K\cap K^\zeta\) back to \(K\)
through the intermediate group \(H\) of (8.2.15)–(8.2.17) and uses the
conjugacy of all extensions (8.2.14). For \(E=F\) a single
orthogonality step suffices. It uses only additive duality and the
graded injectivity of \(x\mapsto bx-xb\) on the \((2,1)\)-block; no
surjectivity or counting is needed.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.1), printed p. 275, (8.2.4)–(8.2.5),
printed pp. 276–277, and (8.2.9)–(8.2.17), printed pp. 278–284, with
additive duality (1.1.4), printed p. 22.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
