# Affine homotopy for pullbacks congruent modulo a square-zero ideal

Let \(I\) be a square-zero ideal in the base ring \(R\), and let \(f,g\colon
A\to B\) be two maps of \(R\)-algebras agreeing modulo \(IB\). Their
difference \(\delta=f-g\) is a derivation with the \(A\)-action on \(B\)
through \(f\), since products of two elements of \(IB\) vanish. The universal
property of the relative Kähler module gives `contractDifferenceOne`, the
contraction \(i_\delta\colon\Omega^1_{A/R}\to B\) sending \(a\,db\) to
\(f(a)\delta(b)\).

`contractDifferenceTwo` sends a wedge \(x\wedge y\) to
\(i_\delta(x)f^*y-i_\delta(y)f^*x\). The exterior square supplies this map
from the alternating two-variable formula. On a generator \(a\,db\), the
Leibniz rule and the formula \(d(a\,db)=da\wedge db\) give
\[
f^*\omega-g^*\omega=d(i_\delta\omega)+i_\delta(d\omega),
\]
which is `mapOne_sub_eq_d_contract_add_contract_d`. The calculation uses
\(IB\,d(IB)=0\), which follows from the relative derivation vanishing on
base scalars. An additive induction using the Kähler presentation extends
the identity to every one-form. For a closed one-form,
`mapOne_sub_eq_d_contract_of_closed` expresses the difference of its
pullbacks as an exact form with the primitive \(i_\delta\omega\).

The contraction takes values in \(IB\) (`contractDifferenceOne_mem`). For
three maps with common reduction, the contractions for \((f,g)\) and
\((g,h)\) sum to that for \((f,h)\) (`contractDifferenceOne_telescopes`).
This follows on \(a\,db\) from the vanishing of
\((f(a)-g(a))(g(b)-h(b))\). The contraction for \((f,f)\) is zero.
Precomposition with an algebra map pulls back the input form
(`contractDifferenceOne_precomp`), and postcomposition applies the algebra
map to the value of the contraction (`contractDifferenceOne_postcomp`).

This is the affine identity for the chartwise comparison in Kai-Wen Lan,
*Arithmetic compactifications of PEL-type Shimura varieties*, revised
14 March 2021, Proposition 2.1.6.4, printed pp. 133–135. In that comparison
the maps \(T_{\alpha\beta}\) with \(T_{\alpha\beta}\circ d\) equal to the
difference of two local lifts are contractions of this kind. The retained
source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
