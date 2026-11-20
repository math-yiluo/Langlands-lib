# Determinant support of the unramified base-change map

`DeterminantSupportReductionStatement` says that Satake character existence over
the extension field and Satake character separation over the base field imply
vanishing of the ordinary orbital integral of \(b(\phi)\) at any \(\gamma\) with
\(\operatorname{ord}_F(\det\gamma)\notin l\mathbb Z\). The statement uses the
existing spherical Hecke algebra, base-change homomorphism predicate, and
orbital integral. It applies for every \(l>0\) and every measure on the left
quotient by the centralizer. The proof also shows pointwise vanishing of
\(b(\phi)\) at all matrices of those determinant orders.

This is the determinant-support argument in the remark after
Henniart–Lemaire (2011), I.6.11, printed p. 53, expressed using the Library's
normalized order. The Lean proof uses the character with uniformizer value
\(z\), given by \(g\mapsto z^{\operatorname{ord}_F(\det g)}\). It is trivial on
the spherical subgroup, so the compact-open character twist preserves the
spherical algebra. The \(i\)-th standard double coset has determinant order
\(i\), and the twist multiplies its characteristic function by \(z^i\).
This is the scaling of the \(i\)-th elementary symmetric coefficient under
the parameter change \(s\mapsto zs\). When \(z^l=1\), both parameters have the
same \(l\)-th power. The base-change identity therefore gives equal values on
\(b(\phi)\) and its twist for every Satake character over \(F\). Separation
applied to their difference gives equality of the functions.

Choose a primitive \(l\)-th root \(z\). If \(l\) fails to divide the determinant
order, the multiplier differs from one and the function value is zero.
Conjugation preserves the determinant, so the integrand is zero on the
entire quotient. To apply this to every regular elliptic non-norm one
additionally needs the arithmetic norm criterion from I.6.12.
