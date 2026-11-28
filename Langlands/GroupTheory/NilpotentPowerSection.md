# Splitting a central extension over a nilpotent group by taking powers

Let \(q:E\to G\) be a surjective group homomorphism with central kernel
killed by \(e\). Suppose \(G\) is nilpotent and its \(e\)-th power map is
bijective. If \(q(x)=q(y)\), then \(x/y\) is central and has \(e\)-th power
one, so \(x^e=y^e\). For \(a\in G\), define its lift \(s(a)\) by taking the
\(e\)-th power of a lift of the unique \(e\)-th root of \(a\). The fiber
calculation makes the result independent of the lift and \(q(s(a))=a\).

A root of a central element of \(G\) is central, by injectivity of the
power map applied to its conjugates. Every element of \(E\) over the center
is central as well. The power of a lift of a central root commutes with
every element by the same fiber calculation, and every lift of the
original central element differs from this power by a central factor in
the kernel. Consequently the power lift is multiplicative on \(Z(G)\),
where lifts of roots commute.

For multiplicativity on all of \(G\), use induction on nilpotent groups
via the quotient by their centers. The power map on \(G/Z(G)\) is again
bijective. If two powers agree modulo \(Z(G)\), their central quotient has
a central root that can be absorbed into one of the original elements, at
which point injectivity on \(G\) applies. The induced map
\(E/s(Z(G))\to G/Z(G)\) has central kernel killed by \(e\), since a lift over
the center differs from the corresponding element of \(s(Z(G))\) by an
element of the original kernel. Taking powers commutes with the quotient
projections, so the two sides of \(s(ab)=s(a)s(b)\) agree in \(E/s(Z(G))\)
by induction. They also have the same image under \(q\), which is
injective on \(s(Z(G))\). This proves multiplicativity and gives the
homomorphism `nilpotentPowerSection`.

Every homomorphic section sends an \(e\)-th power to the \(e\)-th power of
a lift of its root. This proves `nilpotentPowerSection_unique`.
