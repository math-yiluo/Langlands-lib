# Cocycle representatives for a lifted Hodge summand

Let \(I^2=0\) in \(R\) and let \(X\) be smooth and separated over
\(\operatorname{Spec}R\) with a finite affine cover. Suppose \(b_k\) are
compatible closed one-forms whose classes generate the first Hodge step
of degree-one Čech–de Rham cohomology \(H^1\). Let \(M\subseteq H^1\)
have projective quotient and the same image as the first Hodge step in
\(H^1/IH^1\).

`HodgeSummandCocycles` specifies cocycle corrections in \(I Z^1\), where
\(Z^1\) is the module of total degree-one cocycles. The classes of the
corrected cocycles generate \(M\). To construct these representatives,
write each class of \((0,b_k)\) as the sum of an element of \(M\) and
an element of \(IH^1\). The quotient map \(Z^1\to H^1\) takes \(I Z^1\)
onto \(I H^1\), so subtracting a representative of the second summand
gives the desired correction.

The span \(N\) of the resulting classes satisfies \(N\subseteq M\) and
\(N+IH^1=M+IH^1\). Projectivity of \(H^1/M\) gives a projection onto
\(M\). Applying it gives \(N+IM=M\), and multiplying by \(I\) gives
\(IM=IN\) since \(I^2=0\). Hence \(N=M\). Evaluation of the corrections
shows that the overlap functions lie in the extended base ideal and
that the chart forms differ from the original forms by ideal multiples.

This is a calculation in the total Čech complex and its quotient. It
provides representatives for the congruence of Hodge summands used in
Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, Proposition 2.1.6.8, printed p. 136 (PDF p. 164).
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
