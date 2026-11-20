# Actual isogenies from scalar composites

`Hom.isIsogeny_of_scalarComposites_overRing` shows that a formal homomorphism \(f\) between
scalar-divisible formal modules is an actual isogeny if there is a reverse
homomorphism \(g\) and both composites equal the same power of the divisibility
scalar. This is a derived Library lemma for the lift of local quasi-isogenies.
It uses the existing scalar-kernel models, kernel quotients and translations.

Scalar divisibility of the target gives affine fppf local surjectivity of \(f\).
The two scalar kernels give quotient algebras \(K\) and \(L\) corepresenting the
actual kernels of \(f\) and \(g\) respectively. Lift the universal point of the
second kernel through \(f\) over a faithfully flat \(L\)-algebra \(B\). The lift
lies in the composite kernel. Translation by this lift identifies the fibre
over \(B\) with the zero fibre over \(B\), whose algebra is \(K\otimes_R B\).
The proof checks the pushout by subtracting the chosen lift from a composite
kernel point and classifying the difference as a point of the first kernel.

The composite kernel has finite projective coordinates over \(R\), so flat
base change along \(L\to B\) gives \(R\)-flatness of \(K\otimes_R B\).
The zero point of the first kernel gives an algebra retraction onto \(B\).
The zero point of the second kernel gives surjectivity of
\(\operatorname{Spec} L\to\operatorname{Spec} R\), and faithful flatness of
\(L\to B\) gives surjectivity of \(\operatorname{Spec} B\to\operatorname{Spec} L\).
Thus \(B\) is faithfully flat over \(R\). The tensor criterion for flatness then
gives \(R\)-flatness of \(K\). Its module finite presentation upgrades flatness
to projectivity, supplying the finite locally free kernel required for \(f\).
