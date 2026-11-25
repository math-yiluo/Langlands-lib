# From ramification index one to a reduced normalized residue fibre

At a vertical DVR, the generic localization of the original local
ring is its fraction field. After changing the base to a new DVR,
the tensor of fraction fields is a localization of the extended
ambient generic algebra. It is therefore reduced whenever that
ambient algebra is reduced.

For `verticalSolutionNormalizationEquiv`, take injective local maps
\(R\to S\) and \(R\to Q\) of DVRs, with \(S\) finite as an \(R\)-module
and \(Q\) the original vertical DVR. Let \(K=\operatorname{Frac}(R)\),
\(L=\operatorname{Frac}(Q)\) and \(E=\operatorname{Frac}(S)\).
The supplied ring \(C\) is the integral closure of \(Q\) in a ring
presented as \(L\otimes_K E\). The presentation is a \(Q\)-algebra
equivalence for the left factor, and the supplied \(S\)-map into \(C\)
agrees in the tensor with \(s\mapsto 1\otimes s\) via \(S\to E\).
Finiteness of \(S\) over \(R\) makes \(S\otimes_R Q\) integral over
\(Q\). Transitivity and uniqueness of integral closure give an
\(S\)-algebra equivalence between \(C\) and the normalization of
\(S\otimes_R Q\) in its generic fibre.

Suppose every maximal ideal of \(C\) has ramification index one
over \(S\). All maximal ideals contain the image of an
\(S\)-uniformizer by integrality over \(Q\) and compatibility of
the base maps. Each corresponding localization of the quotient
by the uniformizer then has length one and is a field. This gives
ordinary reducedness after tensoring the normalized algebra over
\(S\) with `ResidueField S`.

Conrad's Remark A.7 uses generic smoothness of the special fibre
of a flat normal model to obtain geometric reducedness. The
length-one calculation here supplies the local ordinary
reducedness step for a related approach. In the finite-type
application, the reduced special fibre obtained by the
generic-point criterion is geometrically reduced when the residue
field is perfect. [Conrad, appendix to Prasad–Yu, *On quasi-reductive
group schemes*, printed and PDF p. 30, Remark A.7](https://math.stanford.edu/~conrad/papers/qrg.pdf#page=30).
