# Finite scalar extensions of a CM algebra with involution

Worker 1728. This is a derived construction prerequisite for Clozel 1991,
Section 2, printed pp.101–106, especially Proposition 2.3 and its proof.
It uses the existing actual CM algebra and involution without changing their meanings.

The construction takes actual totally real and CM number fields E and K,
with their specified quadratic extension, actual finite places and their
adic completions. LocalCenter is E_v tensor_E K; LocalAlgebra is E_v tensor_E A;
CompletedAlgebra is K_w tensor_K A. Conjugation and the second-kind
involution are extended by the identity on E_v. The completed center map
is the tensor extension of K -> A. The local involution is proved to
induce exactly the constructed center conjugation.

For an actual prime w above v, the comparison to K_w tensor_K A uses the
existing continuous completion map, not a freely supplied field map. The
pure-tensor formulas and scalar compatibility are proved. Local division
requires every nonzero element of K_w tensor_K A to be a unit. Local
splitting requires a K_w-algebra equivalence with n by n matrices over K_w.
The second-kind involution lives over E_v; it need not fix an individual
K_w factor, since conjugation can exchange the two factors at a split place.

The division reflection theorem uses injectivity of A -> K_w tensor_K A
from flatness over the field K. A nonzero a has unit image, so multiplication
by a on A is injective. The actual finite-dimensionality in D makes this
endomorphism surjective, hence a is a unit. Thus local division implies
D.IsDivision without assuming global division or a realizability witness.

Source: Laurent Clozel, Représentations galoisiennes associées aux
représentations automorphes autoduales de GL(n), Publications mathématiques
de l'IHÉS 73 (1991), 97–145, Section 2, pp.102–106, especially the final
sentence of Proposition 2.3's case (a). Registered source
clozel-1991-selfdual-galois, SHA256
9de7c13c9ae108e481de170327a06e44845cf87a6aabc1d5600176ee695e91ac.
The tensor construction and elementary reflection proof are implemented here;
the global existence theorem is not proved by this module.
