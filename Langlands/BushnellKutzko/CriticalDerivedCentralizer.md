# All-depth adjoint comparison

Internal lemmas for the proof of Bushnell–Kutzko, *The admissible dual of
GL(N) via compact open subgroups* (1993), registered
`bushnell-kutzko-1993-admissible-dual-gln`, (2.4.1)(iii), printed p. 65.
The comparison below is a derived use of their adjoint exactness,
Corollary (1.4.10), printed p. 38, rather than the representative
comparison in §2.4.

`ambientCorestriction` restricts the values of the supplied tame
corestriction to the base field. It preserves each filtration degree for
a normalizing field, annihilates the commutator with the field generator,
and pulls a commutator with a commuting endomorphism through the map.
`exists_adjoint_correction` uses the fourth adjoint sequence at
`m = j + 1`, `k = d - 1` and step one: an element of depth at least `d + j`
whose corestriction has one more degree of depth can be corrected by the
adjoint of an element of depth at least `j + 1`. For a scalar generator,
the kernel description instead makes the corestriction injective, and
filtration image equality gives the result with zero correction.

The two remaining lemmas take explicit correction and filtration premises.
For `β = γ + b`, `b` of depth at least `d`, and `a = s(b)`,
`approx_original_centralizer` corrects a degree-`j` endomorphism commuting
with `β` by a degree-`j + 1` error to one commuting with `γ`. The corrected
endomorphism commutes with `a` modulo degree `d + j + 1`.
Conversely, `approx_perturbed_centralizer` corrects an endomorphism of
this latter kind back to one commuting with `β`, using first the adjoint
of `γ` and then the adjoint of `β`, again modulo degree `j + 1`.
