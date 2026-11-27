# Character values on unit commutators

`characterCommutatorFormula` records membership of a group commutator in the character domain and its value as the element character of the conjugation difference. It packages the two conclusions of BK93 (3.2.6) and (3.2.8), printed pp. 100–103.

The lemmas calculate this value on centralizer units by determinant and combine factorizations of either input using group commutator identities. The product of the two differences in the second input contributes a trace factor, whose triviality is an explicit premise. Another lemma transports the formula through a twist. `exists_mul_of_sub_one_mem_sup` converts an additive decomposition into a product of congruence units under the stated positivity, stability and inverse conditions.
