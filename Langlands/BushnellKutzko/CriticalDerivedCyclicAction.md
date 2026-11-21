# Transport of the free cyclic action

This is an internal construction for the proof of BK93 (2.4.1)(iii), implementing the cyclic-lift idea of §2.5 using the two-index splitting basis and the two monic root relations.

Take a free module over the root algebra, with one summand for each chosen layer generator. Its basis over the base field consists of the single-coordinate vectors `T ^ m * U ^ l`; the basis equivalence sends them to the corresponding cyclic splitting vectors. Conjugate the scalar action on the free module along this equivalence. The transported unit roots commute, satisfy the two defining relations, and send a generator by the indicated short iterates to the splitting vectors. This construction does not assert that the root algebra is a field or that arbitrary powers match the original operators.
