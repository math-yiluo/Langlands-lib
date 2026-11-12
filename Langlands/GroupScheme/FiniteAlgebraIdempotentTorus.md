# Torus morphism from two orthogonal idempotents

This internal derived module constructs an actual group-scheme homomorphism
from the multiplicative group into the units of a finite-dimensional algebra
`A` over `K`, given two idempotents `p,q` with `pq = qp = 0`.
On every coefficient algebra `R`, a unit `t` maps to
`1 + (t-1) ⊗ p + (t⁻¹-1) ⊗ q`.

Orthogonality and idempotence prove the multiplication law by expansion; replacing
`t` by its inverse supplies the inverse unit. The formula is natural under every
coefficient-algebra homomorphism. Applying the established unit point comparison
and Yoneda's fully faithful embedding realizes the stated actual group-scheme
morphism, with the displayed formula on all scheme tests.

The construction does not assert a closed immersion or nontriviality without
further hypotheses on the idempotents, and it imposes no characteristic restriction.
