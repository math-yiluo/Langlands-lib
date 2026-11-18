# Left quotients under a split group projection

This derived construction uses the existing continuous coset maps for a
split group projection `r : G → L` with continuous section `s : L → G`.
If a subgroup `H` contains `ker r`, they give a homeomorphism from the
actual left-coset space `H \ G` to `(H.comap s) \ L`. On representatives
the forward map evaluates `r` and the inverse evaluates `s`. The first
triangle follows from `r (s l) = l`. The other follows because
`g * (s (r g))⁻¹` lies in `ker r` and hence in `H`.

For topological groups the homeomorphism also commutes with right
translation, which is sent from translation by `g` to translation by `r g`.
This follows by evaluating on a representative and applying the
multiplicativity of `r`. The result uses the actual left quotients, so `H`
and `H.comap s` may be nonnormal. In the adjacent Levi case the projection
is the outer Levi projection on the target radical, and its kernel is
contained in the ambient radical intersection. The homeomorphism supplies
the domain comparison used to transport the weak standard integral.
