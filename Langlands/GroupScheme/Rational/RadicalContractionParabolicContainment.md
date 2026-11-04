# Ambient containment from contraction of the original radical

This is a derived construction using the published actual-root Lie criteria,
dynamic connectedness, smoothness, connected unipotence and normality, represented
subgroup factorization, and multiplication/contraction comparison. It introduces
no assertion from external literature and no structural existence theorem.

For a smooth connected affine group over any field in universe `u`, take an
actual homomorphism `t` from a split commutative torus `T`. If its actual relative
roots are closed under negation, then `U(eta) ≤ U(nu)` implies
`P(nu) ≤ P(eta)` on every test scheme. For a root nonnegative on `nu`, a negative
pairing on `eta` would make its negative positive on `eta`. Unipotent containment
makes that negative root positive on `nu`, a contradiction. The published
nonnegative-root Lie criterion and published dynamic connectedness yield the
parabolic containment. A variant obtains root negation from a supplied
`HasRelativeRootSystem t` and monicity of `t` on schemes. The realization is an
explicit hypothesis, rather than a universally asserted root-system theorem.

For a smooth affine ambient group, `unipotent_le_range_of_isUnipotentRadical`
shows that the actual dynamic identity-limit subgroup lies in any supplied
unipotent radical of any supplied representative `p` of its dynamic parabolic.
Factor the affine dynamic unipotent representative through `p`. The factor is
closed; its source is smooth, connected and unipotent, and its range is normal
in the parabolic. Greatestness in `IsUnipotentRadical r` gives containment in
the supplied radical `r`. Postcomposition with `p` gives the all-test ambient
containment. No reductivity of the dynamic centralizer, connectedness of the
ambient group, or maximality of a split torus is needed for this step.

The definition `Dynamic.unipotentRepresentativeToRadical` then factors any
supplied representative `i : H → G` of the dynamic unipotent subgroup through
the same original `r : U → P`. It uses represented factorization through the
monomorphism `r ≫ p`. Its specification states the exact composite
`unipotentRepresentativeToRadical … ≫ r ≫ p = i`.

Combining the two steps, assume `p` represents `P(eta)` for a cocharacter of
that same split torus, and the image of the original supplied radical `r ≫ p`
contracts under `nu`. Then `P(nu)` and its entire ambient centralizer lie in
the original image of `p`. If an actual multiplication isomorphism
`L × U ≅ P` is supplied and the original first factor is fixed by `nu`, the
published multiplication comparison gives `P(nu) = range(p)` and
`Z(nu) = range(l ≫ p)`. Affineness supplies separatedness for this comparison.

All containments and equalities concern subgroup functors on every test scheme.
The common split-torus presentation, root-negation hypothesis (or supplied root
realization), and original radical contraction remain explicit inputs. This
unit does not establish such a presentation for every parabolic, supply the
initial positive direction, prove ambient maximal splitness, or prove the
immutable `MinimalParabolicLeviCentralizerStatement`.
