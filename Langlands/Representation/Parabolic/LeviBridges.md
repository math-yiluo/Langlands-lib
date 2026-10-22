# Algebraic bridges between the parabolic and its Levi

Author: Worker 8, coordinated with Worker 23's construction task.

This pair uses the actual block parabolic `P`, product Levi `M`, diagonal
projection `pi : P -> M`, section `s : M -> P`, and kernel `N` from
`Langlands.Group.GL.Blocks`. The matrix coefficient ring `F` and the
representation coefficient ring `R` are independent commutative rings.
All module universes are independent. Neither topology, smoothness nor
division by a group order is used.

`Langlands.Parabolic.inflate B sigma` is the action `sigma ∘ pi`.
`inflateMap` retains an intertwiner's linear map; its equivariance is proved
by applying the given equivariance at `pi(g)`. The proved `inflate_radical`
formula states that `N` acts trivially.

`LeviCoinvariants B rho` is the actual quotient of the module of a
`P`-representation by the span of `rho(u)v-v` for `u` in `N`.
`leviCoinvariants B rho` is Mathlib's descended normal-subgroup quotient
action, restricted along `s`. It is **unnormalized**. The formula
`m [v] = [rho(s(m))v]` is definitional. `leviCoinvariantsMap` sends `[v]`
to `[f(v)]`; equivariance and the identity/composition laws are proved.

The crucial bridge `mk_action_eq_levi` proves
`[rho(g)v] = [rho(s(pi(g)))v]`. Its proof applies the defining coinvariant
relation to the constructed unipotent factor `g*s(pi(g))^(-1)`.
Consequently `leviCoinvariantsMk` is the quotient map as a `P`-intertwiner
into the inflated Levi quotient, not just as a linear map.

`coinvariantsDesc` constructs the unique descended Levi intertwiner of a
`P`-map `f : rho -> inflate sigma`. Triviality of the target action on `N`
allows the actual linear quotient lift. Equivariance follows by evaluating
the original intertwining identity at `s(m)` and using `pi(s(m))=m`.
`coinvariantsHomEquiv` packages these constructions into the linear equivalence

`Hom_M(leviCoinvariants B rho, sigma) ≃ Hom_P(rho, inflate B sigma)`.

The forward map is composition with the quotient projection. The inverse
sends `[v]` to `f(v)`. Both inverse identities are proved using quotient
surjectivity; linearity is proved on representatives. The two final simp
lemmas record these exact formulas. The constructions are algebraic over
arbitrary commutative rings; they do not assert exactness of coinvariants.

## Sources and scope

This is derived construction infrastructure for Casselman, Chapter III
(April 29, 2019), Section 3, pages 3–4: the relation quotient and universal
property III.3.2, and the factorization immediately before the normalized
Frobenius reciprocity statement III.3.5. The retained source identifier is
`casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The original passages were read, and the normalization formula was checked
visually. The registered literature identifier locates the retained original.

Casselman's Proposition III.3.2 is formulated for smooth
`R`-representations, not only complex representations; the preceding
section discusses commutative Noetherian coefficient rings. The present
algebraic construction removes the smoothness and topological hypotheses
of that setting. Its independent commutative matrix and representation
coefficient rings, with no Noetherian hypothesis, are justified by the
implemented quotient lifts and proved split projection. This does not
extend the source's exactness or admissibility theorems to arbitrary rings.
Neither an arbitrary subgroup nor a predicate stands for the actual Levi.
No modulus, half-character or Haar-measure identification is assumed.
Normalized parabolic functors and their structural theorems remain separate.

The pair imports the current Library's `Langlands.Group.GL.Blocks` and
`Langlands.Representation.Jacquet.Coinvariants`. It reuses Mathlib's actual
normal-subgroup quotient action and the existing Jacquet quotient/lift API.
The intrinsic representation and map obligations are proved here.
Independent checking and semantic review remain required for publication.
