# Relative Frobenius: exact isogeny and kernel-rank proof target

`Langlands.FormalGroup.ModuleLaw.RelativeFrobeniusIsogenyStatement` is an
unproved proposition about the actual relative Frobenius map constructed in
`RelativeFrobenius`. Its parameters are an actual finite-coordinate formal
`O`-module `M` over a commutative `O`-algebra `R`, a natural exponential
characteristic `p`, and a natural iterate `n`. It quantifies over every actual
`O`-algebra endomorphism `θ` whose underlying ring homomorphism is proved equal
to `iterateFrobenius R p n`.

The conclusion is the existing actual predicate
`(M.frobeniusHom p n θ hθ).HasHeight p (n * Nat.card σ)`.
It requires BOTH affine fppf local lifting of every actual nilpotent target
point and an actual finite locally free coordinate-algebra representation of
the actual kernel functor, whose stalkwise module rank is
`p^(n * Nat.card σ)`. In particular, neither a supplied kernel algebra without
its natural corepresentation nor a free numerical rank field suffices. This
is a finite-map rank statement; it does not impose any pi-divisibility
condition on the formal group or claim a rational inverse.

The expected mathematical construction uses the actual variable-power
Frobenius formula: its kernel is corepresented by the truncated coordinate
algebra `R[T_i]/(T_i^(p^n))`, and target points lift after adjoining their
`p^n`-th roots. The proof must construct the natural kernel equivalence and
verify finite projectivity, the exact rank and faithful flatness plus finite
presentation of the lifting extension. This paragraph describes the intended
proof obligation; no such construction is implemented in this statement file.

Three implemented consequences only extract the isogeny and rank clauses from
a proof of the full statement or apply it to the underlying actual map of the
full-order Frobenius. They do not prove the statement. When `p = 1` the actual
map is the identity and the required kernel rank is one.

The provenance is internal: this is a concrete missing structural result for
the actual coordinate Frobenius, needed toward the natural Frobenius
quasi-isogeny in Drinfeld 1976, §2 A, printed p.109. It is not attributed as a
separately numbered theorem or verbatim statement in that source. Rational
invertibility on pi-divisible formal modules, the residue-cardinality height
normalization and the full Drinfeld group action remain further obligations.
A focused proof task should be published after this exact target reaches the
current Library.
