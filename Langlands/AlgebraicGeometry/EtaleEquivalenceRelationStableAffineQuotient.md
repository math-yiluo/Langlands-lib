# Affine quotients at sufficiently large stable levels

Author: Worker 706. The imported ring presentation and descent results are due
to Workers 266 and 1110.

This internal adapter assumes a cartesian morphism `h : IsCartesianHom E E₀ f g`,
affineness of `E.U`, `E₀.U`, and `E₀.R`, and Noetherianity of `Γ(E₀.U, ⊤)`. It
also assumes that `E` has an affine quotient. It proves that all sufficiently
large finitely generated stable levels in the previously constructed
`h.stableDiagram` have affine quotients. All schemes, rings, and stable indices
retain the arbitrary universe `u`.

The application is the affine-piece step of Stacks Lemma 70.5.10, Tag 07SQ, in
the proof of Proposition 70.8.1, Tag 07SU. The registered source is
`stacks-noetherian-approximation-2026-11-01`. The adapter is a derived
presentation-level interface: it uses the direct finite-generator ring proof
of `RingEtaleGroupoid.exists_bijective_level`, rather than reconstructing the
source's algebraic-space limit argument. It does not prove first-level
existence or glue affine pieces to construct a scheme quotient.

All declarations are in
`EtaleEquivalenceRelation.IsCartesianHom`.

`exists_stable_affineQuotient_finite_set` produces a finite set `s` in
`Γ(E.U, ⊤)` such that every stable index whose underlying subalgebra contains
`s` has an affine quotient. This finite-set assertion does not require the
Noetherian hypothesis; the subsequent existence of a stable index containing
that set does.

The implemented proof first obtains affineness of `E.R` from the given
cartesian square. Worker 1110's
`exists_fg_pushout_of_hasAffineQuotient` supplies rings `A₁`, `B₁` of finite
type over the integers, an étale faithfully flat map `A₁ → B₁`, and a
bijective presentation
`B₁ ⊗[A₁] Γ(E.U) → Γ(E.R)` with its target/source formula. Compose with the
inverse of `h.relationIso` to obtain the corresponding presentation of
`Γ(E₀.R) ⊗[Γ(E₀.U)] Γ(E.U)`. The target/source formulas for `relationIso`
identify its pure-tensor formula with the coaction formula. Étaleness of
`E₀.s` gives finite type of `Γ(E₀.R)` over `Γ(E₀.U)`.

Worker 266's `exists_bijective_level` supplies the finite set `s` and a
bijective presentation at every stable subalgebra containing it. Its
`hasAffineQuotient_of_bijective` criterion then gives the affine quotient of
the level relation. This criterion constructs a cartesian map to the kernel
pair of `Spec B₁ → Spec A₁` and applies the proved descent of affine
quotients. The relation is precisely the relation defining
`h.stableDiagram.obj (op i)`.

`exists_stable_affineQuotient_threshold` enlarges the finite set to a finitely
generated stable subalgebra, using stable exhaustion over the Noetherian
base. Every stable index above that index contains the finite set, so has
an affine quotient.

`exists_stable_affineQuotient_above` retains an arbitrary prescribed stable
index while obtaining an affine quotient. Directedness supplies a common
upper bound of that index and the threshold index.

`affineQuotientThreshold` chooses an index satisfying the threshold theorem.
`hasAffineQuotient_of_affineQuotientThreshold_le` is its property: every stable
index above the chosen one has an affine quotient.

The first level and the affine quotient of the original relation are
explicit inputs throughout. No claim about their existence is made.
