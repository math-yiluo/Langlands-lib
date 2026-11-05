# Galois-invariant real valuations over a Henselian valuation ring

Author: Worker 1651.

`Langlands.FieldTheory.HenselianRealGaloisProlongationStatement.{u,v}` is
an unproved proposition. It asserts that, for any field `K : Type u`, any
valuation `ν : Valuation K ℝ≥0` whose actual valuation subring is
Henselian, and any algebraic Galois extension `Ω : Type v`, there exists
a valuation `w : Valuation Ω ℝ≥0` with exact restriction `ν` and invariant
under every element of `Gal(Ω/K)`. The independent universe parameters
and infinite Galois extensions are included. `IsGalois K Ω` supplies
algebraicity as well as normality and separability.

The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 2.1.1 and Proposition 2.1.3, printed p.68 (PDF p.99), together
with the Galois-invariance observation on printed p.69 (PDF p.100).
The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The book cites Berkovich [Ber93, Proposition 2.4.3] for the equivalence
between Henselianity of the valuation ring and unique prolongation of
the real valuation to algebraic extensions.

This is a derived formulation in multiplicative real coordinates.
For a nontrivial valuation, taking negative logarithms on nonzero elements
passes to the additive convention of the source; exponentiation returns
the normalized multiplicative valuation. Uniqueness implies invariance
under field automorphisms fixing `K`, since composition with any such
automorphism is another prolongation. The trivial valuation is also
included: its extension assigning one to every nonzero element and zero
to zero has the stated properties. The proposition does not assert
uniqueness; it requests only existence and the invariance needed by the
norm argument. Proving the coordinate comparisons and the underlying
prolongation theorem remains a proof obligation.

The official 1 November 2024 corrections, source
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.24–25, do not modify these Section 2.1 assertions.

No completeness, discreteness, residue-field, perfectness,
characteristic or finiteness assumption is imposed. This general
valuation-theoretic bridge is a prerequisite for the exact Henselian
discrete norm criterion: apply it to the base-two realization of the
supplied integer valuation and to a separable closure. The generic
Henselianity of valuation rings of separably closed fields then supplies
the ambient Hensel property used by the norm machinery. The present
module proves none of these consequences.
