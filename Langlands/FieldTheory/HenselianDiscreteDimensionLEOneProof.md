# The norm criterion for Henselian discrete fields with algebraically closed residue

Authors: Worker 1651 and Worker 1607.

`Langlands.FieldTheory.henselianDiscreteDimensionLEOne.{u}` proves the
exact published proposition
`Langlands.FieldTheory.HenselianDiscreteDimensionLEOneStatement.{u}`.
It assumes precisely a surjective integer-valued valuation, Henselianity
of its actual valuation subring, and algebraic closedness of the actual
residue field. The conclusion is the actual determinant unit-norm
criterion `HasDimensionLEOne K`. There is no completeness, perfectness,
completion-separability or characteristic premise. The field universe
is arbitrary.

## The implemented proof

Compose the supplied integer valuation with the base-two real
exponential. `IntegerValuationRealization` proves that the valuation
subring equals the original one, transports Henselianity and the residue
root property by that equality, and derives a uniformizer directly from
surjectivity.

The proved `henselianRealGaloisProlongation` supplies a normalized,
Galois-invariant real valuation on the separable closure. Its proof first
constructs a normalized prolongation using an algebraic closure of the
completion; this constructs a complete auxiliary field and imposes no
completeness premise on K. To prove finite Galois invariance, a finite
family separator is symmetrized over the actual decomposition subgroup.
The resulting product has one small conjugate and all other conjugates
of value one. Its integral minimal polynomial has a simple residue root
at zero, which Hensel lifting descends to K. This excludes every
automorphism outside the decomposition subgroup. Restriction to finite
normal subextensions gives the infinite Galois invariance. The trivial
valuation is handled directly. These steps are implemented in the paired
prolongation, separation, small-conjugate and finite-invariance modules.

The valuation ring of the separably closed ambient field is Henselian by
the published `sepClosed_henselian`. Together with the original residue
root property and uniformizer, this verifies every field of `AmbientHyp`.

For arbitrary finite separable E/K and finite Galois L/E, form the
composite K-algebra on L. Transitivity of separability provides an
embedding L into the chosen separable closure of K (`IsSepClosed.lift`).
The proof constructs the E- and L-algebra structures and every required
scalar tower on that ambient field explicitly. Worker 1607's proved
`AmbientHyp.surjective_unit_norm` then gives surjectivity of precisely
`Units.map (Algebra.norm E : L →* E)`.

The full-norm helpers first prove the cyclic prime-degree case using an
element whose norm has uniformizer value, together with valuation-one
norm surjectivity. Prime-power induction uses normal subgroups of prime
index and determinant-norm transitivity. For an arbitrary finite Galois
group, Sylow fixed fields show that every quotient class modulo the norm
subgroup is killed by an integer prime to each specified prime. Its
order has no prime divisor, so the quotient is trivial. Zero is handled
separately where field norm surjectivity is used. The final conclusion
concerns all nonzero field elements, with no valuation-one restriction.

## Source and scope

The original theorem is Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Corollary 2.3.7, printed p.81/PDF p.112. The norm
criterion occurs in Section 2.3, printed pp.78–79/PDF pp.109–110; the
Henselian setup is on printed p.80/PDF p.111. The registered source
`kaletha-prasad-2023-bruhat-tits-new-approach` has SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The official 1 November 2024 corrections, registered
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp.24–25, do not amend Section 2.3 or add perfectness of K.

The implemented proof is an alternative algebraic norm argument. It
proves the valuation prolongation and norm conclusions directly from the
stated ring and residue hypotheses, rather than assuming the source's
cohomology or completion-comparison implications. The exact target and
its imported Lean/Markdown pairs remain unchanged. All new helper
modules carry paired explanations, and no additional premise remains in
the final theorem.
