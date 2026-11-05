# Actual Artinian quotients of augmented noetherian local algebras

This is an internal algebraic construction for the Picard deformation
argument. It extends the quotient construction in `ArtinianQuotients` to
the positive maximal-ideal quotients of a ring that is only assumed
noetherian and local. The original ring need not itself be Artinian.
The results follow from ordinary ideal-quotient universal properties,
nilpotence in local Artinian rings, and Mathlib's noetherian local
Artinian criterion; no external representability assertion is used.

Fix a universe `u`, a commutative ring `k : Type u`, a field `K : Type u`
with a `k`-algebra structure, and a commutative local noetherian
`k`-algebra `R : Type u`. The data include a specified surjective
`k`-algebra homomorphism `ε : R →ₐ[k] K`. Write `m` for the maximal ideal
of `R`. Neither `R` nor any test is given a `K`-algebra structure or a
section of its residue augmentation.

`power_le_ker` uses the equality `ker ε = m` to show
`m^(n+1) ≤ ker ε`. The actual quotient lift
`augmentation ε hε n : R/m^(n+1) →ₐ[k] K` is surjective:
a preimage under `ε` supplies a quotient preimage. The quotient is
nontrivial because it maps to the field `K`. Locality descends along
the surjective quotient map, as does noetherianity.

`quotient_artinian` applies
`isArtinianRing_iff_isNilpotent_maximalIdeal`. The maximal ideal of the
quotient is the image of `m`; its `(n+1)`-st power is the image of
`m^(n+1)`, which is zero. Thus `test ε hε n` is an actual `ArtinianTest`
whose underlying algebra is literally `R/m^(n+1)` and whose specified
augmentation is the lift just constructed. Numbering starts at `R/m`.
`projection` is the actual scalar-preserving quotient map, and
`augmentation_projection` proves its exact augmentation triangle.

For `n ≤ p`, `transition ε hε hnp` is the actual quotient-factor arrow
from the `p`-th test to the `n`-th test. The private
`lift_comp_factor` lemma proves its augmentation compatibility by
precomposition with the quotient map. `toAlgHom_transition` exposes the
ordinary algebra map. `transition_surjective`, `projection_transition`,
`transition_refl`, and `transition_comp` prove surjectivity and the
projection, identity, and composition equations.

`ker_transition` identifies the kernel with the image of `m^(n+1)` in
`R/m^(p+1)`. For consecutive stages, multiplication by the source
maximal ideal gives the image of `m*m^(n+1) = m^(n+2)`, hence zero.
This proves `transition_succ_elementary` in the existing
`ArtinianTest.IsElementarySurjection` convention: a surjection with
maximal-ideal-annihilated kernel, allowing a zero kernel and imposing no
one-dimensional-kernel condition.

For any actual Artinian test `A`, let `α : R →ₐ[k] A.algebra` satisfy
`A.augmentation.comp α = ε`. The proof of `exists_bound` sends `m` into
the maximal ideal of `A.algebra` using the specified augmentations.
That target maximal ideal is nilpotent, so some positive power of `m`
lies in `ker α`. This lemma itself does not require noetherianity of
`R`. For any supplied bound `n`, `factor` is the quotient lift as an
actual augmentation-preserving test arrow. `factor_projection` proves
that precomposing its algebra map with `projection` gives exactly `α`.
Quotient algebra-homomorphism extensionality proves `factor_unique`.
Finally `exists_unique_factor` combines these results: there is a stage
at which exactly one test arrow has that specified composite.
Uniqueness is for the arrow at the chosen stage, not for the stage.

This module supplies the tests of a prospective noetherian local
deformation ring. It does not assume completeness or construct such a
ring, a hull, a formal family, an algebraization, or a smooth atlas.
