# Inverse-unit Weyl conjugation for powered root maps

This is internal derived content for the affine split Isogeny Theorem. It
combines the published genuine-root rescaling rigidity and negative-conjugation
argument with an actual additive-line power map. It does not prove the host
Isogeny Theorem.

Let `R` be a commutative local ring, let `G` be affine over `Spec R`, and let
`i` be a closed coordinate split torus. Fix actual normal simple-root data
`IsNormalSimpleData i P b W u`. This includes reductivity, fibrewise maximality,
the full fibrewise root datum, genuine opposite simple-root parametrizations,
their prescribed Weyl reflections, descending words, and rank-one normality.
Let `F : Ga R ⟶ Ga R` be an actual group homomorphism with the all-test formula
`x ↦ x^q`, for a natural number `q`.

For a simple root `c` and roots `a` and `s_c a` both positive, suppose
conjugation by the genuine simple Weyl point carries `F ≫ v_a` to
`scaleHom κ ≫ F ≫ v_(s_c a)`, where `v` is the genuine target Weyl family
and `κ` is any unit of the original ring. Then the same conjugation carries
`F ≫ v_(-a)` to `scaleHom κ⁻¹ ≫ F ≫ v_(-s_c a)`.
`PoweredNegativeConjugationStatement` states this implication in every universe;
`poweredNegativeConjugation` proves it.

The implementation first proves that scaling before `F` equals scaling by
the `q`-th power after `F`, on every scheme test. Inner conjugation commutes
with any additive-line precomposition. Evaluating the assumed powered
positive-root equality at the point one over `Spec R` identifies the value
of the genuine conjugated map at one with the target map at `κ^q`.
Both maps are genuine parametrizations of the same target root, so the
published `eq_scaleHom_of_base` identifies their whole morphisms, with
rescaling unit `κ^q`. The genuine `IsNormalSimpleData.conj_neg` theorem gives
the inverse unit `(κ^q)⁻¹`. Precomposing by `F` and moving scaling through
the power converts it to the desired original unit `κ⁻¹`.

The auxiliary theorem `conj_neg_precompose_power_of_partner` explicitly
retains partner uniqueness and inverse-unit rescaling. The main theorem
`conj_neg_precompose_power` discharges both with the published actual-root
theorems `rootPartner_unique` and `isWeylPoint_rescale`, using the closed
torus assumption and the geometric data already in `IsNormalSimpleData`.

No powered map is assumed to represent a root subgroup. The proof uses no
injectivity of the power operation on `R` or on test-ring points, and no
reducedness or characteristic restriction. A common power is explicit:
in an application to a root-datum isogeny, reflection invariance of its
root factors supplies that common power. Reindexing source and target
families and words is a separate application of their transport identities.
