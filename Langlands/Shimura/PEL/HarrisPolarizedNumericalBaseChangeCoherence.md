# Coherence of actual numerical Harris polarized pullback

This derived module proves identity and composition for the existing
pointed numerical Harris polarized class and tower pullbacks. It adds
presentation-equality transports and restricts the determinant coherence
laws through the injective numerical subtype inclusion. The maps compared
are exactly `classBaseChange` and `classTowerBaseChange` in
[HarrisPolarizedNumericalBaseChange](HarrisPolarizedNumericalBaseChange.md).

Fix the central simple unitary datum `D` on `A`, the totally real number
field `E`, its CM quadratic extension `F`, signature charts `C` and their
CM-section proof `hΦ`. The displayed rational and field scalar towers
remain. Also fix a CM number field `L` with an `L`-algebra structure on `F`.
These parameters are those of the existing numerical construction; the
module asserts no additional compositum or imaginary-quadratic condition.
All arithmetic types and schemes have universe zero.

The existing numerical `IsoClass` is a subtype of determinant-compatible
Harris polarized classes. Its image predicate requires one representative
with the determinant condition, actual relative dimension
`[E : ℚ] * n²` and the all-chart central Lie trace formula. Dimension
means the actual `SmoothOfRelativeDimension` predicate on the abelian
scheme's structural morphism. The trace formula uses its rational
differential on every finite free Lie chart and smaller open. The
representative's actual polarization and compatible level orbit remain
part of the ambient polarized class.

Two independently supplied structural maps occur:
`s : S ⟶ Spec (D.kottwitzCocharacterReflexField C)` for determinant
coefficients, and `p : S ⟶ Spec F` for central trace coefficients.
No relation between them is imposed. Both are composed with the actual
base morphism by the existing pullback.

All named tensor comparison, composition, unit, associativity, left-unitor
and symmetry propositions; Picard-zero pullback, Mumford-bundle and
universal-base-change propositions; dual abelian naturality and
polarization base-change propositions remain explicit. Identity retains
`LieBaseChangeNaturalityStatement S`; composition retains it on `S` and
the intermediate base `T`. The finite Weil transition and torsion
finite-etale propositions, rational profinite-integer/finite-adele
comparison, invertibility of every positive indexed torsion order,
finite etale roots of unity and ordered-pair dual additivity remain
inputs on their applicable bases. Bases are quasi-separated, and the
point has source `Spec Ω` for a field `Ω`, with the displayed
finite-fibre witnesses on finite-etale covers. No flatness or reducedness
assumption is added.

The dual families are the existing constrained `PositivePullbackDualData`
on each source object's actual abelian-scheme pullback. They retain the
dual construction and evaluation data; they do not provide a chosen
output class or a coherence equation. Composition quantifies the families
for `b`, `c` and `c ≫ b` independently.

`classPresentationEq` transports equal reflex maps `s = v`, equal CM-field
maps `p = q`, and equal points `t = r` on the same scheme. Eliminating
these equalities makes the transport the identity on the existing
numerical subtype. Proof irrelevance handles the finite-fibre witnesses.
`classPresentationEq_val` identifies its determinant-class value with
`harrisClassPresentationEq` at the reflex and point equalities. Changing
the numerical structural-map presentation therefore changes no underlying
determinant class. `classTowerPresentationEq` gives the corresponding
equality transport on the existing original-index tower; its component
formula is `classTowerPresentationEq_app`.

For identity pullback the source has structures `s`, `p` and point
`t ≫ 𝟙 S`; the target has structures `𝟙 S ≫ s`, `𝟙 S ≫ p`
and point `t`. `classBaseChange_id` identifies the existing map with
presentation transport along `(Category.id_comp s).symm`,
`(Category.id_comp p).symm` and `Category.comp_id t`. Function and
subtype extensionality reduce the equation to
`harrisClassBaseChange_id` at the underlying determinant class, using
the transport's value formula. Extensionality at every original level
and class proves `classTowerBaseChange_id`.

For `b : T ⟶ S`, `c : R ⟶ T` and `t : Spec Ω ⟶ R`, successive
pullback starts at point `(t ≫ c) ≫ b` and ends over structural maps
`c ≫ (b ≫ s)` and `c ≫ (b ≫ p)`. Direct pullback starts at
`t ≫ (c ≫ b)` and ends over `(c ≫ b) ≫ s` and `(c ≫ b) ≫ p`.
There are finite-fibre witnesses at all four displayed source and
intermediate points, including `t` and `t ≫ c`.

`classBaseChange_comp` proves
`F_c ∘ F_b = moveTarget ∘ F_direct ∘ moveSource` at every level.
The source transport uses reflexive structural equalities and
`Category.assoc t c b`. The target transport uses
`Category.assoc c b s`, `Category.assoc c b p` and the reflexive point
equality. Function and subtype extensionality and the underlying-value
formulas reduce this to `harrisClassBaseChange_comp` at the underlying
determinant class. `classTowerBaseChange_comp` proves
`F_b ≫ F_c = moveSourceTower ≫ F_direct ≫ moveTargetTower` by evaluating
at each original level and numerical class. The equality concerns the
existing tower on the original Harris transporter category, including
its subgroup and Hecke transporter arrows.

The provenance is internal: equality elimination defines the transports,
and the actual determinant coherence laws give equality after forgetting
the numerical subtype. The existing maps preserve the image using the
same pulled-back representative, so no dimension-invariance assertion
for arbitrary rational isomorphisms is needed. The original-source
conventions and citations remain those documented in
[HarrisNumericalWeilTower](HarrisNumericalWeilTower.md). This module makes
no new original-literature claim.

The result is pointed coherence under the stated construction premises.
It supplies no comparison of the two independent structural maps, normalized
CM restriction, point independence, unpointed moduli functor,
representability, canonical model, representing scheme levels or
coefficient descent. Those constructions remain in the broader task.
