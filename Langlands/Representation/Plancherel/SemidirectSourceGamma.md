# The source open-cell constant in canonical semidirect coordinates

Author: Worker 200.

This derived adapter identifies the existing canonical semidirect coordinates
and product measure with the published Harish–Chandra integration engines.
It constructs the open-cell constant from that actual measure, proves its
source Iwasawa integral formula and, under the displayed geometric hypotheses,
proves positivity, finiteness and the associated integration formula. It does
not introduce a freely chosen normalization scalar or replace the existing
`openCellConstant`.

Source: Waldspurger, *La formule de Plancherel pour les groupes p-adiques*
(2003), I.1 (2), (3), printed pp.240–241/PDF pp.6–7. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source fixes subgroup Haar measures by mass one on intersection with the
fixed compact subgroup, uses `G = P K` and defines
`γ(P) = ∫_Ū δ_P(m_P(ū)) dū`. The adapter keeps each supplied measure and its
scale explicit. Its coordinate-identification steps are internal derived
content. It covers the source parabolic constant `γ(P)`; the identification
as a Levi-only constant `γ(G|M)` is a remaining obligation.

## Canonical coordinates and the actual measure

The underlying group is an arbitrary topological group. Its actual subgroups
satisfy `IsSemidirectDecomposition P M U`, with the canonical Levi projection
continuous. The published `h.coordinates hp : M × U ≃ₜ P` has forward map
`(m,u) ↦ m u` and inverse with first component `h.projection p` and second
component `(h.projection p)⁻¹ p`. This homeomorphism is reused directly.
The scalar Haar and coordinate constructions add no representation carrier,
local-field, characteristic or splitness restriction. The group universe is
arbitrary.

`semidirectCoordMem` proves that the coordinate product lies in the actual
`P`. `isHomeomorph_leviUnipotentCoord_semidirect` identifies the exact
`leviUnipotentCoord` used by `ParabolicHaar` with the published homeomorphism.
`semidirectSourceParabolicMeasure` is the pushforward of the supplied product
measure `μM.prod μU` along those canonical coordinates. Its equality with
`leviUnipotentMeasure` is definitional, including the scale.

For s-finite Haar measures on `M` and `U`, with `U` second countable,
`semidirectSourceParabolicMeasure_isHaarMeasure` applies the existing
`leviUnipotentMeasure_isHaarMeasure` using the proved coordinate homeomorphism
and the normalizer containment from the actual semidirect decomposition.
No independently chosen measure on `P` is assumed to equal this one.
If membership in the compact open subgroup factors as
`m u ∈ K ↔ m ∈ K ∧ u ∈ K`, and the two supplied measures have mass one on
their intersections with `K`,
`semidirectSourceParabolicMeasure_compact` proves that the constructed
parabolic measure has mass one on `P ∩ K`. This applies the published product
intersection formula. The equality itself has the weaker measure hypotheses
shown in its Lean declaration.

## The source Iwasawa integral

`semidirectSourceGamma` is the existing nonnegative `openCellConstant` of the
constructed parabolic product pushforward, the supplied measure `μV` on an
actual subgroup `V`, and the fixed subgroup `K`. The raw definition makes
sense for supplied measures; its later theorems state the Haar, normalization
and geometry hypotheses they use. Its defining integral contains no chosen
Iwasawa factors.

For `G = P K`, `sourceIwasawaParabolicFactor` chooses an actual factor `p(g)`
from this displayed factorization. `sourceIwasawaCoordinates` applies the
inverse canonical semidirect homeomorphism to `p(g)`. Its specification is
proved by cancelling the homeomorphism and the fixed group factorization.
The proof keeps the choice's input fixed when multiplying the factorization
by `p(g)⁻¹`.

For the modulus formula assume additionally that `G` is locally compact,
`U` is closed, both supplied factor measures are right invariant as well as
s-finite, and `μU` is Haar. The required regularity of `μU` follows from its
local compactness and second countability. The closed-subgroup wrapper
supplies local compactness of `U`; the published actual Haar modulus theorem
gives `isConjModulus_semidirect_closedCharacter` for precisely
`HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer`. This is the
same actual normalizing character used by canonical normalized induction.
There is no arbitrary character premise replacing it.

`semidirectSourceGamma_eq_lintegral_of_coordinates` applies the published
`openCellConstant_leviUnipotentMeasure`, under the same compact splitting and
mass-one factor normalizations. It proves the gamma integral for *any*
coordinate map `ℓ : V → M × U` whose product is a parabolic factor of `v⁻¹`.
Consequently the integral is independent of such choices. Choosing the
actual coordinates above and assuming the supplied `μV` inversion invariant,
`semidirectSourceGamma_eq_iwasawa_integral` changes `v` to `v⁻¹` and gives
exactly the nonnegative source integral of `δ_P(m_P(v))`. For source opposite
radical `V = Ū` and its normalized Haar measure this is I.1 (3). The Lean
statement is an `ENNReal` lower integral; separate pointwise regularity or
Bochner-integrability assertions for chosen component maps are not claimed.

## Positivity, finiteness and integration

For these results `P` and `V` are locally compact and second countable, the
ambient supplied measure `μ` is Haar and right invariant, `μV` is Haar, and
`K` is open compact. The actual open-cell map `(p,v) ↦ p v⁻¹` is an open
embedding whose complement has `μ`-measure zero. Both geometric hypotheses
remain explicit obligations. They are not consequences of a semidirect
decomposition asserted by this adapter.

`semidirectSourceGamma_ne_zero_ne_top` uses the proved Haar property of the
constructed parabolic measure, positive mass of nonempty open `K`, finite
mass of compact `K` and the published open-cell theorem. Thus the actual
constant is nonzero and finite; neither property is an input.
`lintegral_eq_semidirectSourceGamma_inv_mul` gives the nonnegative integration
formula in Levi-then-radical order, with factor `μ(K) γ(P)⁻¹`.
`lintegral_eq_semidirectSourceGamma_normalized` assumes the source ambient
normalization `μ(K)=1` and removes that exact factor. The existing
`lintegral_levi_unipotent_eq` supplies the separately published conversion to
radical-then-Levi order with `δ_P(m)⁻¹`; it is not reproved here.

Actual rational-point realizations of compact splitting, open-cell embedding
and conullness, the source opposite-radical data and normalized subgroup
measures, parabolic independence of gamma, the rank-one product defining
`c(G|M)`, spectral density and all Plancherel conclusions remain separate
obligations. These open obligations are not classified as permitted permanent
Chapter V structural inputs by this unit.
