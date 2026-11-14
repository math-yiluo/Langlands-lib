# Apartment charts along a field extension, and the Galois coefficient charts

Author: Worker 47 (Task 6502).

This module constructs the per-automorphism coefficient charts on the unramified apartment and
assembles them into the moving semilinear action data of the Galois action. It uses the generic
chart layer `KPApartmentCoefficientChart`. Every statement holds for an arbitrary supplied
building datum. Nothing here assumes a torus defined over `F`.

## Character values (`section TorusValues`)

- `torusCharacterValue_congr`: transporting a character along an isomorphism `e : S ≅ S'` of
  commutative group schemes, `characterLattice.congr e χ`, and evaluating it at the image of
  `t` under `e` gives `χ(t)`.
- `torusCharacterValue_baseChange`: for a field extension `k → K`, the base-changed character
  `characterLattice.baseChange (algebraBaseMap k K) S χ`, evaluated at the scalar extension of
  `t ∈ S(k)`, is the image of `χ(t)` in `Kˣ`. This follows from the Library's
  `rationalCharacterEval_extend`.

## Field charts (`IntegerValuationBuildingData.FieldChart`, `exists_fieldChart`)

Take fields `k`, `K` with `[Algebra k K]`, integer-valued building data `B₁` over `k` (group
`G₁`) and `B₂` over `K` (group `G₂`), and a map `Φ : G₁(k) → G₂(K)`. A `FieldChart B₁ B₂ Φ`
consists of the following data:

- a bijection `β` between the character lattices of the tori;
- a bijection `τ : S₁(k) ≃ S₂(K)` of torus points;
- a map `a` from apartment points of `B₂` to apartment points of `B₁`, with the transport
  formula `(a x)_χ(u) = x_{β χ}(Φ u)`;
- the torus relation `Φ(i₁ t) = i₂(τ t)`;
- the character relation `(β χ)(τ t) = χ(t)`, read in `Kˣ` through `k → K`.

`exists_fieldChart` assumes the following:

- `k → K` is bijective and preserves the integer orders;
- the order of `v` is not identically zero;
- the base change to `K` of the torus of `B₁` is maximal split;
- `f_G : G₁ ×_k K ≅ G₂` is an isomorphism;
- `Φ₀` is a map with `Φ₀(u) = f_G(u_K)` for all `u` (the hypothesis `hΦ₀`).

Under these assumptions it gives `g ∈ G₂(K)` and a field chart along `u ↦ g Φ₀(u) g⁻¹`. The
proof follows the published proof of axiom 4.1.17 across a field extension
(`ValuationBuildingData.exists_isEquivariantBuildingIso_of_fieldExtension`), but it keeps the
explicit family formulas instead of chart isomorphisms:

1. The torus of `B₂` is conjugated onto the base change of the torus of `B₁` (by
   `maximalSplitTorusConjugacy` over `K`). This gives `e` and `g` with
   `i₁,K ≫ f_G ≫ Int(g) = e ≫ i₂`.
2. The apartment class of `B₂` is transported along `(e, f_G ≫ Int g)⁻¹`
   (`KPApartmentData.transport`). It satisfies V 6 for the base-changed centralizer
   (`CentralizerDatum.baseChangeOfBasedIso` and `IsOmegaCompatible.transport_basedIso`).
3. Field restriction (`IntegerValuation.fieldRestrictApartment`) yields an apartment class of
   `G₁` that satisfies V 6. By uniqueness of omega-compatible apartment classes
   (`integerOmegaCompatibleApartmentUniqueness`), it equals the apartment class of `B₁`.

Hence `a x := fieldRestrict (transport x)` lands in the apartment of `B₁`. The formulas follow
from `transportEquiv_apply` and `fieldRestrict_apply`, with `β = (base change) ≫ congr e`
and `τ = e ∘ (scalar extension)`. The scalar extension is bijective on torus points
(`rationalExtend_bijective_of_bijective`), and `characterLattice.baseChangeEquiv` is a
bijection for split tori.

## Galois charts (`section GaloisCharts`)

Let `F → K` be a field extension, `σ ∈ Aut(K/F)` and `G` a group over `F`.

- `unitsCoeff F σ : Kˣ → Kˣ` is the map `σ⁻¹` on units. `unitsCoeff_one` and `unitsCoeff_mul`
  (`s_{στ} = s_τ ∘ s_σ`) record that these maps compose contravariantly.
- In `section Twisted`, `K` carries an arbitrary algebra structure over itself with
  `halg : algebraMap K K = σ⁻¹` pointwise:
  - `baseMap_eq_galoisBaseMap`, `baseMap_self_over`: its base map is `Spec σ⁻¹`, and it lies
    over `Spec F`.
  - `twistIso halg : G_K ×_{K,σ⁻¹} K ≅ G_K` is the Library's canonical descent isomorphism
    `descentBaseChangeIso`.
  - `twistIso_rationalExtend`: scalar extension along `σ⁻¹` followed by `twistIso` is the
    coefficient conjugation `rationalConjugate F K G σ⁻¹`. It is checked after `pullback.fst`
    through `baseChangeCoeffEquiv`, using `descentBaseChangeIso_hom_fst`,
    `baseChangeBasePoint_fst` and the defining property `baseChangeCoeffEquiv_rationalConjugate`.
  - `selfAlgebra_isMaximalSplitTorus`: base change along `Spec σ⁻¹` keeps the torus maximal
    split (`IsMaximalSplitTorus.baseChange_fieldIso`).
  - `exists_selfFieldChart`: this is `exists_fieldChart` with `B₁ = B₂ = C`,
    `f_G = twistIso` and `Φ₀ = rationalConjugate F K G σ⁻¹`.
  - `exists_coefficientChart_of_algebra`: turns the field chart into a
    `C.apartment.CoefficientChart (rationalConjugate F K G σ) (unitsCoeff F σ)`. With
    `θ = rationalConjugate σ`, take `c = θ(g)`. Then `c⁻¹ θ(u) c = Φ⁻¹(u)` for
    `Φ(u) = g θ⁻¹(u) g⁻¹`, since `rationalConjugate σ⁻¹` inverts `rationalConjugate σ`. The
    chart's `a_val`, `torus` and `char` fields become the coefficient-chart fields.
- `twistAlgebra F σ` is the algebra structure `RingHom.toAlgebra σ⁻¹`. `exists_coefficientChart`
  instantiates the previous theorem with it. Its hypotheses are an integer valuation `v` of `K`
  whose order is invariant under `σ⁻¹` and not identically zero, and a building datum `C` of
  `G_K` over `v`.

The twisted algebra structure stays a variable throughout `section Twisted`. Statements made
directly about the concrete structure `RingHom.toAlgebra σ⁻¹`, and rewriting chains through
the descent isomorphism, led to kernel checks that did not terminate in practice.

## The unramified case (`namespace MaximalUnramified`)

Here `K = inertiaFixedField F` and `C : BuildingData F (baseChanged F K G)` is an arbitrary
supplied datum.

- `exists_coefficientChart C σ`: a coefficient chart exists for every `σ ∈ Aut(K/F)`. The
  order is Galois invariant by `order_galois`, and the mapped uniformizer has order one by
  `exists_order_eq_one`.
- `oneChart C`: the chart along `rationalConjugateAction F K G 1`, with `c = 1`, `β = id`,
  `a = id` and `τ = id`.
- `coefficientChart C σ`: `oneChart C` at `σ = 1`, and a chosen chart otherwise.
  `coefficientChart_one_c` and `coefficientChart_one_a` record the normalization.
- `coefficientActionData C`: the published
  `ApartmentQuotient.MovingSemilinearActionData C.apartment.sharpFixerFamily
  (rationalConjugateAction F K G)`. It is obtained from
  `KPApartmentData.CoefficientChart.movingSemilinearActionData`, using that `K` is infinite
  (it contains the local field `F`), that `G_K` is connected reductive, and that the torus of
  `C` is a split subtorus. Its correction and apartment maps are those of `coefficientChart C σ`
  (`coefficientActionData_correction`, `coefficientActionData_apartment`). For each `σ`, the
  root-norm identity `(coefficientChart C σ).norm_vsub` of the chart layer supplies the
  isometry input.

## Provenance

This is internal infrastructure for the Galois (coefficient) action on the reduced building
over the maximal unramified extension, used in Kaletha–Prasad's unramified descent. The
mathematical content is standard: `σ` transports the apartment of a maximal split torus `S` to
the apartment of `σ(S)`, and conjugating `σ(S)` back to `S` gives a semilinear map of the
apartment. The Lean route is new. It obtains the transported apartment by field restriction
along `σ⁻¹` and identifies it by uniqueness of omega-compatible apartments, following the
Library's proof of axiom 4.1.17 across field extensions. This avoids any torus defined
over `F`.
