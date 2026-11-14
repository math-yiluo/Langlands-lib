# Rank-one Galois descent of an inverse-orbit-matched standard parabolic

Author: Worker 17.

This internal helper module belongs to the proof of the rank-one parabolic rational-orbit
height bound (`Langlands.Global.RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement`).
It contains the algebraic part of Springer's descent argument in semisimple rank one
(T. A. Springer, *Reduction theory over global fields*, 1994, §3.6, pp. 215–216). In
Springer's notation, an element `g ∈ G(A, k)¹` is written over the splitting field `l` as
`g = x t u γ`, and in the "small root" case the parabolic subgroup

`Q = ⋂_{s ∈ Γ} Int(γ⁻¹) P(s.α)`

of `G_l` is `Γ`-stable, hence defined over `k`. Springer then says:

- "the parabolic k-subgroup Q must be k-conjugate to P. This means that, after
  multiplying g on the right by an element of G(k), we may assume that Q = P";
- "if Q = P the element γ must lie in P(l)".

The two main theorems below formalize these two sentences. Springer gives no proof of
them; the statements are adapted to the Library's conventions and the proofs are ours
(provenance: derived). The adaptation differs from Springer in one point. Springer's
Borel subgroup `B` of `G_l` lies in the minimal `k`-parabolic `P`. Here the split torus and
the minimal standard parabolic `P(ν)` of `G_L` are arbitrary, so `P(ν)` need not lie in
`(P_F)_L`. The second theorem therefore fixes a rational point `m₀ ∈ G(L)` with
`m₀ P(ν) m₀⁻¹ ⊆ (P_F)_L` and concludes `δ q⁻¹ = π m₀` with `π ∈ (P_F)_L(L)`, instead of
`γ ∈ P(l)`. Springer's appeal to the unique Galois orbit of simple roots (his reference [4])
is not needed: the descended parabolic is shown proper directly.

The module adds no hypothesis or axiom. It uses the published Galois descent of parabolics
`Descent.parabolicGaloisDescent`, the published inverse-orbit-matching lemma
`SubgroupFunctor.galoisTransport_intersection_eq_of_inverse_orbit_matching`, and the helper
module `Langlands.GroupScheme.Rational.RankOneParabolicConjugacy` (same proof, same author).

## Setting and conventions

`F` and `L` are fields in universe `u` with `[Algebra F L]`. The descent theorems also
assume `[FiniteDimensional F L]` and `[IsGalois F L]`. `G` is a group scheme over `Spec F`
with `[IsAffineHom G.X.hom]`, and `G_L` is `(GroupScheme.baseChange (algebraBaseMap F L)).obj G`,
also assumed to have affine structure map. Over `F`, `iF : TF.toGrp ⟶ G` is a maximal split
torus (`IsMaximalSplitTorus iF`) with a generic cocharacter `νF` (`IsGenericCocharacter iF νF`).
The minimal standard `F`-parabolic is `P_F = standardParabolic iF νF ∅`, the range of the
closed immersion `Standard.parabolicHom iF νF ∅`. *Rank one* means
`simpleRelativeRoots iF νF = {αF}`. Over `L`, `i : T.toGrp ⟶ G_L` is a maximal split torus
of `G_L` with a generic cocharacter `ν`, and `Δ = simpleRelativeRoots i ν`.

For a rational point `h`, `G.innerIso h` is `x ↦ h x h⁻¹`, and `Φ.comap (G.innerIso h).hom` is
`h⁻¹ Φ h`. So `P ≤ Φ.comap (G.innerIso h).hom` means `h P h⁻¹ ⊆ Φ`. The base change of a
rational point `δ ∈ G(F)` is `δ_L = baseChangeBasePoint (algebraBaseMap F L) G δ`.

**Inverse-orbit matching.** A family `J : Gal(L/F) → Set (characterLattice T)` with
`J σ ⊆ Δ`, and a rational point `q ∈ G_L(L)`, are *matched* when for every `σ`

`range (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫ (G_L.innerIso q⁻¹).hom) σ)
  = range (Standard.parabolicHom i ν (J 1) ≫ (G_L.innerIso q⁻¹).hom)`,

that is, the Galois translate by `σ` of `q⁻¹ P_{J σ⁻¹} q` is `q⁻¹ P_{J 1} q`. This is the
hypothesis `hmatch` of both descent theorems. It is the matching condition appearing in
Worker 5268's statement `HasTwistedOverlapMatching` (Springer's §3.5 factorization) and in
the published `IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching`.

## Declarations

### `SubgroupFunctor.range_comp_le_iff`

For `f : K ⟶ H`, `g : H ⟶ G` and a subgroup functor `Φ` of `G`,
`range (f ≫ g) ≤ Φ ↔ range f ≤ Φ.comap g`.

*Proof.* Both directions unfold membership in a range (`mem_range`) and in a preimage
(`mem_comap`) and reassociate the composite.

### `isParabolicSubgroup_baseChange_standardParabolicHom_empty`

If `G` is connected reductive, the base change to `L` of
`Standard.parabolicHom iF νF ∅` is a parabolic subgroup of `G_L`. (No finiteness or Galois
hypothesis on `L/F` is needed.)

*Proof.* `Standard.parabolicHom iF νF ∅` is a closed subgroup
(`Standard.isClosedSubgroup_parabolicHom`) whose range is `standardParabolic iF νF ∅`
(`Standard.isRepresentedBy_parabolicHom`), which equals the dynamic parabolic of
`ν ≫ iF` by the first part of `standardParabolicEndpoints`. Hence it is parabolic by
`isParabolicSubgroup_of_range_eq_dynamicParabolic`. Parabolicity is preserved by field
extension: `parabolic_baseChange_of_structural_statements`, applied to the published
`parabolicDynamic` and `connectedReductiveFieldExtensionStatement`.

### `range_baseChange_standardParabolicHom`

For every `J`, the range of the base change of `Standard.parabolicHom iF νF J` equals
`(standardParabolic iF νF J).baseChange (algebraBaseMap F L)`.

*Proof.* `SubgroupFunctor.range_baseChangeHom` and `Standard.isRepresentedBy_parabolicHom`.

### `exists_rational_minimalParabolic_le_comap_of_inverse_orbit_matching`

Assume `G` and `G_L` are connected reductive, `G` has `F`-rank one, and `J`, `q` are matched
with `J 1 = Δ \ {α}` for some `α ∈ Δ`. Then there is `δ ∈ G(F)` with

`Dynamic.parabolic (ν ≫ i) ≤ ((P_F).baseChange (algebraBaseMap F L)).comap (G_L.innerIso (δ_L * q⁻¹)).hom`,

that is, `(δ_L q⁻¹) P(ν) (δ_L q⁻¹)⁻¹ ⊆ (P_F)_L`. This is Springer's "Q must be k-conjugate
to P".

*Proof.* Put `e = G_L.innerIso q⁻¹`, `p = Standard.finiteParabolicIntersectionHom i ν J`
(the inclusion of `⋂_σ P_{J σ}`), and `P σ = range (Standard.parabolicHom i ν (J σ) ≫ e.hom)`.

1. `p ≫ e.hom` is parabolic (`Standard.isParabolicSubgroup_finiteParabolicIntersectionHom`
   and `IsParabolicSubgroup.comp_iso`), and its range is `intersection P`
   (`Standard.range_finiteParabolicIntersectionHom_comp_iso`). This is Springer's `Q`.
2. `hmatch` rewritten by `SubgroupFunctor.descentTransport_range` says
   `galoisTransport σ (P σ⁻¹) = P 1` for all `σ`. By
   `galoisTransport_intersection_eq_of_inverse_orbit_matching`, `intersection P` is
   Galois-invariant, so the range of every Galois translate `radicalGaloisHom (p ≫ e.hom) σ`
   is the range of `p ≫ e.hom`.
3. `Descent.parabolicGaloisDescent` gives an `F`-parabolic `D.inclusion` whose base change has
   the same range as `p ≫ e.hom` (`D.recovery`, `SubgroupFunctor.range_iso_comp`).
4. `D.inclusion` is proper. Otherwise its range is `⊤`; then the range of `p ≫ e.hom`, hence
   of `p` (`range p = (range (p ≫ e.hom)).comap e.hom`), is `⊤`, so
   `standardParabolic i ν (J 1) = ⊤` (`Standard.range_finiteParabolicIntersectionHom`,
   member `1` of the intersection). By the order isomorphism `standardParabolicOrder` and the
   third part of `standardParabolicEndpoints`, `Δ ⊆ J 1 = Δ \ {α}`, contradicting `α ∈ Δ`.
5. By `exists_range_eq_comap_standardParabolic_empty_of_rankOne` (rank one), there is `δ`
   with `range D.inclusion = (P_F).comap (G.innerIso δ).hom`. Base change
   (`SubgroupFunctor.range_baseChangeHom`, the published
   `SubgroupFunctor.comap_baseChange` of `Langlands.GroupScheme.Derived.CentralIntersectionReduction`,
   `baseChange_innerIso_hom`) gives
   `range (p ≫ e.hom) = ((P_F)_L).comap (G_L.innerIso δ_L).hom`.
6. `Dynamic.parabolic (ν ≫ i) = standardParabolic i ν ∅ ≤ standardParabolic i ν (Δ ∩ ⋂_σ J σ) = range p`
   (`standardParabolicEndpoints`, `Standard.isRepresentedBy_parabolicHom`,
   `standardParabolicOrder`). Combining with steps 4–5 and `SubgroupFunctor.comap_comp`,
   `innerIso_mul_hom` gives the claim.

### `exists_rational_mul_eq_of_inverse_orbit_matching`

Same hypotheses, together with a rational point `m₀ ∈ G_L(L)` satisfying
`Dynamic.parabolic (ν ≫ i) ≤ ((P_F)_L).comap (G_L.innerIso m₀).hom`. Then there are
`δ ∈ G(F)` and `π` in the rational points of the range of the base change of
`Standard.parabolicHom iF νF ∅` (that is, `π ∈ (P_F)_L(L)`) with `δ_L * q⁻¹ = π * m₀`.
This is the coset form of Springer's "if Q = P the element γ must lie in P(l)".

*Proof.* The previous theorem gives `δ`. Both `m₀` and `δ_L q⁻¹` conjugate `P(ν)` into the
range of the base-changed inclusion, which is parabolic
(`isParabolicSubgroup_baseChange_standardParabolicHom_empty`) and equals `(P_F)_L`
(`range_baseChange_standardParabolicHom`). The coset lemma
`exists_mul_eq_of_minimalParabolic_le_comap` over `L` gives `π` with `δ_L q⁻¹ = π m₀`.

## Scope

All results are purely algebraic and hold for an arbitrary finite Galois extension of
fields. The adelic consequences are drawn in the companion module
`Langlands.Global.AdelicRankOneGaloisOrbitHeight`.
