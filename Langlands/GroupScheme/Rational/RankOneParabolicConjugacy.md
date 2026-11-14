# Conjugates of the minimal standard parabolic inside a parabolic, and rank one

Author: Worker 17.

This module proves three facts about parabolic subgroups of a connected reductive group over a
field. They are the two group-theoretic steps of Springer's descent argument in the rank-one case
(Springer 1994, *Reduction theory over global fields*, §3.6, pp. 215–216):

- "the parabolic k-subgroup Q must be k-conjugate to P";
- "if Q = P the element γ must lie in P(l)".

Springer quotes both facts as known. Here they are derived from three published Library
theorems: the dynamic description of parabolics `parabolicDynamic`, the standard-parabolic
classification `standardParabolicClassification`, and self-normalization
`parabolicSelfNormalizer`. The module adds no new hypothesis or axiom.

## Setting and conventions

Throughout, `k` is a field in universe `u` and `G` is a group scheme over `Spec k` with
`hG : IsConnectedReductive G`. Also, `i : T.toGrp ⟶ G` is a maximal split torus
(`IsMaximalSplitTorus i`) and `ν` is a cocharacter that is generic for `i`
(`IsGenericCocharacter i ν`). The minimal standard parabolic is
`P₀ = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)`. By the first part of the published
`standardParabolicEndpoints`, it equals `standardParabolic i ν ∅`. The Lean statements below
use the form `Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)` for the hypotheses and
`standardParabolic i ν ∅` in the conclusion of the last declaration.

A *rational point* is an element of `GroupScheme.rationalPoints G`, the morphisms
`Over.mk (𝟙 (Spec k)) ⟶ G.X`. For such a point `h`, `G.innerIso h` is the inner automorphism
`x ↦ h x h⁻¹`. For a subgroup functor `Q`, the preimage `Q.comap (G.innerIso h).hom` consists
of the `x` with `h x h⁻¹ ∈ Q`. So it is `h⁻¹ Q h`. Accordingly, the hypothesis
`P₀ ≤ (range j).comap (G.innerIso h).hom` says that `h P₀ h⁻¹ ⊆ P`, where `P` is the range of
the closed immersion `j`.

## Declarations

### `SubgroupFunctor.mem_normalizer_of_comap_innerIso_eq`

For a subgroup functor `F` of `G` and a rational point `h`, if
`F.comap (G.innerIso h).hom = F`, then `h` lies in the rational points of `F.normalizer`.

*Proof.* The hypothesis also gives `F.comap (G.innerIso h).inv = F`, using
`SubgroupFunctor.comap_iso_hom_inv`. On a test scheme `V` with structure map `a`, the pulled-back
point `a ≫ h` is the constant point `G.constantPoint h V`. The two membership conditions of the
normalizer, for conjugation by `h` and by `h⁻¹`, then follow from `comp_innerIso_hom`,
`innerIso_inv_hom` and `constantPoint_inv`.

### `mem_rationalPoints_of_minimalParabolic_le_comap`

Let `j : P ⟶ G` be a parabolic subgroup (`IsParabolicSubgroup j`) with `P₀ ≤ range j`, and let
`h` be a rational point with `P₀ ≤ (range j).comap (G.innerIso h).hom`, that is,
`h P₀ h⁻¹ ⊆ P`. Then `h ∈ (range j)(k)`.

*Proof.* By `parabolicDynamic`, `range j = Dynamic.parabolic χ` for some cocharacter `χ` of `G`.
Put `χ' = χ ≫ (G.innerIso h).inv`. By `Dynamic.parabolic_eq_comap_of_iso`,
`Dynamic.parabolic χ' = (Dynamic.parabolic χ).comap (G.innerIso h).hom`. Both parabolics contain
`P₀`. So by the first part of `standardParabolicClassification` they are standard:
`range j = standardParabolic i ν J₁` and
`(range j).comap (G.innerIso h).hom = standardParabolic i ν J₂`, with `J₁, J₂ ⊆ Δ`, where
`Δ = simpleRelativeRoots i ν`.

The second part of the classification applies to `χ'`: the subset `J` with
`Dynamic.parabolic χ' = (standardParabolic i ν J).comap (G.innerIso g).hom` for some `g` is
unique. Two witnesses are available:

- `J₁` with `g = h`;
- `J₂` with `g = 1`, since `innerIso_one_hom` and `SubgroupFunctor.comap_id` reduce the
  preimage to the identity.

Hence `J₁ = J₂`, and `(range j).comap (G.innerIso h).hom = range j`. By the first declaration,
`h` lies in the rational points of `(range j).normalizer`. That normalizer equals `range j` by
`parabolicSelfNormalizer`.

This argument does not use the conjugacy of minimal parabolics (`minimalParabolicConjugacy`).

### `exists_mul_eq_of_minimalParabolic_le_comap`

Let `j : P ⟶ G` be a parabolic subgroup, and let `m` and `h` be rational points with
`m P₀ m⁻¹ ⊆ P` and `h P₀ h⁻¹ ⊆ P`, both stated as `P₀ ≤ (range j).comap (G.innerIso _).hom`.
Then there is `p ∈ (range j)(k)` with `h = p * m`.

*Proof.* Put `j' = j ≫ (G.innerIso m).inv`. Its range is `(range j).comap (G.innerIso m).hom`,
checked by transporting witnesses through `Iso.inv_hom_id` and `Iso.hom_inv_id`. It is
parabolic by `IsParabolicSubgroup.comp_iso` and contains `P₀` by the hypothesis on `m`. The
hypothesis on `h` becomes `P₀ ≤ (range j').comap (G.innerIso (m⁻¹ * h)).hom`, by
`innerIso_mul_hom`, `innerIso_inv_hom` and `SubgroupFunctor.comap_comp`. The previous
declaration gives `m⁻¹ * h ∈ (range j')(k)`. By
`SubgroupFunctor.mem_rationalPoints_comap_innerIso_hom`, this means
`m (m⁻¹ h) m⁻¹ ∈ (range j)(k)`. Take `p = m (m⁻¹ h) m⁻¹`. Then `p * m = h` by `group`.

In Springer's §3.6 this is the step "if Q = P the element γ must lie in P(l)", in coset form.
The proof uses only one conjugate `m P₀ m⁻¹` inside `P`. No Borel factor appears.

### `exists_range_eq_comap_standardParabolic_empty_of_rankOne`

Assume that the simple relative roots form a singleton: `simpleRelativeRoots i ν = {α}`. Let
`jQ : Q ⟶ G` be a parabolic subgroup whose range is not everything (`range jQ ≠ ⊤`). Then there is
a rational point `g` with
`range jQ = (standardParabolic i ν ∅).comap (G.innerIso g).hom`. In the convention above, this
says `Q = g⁻¹ P₀ g`: every proper parabolic is conjugate to `P₀` by a rational point.

*Proof.* By `parabolicDynamic`, `range jQ = Dynamic.parabolic χ`. The second part of
`standardParabolicClassification` gives `J ⊆ {α}` and a rational point `g` with
`Dynamic.parabolic χ = (standardParabolic i ν J).comap (G.innerIso g).hom`. By
`Set.subset_singleton_iff_eq`, either `J = ∅` or `J = {α}`. If `J = ∅`, this is the conclusion.
If `J = {α} = Δ`, then `standardParabolic i ν Δ = ⊤` by the third part of
`standardParabolicEndpoints`, so
`range jQ = ⊤.comap _ = ⊤` (`SubgroupFunctor.comap_top`), contradicting the hypothesis.

This is Springer's "the parabolic k-subgroup Q must be k-conjugate to P" in semisimple rank one.

## Scope

The module has four declarations; the last three are the mathematical results. They hold over an arbitrary field. They assume only `IsConnectedReductive G`, a
maximal split torus and a generic cocharacter. The rank-one hypothesis is used only in the last
declaration. No topology, number field or adelic structure is involved.
