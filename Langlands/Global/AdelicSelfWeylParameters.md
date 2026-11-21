# The self Weyl set `Ω(P, P)`: finiteness and invariance of Lebesgue measure

Module `Langlands.Global.AdelicSelfWeylParameters` proves two facts about the
Weyl set `Ω(P, P) = weylParameterSet p l p l π` of a presented parabolic
`P = MU` (`r : ParabolicRootPresentation p l a`) with a Levi projection
`π : P → M`. Both are used by the proof of the bound (19) of Lapid's Lemma 10
(`Langlands.Global.LocalWavePacketNormBoundReduction`):

1. `Ω(P, P)` is finite (`finite_weylParameterSet_self`).
2. For every Weyl conjugation `(w, c)` from `P` to itself and every linear
   coordinate system `e : ℝⁿ ≃ X^*(P) ⊗ ℝ`, the coordinate change
   `x ↦ e⁻¹(realWeylParameter l c π (e x))` preserves Lebesgue measure
   (`measurePreserving_realWeylParameter`). In Lapid's notation this is the
   invariance of `dλ` on `i𝔞_P^*` under `λ ↦ sλ` for `s ∈ Ω(P, P)`.

All declarations are in namespace `Langlands.Global.AdelicGroupPoints`.

## Provenance

Derived. Lapid 2011, §2, p.311 (registered as
`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, PDF page = printed
page + 9) takes `Ω(P, Q)` from Arthur. Getz–Hahn 2024, §10.2, p.273
(registered as `getz-hahn-2024-automorphic-representations`, PDF page 285)
defines `W(𝔞_M, 𝔞_{M'})` as the set of linear isomorphisms `𝔞_M → 𝔞_{M'}`
obtained by restricting elements of the Weyl group `W(G, T)(F)`; it is finite
because `W(G, T)(F)` is. The Library's `weylParameterSet` is defined
differently, by the pairs `(w, c)` with `w ∈ G(F)` and `c : M ≅ M` such that
`l(c(m)) = w⁻¹ l(m) w` (`IsWeylConjugation`), acting on `X^*(P) ⊗ ℂ` by
`χ ↦ χ ∘ l ∘ c ∘ π` (`weylParameter`). The proof below therefore does not pass
through `W(G, T)(F)`. It uses the finiteness of the full Weyl image of a closed
split torus (`splitTorusWeylImageFinite`, module
`Langlands.GroupScheme.Torus.WeylImageFinite`) for the split component `A` of
`M`. The finite-order and measure-preservation statements are elementary
consequences.

## Weyl conjugations normalize the split component (section `Weyl`)

Variables: a field `F`, a parabolic `p : P → G` with Levi `l : M → P`, a
commutative group scheme `A` with `a : A → M`, a point
`w : Spec F → G` and `c : M → M`.

- `IsWeylConjugation.inv_comp_eq_self`: for a Weyl conjugation `(w, c)` from
  `P` to itself (with `c` an isomorphism),
  `c⁻¹ ≫ l ≫ p = (l ≫ p) ≫ int(w)`. This rewrites `IsWeylConjugation.comp_eq`
  (`c ≫ l ≫ p = l ≫ p ≫ int(w)⁻¹`).
- `IsWeylConjugation.isNormalizingPoint_splitComponent`: if `a` is a split
  component of `M` (`IsSplitComponent a`), then `w` normalizes the torus
  `a ≫ l ≫ p` of `G`, through the automorphism of `A` induced by `c⁻¹`
  (the published `IsSplitComponent.automorphismRestrictionIso` and
  `IsSplitComponent.isNormalizingPoint_of_normalizes`).
- `IsWeylConjugation.weylAction_characterRestrict`: the published Weyl action
  of this normalizing point on `X^*(A)` sends the restriction `χ ∘ a` of a
  character `χ` of `M` to `(χ ∘ c) ∘ a`. The proof uses
  `IsSplitComponent.automorphismRestriction_comp`.
- `IsWeylConjugation.characterRestrict_eq_of_weylAction_eq`: if restriction
  of characters from `M` to `A` is injective, two Weyl conjugations
  `(w, c)`, `(w', c')` from `P` to itself with the same Weyl action on `X^*(A)`
  restrict characters of `M` in the same way:
  `characterRestrict c = characterRestrict c'`.

## Finiteness (section `Finite`)

Additionally `G` is affine and locally of finite type over `F`.

- `finite_selfWeylCharacterMaps r π`: the set of additive maps
  `characterRestrict (π ≫ c ≫ l) : X^*(P) → X^*(P)`, for the Weyl conjugations
  `(w, c)` from `P` to itself, is finite. Proof: the Levi is connected
  reductive and `a` is a split component (fields of `r.isCompatible`), so
  `a ≫ l ≫ p` is a closed split torus of `G`; its full Weyl image is finite by
  `splitTorusWeylImageFinite`. Choose a Weyl conjugation for each element of
  the set and map it to the Weyl action of `w` on `X^*(A)`. This map is
  injective: restriction from `M` to `A` is injective
  (`characterRestrict_injective_of_centralSplitTorusCharacter` with the
  published `centralSplitTorusCharacter`). Equal actions therefore give
  `characterRestrict c = characterRestrict c'`. The element is
  `characterRestrict π ∘ characterRestrict c ∘ characterRestrict l`.
- `finite_weylParameterSet_self r π`: `(weylParameterSet p l p l π).Finite`
  over a number field. `weylParameter l c π` is the scalar extension to `ℂ` of
  `characterRestrict (π ≫ c ≫ l)`, so the set is contained in the image of
  the finite set above.

## Real parameters (section `Real`)

Over a number field `F`:

- `realWeylParameter_tmul`: `realWeylParameter l c π (s ⊗ χ) = s ⊗ (χ ∘ l ∘ c ∘ π)`,
  that is, `χ` is precomposed with `π ≫ c ≫ l : P → P`
  (`characterRestrict (π ≫ c ≫ l) χ`; by definition).
- `realWeylParameter_comp hlπ c c'`: for `l ≫ π = 𝟙 M`,
  `realWeylParameter l c' π ∘ realWeylParameter l c π = realWeylParameter l (c' ≫ c) π`,
  because `π ≫ c' ≫ l ≫ π ≫ c ≫ l = π ≫ (c' ≫ c) ≫ l`.
- `realWeylParameter_id r hlπ`: `realWeylParameter l (𝟙 M) π` is the identity.
  Restriction along `l` is injective, because restriction along `a ≫ l` is
  (the published `characterRestrict_splitComponent_injective`). The map
  `realWeylParameter l (𝟙 M) π` sends `s ⊗ χ` to `s ⊗ (χ ∘ l ∘ π)`
  (precomposition with `π ≫ l : P → P`). Restriction along `l` sends
  `χ ∘ l ∘ π` to `χ ∘ l ∘ π ∘ l = χ ∘ l`, because `π ∘ l` is the identity of
  `M` (`l ≫ π = 𝟙 M`). Injectivity of restriction along `l` then gives
  `χ ∘ l ∘ π = χ`.
- `isWeylConjugation_one`: `(1, 𝟙 M)` is a Weyl conjugation from `P` to itself.
- `finite_realSelfWeylParameters r π`: the real parameter maps of the Weyl
  conjugations from `P` to itself form a finite set (the image of the finite
  set of `finite_selfWeylCharacterMaps` under scalar extension to `ℝ`).
- `exists_pow_realWeylParameter_eq_one r hlπ h`: for a Weyl conjugation
  `(w, c)` from `P` to itself, some positive power of
  `L = realWeylParameter l c π` is the identity. Every power `L^k` is the real
  parameter map of a Weyl conjugation (by induction with
  `IsWeylConjugation.comp` and `realWeylParameter_comp`; `L^0` from
  `isWeylConjugation_one` and `realWeylParameter_id`). The set of these maps
  is finite, so `L^i = L^j` for some `i ≠ j`. The inverse conjugation
  (`IsWeylConjugation.exists_symm`) gives a two-sided inverse of `L`, so `L` is
  a unit and `L^{|j - i|} = 1`.
- `measurePreserving_realWeylParameter r hlπ h e`: the map
  `τ = e⁻¹ ∘ L ∘ e` of `ℝⁿ` satisfies `τ^m = 1` for some `m > 0`, so
  `det(τ)^m = 1` and `|det τ| = 1`. Then
  `Measure.map_linearMap_addHaar_eq_smul_addHaar` shows that `τ` preserves
  Lebesgue measure.
