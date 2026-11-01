# Fibre frame lifting from restriction-compatible models and the algebraic spreading

Author: Worker 1119.

This module proves

`Langlands.AlgebraicGeometry.Picard.FibreFrameLifting.fibreFrameLifting_of_models
  (h1 : RestrictionPerfectModelsStatement.{u})
  (h2 : ModuleComplex.FibreH0RestrictionSpreadStatement.{u}) : FibreFrameLiftingStatement.{u}`.

So the target proposition follows from the two prerequisite propositions, which appear only as
explicit hypotheses. Both are published Library statements, imported from
`Langlands.AlgebraicGeometry.Modules.RestrictionPerfectModelsStatement` and
`Langlands.Cohomology.ModuleComplex.FibreH0RestrictionSpreadStatement`. The exact-target proof
`Langlands.AlgebraicGeometry.Picard.fibreFrameLifting` (module `FibreFrameLiftingProof`) applies
this theorem to proofs of the two propositions. The module contains no `sorry` and no new
axioms. Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Proof

Introduce the data of the target: `S`, `X X₁ X₂ : Over S` (smooth, proper, geometrically
connected), the closed immersions `iₖ`, `L`, `s`, the trivializations `iₖ^* L ≅ 𝒪`,
`(X.hom.fiberι s)^* L ≅ 𝒪`, the maps of fibres `jₖ`, and the degree-one hypothesis `hH1`.

1. Affine neighbourhood. Choose an affine open `V ∋ s`
   (`exists_isAffineOpen_mem_and_subset`), and let `e = hV.fromSpec`,
   `k = IsLocalRing.ResidueField (stalk s)` and `φ₀ = germ ≫ residue : Γ(S, V) ⟶ k`. Then
   `S.fromSpecResidueField s = Spec.map φ₀ ≫ e` (`fromSpecResidueField_eq_comp_fromSpec`), and
   `S.residueField s` is by definition `CommRingCat.of k`.
2. Base change to `Spec Γ(S, V)`. Let `f = pullback.snd X.hom e` and `L'` the pullback of `L`
   along `pullback.fst X.hom e`. Let `gₖ = mapOver X.hom Xₖ.hom iₖ.left _ e`: closed immersions
   by `isPullback_mapOver`, with `gₖ ≫ f = pullback.snd Xₖ.hom e` smooth, proper and
   geometrically connected, and `gₖ^* L' ≅ 𝒪` (`nonempty_pullback_pullback_iso_unit`).
3. Fibre. With `t = S.fromSpecResidueField s`, the fibre `X.hom.fiber s = pullback X.hom t` maps
   to `pullback X.hom e` by `liftPoint`, giving the square `isPullback_liftPoint`. The target's
   `jₖ` is `mapOver … t` definitionally, so `isPullback_liftPoint_mapOver` gives the closed fibre
   squares. `(liftPoint)^* L' ≅ 𝒪` comes from the target's fibre trivialization. Applying
   `exists_spread_of_models` (module `Core`) with `hH1` gives `r ∈ Γ(S, V)` with
   `φ₀ r ≠ 0` and the spreading property.
4. Basic open. `U = S.basicOpen r` contains `s`, because `φ₀ r ≠ 0` means the germ of `r` at
   `s` is a unit (`IsLocalRing.residue_ne_zero_iff_isUnit`). `U` is affine, and `r` restricts to
   a unit on `U` (`RingedSpace.isUnit_res_basicOpen`). The square `isPullback_liftAffineOpen`
   presents `pullback X.hom U.ι` over `Spec Γ(S, U)`. The spreading property, applied to it and
   to `pullback g₁ p`, makes the global sections of the unit `M ⟶ g'_* g'^* M` bijective, where
   `p = liftAffineOpen …`, `M = p^* L'` and `g' = pullback.snd g₁ p`.
5. Section. Let `b = pullback.snd X.hom U.ι` (smooth, proper, geometrically connected by base
   change). `g' ≫ b` is geometrically connected: the composite `g' ≫ b ≫ hU.isoSpec.hom` is a
   base change of `g₁ ≫ f`, and an isomorphism square (`IsPullback.of_horiz_isIso`) removes
   `hU.isoSpec.hom`. `g'^* M ≅ 𝒪`. On the fibre of `b` over `⟨s, hs⟩`, `M` is trivial: the fibre
   maps to `X.hom.fiber s` over `X` (`fiberι_fst_comp_eq`), and the target's fibre
   trivialization is pulled back. `exists_isIso_fiber_pullback` (module `Frame`) gives
   `σ : 𝒪 ⟶ M` whose fibre pullback is an isomorphism.
6. Conclusion. Compose `σ` with the canonical isomorphism
   `M = p^* (fst^* L) ≅ (pullback.fst X.hom U.ι)^* L` (`pullbackComp`, `pullbackCongr`,
   `liftAffineOpen_fst`). Its fibre pullback is a composite of isomorphisms, which gives the
   target with this `U`, `hs` and this morphism.

## Provenance

The target is the intermediate conclusion of the proof of Stacks tag 0BF2, specialized as
explained in `FibreFrameLiftingStatement.md` (`more-morphisms.tex`, statement lines
9518–9541, proof lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`, commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The route follows the source: shrink to an affine
neighbourhood of `s`, use base-change-compatible perfect models with chain maps representing the
restrictions, show the degree-zero restriction is an isomorphism after shrinking, and lift a
frame. There are two differences. The source works with minimal models and matrices directly;
here these steps are the content of the hypothesis `h2`. And the lifted section is obtained from
the frame of the first closed piece, through the degree-zero restriction isomorphism, rather than
from the frame of the fibre.
