/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap
import WeilConjectures.AlgebraicGeometry.AbelianRepresentableCohomologyMapNaturality
import WeilConjectures.AlgebraicGeometry.CyclicCoefficientPullbackCompatibility

/-! # Naturality of cyclic free-representable cohomology comparison
Source: Stacks Project, Tag 03Q8, restricted cohomology presheaf.
(blueprint: lem-sbc-cyclic-representable-cohomology-map-naturality). -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- The explicit comparison commutes with geometric restriction after identifying
pulled-back constant coefficients with constant coefficients.

Source: Stacks Project, Tag 03Q8, restricted cohomology presheaf, and naturality
of the free-sheaf adjunction in `HigherDirectImage/FreeSheaf.lean`.
(blueprint: lem-sbc-cyclic-representable-cohomology-map-naturality).

Proof: For v : V → W over X let g : Y ×_X V → Y ×_X W be its base change.
The section defining abelianRepresentableGenerator for V maps under Z[v] to
the pullback of the section for W. This follows by naturality of the inverse
image/direct image adjunction unit, evaluation at the representable identity,
and naturality of the localization restriction isomorphism. Convert derived
Hom to Ext through the fully faithful inclusion D+ → D. Pulling back an Ext
class respects composition, so the universal-section equality identifies
precomposition by Z[v] with pullback along g followed by the generator for V.
Finally the canonical constant-sheaf pullback comparisons commute with
composition of inverse images; applying Sheaf.H.map yields the equality below.
No invertibility of e or positivity of q is required; identity maps, e = 0,
and empty fibre products satisfy the same adjunction identities. -/
theorem cyclicRepresentableCohomologyMap_naturality {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) :
    let P := (uliftYoneda.{u + 1} ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
      presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      upperStar AddCommGrpCat.{u + 1} h ⋙ DerivedCategory.Plus.singleFunctor _ 0).op ⋙
        preadditiveYoneda.obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod e))⟦(q : ℤ)⟧)
    ∀ (W V : X.Etale) (v : V ⟶ W) (ξ : P.obj (op W)),
      let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
      Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app
          (AddCommGrpCat.of (ULift (ZMod e)))).hom q
        (cohomologyMap g _ q (cyclicRepresentableCohomologyMap h e q W ξ)) =
          cyclicRepresentableCohomologyMap h e q V (P.map v.op ξ) := by
  dsimp only
  intro W V v ξ
  let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
  let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
    (pullback.fst h V.hom) (by simp [g])
  have hn := abelianRepresentableCohomologyMap_naturality h
    (Y.constantZMod e) q W V v ξ
  have hc := cyclicCoefficientPullbackCompatibility h e q W V v
    (abelianRepresentableCohomologyMap h (Y.constantZMod e) q W ξ)
  dsimp [g] at hn hc ⊢
  have hfinal := hc
  rw [hn] at hfinal
  unfold cyclicRepresentableCohomologyMap
  convert hfinal using 1 <;> rfl

end AlgebraicGeometry.Etale
