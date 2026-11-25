/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap
import WeilConjectures.AlgebraicGeometry.ConstantPullbackCompositionCoherence

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Compatibility of the canonical cyclic coefficient comparisons with pullback.
Source: Stacks Project, Tag 03Q8, and the constant-sheaf pullback coherence.
(blueprint: lem-sbc-cyclic-coefficient-pullback-compatibility).

Proof: Apply `cohomologyMap_map` to the coefficient comparison on the target.
The composition identity for constant-sheaf inverse images identifies the
resulting coefficient morphism with the comparison on the source composed with
the inverse of the upper-star composition isomorphism.
-/
theorem cyclicCoefficientPullbackCompatibility {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) (W V : X.Etale) (v : V ⟶ W)
    (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).obj
      (Y.constantZMod e)) q) :
    let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
    let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
      (pullback.fst h V.hom) (by simp [g])
    Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app
        (AddCommGrpCat.of (ULift (ZMod e)))).hom q
      (cohomologyMap g _ q
        (Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst h W.hom)).app
            (AddCommGrpCat.of (ULift (ZMod e)))).hom q x)) =
      Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (pullback.fst h V.hom)).app
          (AddCommGrpCat.of (ULift (ZMod e)))).hom q
        (Sheaf.H.map (i.inv.app (Y.constantZMod e)) q
          (cohomologyMap g _ q x)) := by
  dsimp only
  let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
  let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
    (pullback.fst h V.hom) (by simp [g])
  let M := AddCommGrpCat.of (ULift (ZMod e))
  have hg : g ≫ pullback.fst h W.hom = pullback.fst h V.hom := by simp [g]
  -- Equality induction preserves the proof argument of the composition isomorphism.
  have hgeneral : ∀ (k : pullback h V.hom ⟶ Y)
      (hk : k = g ≫ pullback.fst h W.hom),
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).inv.app M ≫
          (upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom) k hk).hom.app
            (Y.constantZMod e) =
        (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app M ≫
          (upperStar AddCommGrpCat.{u + 1} g).map
            ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
              (pullback.fst h W.hom)).inv.app M) := by
    intro k hk
    subst k
    exact constantPullbackCompositionCoherence g (pullback.fst h W.hom) M
  have hc := hgeneral (pullback.fst h V.hom) hg.symm
  have hcoeff :
      (upperStar AddCommGrpCat.{u + 1} g).map
          ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
            (pullback.fst h W.hom)).hom.app M) ≫
        (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M =
      i.inv.app (Y.constantZMod e) ≫
        (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst h V.hom)).hom.app M := by
    -- Invert the equality of composed isomorphisms to obtain the hom comparison.
    have hi :
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst h V.hom)).app M).symm ≪≫ i.app (Y.constantZMod e) =
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app M).symm ≪≫
          (upperStar AddCommGrpCat.{u + 1} g).mapIso
            (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
              (pullback.fst h W.hom)).app M).symm) := Iso.ext hc
    exact (congrArg Iso.inv hi).symm
  let cf := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (pullback.fst h W.hom)).hom.app M
  let cg := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M
  let cv := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (pullback.fst h V.hom)).hom.app M
  change Sheaf.H.map cg q (cohomologyMap g _ q (Sheaf.H.map cf q x)) =
    Sheaf.H.map cv q (Sheaf.H.map (i.inv.app (Y.constantZMod e)) q
      (cohomologyMap g _ q x))
  calc
    _ = Sheaf.H.map cg q
        (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} g).map cf) q
          (cohomologyMap g _ q x)) :=
      congrArg (Sheaf.H.map cg q) (cohomologyMap_map g q cf x)
    _ = Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} g).map cf ≫ cg) q
        (cohomologyMap g _ q x) := (Sheaf.H.map_comp_apply _ _ _).symm
    _ = Sheaf.H.map (i.inv.app (Y.constantZMod e) ≫ cv) q
        (cohomologyMap g _ q x) :=
      congrArg (fun φ ↦ Sheaf.H.map φ q (cohomologyMap g _ q x)) hcoeff
    _ = _ := Sheaf.H.map_comp_apply _ _ _

end AlgebraicGeometry.Etale
