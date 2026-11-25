/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-!
# Explicit restriction and restricted pullback on étale cohomology

Source: Stacks Project, Tag 01F7 and Tag 0A50.
These abbreviations expand to the maps of etale_mayerVietoris_pullback.
(blueprint: lem-weil-pbc-open-cohomology-whole-restriction-naturality).
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Restriction from an open B to an open A contained in B, with the composition comparison.
Source: Stacks Project, Tag 01F7. -/
noncomputable def openCohomologyRestriction {X : Scheme.{u}} {A B : X.Opens}
    (h : A ≤ B) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} B.ι).obj G) q →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} A.ι).obj G) q :=
  (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) B.ι
    A.ι (X.homOfLE_ι h).symm).inv.app G) q).comp
      (cohomologyMap (X.homOfLE h) ((upperStar AddCommGrpCat.{u + 1} B.ι).obj G) q)

/-- Pullback on an open, transported to the restriction of the pulled-back sheaf.
Source: Stacks Project, Tag 01F7. -/
noncomputable def openCohomologyPullback {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q :=
  (Sheaf.H.map (((upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
    ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm).inv ≫
      (upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g).hom).app G) q).comp
        (cohomologyMap (g ∣_ W) ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q)

private theorem cohomologyMap_comp_explicit {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = a ≫ b)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H G q) :
    cohomologyMap a ((upperStar AddCommGrpCat.{u + 1} b).obj G) q
      (cohomologyMap b G q x) =
      Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b c hc).hom.app G) q
        (cohomologyMap c G q x) := by
  subst c
  exact (cohomologyPullbackFunctorial a b G q).2.1 x

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from the whole scheme commutes with pullback.
Source: Stacks Project, Tag 01F7; this is composition functoriality twice, followed by
cancellation of the inverse composition comparison.
(blueprint: lem-weil-pbc-open-cohomology-whole-restriction-naturality) -/
theorem openCohomologyPullback_restrict {X Y : Scheme.{u}} (g : Y ⟶ X) (W : X.Opens)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (x : Sheaf.H G q) :
    cohomologyMap (g ⁻¹ᵁ W).ι ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
      (cohomologyMap g G q x) =
      openCohomologyPullback g W G q (cohomologyMap W.ι G q x) := by
  let e := upperStarComp AddCommGrpCat.{u + 1} (g ∣_ W) W.ι
    ((g ⁻¹ᵁ W).ι ≫ g) (morphismRestrict_ι g W).symm
  let e' := upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ W).ι g
  let y := cohomologyMap ((g ⁻¹ᵁ W).ι ≫ g) G q x
  have hc : Sheaf.H.map (e.inv.app G) q
      (Sheaf.H.map (e.hom.app G) q y) = y := by
    calc
      _ = Sheaf.H.map (e.hom.app G ≫ e.inv.app G) q y :=
        (Sheaf.H.map_comp_apply (e.hom.app G) (e.inv.app G) y).symm
      _ = y := by simp
  calc
    _ = Sheaf.H.map (e'.hom.app G) q y :=
      cohomologyMap_comp_explicit (g ⁻¹ᵁ W).ι g _ rfl G q x
    _ = Sheaf.H.map (e'.hom.app G) q
        (Sheaf.H.map (e.inv.app G) q (Sheaf.H.map (e.hom.app G) q y)) :=
      congrArg (Sheaf.H.map (e'.hom.app G) q) hc.symm
    _ = Sheaf.H.map (e'.hom.app G) q
        (Sheaf.H.map (e.inv.app G) q
          (cohomologyMap (g ∣_ W) ((upperStar AddCommGrpCat.{u + 1} W.ι).obj G) q
            (cohomologyMap W.ι G q x))) := by
      exact congrArg (fun z ↦ Sheaf.H.map (e'.hom.app G) q
        (Sheaf.H.map (e.inv.app G) q z))
        (cohomologyMap_comp_explicit (g ∣_ W) W.ι _
          (morphismRestrict_ι g W).symm G q x).symm
    _ = _ := by
      exact (Sheaf.H.map_comp_apply (e.inv.app G) (e'.hom.app G) _).symm

end AlgebraicGeometry.Etale
