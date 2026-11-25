/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Pullback and restriction between two opens

Source: Stacks Project, Tag 01F7; the restriction comparison in the proof of Tag 0A50.
(blueprint: lem-weil-pbc-open-cohomology-restriction-naturality).
-/

@[expose] public section

universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem cohomologyMap_transported_comp {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = a ≫ b)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (l : (upperStar AddCommGrpCat.{u + 1} b).obj G ⟶ F)
    (k : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ K)
    (q : ℕ) (x : Sheaf.H G q) :
    Sheaf.H.map k q (cohomologyMap a F q (Sheaf.H.map l q (cohomologyMap b G q x))) =
      Sheaf.H.map (((upperStarComp AddCommGrpCat.{u + 1} a b c hc).hom.app G) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map l ≫ k) q (cohomologyMap c G q x) := by
  let y := cohomologyMap c G q x
  let m := (upperStar AddCommGrpCat.{u + 1} a).map l
  let e := upperStarComp AddCommGrpCat.{u + 1} a b c hc
  calc
    _ = Sheaf.H.map k q (Sheaf.H.map m q
        (cohomologyMap a ((upperStar AddCommGrpCat.{u + 1} b).obj G) q
          (cohomologyMap b G q x))) :=
      congrArg (Sheaf.H.map k q) (cohomologyMap_map a q l (cohomologyMap b G q x))
    _ = Sheaf.H.map k q (Sheaf.H.map m q (Sheaf.H.map (e.hom.app G) q y)) :=
      congrArg (fun z ↦ Sheaf.H.map k q (Sheaf.H.map m q z))
        (by
          subst c
          exact (cohomologyPullbackFunctorial a b G q).2.1 x)
    _ = Sheaf.H.map (m ≫ k) q (Sheaf.H.map (e.hom.app G) q y) :=
      (Sheaf.H.map_comp_apply m k _).symm
    _ = _ := (Sheaf.H.map_comp_apply (e.hom.app G) (m ≫ k) y).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pullback commutes with restriction between nested opens.
Source: Stacks Project, Tag 01F7; agent-written consequence of pullback functoriality and
inverse-image composition, also used in the proof of Tag 0A50.
(blueprint: lem-weil-pbc-open-cohomology-restriction-naturality)

Proof: Write i : A → B and i' : g⁻¹A → g⁻¹B for the two inclusions, and g_A and g_B
for the restricted morphisms. The equality i' ≫ g_B = g_A ≫ i follows by composing
with the monomorphism B.ι and using the restriction identities. Apply composition
functoriality of cohomologyMap to these two factorizations. Naturality with respect to
coefficient morphisms moves the inverse composition identifications through pullback.
The associativity law for upperStarComp, first for i', (g⁻¹B).ι, g and then for g_A,
i, B.ι, identifies the resulting coefficient morphisms: each transports pullback along
i' ≫ (g⁻¹B).ι ≫ g = g_A ≫ i ≫ B.ι to restriction of g⁻¹G to g⁻¹A.
Cancel adjacent inverse composition comparisons and apply Sheaf.H.map_comp_apply.
This gives precisely the equality below. No cover or connecting morphism is involved.
For A = B this is the identity comparison law; for A empty both sides land in the
cohomology of the empty scheme; for g the identity it is the identity pullback law. -/
theorem openCohomologyPullback_restriction {X Y : Scheme.{u}} (g : Y ⟶ X)
    {A B : X.Opens} (h : A ≤ B)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} B.ι).obj G) q) :
    openCohomologyRestriction (g.preimage_mono h)
        ((upperStar AddCommGrpCat.{u + 1} g).obj G) q
        (openCohomologyPullback g B G q x) =
      openCohomologyPullback g A G q (openCohomologyRestriction h G q x) := by
  let i := X.homOfLE h
  let i' := Y.homOfLE (g.preimage_mono h)
  let a := g ∣_ A
  let b := g ∣_ B
  let c := i' ≫ b
  let hA := (g ⁻¹ᵁ A).ι ≫ g
  let hB := (g ⁻¹ᵁ B).ι ≫ g
  have hc : c = a ≫ i := by
    apply (cancel_mono B.ι).1
    dsimp [c, a, b, i, i']
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Y.homOfLE_ι,
      Category.assoc, X.homOfLE_ι, morphismRestrict_ι]
  have hcA : hA = c ≫ B.ι := by
    dsimp [hA, c, b, i']
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Y.homOfLE_ι]
  let eB := upperStarComp AddCommGrpCat.{u + 1} b B.ι hB
    (morphismRestrict_ι g B).symm
  let eA := upperStarComp AddCommGrpCat.{u + 1} a A.ι hA
    (morphismRestrict_ι g A).symm
  let eX := upperStarComp AddCommGrpCat.{u + 1} i B.ι A.ι (X.homOfLE_ι h).symm
  let eY := upperStarComp AddCommGrpCat.{u + 1} i' (g ⁻¹ᵁ B).ι (g ⁻¹ᵁ A).ι
    (Y.homOfLE_ι (g.preimage_mono h)).symm
  let eBY := upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ B).ι g
  let eAY := upperStarComp AddCommGrpCat.{u + 1} (g ⁻¹ᵁ A).ι g
  let eL := upperStarComp AddCommGrpCat.{u + 1} i' b c rfl
  let eR := upperStarComp AddCommGrpCat.{u + 1} a i c hc
  have left₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' b B.ι c hB hA rfl
      (morphismRestrict_ι g B).symm hcA G
  have left₂ := map_upperStarComp_hom_app_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' (g ⁻¹ᵁ B).ι g (g ⁻¹ᵁ A).ι hB hA
      (Y.homOfLE_ι (g.preimage_mono h)).symm rfl rfl G
  have right₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} a i B.ι c A.ι hA hc (X.homOfLE_ι h).symm hcA G
  have hcoeff : eL.hom.app ((upperStar AddCommGrpCat.{u + 1} B.ι).obj G) ≫
      (upperStar AddCommGrpCat.{u + 1} i').map (eB.inv.app G ≫ eBY.hom.app G) ≫
        eY.inv.app ((upperStar AddCommGrpCat.{u + 1} g).obj G) =
      eR.hom.app ((upperStar AddCommGrpCat.{u + 1} B.ι).obj G) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map (eX.inv.app G) ≫
          (eA.inv.app G ≫ eAY.hom.app G) := by
    simp only [Functor.map_comp]
    rw [← Category.assoc, ← Category.assoc, left₁, Category.assoc, Category.assoc,
      left₂, Iso.hom_inv_id_app_assoc]
    rw [← Category.assoc, right₁, Category.assoc, Iso.hom_inv_id_app_assoc]
  change Sheaf.H.map (eY.inv.app ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q
      (cohomologyMap i' ((upperStar AddCommGrpCat.{u + 1} (g ⁻¹ᵁ B).ι).obj
        ((upperStar AddCommGrpCat.{u + 1} g).obj G)) q
          (Sheaf.H.map (eB.inv.app G ≫ eBY.hom.app G) q (cohomologyMap b _ q x))) =
    Sheaf.H.map (eA.inv.app G ≫ eAY.hom.app G) q
      (cohomologyMap a _ q (Sheaf.H.map (eX.inv.app G) q (cohomologyMap i _ q x)))
  calc
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) :=
      cohomologyMap_transported_comp i' b c rfl _ _ _ _ _ q x
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) := by rw [hcoeff]
    _ = _ := (cohomologyMap_transported_comp a i c hc _ _ _ _ _ q x).symm

end AlgebraicGeometry.Etale
