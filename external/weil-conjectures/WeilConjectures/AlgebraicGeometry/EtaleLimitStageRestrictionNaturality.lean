/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLimitOpenCohomologyCoconeDegree
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyMaps
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-! # Naturality of a single restricted cohomology map

Source: Stacks Project, Tags 01F7 and 09YQ; the restricted square specialization
in the proof of the difference-map naturality lemma.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar cohomologyMap openCohomologyRestriction
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
/-- Composition with coefficient morphisms, from cohomology pullback functoriality.
Source: Stacks Project, Tag 01F7. Move the first coefficient map through pullback
using cohomologyMap_map, use composition functoriality, and combine the three
coefficient maps using Sheaf.H.map_comp_apply. -/
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

/-- For arbitrary nested opens A ≤ B of X, restriction on the inverse-image opens
commutes with each actual tail-stage cohomology transition, including its arbitrary
coefficient morphism φ. There is no condition on identities or compositions of φ.

Source: Stacks Project, Tag 01F7 (pullback and coefficient functoriality),
Tag 09YQ (restricted stage and cone maps); parent proof step 1.
(blueprint: lem-weil-pbc-etale-limit-stage-restriction-naturality)

Proof: Let i and i' be the inclusions A_j → B_j and A_k → B_k, let a and b
be the actual stage transitions on A and B, and let t be D.map of the opposite
stage arrow. Put c = i' ≫ b. The equations tailStageOpenMap followed by the
stage-open inclusion = stage-open inclusion followed by t, and homOfLE_ι,
give c = a ≫ i by cancellation of the monomorphism B_j.ι. They also give
A_k.ι ≫ t = c ≫ B_j.ι.
For arbitrary composable scheme maps and coefficient maps, cohomologyMap_map,
cohomologyPullbackFunctorial and Sheaf.H.map_comp_apply express the composite
cohomology map as pullback along their composite followed by a single coefficient
map; the private transported-composition helper proves this equality directly.
Apply this to i', b on the left and a, i on the right. Naturality of the inverse
upperStarComp for i', B_k.ι moves the arbitrary coefficient morphism φ past the
restriction comparison. Apply the component associativity laws in
WeilConjectures.SixFunctors.BaseChange.Pasting to the triples i', b, B_j.ι and
i', B_k.ι, t for the left coefficient map, and to a, i, B_j.ι for the right.
Cancel the adjacent hom and inv comparisons. Both coefficient maps become the
inverse comparison for c, B_j.ι followed by the comparison for A_k.ι, t and the
restriction of φ to A_k. Hence the two transported cohomology maps agree.
Unfold openCohomologyRestriction, tailOpenCohomologyMapDegree and
openSquareCoefficient to identify this equality with the claim; proof irrelevance
identifies the commuting-square and inclusion proofs. No coefficient-system laws
are used. Empty and equal opens, identity stage arrows and zero φ are included. -/
theorem tailOpenCohomologyMapDegree_restriction
    {X : Scheme.{u}} {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (q : ℕ) {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X)
    (A B : X.Opens) (h : A ≤ B) (j k : Set.Ici i₀) (f : j ⟶ k)
      (x : Sheaf.H.{u + 1} ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D g₀ B j).ι).obj (F j.val)) q) :
      openCohomologyRestriction
        ((D.map (homOfLE k.property).op ≫ g₀).preimage_mono h) (F k.val) q
        ((tailOpenCohomologyMapDegree D g₀ B F φ q f).hom x) =
      (tailOpenCohomologyMapDegree D g₀ A F φ q f).hom (openCohomologyRestriction
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h) (F j.val) q x) := by
  let i := (D.obj (op j.val)).homOfLE
    ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h)
  let i' := (D.obj (op k.val)).homOfLE
    ((D.map (homOfLE k.property).op ≫ g₀).preimage_mono h)
  let a := tailStageOpenMap D g₀ A f
  let b := tailStageOpenMap D g₀ B f
  let t := D.map (homOfLE (show j.val ≤ k.val from f.le)).op
  let c := i' ≫ b
  let aj := (tailStageOpen D g₀ A j).ι
  let bj := (tailStageOpen D g₀ B j).ι
  let ak := (tailStageOpen D g₀ A k).ι
  let bk := (tailStageOpen D g₀ B k).ι
  have ha : ak ≫ t = a ≫ aj := by
    simp only [a, ak, aj, t, tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
  have hb : bk ≫ t = b ≫ bj := by
    simp only [b, bk, bj, t, tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
  have hi : i ≫ bj = aj := (D.obj (op j.val)).homOfLE_ι _
  have hi' : i' ≫ bk = ak := (D.obj (op k.val)).homOfLE_ι _
  have hc : c = a ≫ i := by
    apply (cancel_mono bj).1
    dsimp only [c]
    rw [Category.assoc, ← hb, ← Category.assoc, hi', Category.assoc, hi, ← ha]
  have hcA : ak ≫ t = c ≫ bj := by
    dsimp only [c]
    rw [Category.assoc, ← hb, ← Category.assoc, hi']
  let eB := upperStarComp AddCommGrpCat.{u + 1} b bj (bk ≫ t) hb
  let eA := upperStarComp AddCommGrpCat.{u + 1} a aj (ak ≫ t) ha
  let eX := upperStarComp AddCommGrpCat.{u + 1} i bj aj hi.symm
  let eY := upperStarComp AddCommGrpCat.{u + 1} i' bk ak hi'.symm
  let eBY := upperStarComp AddCommGrpCat.{u + 1} bk t
  let eAY := upperStarComp AddCommGrpCat.{u + 1} ak t
  let eL := upperStarComp AddCommGrpCat.{u + 1} i' b c rfl
  let eR := upperStarComp AddCommGrpCat.{u + 1} a i c hc
  let ψ := φ (homOfLE (show j.val ≤ k.val from f.le))
  have left₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' b bj c (bk ≫ t) (ak ≫ t) rfl hb hcA (F j.val)
  have left₂ := map_upperStarComp_hom_app_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' bk t ak (bk ≫ t) (ak ≫ t) hi'.symm rfl rfl (F j.val)
  have right₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} a i bj c aj (ak ≫ t) hc hi.symm hcA (F j.val)
  have hn := eY.inv.naturality ψ
  simp only [Functor.comp_map] at hn
  have hcoeff : eL.hom.app ((upperStar AddCommGrpCat.{u + 1} bj).obj (F j.val)) ≫
      (upperStar AddCommGrpCat.{u + 1} i').map
        (eB.inv.app (F j.val) ≫ eBY.hom.app (F j.val) ≫
          (upperStar AddCommGrpCat.{u + 1} bk).map ψ) ≫ eY.inv.app (F k.val) =
      eR.hom.app ((upperStar AddCommGrpCat.{u + 1} bj).obj (F j.val)) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map (eX.inv.app (F j.val)) ≫
          (eA.inv.app (F j.val) ≫ eAY.hom.app (F j.val) ≫
            (upperStar AddCommGrpCat.{u + 1} ak).map ψ) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hn]
    rw [reassoc_of% left₁, reassoc_of% left₂, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% right₁, Iso.hom_inv_id_app_assoc]
  unfold openCohomologyRestriction tailOpenCohomologyMapDegree
  simp only [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom,
    AddMonoidHom.comp_apply]
  unfold openSquareCoefficient
  change Sheaf.H.map (eY.inv.app (F k.val)) q
      (cohomologyMap i' ((upperStar AddCommGrpCat.{u + 1} bk).obj (F k.val)) q
        (Sheaf.H.map
          (eB.inv.app (F j.val) ≫ eBY.hom.app (F j.val) ≫
            (upperStar AddCommGrpCat.{u + 1} bk).map ψ) q
          (cohomologyMap b _ q x))) =
    Sheaf.H.map
      (eA.inv.app (F j.val) ≫ eAY.hom.app (F j.val) ≫
        (upperStar AddCommGrpCat.{u + 1} ak).map ψ) q
      (cohomologyMap a _ q (Sheaf.H.map (eX.inv.app (F j.val)) q
        (cohomologyMap i _ q x)))
  calc
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) :=
      cohomologyMap_transported_comp i' b c rfl _ _ _ _ _ q x
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) := by rw [hcoeff]
    _ = _ := (cohomologyMap_transported_comp a i c hc _ _ _ _ _ q x).symm

end AlgebraicGeometry.Etale
