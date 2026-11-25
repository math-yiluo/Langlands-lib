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

attribute [local irreducible] upperStar upperStarComp Sheaf.H.map
  cohomologyMap openCohomologyRestriction
  tailOpenCohomologyMapDegree tailOpenCohomologyLegDegree

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyMap_transported_comp_hom {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (hc : c = a ≫ b)
    (G : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (K : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (l : (upperStar AddCommGrpCat.{u + 1} b).obj G ⟶ F)
    (k : (upperStar AddCommGrpCat.{u + 1} a).obj F ⟶ K)
    (q : ℕ) :
    (Sheaf.H.map k q).comp ((cohomologyMap a F q).comp
      ((Sheaf.H.map l q).comp (cohomologyMap b G q))) =
      (Sheaf.H.map (((upperStarComp AddCommGrpCat.{u + 1} a b c hc).hom.app G) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map l ≫ k) q).comp
          (cohomologyMap c G q) := by
  ext x
  change Sheaf.H.map k q
    (cohomologyMap a F q (Sheaf.H.map l q (cohomologyMap b G q x))) = _
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
private theorem openSquare_restriction
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    {A B : X.Opens} (h : A ≤ B) {C E : Y.Opens} (h' : C ≤ E)
    (a : C.toScheme ⟶ A.toScheme) (b : E.toScheme ⟶ B.toScheme)
    (ha : C.ι ≫ f = a ≫ A.ι) (hb : E.ι ≫ f = b ≫ B.ι)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G)
    (q : ℕ) (x : Sheaf.H ((upperStar AddCommGrpCat.{u + 1} B.ι).obj F) q) :
    openCohomologyRestriction h' G q
      (Sheaf.H.map (openSquareCoefficient f B.ι E.ι b hb F G φ) q
        (cohomologyMap b _ q x)) =
    Sheaf.H.map (openSquareCoefficient f A.ι C.ι a ha F G φ) q
      (cohomologyMap a _ q (openCohomologyRestriction h F q x)) := by
  let i := X.homOfLE h
  let i' := Y.homOfLE h'
  let c := i' ≫ b
  let t := C.ι ≫ f
  let s := E.ι ≫ f
  have hc : c = a ≫ i := by
    apply (cancel_mono B.ι).1
    dsimp [c, i, i']
    rw [Category.assoc, ← hb, ← Category.assoc, Y.homOfLE_ι,
      Category.assoc, X.homOfLE_ι, ← ha]
  have ht : t = c ≫ B.ι := by
    dsimp [t, c, i']
    rw [Category.assoc, ← hb, ← Category.assoc, Y.homOfLE_ι]
  let eB := upperStarComp AddCommGrpCat.{u + 1} b B.ι s hb
  let eA := upperStarComp AddCommGrpCat.{u + 1} a A.ι t ha
  let eX := upperStarComp AddCommGrpCat.{u + 1} i B.ι A.ι (X.homOfLE_ι h).symm
  let eY := upperStarComp AddCommGrpCat.{u + 1} i' E.ι C.ι (Y.homOfLE_ι h').symm
  let eBY := upperStarComp AddCommGrpCat.{u + 1} E.ι f
  let eAY := upperStarComp AddCommGrpCat.{u + 1} C.ι f
  let eL := upperStarComp AddCommGrpCat.{u + 1} i' b c rfl
  let eR := upperStarComp AddCommGrpCat.{u + 1} a i c hc
  have left₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' b B.ι c s t rfl hb ht F
  have left₂ := map_upperStarComp_hom_app_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} i' E.ι f C.ι s t
      (Y.homOfLE_ι h').symm rfl rfl F
  have right₁ := upperStarComp_hom_app_map_upperStarComp_inv_app
    AddCommGrpCat.{u + 1} a i B.ι c A.ι t hc (X.homOfLE_ι h).symm ht F
  have hn := eY.inv.naturality φ
  simp only [Functor.comp_map] at hn
  have hcoeff : eL.hom.app ((upperStar AddCommGrpCat.{u + 1} B.ι).obj F) ≫
      (upperStar AddCommGrpCat.{u + 1} i').map
        (eB.inv.app F ≫ eBY.hom.app F ≫ (upperStar AddCommGrpCat.{u + 1} E.ι).map φ) ≫
        eY.inv.app G =
      eR.hom.app ((upperStar AddCommGrpCat.{u + 1} B.ι).obj F) ≫
        (upperStar AddCommGrpCat.{u + 1} a).map (eX.inv.app F) ≫
          (eA.inv.app F ≫ eAY.hom.app F ≫
            (upperStar AddCommGrpCat.{u + 1} C.ι).map φ) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hn, reassoc_of% left₁, reassoc_of% left₂, Iso.hom_inv_id_app_assoc,
      reassoc_of% right₁, Iso.hom_inv_id_app_assoc]
  unfold openCohomologyRestriction
  dsimp only [AddMonoidHom.comp_apply]
  change Sheaf.H.map (eY.inv.app G) q
      (cohomologyMap i' ((upperStar AddCommGrpCat.{u + 1} E.ι).obj G) q
        (Sheaf.H.map (eB.inv.app F ≫ eBY.hom.app F ≫
          (upperStar AddCommGrpCat.{u + 1} E.ι).map φ) q (cohomologyMap b _ q x))) =
    Sheaf.H.map (eA.inv.app F ≫ eAY.hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} C.ι).map φ) q
        (cohomologyMap a _ q (Sheaf.H.map (eX.inv.app F) q (cohomologyMap i _ q x)))
  calc
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) :=
      by
        exact DFunLike.congr_fun
          (cohomologyMap_transported_comp_hom i' b c rfl _ _ _ _ _ q) x
    _ = Sheaf.H.map _ q (cohomologyMap c _ q x) := by rw [hcoeff]
    _ = _ := (by
        exact (DFunLike.congr_fun
          (cohomologyMap_transported_comp_hom a i c hc _ _ _ _ _ q) x).symm)

/-- For arbitrary nested opens A ≤ B of X, restriction from B to A on the limit
inverse-image opens commutes with the actual cohomology leg from each tail stage.
The coefficient map is (eG j.val).inv followed by the cocone leg. The cone and
coefficient cocone need not be limiting or colimiting.

Source: Stacks Project, Tag 01F7 (pullback and coefficient functoriality),
Tag 09YQ (restricted stage and cone maps); parent proof step 1.
(blueprint: lem-weil-pbc-etale-limit-cone-restriction-naturality)

Proof: First prove restriction naturality for arbitrary commuting open squares and
an arbitrary coefficient morphism φ : f*F → G. Cancel the larger stage-open inclusion
to identify the two composites from the smaller source open to the larger stage open.
Coefficient naturality and composition functoriality of cohomology express both paths
as the same pullback followed by a coefficient map. Naturality of upperStarComp.inv
moves φ to the last factor; the three component associativity identities for
upperStarComp then identify the coefficient maps by cancelling adjacent hom/inv pairs.
Specialize this square calculation to f = c.π.app (op j.val), the nested stage and
limit opens, tailLimitOpenMap for their two vertical maps, and coefficient
(eG j.val).inv ≫ L.ι.app j.val. The commuting-square hypotheses are exactly
Scheme.Hom.resLE_comp_ι. Expanding tailOpenCohomologyLegDegree gives the claimed
pointwise equality. No universal property, coefficient-system naturality, directedness,
or nonemptiness is used. Empty and equal opens and zero coefficients are included. -/
theorem tailOpenCohomologyLegDegree_restriction
    {X : Scheme.{u}} {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (q : ℕ) {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X)
    (A B : X.Opens) (h : A ≤ B) (j : Set.Ici i₀)
      (x : Sheaf.H.{u + 1} ((upperStar AddCommGrpCat.{u + 1}
        (tailStageOpen D g₀ B j).ι).obj (F j.val)) q) :
      openCohomologyRestriction
        ((c.π.app (op i₀) ≫ g₀).preimage_mono h) L.pt q
        ((tailOpenCohomologyLegDegree D c g₀ B F G eG L q j).hom x) =
      (tailOpenCohomologyLegDegree D c g₀ A F G eG L q j).hom (openCohomologyRestriction
        ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h) (F j.val) q x) := by
  unfold tailOpenCohomologyLegDegree
  exact openSquare_restriction (c.π.app (op j.val))
    ((D.map (homOfLE j.property).op ≫ g₀).preimage_mono h)
    ((c.π.app (op i₀) ≫ g₀).preimage_mono h)
    (tailLimitOpenMap D c g₀ A j) (tailLimitOpenMap D c g₀ B j)
    (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι])
    (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι])
    (F j.val) L.pt ((eG j.val).inv ≫ L.ι.app j.val) q x

end AlgebraicGeometry.Etale
