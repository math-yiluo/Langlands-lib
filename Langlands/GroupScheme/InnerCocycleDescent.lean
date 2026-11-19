import Langlands.GroupScheme.InnerCocycleTwist
import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.LocalGroupIsoBaseChangeNaturality

/-! # Inner descent data of natural cocycles -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cocycle

variable {B : Scheme.{u}} {G : GroupScheme B} {U : Over B} (ξ : Cocycle G U)

open Descent

local notation "p" => Over.hom U
local notation "W" => Over.mk (Descent.fst p ≫ p)
local notation "GU" => Functor.obj (GroupScheme.baseChange p) G

private def overlapFirst : W ⟶ U := Over.homMk (Descent.fst p) rfl

private def overlapSecond : W ⟶ U := Over.homMk (Descent.snd p) pullback.condition.symm

/-- At an overlap point conjugate by the inverse cocycle value. -/
private def innerOverlapChart : LocalGroupIso G G W where
  toFun w := MulAut.conj (w ≫ ξ.toFun overlapFirst overlapSecond)⁻¹
  naturality t w x := by
    simp only [MulAut.conj_apply, MonObj.comp_mul, GrpObj.comp_inv,
      Category.assoc]

private theorem innerOverlapChart_apply {T : Over B} (w : T ⟶ W) (x : T ⟶ G.X) :
    (innerOverlapChart ξ).toFun w x =
      (ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))⁻¹ * x *
        ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond) := by
  rw [ξ.naturality]
  simp only [innerOverlapChart, MulAut.conj_apply, inv_inv]

/-- The overlap map of the inner datum on the pullback of `G` to `U`. -/
def innerOverlap : OverlapIso p GU :=
  pullbackComparison p (Descent.fst p) (W).hom rfl G ≪≫
    (innerOverlapChart ξ).toBaseChangeIso ≪≫
    (pullbackComparison p (Descent.snd p) (W).hom pullback.condition.symm G).symm

private theorem innerOverlap_apply {T : Over B} (w : T ⟶ W) (x : T ⟶ G.X) :
    let y := (LocalGroupIso.coverPointsEquiv G (w ≫ overlapFirst)).symm x
    pullback.lift y.left w.left (Over.w y) ≫
        (innerOverlap ξ).hom.hom.hom.left ≫ pullback.fst (GU).X.hom (Descent.snd p) ≫
          pullback.fst G.X.hom p =
      (((ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))⁻¹ * x *
        ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))).left := by
  intro y
  let e := pullbackComparison p (Descent.fst p) (W).hom rfl G
  have hh : pullback.lift y.left w.left (Over.w y) ≫ e.hom.hom.hom.left =
      ((LocalGroupIso.coverPointsEquiv G w).symm x).left := by
    apply pullback.hom_ext
    · simp only [e, Category.assoc, pullbackComparison_hom_fst,
        LocalGroupIso.coverPointsEquiv_symm_left, pullback.lift_fst, y]
      erw [pullback.lift_fst_assoc, pullback.lift_fst]
    · have hw := Over.w e.hom.hom.hom
      change e.hom.hom.hom.left ≫ pullback.snd G.X.hom (W).hom =
        pullback.snd (GU).X.hom (Descent.fst p) at hw
      simp only [Category.assoc, hw]
      erw [pullback.lift_snd]
      exact (Over.w ((LocalGroupIso.coverPointsEquiv G w).symm x)).symm
  change pullback.lift y.left w.left (Over.w y) ≫
      ((e ≪≫ (innerOverlapChart ξ).toBaseChangeIso ≪≫
        (pullbackComparison p (Descent.snd p) (W).hom pullback.condition.symm G).symm).hom.hom.hom.left) ≫
          pullback.fst (GU).X.hom (Descent.snd p) ≫ pullback.fst G.X.hom p = _
  simp only [Iso.trans_hom, Iso.symm_hom, Grp.comp_hom_hom, Over.comp_left, Category.assoc,
    pullbackComparison_inv_fst]
  rw [← Category.assoc (pullback.lift _ _ _) e.hom.hom.hom.left]
  erw [hh, ← LocalGroupIso.ofBaseChangeIso_toFun_left]
  rw [LocalGroupIso.ofBaseChangeIso_toBaseChangeIso, innerOverlapChart_apply]

private def towerPoint {T : Over B} {A : Scheme.{u}} (t : T.left ⟶ A) (a : A ⟶ U.left)
    (h : t ≫ a ≫ p = T.hom) (x : T ⟶ G.X) :
    T.left ⟶ ((GroupScheme.baseChange a).obj GU).X.left :=
  pullback.lift (pullback.lift x.left (t ≫ a) (by rw [Over.w x, Category.assoc, h])) t
    (pullback.lift_snd _ _ _)

@[reassoc] private theorem towerPoint_original {T : Over B} {A : Scheme.{u}}
    (t : T.left ⟶ A) (a : A ⟶ U.left) (h : t ≫ a ≫ p = T.hom) (x : T ⟶ G.X) :
    towerPoint t a h x ≫ pullback.fst (GU).X.hom a ≫ pullback.fst G.X.hom p = x.left := by
  simp only [towerPoint, pullback.lift_fst_assoc, pullback.lift_fst]

private theorem towerPoint_base {T : Over B} {A : Scheme.{u}}
    (t : T.left ⟶ A) (a : A ⟶ U.left) (h : t ≫ a ≫ p = T.hom) (x : T ⟶ G.X) :
    towerPoint t a h x ≫ pullback.snd (GU).X.hom a = t :=
  pullback.lift_snd _ _ _

private theorem eq_towerPoint {T : Over B} {A : Scheme.{u}} (t : T.left ⟶ A)
    (a : A ⟶ U.left) (h : t ≫ a ≫ p = T.hom) (x : T ⟶ G.X)
    (y : T.left ⟶ ((GroupScheme.baseChange a).obj GU).X.left)
    (hy : y ≫ pullback.snd (GU).X.hom a = t)
    (hx : y ≫ pullback.fst (GU).X.hom a ≫ pullback.fst G.X.hom p = x.left) :
    y = towerPoint t a h x := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, towerPoint_original] using hx
    · have hy' : y ≫ pullback.fst (GU).X.hom a ≫ pullback.snd G.X.hom p = t ≫ a := by
        change y ≫ pullback.fst (GU).X.hom a ≫ (GU).X.hom = _
        rw [pullback.condition, ← Category.assoc, hy]
      rw [Category.assoc, Category.assoc, hy']
      simp only [towerPoint, pullback.lift_fst_assoc, pullback.lift_snd]
  · exact hy.trans (towerPoint_base t a h x).symm

/-- The inner overlap gives conjugation after pulling to any pair of base coordinates. -/
private theorem innerPullHom_tower {T : Over B} {A : Scheme.{u}}
    (q : A ⟶ Overlap p) {a b : A ⟶ U.left}
    (ha : q ≫ Descent.fst p = a) (hb : q ≫ Descent.snd p = b)
    (t : T.left ⟶ A) (h₁ : t ≫ a ≫ p = T.hom) (h₂ : t ≫ b ≫ p = T.hom)
    (a₀ b₀ : T ⟶ U) (ha₀ : t ≫ a = a₀.left) (hb₀ : t ≫ b = b₀.left)
    (x : T ⟶ G.X) :
    let c := ξ.toFun a₀ b₀
    towerPoint t a h₁ x ≫ (pullHom q ha hb (innerOverlap ξ).hom).hom.hom.left =
      towerPoint t b h₂ (c⁻¹ * x * c) := by
  intro c
  let w : T ⟶ W := Over.homMk (t ≫ q)
    (by rw [Category.assoc, show (W).hom = Descent.fst p ≫ p from rfl,
      ← Category.assoc q, ha]; exact h₁)
  have hwa : w ≫ overlapFirst = a₀ := by
    apply Over.OverMorphism.ext
    change (t ≫ q) ≫ Descent.fst p = _
    rw [Category.assoc, ha, ha₀]
  have hwb : w ≫ overlapSecond = b₀ := by
    apply Over.OverMorphism.ext
    change (t ≫ q) ≫ Descent.snd p = _
    rw [Category.assoc, hb, hb₀]
  apply eq_towerPoint
  · have hw := Over.w (pullHom q ha hb (innerOverlap ξ).hom).hom.hom
    change (pullHom q ha hb (innerOverlap ξ).hom).hom.hom.left ≫
      pullback.snd (GU).X.hom b = pullback.snd (GU).X.hom a at hw
    rw [Category.assoc, hw, towerPoint_base]
  · have hy : (w ≫ overlapFirst).left = t ≫ a := by
      change (t ≫ q) ≫ Descent.fst p = _
      rw [Category.assoc, ha]
    let y := (LocalGroupIso.coverPointsEquiv G (w ≫ overlapFirst)).symm x
    have hleft : y.left = pullback.lift x.left (t ≫ a) (by rw [Over.w x, Category.assoc, h₁]) := by
      erw [LocalGroupIso.coverPointsEquiv_symm_left]
      apply pullback.hom_ext
      · simp only [pullback.lift_fst]
      · simp only [pullback.lift_snd, hy]
    have hyBase : (show T.left ⟶ (GU).X.left from y.left) ≫ (GU).X.hom = t ≫ a :=
      (Over.w y).trans hy
    have htower : towerPoint t a h₁ x = pullback.lift y.left t hyBase := by
      apply pullback.hom_ext
      · erw [pullback.lift_fst, pullback.lift_fst]
        exact hleft.symm
      · exact (towerPoint_base t a h₁ x).trans (pullback.lift_snd _ _ _).symm
    simp only [Category.assoc, htower]
    erw [reassoc_of% (pullHom_eval q ha hb (innerOverlap ξ).hom y.left t hyBase)]
    have hconj : (ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))⁻¹ * x *
        ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond) = c⁻¹ * x * c := by
      rw [hwa, hwb]
    exact (innerOverlap_apply ξ w x).trans (congrArg (fun z => z.left) hconj)

/-- The conjugation overlap satisfies the Čech cocycle identity. -/
theorem innerOverlap_cocycle : Descent.Cocycle (innerOverlap ξ) := by
  let J := (GroupScheme.baseChange (p1 p)).obj GU
  let t := J.X.hom
  let T : Over B := Over.mk (t ≫ p1 p ≫ p)
  have h₁ : t ≫ p1 p ≫ p = T.hom := rfl
  have h₂ : t ≫ p2 p ≫ p = T.hom := by
    change t ≫ (p12 p ≫ Descent.snd p) ≫ p = t ≫ (p12 p ≫ Descent.fst p) ≫ p
    simpa only [Category.assoc] using
      congrArg (fun f : Overlap p ⟶ B => t ≫ p12 p ≫ f)
        (pullback.condition (f := p) (g := p)).symm
  have h₃ : t ≫ p3 p ≫ p = T.hom := by
    calc
      _ = t ≫ (p23 p ≫ Descent.fst p) ≫ p := by
        simpa only [p3, Category.assoc] using
          congrArg (fun f : Overlap p ⟶ B => t ≫ p23 p ≫ f)
            (pullback.condition (f := p) (g := p)).symm
      _ = _ := by rw [p23_fst]; exact h₂
  let a₁ : T ⟶ U := Over.homMk (t ≫ p1 p) ((Category.assoc _ _ _).trans h₁)
  let a₂ : T ⟶ U := Over.homMk (t ≫ p2 p) ((Category.assoc _ _ _).trans h₂)
  let a₃ : T ⟶ U := Over.homMk (t ≫ p3 p) ((Category.assoc _ _ _).trans h₃)
  let x : T ⟶ G.X := Over.homMk
    (pullback.fst (GU).X.hom (p1 p) ≫ pullback.fst G.X.hom p) (by
      change (_ ≫ _) ≫ G.X.hom = t ≫ p1 p ≫ p
      rw [Category.assoc, pullback.condition]
      change pullback.fst (GU).X.hom (p1 p) ≫ (GU).X.hom ≫ p = _
      erw [← Category.assoc, pullback.condition, Category.assoc])
  have hx : towerPoint (T := T) t (p1 p) h₁ x = 𝟙 J.X.left := by
    symm
    apply eq_towerPoint (T := T)
    · exact Category.id_comp _
    · exact Category.id_comp _
  let x₂ := (ξ.toFun a₁ a₂)⁻¹ * x * ξ.toFun a₁ a₂
  have hc : (ξ.toFun a₂ a₃)⁻¹ * x₂ * ξ.toFun a₂ a₃ =
      (ξ.toFun a₁ a₃)⁻¹ * x * ξ.toFun a₁ a₃ := by
    rw [ξ.cocycle a₁ a₂ a₃]
    dsimp only [x₂]
    group
  have h12 := innerPullHom_tower (T := T) ξ (p12 p) rfl rfl t h₁ h₂ a₁ a₂ rfl rfl x
  have h23 := innerPullHom_tower (T := T) ξ (p23 p) (p23_fst p) rfl t h₂ h₃ a₂ a₃ rfl rfl x₂
  have h13 := innerPullHom_tower (T := T) ξ (p13 p) (p13_fst p) (p13_snd p) t h₁ h₃ a₁ a₃
    rfl rfl x
  change (iso12 (innerOverlap ξ)).hom ≫ (iso23 (innerOverlap ξ)).hom =
    (iso13 (innerOverlap ξ)).hom
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (pullHom (p12 p) rfl rfl (innerOverlap ξ).hom).hom.hom.left ≫
    (pullHom (p23 p) (p23_fst p) rfl (innerOverlap ξ).hom).hom.hom.left =
      (pullHom (p13 p) (p13_fst p) (p13_snd p) (innerOverlap ξ).hom).hom.hom.left
  calc
    _ = (towerPoint (T := T) t (p1 p) h₁ x ≫
          (pullHom (p12 p) rfl rfl (innerOverlap ξ).hom).hom.hom.left) ≫
        (pullHom (p23 p) (p23_fst p) rfl (innerOverlap ξ).hom).hom.hom.left := by
      rw [hx]
      erw [Category.id_comp]
    _ = towerPoint (T := T) t (p3 p) h₃ ((ξ.toFun a₂ a₃)⁻¹ * x₂ * ξ.toFun a₂ a₃) := by
      rw [h12, h23]
    _ = _ := by
      rw [hc, ← h13, hx]
      exact Category.id_comp _

/-- The descent datum obtained by conjugating each overlap by the inverse cocycle value. -/
def innerDatum : Datum p GU where
  overlap := innerOverlap ξ
  cocycle := innerOverlap_cocycle ξ

private theorem towerPoint_first {T : Over B} {A : Scheme.{u}}
    (t : T.left ⟶ A) (a : A ⟶ U.left) (h : t ≫ a ≫ p = T.hom)
    (a₀ : T ⟶ U) (ha : t ≫ a = a₀.left) (x : T ⟶ G.X) :
    towerPoint t a h x ≫ pullback.fst (GU).X.hom a =
      ((LocalGroupIso.coverPointsEquiv G a₀).symm x).left := by
  rw [towerPoint, pullback.lift_fst]
  erw [LocalGroupIso.coverPointsEquiv_symm_left]
  apply pullback.hom_ext
  · simp only [pullback.lift_fst]
  · simp only [pullback.lift_snd, ha]

@[reassoc] private theorem towerPoint_map_iso {H : GroupScheme B}
    (e : (GroupScheme.baseChange p).obj H ≅ GU) {T : Over B} {A : Scheme.{u}}
    (t : T.left ⟶ A) (a : A ⟶ U.left) (h : t ≫ a ≫ p = T.hom)
    (a₀ : T ⟶ U) (ha : t ≫ a = a₀.left) (x : T ⟶ H.X) :
    towerPoint t a h x ≫ ((GroupScheme.baseChange a).map e.hom).hom.hom.left =
      towerPoint t a h ((LocalGroupIso.ofBaseChangeIso e).toFun a₀ x) := by
  apply eq_towerPoint
  · rw [Category.assoc, show ((GroupScheme.baseChange a).map e.hom).hom.hom.left ≫
        pullback.snd (GU).X.hom a =
        pullback.snd ((GroupScheme.baseChange p).obj H).X.hom a from Over.w _, towerPoint_base]
  · have he : ((GroupScheme.baseChange a).map e.hom).hom.hom.left ≫
        pullback.fst (GU).X.hom a =
      pullback.fst ((GroupScheme.baseChange p).obj H).X.hom a ≫ e.hom.hom.hom.left :=
        pullback.lift_fst _ _ _
    rw [Category.assoc, ← Category.assoc ((GroupScheme.baseChange a).map e.hom).hom.hom.left,
      he, Category.assoc, ← Category.assoc (towerPoint t a h x), towerPoint_first t a h a₀ ha]
    exact (LocalGroupIso.ofBaseChangeIso_toFun_left e a₀ x).symm

@[reassoc] private theorem towerPoint_canonicalOverlap {T : Over B}
    (t : T.left ⟶ Overlap p) (h₁ : t ≫ Descent.fst p ≫ p = T.hom)
    (h₂ : t ≫ Descent.snd p ≫ p = T.hom) (x : T ⟶ G.X) :
    towerPoint t (Descent.fst p) h₁ x ≫ (canonicalOverlap p G).hom.hom.hom.left =
      towerPoint t (Descent.snd p) h₂ x := by
  apply eq_towerPoint
  · rw [Category.assoc, show (canonicalOverlap p G).hom.hom.hom.left ≫
        pullback.snd (GU).X.hom (Descent.snd p) =
        pullback.snd (GU).X.hom (Descent.fst p) from Over.w _, towerPoint_base]
  · simp only [Category.assoc, canonicalOverlap_fst, towerPoint_original]

private theorem towerPoint_innerOverlap {T : Over B} (w : T ⟶ W)
    (h₁ : w.left ≫ Descent.fst p ≫ p = T.hom) (x : T ⟶ G.X) :
    towerPoint w.left (Descent.fst p) h₁ x ≫ (innerOverlap ξ).hom.hom.hom.left ≫
        pullback.fst (GU).X.hom (Descent.snd p) ≫ pullback.fst G.X.hom p =
      (((ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))⁻¹ * x *
        ξ.toFun (w ≫ overlapFirst) (w ≫ overlapSecond))).left := by
  let y := (LocalGroupIso.coverPointsEquiv G (w ≫ overlapFirst)).symm x
  have hpoint : towerPoint w.left (Descent.fst p) h₁ x = pullback.lift y.left w.left (Over.w y) := by
    apply pullback.hom_ext
    · exact (towerPoint_first w.left (Descent.fst p) h₁ (w ≫ overlapFirst) rfl x).trans
        (pullback.lift_fst _ _ _).symm
    · exact (towerPoint_base w.left (Descent.fst p) h₁ x).trans (pullback.lift_snd _ _ _).symm
  rw [hpoint]
  exact innerOverlap_apply ξ w x

private theorem innerSolution_transition (s : Solution (ξ.innerDatum))
    {T : Over B} (a b : T ⟶ U) (x : T ⟶ s.obj.X) :
    (LocalGroupIso.ofBaseChangeIso s.iso).toFun b x =
      (ξ.toFun a b)⁻¹ * (LocalGroupIso.ofBaseChangeIso s.iso).toFun a x * ξ.toFun a b := by
  let t := pullback.lift a.left b.left ((Over.w a).trans (Over.w b).symm)
  have ha : t ≫ Descent.fst p = a.left := pullback.lift_fst _ _ _
  have hb : t ≫ Descent.snd p = b.left := pullback.lift_snd _ _ _
  have h₁ : t ≫ Descent.fst p ≫ p = T.hom := by rw [← Category.assoc, ha, Over.w a]
  have h₂ : t ≫ Descent.snd p ≫ p = T.hom := by rw [← Category.assoc, hb, Over.w b]
  let w : T ⟶ W := Over.homMk t h₁
  have hwa : w ≫ overlapFirst = a := Over.OverMorphism.ext ha
  have hwb : w ≫ overlapSecond = b := Over.OverMorphism.ext hb
  let y := towerPoint t (Descent.fst p) h₁ x
  have h := congrArg (fun f => y ≫ f.hom.hom.left ≫
    pullback.fst (GU).X.hom (Descent.snd p) ≫ pullback.fst G.X.hom p) s.compatible
  change y ≫ (((GroupScheme.baseChange (Descent.fst p)).map s.iso.hom ≫
      (innerOverlap ξ).hom).hom.hom.left) ≫ _ =
    y ≫ (((canonicalOverlap p s.obj).hom ≫
      (GroupScheme.baseChange (Descent.snd p)).map s.iso.hom).hom.hom.left) ≫ _ at h
  simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc, y,
    towerPoint_map_iso_assoc s.iso t (Descent.fst p) h₁ a ha x,
    towerPoint_canonicalOverlap_assoc t h₁ h₂ x,
    towerPoint_map_iso_assoc s.iso t (Descent.snd p) h₂ b hb x,
    towerPoint_original] at h
  have h' := towerPoint_innerOverlap ξ w h₁ ((LocalGroupIso.ofBaseChangeIso s.iso).toFun a x)
  rw [hwa, hwb] at h'
  apply Over.OverMorphism.ext
  exact h.symm.trans h'

private def innerAffineSolution (hB : IsAffine B) (hU : IsAffine U.left)
    (hGU : IsAffine (GU).X.left) (hp : Flat p) (hs : Surjective p) : Solution (ξ.innerDatum) :=
  @Datum.affineSolution B U.left p GU (ξ.innerDatum) hB hU hGU hp hs

/-- Effective affine descent of the conjugation datum supplies the inner form and its chart. -/
def innerTwist [hB : IsAffine B] [hU : IsAffine U.left] (hGU : IsAffine (GU).X.left)
    (hp : Flat p) (hs : Surjective p) : ξ.InnerTwist where
  obj := (innerAffineSolution ξ hB hU hGU hp hs).obj
  chart := LocalGroupIso.ofBaseChangeIso (innerAffineSolution ξ hB hU hGU hp hs).iso
  transition := ξ.innerSolution_transition (innerAffineSolution ξ hB hU hGU hp hs)

/-- Over the original cover the descended group is isomorphic to the original group. -/
def innerTwistIso [hB : IsAffine B] [hU : IsAffine U.left] (hGU : IsAffine (GU).X.left)
    (hp : Flat p) (hs : Surjective p) :
    (GroupScheme.baseChange p).obj (ξ.innerTwist hGU hp hs).obj ≅ GU :=
  (innerAffineSolution ξ hB hU hGU hp hs).iso

end Langlands.GroupScheme.Cocycle
