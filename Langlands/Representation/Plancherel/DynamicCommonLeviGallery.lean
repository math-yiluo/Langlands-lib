import Langlands.GroupScheme.Rational.ParabolicGalleryAvoidingProof
import Langlands.GroupScheme.Rational.DynamicUnipotentIntersectionRoots
import Langlands.Representation.Plancherel.DynamicCommonLeviComposition

/-! # Distance-additive galleries for dynamic parabolics with a common Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LinearAlgebra.FiniteHyperplaneSegment
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.Plancherel.DynamicCommonLeviComposition

open DynamicOppositeStandardIntertwining
attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine

section Segment

variable {V I : Type*} [AddCommGroup V] [Module ℚ V]
  (f : I → Module.Dual ℚ V)

private def SignsBetween (x y z : V) : Prop :=
  (∀ i, 0 < f i x → 0 < f i z → 0 < f i y) ∧
    (∀ i, f i x < 0 → f i z < 0 → f i y < 0)

private theorem signsBetween_segment {x y : V} {a b c : ℚ} (hab : a ≤ b) (hbc : b ≤ c) :
    SignsBetween f (segment x y a) (segment x y b) (segment x y c) := by
  have hf (i : I) (t : ℚ) :
      f i (segment x y t) = f i x + t * (f i y - f i x) :=
    apply_segment_formula (f i) x y t
  constructor
  · intro i ha hc
    rw [hf] at ha hc ⊢
    rcases le_total (f i x) (f i y) with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr h)]
  · intro i ha hc
    rw [hf] at ha hc ⊢
    rcases le_total (f i x) (f i y) with h | h
    · nlinarith [mul_nonneg (sub_nonneg.mpr hbc) (sub_nonneg.mpr h)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]

private theorem signsBetween_of_sameChamber_right {x y z z' : V} (h : SignsBetween f x y z)
    (hzz' : SameChamber f z z') : SignsBetween f x y z' := by
  constructor
  · intro i hx hz'
    apply h.1 i hx
    exact pos_of_mul_pos_left (hzz' i) hz'.le
  · intro i hx hz'
    apply h.2 i hx
    exact neg_of_mul_pos_left (hzz' i) hz'.le

private theorem chamberChain_between [Finite I] {x y : V}
    (hx : Regular f x) (hy : Regular f y) :
    Relation.ReflTransGen (fun v w =>
      ChamberStep f (fun _ => False) v w ∧ SignsBetween f x v w ∧ SignsBetween f v w y)
      x y := by
  obtain ⟨z, hz, hyz, hprop⟩ := exists_segment_with_proportional_crossings f hx hy
  let R : V → V → Prop := fun v w =>
    ChamberStep f (fun _ => False) v w ∧ SignsBetween f x v w ∧ SignsBetween f v w y
  let r : ℚ → ℚ → Prop := fun a b => R (segment x z a) (segment x z b)
  have hchain : Relation.ReflTransGen r 0 1 := by
    apply reflTransGen_of_sparse_intervals r (crossingTimes f x z) (by norm_num)
      (fun t ht => ((mem_crossingTimes_iff f x z t).mp ht).1)
    intro a b ha hab hb ha' hb' hs
    have h₁ : SignsBetween f x (segment x z a) (segment x z b) := by
      simpa only [LinearAlgebra.FiniteHyperplaneSegment.segment, sub_zero, one_smul, zero_smul,
        add_zero] using
        signsBetween_segment f (x := x) (y := z) ha hab.le
    have h₂ : SignsBetween f (segment x z a) (segment x z b) z := by
      simpa only [LinearAlgebra.FiniteHyperplaneSegment.segment, sub_self, zero_smul, one_smul,
        zero_add] using
        signsBetween_segment f (x := x) (y := z) hab.le hb
    exact ⟨chamberStep_of_sparse_interval f _ hx hz hprop (fun _ h => h.elim)
      ha hab hb ha' hb' hs, h₁, signsBetween_of_sameChamber_right f h₂ (sameChamber_symm f hyz)⟩
  have h := Relation.ReflTransGen.lift (segment x z) (p := R) (fun _ _ h => h) 0 1 hchain
  change Relation.ReflTransGen R (segment x z 0) (segment x z 1) at h
  have hxz : Relation.ReflTransGen R x z := by
    simpa [LinearAlgebra.FiniteHyperplaneSegment.segment] using h
  have hzy : R z y := by
    refine ⟨Or.inl (sameChamber_symm f hyz), ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro i _ h
      exact pos_of_mul_pos_left ((sameChamber_symm f hyz) i) h.le
    · intro i _ h
      exact neg_of_mul_pos_left ((sameChamber_symm f hyz) i) h.le
    · exact fun _ _ h => h
    · exact fun _ _ h => h
  exact hxz.tail hzy

end Segment

section RootSigns

open RationalCocharacter

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}

private theorem distanceAdditive_of_signsBetween (hA : IsSplitTorus A.toGrp)
    (i : A.toGrp ⟶ G) {x y z : Space A}
    (r : IntegralRealization x) (s : IntegralRealization y) (t : IntegralRealization z)
    (h : SignsBetween (rootForms i) x y z) :
    IsDistanceAdditive (CommGroupScheme.groupHom r.cocharacter ≫ i)
      (CommGroupScheme.groupHom s.cocharacter ≫ i)
      (CommGroupScheme.groupHom t.cocharacter ≫ i) := by
  constructor
  · apply RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots inferInstance inferInstance hA i
    intro α hα hx
    exact (s.pairing_pos_iff α).2
      (h.1 ⟨α, hα.1⟩ ((r.pairing_pos_iff α).1 hx) ((t.pairing_pos_iff α).1 hα.2))
  · change radical (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom r.cocharacter ≫ i)) ⊓
        radical (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom t.cocharacter ≫ i)) ≤
      radical (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom s.cocharacter ≫ i))
    simp only [← groupHom_neg_comp_eq_oppositeCocharacter]
    apply RelativeRoot.dynamicUnipotent_inf_le_of_positiveRoots inferInstance inferInstance hA i
    intro α hα hx
    have pairing_neg (w : Space A) (q : IntegralRealization w) :
        0 < latticePairing A α (-q.cocharacter) ↔ w (toRat α) < 0 := by
      rw [map_neg, neg_pos]
      simpa only [not_le] using not_congr (q.pairing_nonneg_iff α)
    exact (pairing_neg _ s).2 (h.2 ⟨α, hα.1⟩ ((pairing_neg _ r).1 hx)
      ((pairing_neg _ t).1 hα.2))

end RootSigns

section Walls

open RationalCocharacter

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

/-- A rank-one wall with an actual dynamic outer parabolic and Levi.
The inner parabolic data retain the original representative of the common Levi. -/
structure DynamicRankOneWall (χ ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) where
  outer : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G
  wall : RationalRankOneWallData (Dynamic.Affine.centralizerHom χ)
    (Dynamic.parabolic ψ) (Dynamic.parabolic ψ')
  outerParabolic : (Dynamic.parabolic outer).IsRepresentedBy wall.p
  outerLevi : (Dynamic.centralizer outer).IsRepresentedBy (wall.m ≫ wall.p)
  outerRadical_le : radical outer ≤ radical ψ
  outerRadical_le' : radical outer ≤ radical ψ'

/-- The cocharacters have the same parabolic and the same two radicals. -/
def SameDynamicChamber (ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop :=
  Dynamic.parabolic ψ = Dynamic.parabolic ψ' ∧ Dynamic.unipotent ψ = Dynamic.unipotent ψ' ∧
    Dynamic.unipotent (Dynamic.inverseCocharacter ψ) =
      Dynamic.unipotent (Dynamic.inverseCocharacter ψ')

/-- A step retains the common centralizer and both endpoint distance equalities.
It can preserve the chamber or cross one rank-one wall. -/
structure DynamicGalleryStep
    (χ first last ψ ψ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop where
  centralizer : Dynamic.centralizer ψ = Dynamic.centralizer χ
  centralizer' : Dynamic.centralizer ψ' = Dynamic.centralizer χ
  distanceFromFirst : IsDistanceAdditive first ψ ψ'
  distanceToLast : IsDistanceAdditive ψ ψ' last
  chamber_or_wall : SameDynamicChamber ψ ψ' ∨ Nonempty (DynamicRankOneWall χ ψ ψ')

private theorem sameDynamicChamber_of_sameChamber [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (hA : IsSplitTorus A.toGrp) (i : A.toGrp ⟶ G)
    {x y : Space A} (r : IntegralRealization x) (s : IntegralRealization y)
    (hxy : SameChamber (rootForms i) x y) :
    SameDynamicChamber (CommGroupScheme.groupHom r.cocharacter ≫ i)
      (CommGroupScheme.groupHom s.cocharacter ≫ i) := by
  have hsign (α : characterLattice A) (hα : α ∈ relativeRoots i) :
      0 < x (toRat α) ↔ 0 < y (toRat α) :=
    ⟨fun hp => pos_of_mul_pos_right (hxy ⟨α, hα⟩) hp.le,
      fun hp => pos_of_mul_pos_left (hxy ⟨α, hα⟩) hp.le⟩
  have hneg (α : characterLattice A) (hα : α ∈ relativeRoots i) :
      x (toRat α) < 0 ↔ y (toRat α) < 0 :=
    ⟨fun hp => neg_of_mul_pos_right (hxy ⟨α, hα⟩) hp.le,
      fun hp => neg_of_mul_pos_left (hxy ⟨α, hα⟩) hp.le⟩
  refine ⟨?_, ?_, ?_⟩
  · exact (parabolic_eq_of_realization hA i r).symm.trans
      ((parabolic_eq_of_sameChamber hA i hxy).trans (parabolic_eq_of_realization hA i s))
  · apply le_antisymm
    · apply (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hA i _ _).2
      intro α hα h
      exact (s.pairing_pos_iff α).2 ((hsign α hα).1 ((r.pairing_pos_iff α).1 h))
    · apply (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hA i _ _).2
      intro α hα h
      exact (r.pairing_pos_iff α).2 ((hsign α hα).2 ((s.pairing_pos_iff α).1 h))
  · change Dynamic.unipotent (Dynamic.oppositeCocharacter _) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter _)
    simp only [← groupHom_neg_comp_eq_oppositeCocharacter]
    have hpair (z : Space A) (p : IntegralRealization z) (α : characterLattice A) :
        0 < latticePairing A α (-p.cocharacter) ↔ z (toRat α) < 0 := by
      rw [map_neg, neg_pos]
      simpa only [not_le] using not_congr (p.pairing_nonneg_iff α)
    apply le_antisymm
    · apply (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hA i _ _).2
      intro α hα h
      exact (hpair y s α).2 ((hneg α hα).1 ((hpair x r α).1 h))
    · apply (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hA i _ _).2
      intro α hα h
      exact (hpair x r α).2 ((hneg α hα).2 ((hpair y s α).1 h))

variable {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G} {a : A.toGrp ⟶ parameterScheme χ}

private def dynamicRankOneWallOfDirection
    (hG : IsConnectedReductive G) (ha : IsSplitComponent a)
    (hj : (torusCentralizer (a ≫ Dynamic.Affine.centralizerHom χ)).IsRepresentedBy
      (Dynamic.Affine.centralizerHom χ))
    {x y w : Space A} (r : IntegralRealization x) (s : IntegralRealization y)
    (hw : IsWallDirection (a ≫ Dynamic.Affine.centralizerHom χ) x y w) :
    DynamicRankOneWall χ (CommGroupScheme.groupHom r.cocharacter ≫ a ≫ Dynamic.Affine.centralizerHom χ)
      (CommGroupScheme.groupHom s.cocharacter ≫ a ≫ Dynamic.Affine.centralizerHom χ) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let hA := ha.1.1.1
  let j := Dynamic.Affine.centralizerHom χ
  let i := a ≫ j
  let t := integralRealization hA w
  let θ := CommGroupScheme.groupHom t.cocharacter ≫ i
  let d := hw.wallModel hG ha (Dynamic.Affine.isClosedSubgroup_centralizerHom χ) hj
  have hP : (Dynamic.parabolic θ).IsRepresentedBy d.wall.p :=
    (Dynamic.rationalParabolicModel hG θ).parabolic_rep
  have hM : (Dynamic.centralizer θ).IsRepresentedBy (d.wall.m ≫ d.wall.p) :=
    d.centralizer_rep
  have hout (z : Space A) (p : IntegralRealization z)
      (h : ∀ α ∈ relativeRoots i, 0 < w (toRat α) → 0 < z (toRat α)) :
      radical θ ≤ radical (CommGroupScheme.groupHom p.cocharacter ≫ i) := by
    have hU := (RelativeRoot.unipotent_le_iff_positive_rootSupport_of_smooth hA i
      t.cocharacter p.cocharacter).2 (fun α hα hp =>
        (p.pairing_pos_iff α).2 (h α hα ((t.pairing_pos_iff α).1 hp)))
    exact hU _
  have hU := hout x r (fun α hα hαw =>
    pos_of_mul_pos_left (hw.same α hα hαw.ne').1 hαw.le)
  have hU' := hout y s (fun α hα hαw =>
    pos_of_mul_pos_left (hw.same α hα hαw.ne').2 hαw.le)
  have hwall (X Y : SubgroupFunctor G) (hx : parabolic hA i x = X) (hy : parabolic hA i y = Y) :
      ∃ e : RationalRankOneWallData j X Y,
        (Dynamic.parabolic θ).IsRepresentedBy e.p ∧
        (Dynamic.centralizer θ).IsRepresentedBy (e.m ≫ e.p) := by
    subst X Y
    exact ⟨d.wall, hP, hM⟩
  let e := hwall _ _ (parabolic_eq_of_realization hA i r) (parabolic_eq_of_realization hA i s)
  exact ⟨θ, e.choose, e.choose_spec.1, e.choose_spec.2, hU, hU'⟩

set_option quotPrecheck false in
local notation "i" => a ≫ Dynamic.Affine.centralizerHom χ

set_option quotPrecheck false in
local notation "f" => rootForms i

private theorem dynamicGalleryStep_of_chamberStep (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a)
    (hj : (torusCentralizer i).IsRepresentedBy (Dynamic.Affine.centralizerHom χ))
    {x y v w : Space A}
    (rx : IntegralRealization x) (ry : IntegralRealization y)
    (rv : IntegralRealization v) (rw : IntegralRealization w)
    (h : ChamberStep f (fun _ => False) v w)
    (h₁ : SignsBetween f x v w) (h₂ : SignsBetween f v w y) :
    DynamicGalleryStep χ (CommGroupScheme.groupHom rx.cocharacter ≫ i)
      (CommGroupScheme.groupHom ry.cocharacter ≫ i) (CommGroupScheme.groupHom rv.cocharacter ≫ i)
      (CommGroupScheme.groupHom rw.cocharacter ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let hA := ha.1.1.1
  have hr : Regular f v ∧ Regular f w := by
    rcases h with hs | hw
    · exact ⟨fun α => (mul_ne_zero_iff.mp (hs α).ne').1,
        fun α => (mul_ne_zero_iff.mp (hs α).ne').2⟩
    · exact ⟨hw.1, hw.2.1⟩
  have hT : torusCentralizer i = Dynamic.centralizer χ :=
    hj.2.symm.trans (Dynamic.Affine.isRepresentedBy_centralizerHom χ).2
  have hc {z : Space A} (p : IntegralRealization z) (hz : Regular f z) :
      Dynamic.centralizer (CommGroupScheme.groupHom p.cocharacter ≫ i) =
        Dynamic.centralizer χ :=
    (centralizer_eq_of_realization hA i p).symm.trans
      ((centralizer_eq_torusCentralizer_of_regular hA i hz).trans hT)
  refine ⟨hc rv hr.1, hc rw hr.2, distanceAdditive_of_signsBetween hA i rx rv rw h₁,
    distanceAdditive_of_signsBetween hA i rv rw ry h₂, ?_⟩
  rcases h with hs | hw
  · exact Or.inl (sameDynamicChamber_of_sameChamber hA i rv rw hs)
  · obtain ⟨_, hd, _⟩ := exists_isWallDirection_of_wallAdjacent hw
    exact Or.inr ⟨dynamicRankOneWallOfDirection hG ha hj rv rw hd⟩

private theorem galleryOfRealizations (hG : IsConnectedReductive G)
    (ha : IsSplitComponent a)
    (hj : (torusCentralizer i).IsRepresentedBy (Dynamic.Affine.centralizerHom χ))
    {x y : Space A} (hx : Regular f x) (hy : Regular f y)
    (rx : IntegralRealization x) (ry : IntegralRealization y) :
    Relation.ReflTransGen (DynamicGalleryStep χ (CommGroupScheme.groupHom rx.cocharacter ≫ i)
      (CommGroupScheme.groupHom ry.cocharacter ≫ i))
      (CommGroupScheme.groupHom rx.cocharacter ≫ i) (CommGroupScheme.groupHom ry.cocharacter ≫ i) := by
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let hA := ha.1.1.1
  let R := DynamicGalleryStep χ (CommGroupScheme.groupHom rx.cocharacter ≫ i)
    (CommGroupScheme.groupHom ry.cocharacter ≫ i)
  let r := integralRealization hA
  let cochar (v : Space A) := CommGroupScheme.groupHom (r v).cocharacter ≫ i
  let : Finite (relativeRoots i) := (hA.finite_relativeRoots i).to_subtype
  have hgal := chamberChain_between f hx hy
  have hchain : Relation.ReflTransGen R (cochar x) (cochar y) :=
    Relation.ReflTransGen.lift cochar (p := R) (fun v w h =>
      dynamicGalleryStep_of_chamberStep hG ha hj rx ry (r v) (r w) h.1 h.2.1 h.2.2)
      x y hgal
  have hsx : SameChamber f x x := fun α => mul_self_pos.mpr (hx α)
  have hsy : SameChamber f y y := fun α => mul_self_pos.mpr (hy α)
  have hfirst := dynamicGalleryStep_of_chamberStep hG ha hj rx ry rx (r x) (Or.inl hsx)
    ⟨fun _ h _ => h, fun _ h _ => h⟩ ⟨fun _ h _ => h, fun _ h _ => h⟩
  have hlast := dynamicGalleryStep_of_chamberStep hG ha hj rx ry (r y) ry (Or.inl hsy)
    ⟨fun _ _ h => h, fun _ _ h => h⟩ ⟨fun _ _ h => h, fun _ _ h => h⟩
  exact (hchain.head hfirst).tail hlast

/-- A finite gallery with distance additivity at each step relative to both endpoints. -/
def HasDistanceAdditiveDynamicGallery
    (χ first last : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : Prop :=
  Relation.ReflTransGen (DynamicGalleryStep χ first last) first last

/-- The two actual dynamic parabolics with a common Levi are connected by a
distance-additive gallery of actual rank-one walls and same-chamber identifications. -/
theorem hasDistanceAdditiveDynamicGallery (hG : IsConnectedReductive G)
    (χ first last : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hfirst : Dynamic.centralizer first = Dynamic.centralizer χ)
    (hlast : Dynamic.centralizer last = Dynamic.centralizer χ) :
    HasDistanceAdditiveDynamicGallery χ first last := by
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let j := Dynamic.Affine.centralizerHom χ
  have hj := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  let d := fixedLeviParabolicModel hG χ hj
  have hL := d.levi.isConnectedReductive
  let : IsAffineHom (parameterScheme χ).X.hom := hL.isAffineHom
  let : Smooth (parameterScheme χ).X.hom := hL.smooth
  let : LocallyOfFiniteType (parameterScheme χ).X.hom := inferInstance
  obtain ⟨A, a, ha⟩ := exists_isSplitComponent (parameterScheme χ)
  have hP : IsRationalParabolicWithLevi j (Dynamic.parabolic χ) :=
    ⟨d.P, d.p, d.l, d.parabolic, d.levi, d.comp, d.parabolic_rep.2⟩
  have hT := torusCentralizer_eq_range_of_isRationalParabolicWithLevi hG ha hP
  have hjT : (torusCentralizer (a ≫ j)).IsRepresentedBy j := ⟨hj.1, hT.symm⟩
  obtain ⟨ν, hν⟩ := ha.exists_cocharacter_factor_of_dynamicCentralizer first (hfirst.symm ▸ hj)
  obtain ⟨ν', hν'⟩ := ha.exists_cocharacter_factor_of_dynamicCentralizer last (hlast.symm ▸ hj)
  let x := rationalCocharacterEvaluation ν
  let y := rationalCocharacterEvaluation ν'
  have hx : Regular (rootForms (a ≫ j)) x := by
    apply regular_ofIntegral_of_centralizer_eq ha.1.1.1
    rw [hν, hfirst, ← hj.2, hT]
  have hy : Regular (rootForms (a ≫ j)) y := by
    apply regular_ofIntegral_of_centralizer_eq ha.1.1.1
    rw [hν', hlast, ← hj.2, hT]
  let r (ζ : cocharacterLattice A) :
      IntegralRealization (rationalCocharacterEvaluation ζ) :=
    ⟨1, by norm_num, ζ, by intro α; simp only [rationalCocharacterEvaluation_toRat, Int.cast_one,
      one_mul]⟩
  have hgal := galleryOfRealizations hG ha hjT hx hy (r ν) (r ν')
  change HasDistanceAdditiveDynamicGallery χ (CommGroupScheme.groupHom ν ≫ a ≫ j)
    (CommGroupScheme.groupHom ν' ≫ a ≫ j) at hgal
  rwa [hν, hν'] at hgal

end Walls

end Langlands.Plancherel.DynamicCommonLeviComposition
