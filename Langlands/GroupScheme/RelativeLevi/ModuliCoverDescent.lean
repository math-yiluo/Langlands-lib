import Langlands.GroupScheme.RelativeLevi.ModuliFunctorConstruction
import Langlands.GroupScheme.RelativeLevi.LeviCoverDescent
import Langlands.GroupScheme.RelativeLevi.UnipotentRadicalProof
import Langlands.GroupScheme.RelativeLevi.ParabolicBaseChange

/-! # Descent of actual relative Levi images on etale covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

open TorusSubgroupModuli

variable {S : Scheme.{u}} {P : GroupScheme S} {M N T : Over S}

/-- Equality of restricted subgroup conditions transfers membership between
points having the same projection to the original ambient group. -/
theorem mem_of_restrictImage_eq (a : T ⟶ M) (b : T ⟶ N)
    (F : SubgroupFunctor ((baseChange M.hom).obj P))
    (H : SubgroupFunctor ((baseChange N.hom).obj P))
    (hFH : restrictImage a F = restrictImage b H)
    (x : Over.mk a.left ⟶ ((baseChange M.hom).obj P).X)
    (y : Over.mk b.left ⟶ ((baseChange N.hom).obj P).X)
    (hxy : x.left ≫ pullback.fst P.X.hom M.hom =
      y.left ≫ pullback.fst P.X.hom N.hom)
    (hy : y ∈ H.carrier (Over.mk b.left)) :
    x ∈ F.carrier (Over.mk a.left) := by
  let R : Over T.left := Over.mk (𝟙 T.left)
  let q : (Over.map T.hom).obj R ⟶ P.X :=
    Over.homMk (x.left ≫ pullback.fst P.X.hom M.hom) (by
      have hx : x.left ≫ pullback.snd P.X.hom M.hom = a.left := Over.w x
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx]
      change a.left ≫ M.hom = (𝟙 T.left) ≫ T.hom
      simpa only [Category.id_comp] using Over.w a)
  let z := (baseChangePointsEquiv T.hom P R).symm q
  have hz : z.left ≫ pullback.fst P.X.hom T.hom =
      x.left ≫ pullback.fst P.X.hom M.hom :=
    congrArg (fun f => f.left) ((baseChangePointsEquiv T.hom P R).apply_symm_apply q)
  let d : (Over.map b.left).obj R ⟶ Over.mk b.left :=
    Over.homMk (𝟙 _) (by simp [R])
  have hzH : z ∈ (restrictImage b H).carrier R := by
    rw [mem_restrictImage,
      familyPointsEquiv_eq_of_original b R (Over.mk b.left) d z y
        (by simpa only [d, Over.homMk_left, Category.id_comp] using hz.trans hxy)]
    exact H.comp_mem d hy
  have hzF : z ∈ (restrictImage a F).carrier R := by
    rw [hFH]
    exact hzH
  rw [mem_restrictImage] at hzF
  let c : Over.mk a.left ⟶ (Over.map a.left).obj R :=
    Over.homMk (𝟙 _) (by simp [R])
  have heq : c ≫ familyPointsEquiv (G := P) a R z = x := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa only [Over.comp_left, c, Over.homMk_left, Category.id_comp,
        familyPointsEquiv_original] using hz
    · exact (Over.w (c ≫ familyPointsEquiv (G := P) a R z)).trans (Over.w x).symm
  simpa only [heq] using F.comp_mem c hzF

/-- An etale cover of the parameter scheme as a family in its big slice. -/
def etaleCoverOver (T : Over S)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T.left) :
    PreZeroHypercover.{u} T where
  I₀ := 𝒰.I₀
  X i := Over.mk (𝒰.f i ≫ T.hom)
  f i := Over.homMk (𝒰.f i) rfl

variable (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) T.left)

/-- A local Levi image expressed in the iterated ambient pullback. -/
def coverLeviImage
    (F : ∀ i, LeviImage ((baseChange ((etaleCoverOver T 𝒰).X i).hom).obj P))
    (i : 𝒰.I₀) :
    LeviImage ((baseChange (𝒰.f i)).obj ((baseChange T.hom).obj P)) :=
  (F i).mapIso (Descent.pullbackComparison T.hom (𝒰.f i)
    ((etaleCoverOver T 𝒰).X i).hom rfl P).symm

/-- Ordinary matching of the local actual subgroup images. -/
def IsMatchingLevi
    (F : ∀ i, LeviImage ((baseChange ((etaleCoverOver T 𝒰).X i).hom).obj P)) : Prop :=
  ∀ (i j : 𝒰.I₀) (A : Over S)
    (a : A ⟶ (etaleCoverOver T 𝒰).X i)
    (b : A ⟶ (etaleCoverOver T 𝒰).X j),
    a ≫ (etaleCoverOver T 𝒰).f i = b ≫ (etaleCoverOver T 𝒰).f j →
      restrictImage a (F i).val = restrictImage b (F j).val

variable (F : ∀ i,
  LeviImage ((baseChange ((etaleCoverOver T 𝒰).X i).hom).obj P))

/-- Ordinary matching implies all-test matching in the iterated pullbacks. -/
theorem isMatching_coverLeviImage (hF : IsMatchingLevi 𝒰 F) :
    SubgroupFunctor.CoverDescent.IsMatching 𝒰
      (fun i => (coverLeviImage 𝒰 F i).val) := by
  let J := (baseChange T.hom).obj P
  let e (i : 𝒰.I₀) := Descent.pullbackComparison T.hom (𝒰.f i)
    ((etaleCoverOver T 𝒰).X i).hom rfl P
  intro i j V W a x hx
  let v := (baseChangePointsEquiv (𝒰.f i) J V).symm
    (a ≫ baseChangePointsEquiv (𝒰.f j) J W x)
  let xi := v ≫ (e i).hom.hom.hom
  let yj := x ≫ (e j).hom.hom.hom
  have hyj : yj ∈ (F j).val.carrier W := hx
  let A : Over S := Over.mk (V.hom ≫ ((etaleCoverOver T 𝒰).X i).hom)
  let ai : A ⟶ (etaleCoverOver T 𝒰).X i := Over.homMk V.hom rfl
  have hbase : (a.left ≫ W.hom) ≫ 𝒰.f j = V.hom ≫ 𝒰.f i := by
    have ha : a.left ≫ (W.hom ≫ 𝒰.f j) = V.hom ≫ 𝒰.f i := Over.w a
    simpa only [Category.assoc] using ha
  let aj : A ⟶ (etaleCoverOver T 𝒰).X j :=
    Over.homMk (a.left ≫ W.hom) (by
      change (a.left ≫ W.hom) ≫ (𝒰.f j ≫ T.hom) =
        V.hom ≫ (𝒰.f i ≫ T.hom)
      simp only [← Category.assoc, hbase])
  have hab : ai ≫ (etaleCoverOver T 𝒰).f i =
      aj ≫ (etaleCoverOver T 𝒰).f j := by
    apply Over.OverMorphism.ext
    exact hbase.symm
  let b : Over.mk aj.left ⟶ W := Over.homMk a.left rfl
  have hp : xi.left ≫ pullback.fst P.X.hom ((etaleCoverOver T 𝒰).X i).hom =
      (b ≫ yj).left ≫ pullback.fst P.X.hom ((etaleCoverOver T 𝒰).X j).hom := by
    have hv := congrArg (fun z => z.left ≫ pullback.fst P.X.hom T.hom)
      ((baseChangePointsEquiv (𝒰.f i) J V).apply_symm_apply
        (a ≫ baseChangePointsEquiv (𝒰.f j) J W x))
    simpa only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
      xi, yj, e, b, Over.homMk_left, Descent.pullbackComparison_hom_fst,
      Descent.pullbackComparison_hom_fst_assoc] using hv
  exact mem_of_restrictImage_eq ai aj (F i).val (F j).val (hF i j A ai aj hab)
    xi (b ≫ yj) hp ((F j).val.comp_mem b hyj)

/-- The all-test subgroup constructed from a matching family. -/
def matchingLeviSubgroup : SubgroupFunctor ((baseChange T.hom).obj P) :=
  SubgroupFunctor.CoverDescent.subgroup 𝒰 (fun i => (coverLeviImage 𝒰 F i).val)

/-- The constructed subgroup has the prescribed local base changes. -/
theorem baseChange_matchingLeviSubgroup (hF : IsMatchingLevi 𝒰 F) (i : 𝒰.I₀) :
    (matchingLeviSubgroup 𝒰 F).baseChange (𝒰.f i) = (coverLeviImage 𝒰 F i).val :=
  SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 _ (isMatching_coverLeviImage 𝒰 F hF) i

/-- Restricting the constructed all-test subgroup recovers the original image. -/
theorem restrictImage_matchingLeviSubgroup (hF : IsMatchingLevi 𝒰 F) (i : 𝒰.I₀) :
    restrictImage ((etaleCoverOver T 𝒰).f i) (matchingLeviSubgroup 𝒰 F) = (F i).val := by
  change ((matchingLeviSubgroup 𝒰 F).baseChange (𝒰.f i)).comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      ((etaleCoverOver T 𝒰).X i).hom rfl P).inv = _
  rw [baseChange_matchingLeviSubgroup 𝒰 F hF i]
  change ((F i).val.comap
    (Descent.pullbackComparison T.hom (𝒰.f i)
      ((etaleCoverOver T 𝒰).X i).hom rfl P).hom).comap _ = _
  rw [← SubgroupFunctor.comap_comp]
  simp only [Iso.inv_hom_id, SubgroupFunctor.comap_id]

/-- Ordinary pullback is image restriction followed by the inverse ambient
identification. -/
theorem baseChange_eq_comap_restrictImage
    (H : SubgroupFunctor ((baseChange T.hom).obj P)) (i : 𝒰.I₀) :
    H.baseChange (𝒰.f i) =
      (restrictImage ((etaleCoverOver T 𝒰).f i) H).comap
        (Descent.pullbackComparison T.hom (𝒰.f i)
          ((etaleCoverOver T 𝒰).X i).hom rfl P).hom := by
  let e := Descent.pullbackComparison T.hom (𝒰.f i)
    ((etaleCoverOver T 𝒰).X i).hom rfl P
  change H.baseChange (𝒰.f i) = ((H.baseChange (𝒰.f i)).comap e.inv).comap e.hom
  rw [← SubgroupFunctor.comap_comp, e.hom_inv_id, SubgroupFunctor.comap_id]

/-- Equality of actual Levi images is detected on any etale parameter cover. -/
theorem LeviImage.eq_of_restrictImage_etaleCover
    (H K : LeviImage ((baseChange T.hom).obj P))
    (h : ∀ i, restrictImage ((etaleCoverOver T 𝒰).f i) H.val =
      restrictImage ((etaleCoverOver T 𝒰).f i) K.val) : H = K := by
  obtain ⟨L, l, hl, hL⟩ := H.exists_presentation
  obtain ⟨N, n, hn, hN⟩ := K.exists_presentation
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion n.hom.hom.left := hn.isClosedSubgroup
  let : Mono l.hom.hom := Over.mono_of_mono_left _
  let : Mono n.hom.hom := Over.mono_of_mono_left _
  apply LeviImage.ext
  rw [← hL, ← hN]
  apply SubgroupFunctor.range_eq_of_baseChange_etaleCover 𝒰 l n
  intro i
  rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
    hL, hN, baseChange_eq_comap_restrictImage 𝒰 H.val i,
    baseChange_eq_comap_restrictImage 𝒰 K.val i, h i]

variable {G U : GroupScheme S} (i : P ⟶ G) (r : U ⟶ P)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i)
    (hU : ∀ {B : Scheme.{u}} (b : B ⟶ S),
      IsRelativeUnipotentRadical ((baseChange b).map r))

include i r hG hi hU in
/-- Matching actual Levi images descend effectively when the supplied radical
survives the parameter base change. -/
theorem isLeviImage_matchingLeviSubgroup (hF : IsMatchingLevi 𝒰 F) :
    IsLeviImage (matchingLeviSubgroup 𝒰 F) := by
  choose L l hl hrep using fun j => (coverLeviImage 𝒰 F j).exists_presentation
  choose R rloc hrloc hmul using fun j => (hl j).exists_unipotentRadical
  let rT := (baseChange T.hom).map r
  have hrT : IsRelativeUnipotentRadical rT := hU T.hom
  let : IsAffineHom ((baseChange T.hom).obj P).X.hom :=
    (hi.baseChange hG T.hom).isAffineHom
  have hrad (j : 𝒰.I₀) :
      SubgroupFunctor.range ((baseChange (𝒰.f j)).map rT) =
        SubgroupFunctor.range (rloc j) := by
    obtain ⟨_, _, _, huniq⟩ := relativeUnipotentRadical (𝒰.X j)
      ((baseChange (𝒰.f j)).obj ((baseChange T.hom).obj G))
      ((baseChange (𝒰.f j)).obj ((baseChange T.hom).obj P))
      ((baseChange (𝒰.f j)).map ((baseChange T.hom).map i))
      ((hG.baseChange T.hom).baseChange (𝒰.f j))
      ((hi.baseChange hG T.hom).baseChange (hG.baseChange T.hom) (𝒰.f j))
    exact (huniq _ _ (hrT.baseChange_etale (𝒰.f j))).trans
      (huniq _ _ (hrloc j)).symm
  let c := leviRepresentativeOfEtaleCover 𝒰 rT hrT
    (fun j => (coverLeviImage 𝒰 F j).val) (isMatching_coverLeviImage 𝒰 F hF)
    L R l rloc
    (fun j => by
      let : IsClosedImmersion (l j).hom.hom.left := (hl j).isClosedSubgroup
      exact ⟨Over.mono_of_mono_left _, hrep j⟩)
    (fun j => (hl j).isClosedSubgroup) (fun j => (hrloc j).isClosedSubgroup)
    (fun j => (hl j).smooth) hmul hrad
  exact ⟨c.group, c.hom, c.isLevi, c.represents.2⟩

end Langlands.GroupScheme.RelativeLevi
