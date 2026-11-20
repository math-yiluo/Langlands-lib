import Langlands.GroupScheme.HomScheme.TorusCentralizerPresheaf
import Langlands.GroupScheme.HomScheme.AdmissibleSheaf

/-! # Zariski descent for actual centralizer families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : HasAffineResidueFibers G)
variable {T : Over S} (𝒰 : Scheme.OpenCover.{u} T.left)

private abbrev coverComparison (i : 𝒰.I₀) :=
  Descent.pullbackComparison T.hom (𝒰.f i) (coverObj 𝒰 i : Over S).hom rfl G

private theorem baseChange_eq_comap_restrictCentralizer
    (F : CentralizerSubgroup ((baseChange T.hom).obj G)) (i : 𝒰.I₀) :
    F.val.baseChange (𝒰.f i) =
      (restrictCentralizer hG (coverMap 𝒰 i) F).val.comap (coverComparison (G := G) 𝒰 i).hom := by
  rw [restrictCentralizer_val_eq, ← comap_comp]
  change F.val.baseChange (𝒰.f i) = (F.val.baseChange (𝒰.f i)).comap
    ((coverComparison (G := G) 𝒰 i).hom ≫ (coverComparison (G := G) 𝒰 i).inv)
  simp only [coverComparison, Iso.hom_inv_id, comap_id]

variable (F : ∀ i, CentralizerSubgroup ((baseChange (coverObj 𝒰 i : Over S).hom).obj G))

private def iteratedCoverSubgroup (i : 𝒰.I₀) :
    SubgroupFunctor ((baseChange (𝒰.f i)).obj ((baseChange T.hom).obj G)) :=
  (F i).val.comap (coverComparison (G := G) 𝒰 i).hom

private theorem isMatching_iteratedCoverSubgroup
    (hm : ∀ (i j : 𝒰.I₀) (A : Over S) (a : A ⟶ coverObj 𝒰 i) (b : A ⟶ coverObj 𝒰 j),
      a ≫ coverMap 𝒰 i = b ≫ coverMap 𝒰 j →
        restrictCentralizer hG a (F i) = restrictCentralizer hG b (F j)) :
    IsMatching 𝒰 (iteratedCoverSubgroup 𝒰 F) := by
  let J := (baseChange T.hom).obj G
  intro i j V W a x hx
  let qi := (baseChangePointsEquiv (𝒰.f i) J V).symm (a ≫ baseChangePointsEquiv (𝒰.f j) J W x)
  let xi := qi ≫ (coverComparison (G := G) 𝒰 i).hom.hom.hom
  let xj := x ≫ (coverComparison (G := G) 𝒰 j).hom.hom.hom
  change xj ∈ (F j).val.carrier W at hx
  change xi ∈ (F i).val.carrier V
  let A : Over S := Over.mk (V.hom ≫ (coverObj 𝒰 i : Over S).hom)
  let ai : A ⟶ coverObj 𝒰 i := Over.homMk V.hom rfl
  have hbase : (a.left ≫ W.hom) ≫ 𝒰.f j = V.hom ≫ 𝒰.f i := by
    have ha : a.left ≫ (W.hom ≫ 𝒰.f j) = V.hom ≫ 𝒰.f i := Over.w a
    simpa only [Category.assoc] using ha
  let aj : A ⟶ coverObj 𝒰 j := Over.homMk (a.left ≫ W.hom) (by
    change (a.left ≫ W.hom) ≫ (𝒰.f j ≫ T.hom) = V.hom ≫ (𝒰.f i ≫ T.hom)
    simp only [← Category.assoc, hbase])
  have hab : ai ≫ coverMap 𝒰 i = aj ≫ coverMap 𝒰 j := Over.OverMorphism.ext hbase.symm
  let B : Over A.left := Over.mk (𝟙 A.left)
  let p : (Over.map ai.left).obj B ⟶ V := Over.homMk (𝟙 _) (by simp [B, ai])
  let p' : V ⟶ (Over.map ai.left).obj B := Over.homMk (𝟙 _) (by simp [B, ai])
  let q : (Over.map aj.left).obj B ⟶ W := Over.homMk a.left (by simp [B, aj])
  let z := (familyPointsEquiv (G := G) ai B).symm (p ≫ xi)
  have hz : familyPointsEquiv ai B z = p ≫ xi := MulEquiv.apply_symm_apply _ _
  have hproj : xi.left ≫ pullback.fst G.X.hom (coverObj 𝒰 i : Over S).hom =
      a.left ≫ xj.left ≫ pullback.fst G.X.hom (coverObj 𝒰 j : Over S).hom := by
    have hv := congrArg (fun w => w.left ≫ pullback.fst G.X.hom T.hom)
      ((baseChangePointsEquiv (𝒰.f i) J V).apply_symm_apply (a ≫ baseChangePointsEquiv (𝒰.f j) J W x))
    simpa only [baseChangePointsEquiv_left, Over.comp_left, Category.assoc,
      xi, xj, coverComparison, Descent.pullbackComparison_hom_fst,
      Descent.pullbackComparison_hom_fst_assoc] using hv
  have hz' : familyPointsEquiv aj B z = q ≫ xj := by
    apply familyPointsEquiv_eq_of_original aj B W q z xj
    rw [← familyPointsEquiv_original ai B z, hz]
    simpa only [p, q, Over.homMk_left, Over.comp_left, Category.id_comp] using hproj
  have hmem : z ∈ (restrictCentralizer hG aj (F j)).val.carrier B := by
    rw [restrictCentralizer_val_eq]
    change familyPointsEquiv aj B z ∈ (F j).val.carrier ((Over.map aj.left).obj B)
    rw [hz']
    exact (F j).val.comp_mem q hx
  rw [← hm i j A ai aj hab, restrictCentralizer_val_eq] at hmem
  change familyPointsEquiv ai B z ∈ (F i).val.carrier ((Over.map ai.left).obj B) at hmem
  have hpp : p' ≫ p = 𝟙 V := Over.OverMorphism.ext (by simp [p, p'])
  rw [hz] at hmem
  simpa only [← Category.assoc, hpp, Category.id_comp] using (F i).val.comp_mem p' hmem

include hG in
private theorem isCentralizerFamily_descentSubgroup
    (hm : IsMatching 𝒰 (iteratedCoverSubgroup 𝒰 F)) :
    IsCentralizerFamily (descentSubgroup 𝒰 (iteratedCoverSubgroup 𝒰 F)) := by
  let r i := centralizerRepresentative (F i)
  let e i := coverComparison (G := G) 𝒰 i
  let j i := (r i).hom ≫ (e i).inv
  have hr i : (iteratedCoverSubgroup 𝒰 F i).IsRepresentedBy (j i) := by
    have hc : IsClosedSubgroup (j i) := (r i).closed.comp_iso (e i).symm
    refine ⟨IsClosedSubgroup.mono_overHom hc, ?_⟩
    rw [show j i = (r i).hom ≫ (e i).symm.hom from rfl, range_comp_iso, (r i).represents.2]
    rfl
  let R := closedRepresentativeOfMatching 𝒰 _ hm
    (fun i => ⟨(r i).group, j i, hr i, (r i).closed.comp_iso (e i).symm⟩)
  have hrep i : (iteratedCoverSubgroup 𝒰 F i).IsRepresentedBy ((baseChange (𝒰.f i)).map R.hom) := by
    rw [← baseChange_descentSubgroup 𝒰 _ hm i]
    exact R.represents.baseChange (𝒰.f i)
  let c i := (hrep i).isoOfIsRepresentedBy (hr i)
  have hp (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (hP : ∀ i, P (r i).group.X.hom) : P R.group.X.hom := by
    apply IsZariskiLocalAtTarget.of_openCover 𝒰
    intro i
    change P ((baseChange (𝒰.f i)).obj R.group).X.hom
    let d := (Grp.forget _ ⋙ Over.forget _).mapIso (c i)
    have he : d.hom ≫ (r i).group.X.hom = ((baseChange (𝒰.f i)).obj R.group).X.hom :=
      Over.w (c i).hom.hom.hom
    exact he ▸ MorphismProperty.RespectsIso.precomp P d.hom _ (hP i)
  have hSmooth : Smooth R.group.X.hom := hp @Smooth (fun i => (r i).smooth)
  have hConn : GeometricallyConnected R.group.X.hom := by
    rw [GeometricallyConnected.eq_geometrically]
    apply hp
    intro i
    rw [← GeometricallyConnected.eq_geometrically]
    exact (r i).connected
  refine ⟨R.group, R.hom, R.closed, hSmooth, hConn, ?_, R.represents⟩
  intro s
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq s
  apply (isTorusCentralizerAt_baseChange_iff (hG.baseChange T.hom) R.hom R.closed (𝒰.f i) x).mp
  have he := (hrep i).isoOfIsRepresentedBy_hom_comp (hr i)
  rw [← he]
  apply (hasTorusCentralizerResidueFibres_iso_comp_iff (c i) (j i)).mpr _ x
  exact (hasTorusCentralizerResidueFibres_comp_iso_iff (r i).hom (e i).symm).mpr (r i).fibres

/-- Compatible relative centralizer families glue uniquely on every open cover. -/
theorem centralizer_isSheafFor_cover :
    Presieve.IsSheafFor (centralizerPresheaf hG)
      (Langlands.AlgebraicGeometry.Picard.openCoverOver T 𝒰).presieve₀ := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro q hq
  let L i := centralizerEquiv hG (coverObj 𝒰 i) (q i)
  have hm := isMatching_iteratedCoverSubgroup hG 𝒰 L (fun i j A a b hab => by
    have h := congrArg (centralizerEquiv hG A) (hq i j A a b hab)
    rw [centralizerEquiv_map, centralizerEquiv_map] at h
    exact h)
  let D : CentralizerSubgroup ((baseChange T.hom).obj G) :=
    ⟨descentSubgroup 𝒰 (iteratedCoverSubgroup 𝒰 L), isCentralizerFamily_descentSubgroup hG 𝒰 L hm⟩
  have hD (i : 𝒰.I₀) : restrictCentralizer hG (coverMap 𝒰 i) D = L i := by
    apply Subtype.ext
    rw [restrictCentralizer_val_eq]
    change (D.val.baseChange (𝒰.f i)).comap (coverComparison (G := G) 𝒰 i).inv = (L i).val
    rw [baseChange_descentSubgroup 𝒰 _ hm i]
    simp only [iteratedCoverSubgroup, ← comap_comp, Iso.inv_hom_id, comap_id]
  refine ⟨(centralizerEquiv hG T).symm D, ?_, ?_⟩
  · intro i
    apply (centralizerEquiv hG _).injective
    rw [centralizerEquiv_map, Equiv.apply_symm_apply]
    exact hD i
  · intro q' hq'
    let D' := centralizerEquiv hG T q'
    apply (centralizerEquiv hG T).injective
    rw [Equiv.apply_symm_apply]
    change D' = D
    apply Subtype.ext
    apply (eq_iff_isRepresentedBy_baseChange_openCover 𝒰
      (centralizerRepresentative D').represents (centralizerRepresentative D).represents).mpr
    intro i
    have hi := congrArg (centralizerEquiv hG _) (hq' i)
    rw [centralizerEquiv_map] at hi
    change restrictCentralizer hG (coverMap 𝒰 i) D' = L i at hi
    rw [baseChange_eq_comap_restrictCentralizer hG 𝒰 D' i,
      baseChange_eq_comap_restrictCentralizer hG 𝒰 D i, hi, hD]
/-- Actual centralizer families with their structural maps form a big Zariski sheaf. -/
def TorusCentralizerZariskiSheafStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) (hG : HasAffineResidueFibers G),
    Presieve.IsSheaf Scheme.zariskiTopology (totalCentralizerPresheaf hG)

theorem torusCentralizerZariskiSheaf : TorusCentralizerZariskiSheafStatement.{u} := by
  intro S G hG
  exact isSheaf_overTotal_of_openCover (centralizerPresheaf hG)
    (fun _ => centralizer_isSheafFor_cover hG)

/-- The absolute sheaf used to glue representable centralizer charts. -/
def centralizerSheaf : Sheaf Scheme.zariskiTopology (Type u) :=
  ⟨totalCentralizerPresheaf hG,
    (isSheaf_iff_isSheaf_of_type _ _).mpr (torusCentralizerZariskiSheaf S G hG)⟩

end Langlands.GroupScheme.TorusSubgroupModuli
