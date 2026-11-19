import Langlands.GroupScheme.RelativeLevi.FaceQuotientOverlap
import Langlands.GroupScheme.RelativeLevi.FaceQuotientScalarCoordinates
import Langlands.GroupScheme.RelativeLevi.FaceCoverSeriesAssembly

/-! # Finite vector-bundle filtrations of supplied relative unipotent radicals -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent

private lemma affineCoefficient_liftCoordinates {S : Scheme.{u}} {R A : CommRingCat.{u}}
    {n : ℕ} (p : Spec R ⟶ S) (b : Spec A ⟶ Spec R) (a : Spec A ⟶ S)
    (hb : b ≫ p = a) (Q : GroupScheme S)
    (e : (baseChange p).obj Q ≅ VectorGroup.groupScheme R n)
    (T : Over S) (k : T.left ⟶ Spec A) (hk : k ≫ a = T.hom) (x : T ⟶ Q.X) :
    (VectorGroup.coordinates A n (Over.mk k)
      (LiftedModuleCharts.liftPointsEquiv a Q T k hk x ≫
        (((Descent.pullbackComparison p b a hb Q).symm ≪≫ (baseChange b).mapIso e) ≪≫
          VectorGroup.affineCoefficientIso b n).hom.hom.hom)).toAdd =
      (VectorGroup.coordinates R n (Over.mk (k ≫ b))
        (LiftedModuleCharts.liftPointsEquiv p Q T (k ≫ b)
          (by rw [Category.assoc, hb, hk]) x ≫ e.hom.hom.hom)).toAdd := by
  let L := VectorGroup.groupScheme R n
  let z := LiftedModuleCharts.liftPointsEquiv a Q T k hk x
  let t := Descent.pullbackComparison p b a hb Q
  let f := VectorGroup.affineCoefficientIso (R := R) (A := A) b n
  let y : Over.mk k ⟶ ((baseChange b).obj L).X :=
    (z ≫ t.inv.hom.hom) ≫ ((baseChange b).map e.hom).hom.hom
  have ht := LiftedModuleCharts.liftPointsEquiv_tower p b a hb Q T k hk x
  have h : baseChangePointsEquiv b L (Over.mk k) y =
      LiftedModuleCharts.liftPointsEquiv p Q T (k ≫ b)
        (by rw [Category.assoc, hb, hk]) x ≫ e.hom.hom.hom := by
    change baseChangePointsEquiv b L (Over.mk k)
      ((z ≫ t.inv.hom.hom) ≫ ((baseChange b).map e.hom).hom.hom) = _
    rw [baseChangePointsEquiv_comp]
    exact congrArg (fun v => v ≫ e.hom.hom.hom) ht
  change (VectorGroup.coordinates A n (Over.mk k)
    (z ≫ (t.inv.hom.hom ≫ ((baseChange b).map e.hom).hom.hom) ≫ f.hom.hom.hom)).toAdd = _
  rw [← Category.assoc z, ← Category.assoc z]
  change (VectorGroup.coordinates A n (Over.mk k) (y ≫ f.hom.hom.hom)).toAdd = _
  rw [VectorGroup.coordinates_affineCoefficientIso_hom, h]
  rfl

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

private def componentCoordinates (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    Fin (D.layerRank d i) → Γ(T.left, ⊤) :=
  (VectorGroup.coordinates (CommRingCat.of (D.charts i.down).2.ring)
    (D.layerRank d i) (Over.mk b) (D.quotientComponentPoint r hG hp hr d i T b hb x)).toAdd

private lemma componentCoordinates_injective (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom) :
    Function.Injective (D.componentCoordinates r hG hp hr d i T b hb) := by
  intro x y h
  apply D.quotientComponentPoint_injective r hG hp hr d i T b hb
  apply (VectorGroup.coordinates (CommRingCat.of (D.charts i.down).2.ring)
    (D.layerRank d i) (Over.mk b)).injective
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private lemma componentCoordinates_scaledPoint (d : ℕ) (i : D.Index) (T : Over S)
    (b : T.left ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (s : Γ(T.left, ⊤)) (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    D.componentCoordinates r hG hp hr d i T b hb
        ((D.globalFaceQuotientCharts r hG hp hr d).scaledPoint T (b ≫ D.componentMap i)
          (by rw [Category.assoc, D.componentMap_comp_groupsBaseMap, hb]) s x) =
      s • D.componentCoordinates r hG hp hr d i T b hb x :=
  D.quotientComponentPoint_scaledPoint_coordinates r hG hp hr d i T b hb s x

private lemma componentCoordinates_affineParameter (d : ℕ) (i : D.Index)
    (A : CommRingCat.{u}) (a : Spec A ⟶ S) (b : Spec A ⟶ Spec (D.charts i.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = a) (T : Over S)
    (k : T.left ⟶ Spec A) (hk : k ≫ a = T.hom)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    (VectorGroup.coordinates A (D.layerRank d i) (Over.mk k)
      (LiftedModuleCharts.liftPointsEquiv a (D.globalFaceQuotientData r hG hp hr d).group T k hk x ≫
        (D.globalFaceQuotientAffineIso r hG hp hr d i A b a hb).hom.hom.hom)).toAdd =
      D.componentCoordinates r hG hp hr d i T (k ≫ b)
        (by rw [Category.assoc, hb, hk]) x := by
  have h := affineCoefficient_liftCoordinates
    (R := CommRingCat.of (D.charts i.down).2.ring) (A := A) (n := D.layerRank d i)
    (D.charts i.down).2.projection b a hb (D.globalFaceQuotientData r hG hp hr d).group
    (D.globalFaceQuotientComponentIso r hG hp hr d i) T k hk x
  dsimp only [globalFaceQuotientAffineIso, globalFaceQuotientParameterIso,
    componentCoordinates, quotientComponentPoint]
  exact h

private lemma componentCoordinates_congr (d : ℕ) (i : D.Index) (T : Over S)
    {b c : T.left ⟶ Spec (D.charts i.down).2.ring}
    (hb : b ≫ (D.charts i.down).2.projection = T.hom)
    (hc : c ≫ (D.charts i.down).2.projection = T.hom) (h : b = c)
    (x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
    D.componentCoordinates r hG hp hr d i T b hb x =
      D.componentCoordinates r hG hp hr d i T c hc x := by
  subst c
  rfl

private lemma exists_componentCoordinates_overlap_matrix (d : ℕ) (i j : D.Index)
    (A : CommRingCat.{u}) (a : Spec A ⟶ S)
    (b : Spec A ⟶ Spec (D.charts i.down).2.ring)
    (c : Spec A ⟶ Spec (D.charts j.down).2.ring)
    (hb : b ≫ (D.charts i.down).2.projection = a)
    (hc : c ≫ (D.charts j.down).2.projection = a)
    (T : Over S) (k : T.left ⟶ Spec A) (hk : k ≫ a = T.hom) :
    ∃ M : Matrix (Fin (D.layerRank d j)) (Fin (D.layerRank d i)) Γ(T.left, ⊤),
      ∀ x : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X,
        D.componentCoordinates r hG hp hr d j T (k ≫ c)
            (by rw [Category.assoc, hc, hk]) x =
          M *ᵥ D.componentCoordinates r hG hp hr d i T (k ≫ b)
            (by rw [Category.assoc, hb, hk]) x := by
  let E : VectorGroup.groupScheme A (D.layerRank d i) ≅
      VectorGroup.groupScheme A (D.layerRank d j) :=
    AffineParabolicFaceChart.restrictionQuotientIso (p := p)
      (D.charts i.down).2 (D.charts j.down).2 r hG hp hr A b c a hb hc d
  let ei := D.globalFaceQuotientAffineIso r hG hp hr d i A b a hb
  let ej := D.globalFaceQuotientAffineIso r hG hp hr d j A c a hc
  have he : ei.hom ≫ E.hom = ej.hom :=
    D.globalFaceQuotientAffineIso_overlap r hG hp hr d i j A b c a hb hc
  let M := (VectorGroup.weightMatrix (VectorGroup.pointTransformation E.hom)).map
    (Langlands.GroupScheme.scalarMap (Over.mk k))
  refine ⟨M, ?_⟩
  intro x
  let z := LiftedModuleCharts.liftPointsEquiv a
    (D.globalFaceQuotientData r hG hp hr d).group T k hk x
  let xi := z ≫ ei.hom.hom.hom
  let xj := z ≫ ej.hom.hom.hom
  have hxy : xi ≫ E.hom.hom.hom = xj := by
    change (z ≫ ei.hom.hom.hom) ≫ E.hom.hom.hom = z ≫ ej.hom.hom.hom
    rw [Category.assoc]
    exact congrArg (fun f => z ≫ f.hom.hom) he
  have hM := AffineParabolicFaceChart.coordinates_restrictionQuotientIso (p := p)
    (D.charts i.down).2 (D.charts j.down).2 r hG hp hr A b c a hb hc d (Over.mk k) xi
  change (VectorGroup.coordinates A (D.layerRank d j) (Over.mk k)
      (xi ≫ E.hom.hom.hom)).toAdd =
    M *ᵥ (VectorGroup.coordinates A (D.layerRank d i) (Over.mk k) xi).toAdd at hM
  rw [hxy] at hM
  have hi := D.componentCoordinates_affineParameter r hG hp hr d i A a b hb T k hk x
  have hj := D.componentCoordinates_affineParameter r hG hp hr d j A a c hc T k hk x
  exact hj.symm.trans (hM.trans (congrArg (fun v => M *ᵥ v) hi))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private lemma globalFaceQuotient_specComponentIndependent (d : ℕ) :
    (D.globalFaceQuotientCharts r hG hp hr d).SpecComponentIndependent D.groupsOpenCover := by
  intro A a f g hf hg hfac hgc s x
  obtain ⟨i, b, rfl⟩ := hfac
  obtain ⟨j, c, rfl⟩ := hgc
  change D.Index at i j
  change Spec A ⟶ Spec (D.charts i.down).2.ring at b
  change Spec A ⟶ Spec (D.charts j.down).2.ring at c
  change (b ≫ D.componentMap i) ≫ D.groupsBaseMap = a at hf
  change (c ≫ D.componentMap j) ≫ D.groupsBaseMap = a at hg
  have hb : b ≫ (D.charts i.down).2.projection = a := by
    rwa [Category.assoc, D.componentMap_comp_groupsBaseMap] at hf
  have hc : c ≫ (D.charts j.down).2.projection = a := by
    rwa [Category.assoc, D.componentMap_comp_groupsBaseMap] at hg
  let T := Over.mk a
  let scalar : Γ(T.left, ⊤) := s
  obtain ⟨M, hM⟩ := D.exists_componentCoordinates_overlap_matrix r hG hp hr d i j
    A a b c hb hc T (𝟙 (Spec A)) (Category.id_comp a)
  let vi := D.componentCoordinates r hG hp hr d i T b hb
  let vj := D.componentCoordinates r hG hp hr d j T c hc
  have htrans (y : T ⟶ (D.globalFaceQuotientData r hG hp hr d).group.X) :
      vj y = M *ᵥ vi y := by
    have hi := D.componentCoordinates_congr r hG hp hr d i T
      (by rw [Category.id_comp]; exact hb) hb (Category.id_comp b) y
    have hj := D.componentCoordinates_congr r hG hp hr d j T
      (by rw [Category.id_comp]; exact hc) hc (Category.id_comp c) y
    exact hj.symm.trans ((hM y).trans (congrArg (fun v => M *ᵥ v) hi))
  let charts := D.globalFaceQuotientCharts r hG hp hr d
  let xi := charts.scaledPoint T (b ≫ D.componentMap i) hf scalar x
  let xj := charts.scaledPoint T (c ≫ D.componentMap j) hg scalar x
  change xi = xj
  apply D.componentCoordinates_injective r hG hp hr d j T c hc
  have hi : vi xi = scalar • vi x :=
    D.componentCoordinates_scaledPoint r hG hp hr d i T b hb scalar x
  have hj : vj xj = scalar • vj x :=
    D.componentCoordinates_scaledPoint r hG hp hr d j T c hc scalar x
  calc
    vj xi = M *ᵥ vi xi := htrans xi
    _ = M *ᵥ (scalar • vi x) := congrArg (fun v => M *ᵥ v) hi
    _ = scalar • (M *ᵥ vi x) := Matrix.mulVec_smul M scalar _
    _ = scalar • vj x := congrArg (fun v => scalar • v) (htrans x).symm
    _ = vj xj := hj.symm

end Langlands.GroupScheme.RelativeLevi.FiniteParabolicFaceCover

namespace Langlands.GroupScheme

/-- Every supplied relative unipotent radical over an affine base has a finite
series with vector-bundle additive successive quotients. -/
theorem relativeUnipotentRadicalFiltration : RelativeUnipotentRadicalFiltrationStatement.{u} := by
  apply RelativeLevi.relativeUnipotentRadicalFiltration_of_globalFaceQuotients
  intro S _ G H U _ p r hG hp hr D d
  exact D.isVectorBundleAdditive_globalFaceQuotient_of_specComponents r hG hp hr d
    (D.globalFaceQuotient_specComponentIndependent r hG hp hr d)

end Langlands.GroupScheme
