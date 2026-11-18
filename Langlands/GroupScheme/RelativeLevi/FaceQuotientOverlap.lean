import Langlands.GroupScheme.RelativeLevi.AffineFaceQuotientRestriction
import Langlands.GroupScheme.RelativeLevi.FaceQuotientParameterRecovery

/-! # Original quotient comparison on common affine chart parameters -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme

namespace VectorGroup

/-- The affine coefficient isomorphism keeps the original vector coordinates. -/
lemma coordinates_affineCoefficientIso_hom {R A : CommRingCat.{u}}
    (b : Spec A ⟶ Spec R) (n : ℕ) (T : Over (Spec A))
    (x : T ⟶ ((baseChange b).obj (groupScheme R n)).X) :
    coordinates A n T (x ≫ (affineCoefficientIso b n).hom.hom.hom) =
      coordinates R n ((Over.map b).obj T)
        (baseChangePointsEquiv b (groupScheme R n) T x) := by
  obtain ⟨ρ, rfl⟩ : ∃ ρ : R ⟶ A, Spec.map ρ = b := ⟨Spec.preimage b, Spec.map_preimage b⟩
  rw [affineCoefficientIso_map]
  exact coordinates_baseChangeIso_hom ρ T x

end VectorGroup

section OverlapSquares

variable {T : Scheme.{u}} {K I J G Q V W : GroupScheme T}

private lemma comp_eq_of_ambient (ki : K ⟶ I) (kj : K ⟶ J) (e : I ⟶ J)
    (ui : I ⟶ G) (uj : J ⟶ G) (hmono : Mono uj.hom.hom)
    (he : e ≫ uj = ui) (hk : ki ≫ ui = kj ≫ uj) :
    ki ≫ e = kj := by
  have hrep : (SubgroupFunctor.range uj).IsRepresentedBy uj := ⟨hmono, rfl⟩
  apply hrep.hom_ext
  rw [Category.assoc, he, hk]

private lemma comp_eq_of_quotient (q : K ⟶ Q) (ki : K ⟶ I) (kj : K ⟶ J)
    (ei : Q ⟶ V) (ej : Q ⟶ W) (qi : I ⟶ V) (qj : J ⟶ W)
    (e : I ⟶ J) (E : V ⟶ W) {N : SubgroupFunctor K}
    (hq : RelativeRoot.IsFppfQuotient N q) (hi : q ≫ ei = ki ≫ qi)
    (hj : q ≫ ej = kj ≫ qj) (he : qi ≫ E = e ≫ qj) (hk : ki ≫ e = kj) :
    ei ≫ E = ej := by
  apply FppfQuotientComparison.hom_ext hq
  rw [← Category.assoc, hi, Category.assoc, he, ← Category.assoc, hk, hj]

end OverlapSquares

namespace RelativeLevi.AffineParabolicFaceChart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H U : GroupScheme S} [IsAffineHom G.X.hom] {p : H ⟶ G}
  {s t : S} (C : AffineParabolicFaceChart p s) (E : AffineParabolicFaceChart p t)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)
  (A : CommRingCat.{u}) (b : Spec A ⟶ Spec C.ring) (c : Spec A ⟶ Spec E.ring)
  (a : Spec A ⟶ S) (hb : b ≫ C.projection = a) (hc : c ≫ E.projection = a)

private lemma restricted_terms_agree (d : ℕ) {K : GroupScheme (Spec A)}
    (ki : K ⟶ (baseChange b).obj (C.termGroup d))
    (kj : K ⟶ (baseChange c).obj (E.termGroup d))
    (h : ki ≫ ((baseChange b).map (C.termInclusion d) ≫
        (Descent.pullbackComparison C.projection b a hb G).hom) =
      kj ≫ ((baseChange c).map (E.termInclusion d) ≫
        (Descent.pullbackComparison E.projection c a hc G).hom)) :
    ki ≫ (C.restrictionTermIso E r hG hp hr A b c a hb hc d).hom = kj := by
  let uj := (baseChange c).map (E.termInclusion d) ≫
    (Descent.pullbackComparison E.projection c a hc G).hom
  have hv : IsClosedSubgroup uj := ((E.isClosedSubgroup_termInclusion d).baseChange c).comp_iso
    (Descent.pullbackComparison E.projection c a hc G)
  have : Mono uj.hom.hom.left := hv.mono
  exact comp_eq_of_ambient ki kj _ _ uj (Over.mono_of_mono_left _)
    (C.restrictionTermIso_hom_comp E r hG hp hr A b c a hb hc d) h

local instance overlapAmbientAffine {Y : Scheme.{u}} (f : Y ⟶ S) :
    IsAffineHom ((baseChange f).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom f inferInstance

local instance overlapChartAffine {R : CommRingCat.{u}} (f : Spec R ⟶ S) :
    IsAffine ((baseChange f).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange f).obj G).X.hom

local instance overlapCoordinateFintype {x : S} (M : AffineParabolicFaceChart p x) :
    Fintype M.coordinateType := M.coordinateFintype

local instance overlapRootFintype {x : S} (M : AffineParabolicFaceChart p x) :
    Fintype M.rootType := M.rootFintype

private lemma restricted_quotients_agree (d : ℕ) {K Q : GroupScheme (Spec A)}
    {N : SubgroupFunctor K} (q : K ⟶ Q) (hq : RelativeRoot.IsFppfQuotient N q)
    (ki : K ⟶ (baseChange b).obj (C.termGroup d))
    (kj : K ⟶ (baseChange c).obj (E.termGroup d))
    (ei : Q ⟶ VectorGroup.groupScheme A (Nat.card (C.chart.weights.exactSupport d)))
    (ej : Q ⟶ VectorGroup.groupScheme A (Nat.card (E.chart.weights.exactSupport d)))
    (hi : q ≫ ei = ki ≫ C.restrictionQuotientMap A b d)
    (hj : q ≫ ej = kj ≫ E.restrictionQuotientMap A c d)
    (hk : ki ≫ ((baseChange b).map (C.termInclusion d) ≫
        (Descent.pullbackComparison C.projection b a hb G).hom) =
      kj ≫ ((baseChange c).map (E.termInclusion d) ≫
        (Descent.pullbackComparison E.projection c a hc G).hom)) :
    ei ≫ (C.restrictionQuotientIso E r hG hp hr A b c a hb hc d).hom = ej :=
  comp_eq_of_quotient q ki kj ei ej _ _ _ _ hq hi hj
    (C.restrictionQuotientIso_fac E r hG hp hr A b c a hb hc d)
    (C.restricted_terms_agree E r hG hp hr A b c a hb hc d ki kj hk)

end RelativeLevi.AffineParabolicFaceChart

namespace RelativeLevi.FiniteParabolicFaceCover

open RelativeUnipotent

variable {S : Scheme.{u}} [IsAffine S] {G H U : GroupScheme S}
  [IsAffineHom G.X.hom] {p : H ⟶ G}
  (D : FiniteParabolicFaceCover p)
  (r : U ⟶ H) (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)
  (hr : IsRelativeUnipotentRadical r)

/-- The original global quotient on an affine chart parameter, with its
canonical vector coefficients over that parameter. -/
def globalFaceQuotientAffineIso (d : ℕ) (i : D.Index) (A : CommRingCat.{u})
    (b : Spec A ⟶ Spec (D.charts i.down).2.ring) (a : Spec A ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).obj (D.globalFaceQuotientData r hG hp hr d).group ≅
      VectorGroup.groupScheme A (D.layerRank d i) :=
  let e : (baseChange b).obj ((D.charts i.down).2.layerGroup d) ≅
      VectorGroup.groupScheme A (D.layerRank d i) :=
    VectorGroup.affineCoefficientIso (R := CommRingCat.of (D.charts i.down).2.ring)
      (A := A) b (D.layerRank d i)
  D.globalFaceQuotientParameterIso r hG hp hr d i b a hb ≪≫ e

/-- The affine coefficient comparison commutes with the original full quotient map. -/
lemma globalFaceQuotientAffineIso_projection (d : ℕ) (i : D.Index) (A : CommRingCat.{u})
    (b : Spec A ⟶ Spec (D.charts i.down).2.ring) (a : Spec A ⟶ S)
    (hb : b ≫ (D.charts i.down).2.projection = a) :
    (baseChange a).map (D.globalFaceQuotientData r hG hp hr d).projection ≫
        (D.globalFaceQuotientAffineIso r hG hp hr d i A b a hb).hom =
      (D.globalTermParameterIso r hG hp hr d i b a hb).hom ≫
        (D.charts i.down).2.restrictionQuotientMap A b d := by
  have h := D.globalFaceQuotientParameterIso_projection r hG hp hr d i b a hb
  let e : (baseChange b).obj ((D.charts i.down).2.layerGroup d) ≅
      VectorGroup.groupScheme A (D.layerRank d i) :=
    VectorGroup.affineCoefficientIso (R := CommRingCat.of (D.charts i.down).2.ring)
      (A := A) b (D.layerRank d i)
  change _ ≫ ((D.globalFaceQuotientParameterIso r hG hp hr d i b a hb).hom ≫
    e.hom) = _ ≫ ((baseChange b).map ((D.charts i.down).2.layerProjection d) ≫ e.hom)
  simpa only [Category.assoc] using
    congrArg (fun v => v ≫ e.hom) h

variable (d : ℕ) (i j : D.Index) (A : CommRingCat.{u})
  (b : Spec A ⟶ Spec (D.charts i.down).2.ring)
  (c : Spec A ⟶ Spec (D.charts j.down).2.ring) (a : Spec A ⟶ S)
  (hb : b ≫ (D.charts i.down).2.projection = a)
  (hc : c ≫ (D.charts j.down).2.projection = a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original affine quotient parameter maps differ by the canonical
comparison of the two original full vector quotients. -/
lemma globalFaceQuotientAffineIso_overlap :
    let E : VectorGroup.groupScheme A (D.layerRank d i) ≅
        VectorGroup.groupScheme A (D.layerRank d j) :=
      AffineParabolicFaceChart.restrictionQuotientIso (p := p)
        (D.charts i.down).2 (D.charts j.down).2 r hG hp hr A b c a hb hc d
    (D.globalFaceQuotientAffineIso r hG hp hr d i A b a hb).hom ≫ E.hom =
      (D.globalFaceQuotientAffineIso r hG hp hr d j A c a hc).hom := by
  let q := (baseChange a).map (D.globalFaceQuotientData r hG hp hr d).projection
  let ki := (D.globalTermParameterIso r hG hp hr d i (Y := Spec A) b a hb).hom
  let kj := (D.globalTermParameterIso r hG hp hr d j (Y := Spec A) c a hc).hom
  let ei := (D.globalFaceQuotientAffineIso r hG hp hr d i A b a hb).hom
  let ej := (D.globalFaceQuotientAffineIso r hG hp hr d j A c a hc).hom
  have hq := (D.globalFaceQuotientData r hG hp hr d).quotient.baseChange a
  have hi := D.globalFaceQuotientAffineIso_projection r hG hp hr d i A b a hb
  have hj := D.globalFaceQuotientAffineIso_projection r hG hp hr d j A c a hc
  have hki := D.globalTermParameterIso_ambient r hG hp hr d i (Y := Spec A) b a hb
  have hkj := D.globalTermParameterIso_ambient r hG hp hr d j (Y := Spec A) c a hc
  have hk := hki.trans hkj.symm
  have h := AffineParabolicFaceChart.restricted_quotients_agree (p := p)
    (D.charts i.down).2 (D.charts j.down).2 r hG hp hr A b c a hb hc d
    q hq ki kj ei ej hi hj hk
  exact h

end RelativeLevi.FiniteParabolicFaceCover
end Langlands.GroupScheme
