import Langlands.GroupScheme.Reductive.LocalRankOneCentralizer
import Langlands.GroupScheme.Reductive.LocalRankOneWeylData
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.LocalSplitRootTransport
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Torus.PointedEtaleNormalizer
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport

/-! # Actual pointed etale rank-one normalizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace LocalSplitRootBaseChange

open LocalSplitCell

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- The coordinate-preserving base change of a root map commutes with a
homomorphism of its ambient group. -/
theorem baseChangeRoot_comp (x : Ga R ⟶ G) (j : G ⟶ H) :
    baseChangeRoot A (x ≫ j) =
      baseChangeRoot A x ≫ (GroupScheme.baseChange (algebraBaseMap R A)).map j := by
  simp only [baseChangeRoot, Functor.map_comp, Category.assoc]

end LocalSplitRootBaseChange

namespace splitTorus

variable {S S' : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme S} (i : splitTorus S I ⟶ G) (b : S' ⟶ S)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    {n : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X}

/-- A normalizer expressed in standard torus coordinates normalizes the
actual pullback torus through the pullback of the same integral action. -/
theorem isNormalizingPoint_baseChange_of_coordinates
    (hn : IsNormalizingPoint (T := commGroupScheme S' I)
      ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) n
      (exponentCommIso S' I e)) :
    IsNormalizingPoint
      (T := (CommGroupScheme.baseChange b).obj (commGroupScheme S I))
      ((GroupScheme.baseChange b).map i) n
      ((CommGroupScheme.baseChange b).mapIso (exponentCommIso S I e)) := by
  apply (cancel_epi (baseChangeIso b I).inv).mp
  change ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
      (((GroupScheme.baseChange b).obj G).innerIso n).hom =
    (baseChangeIso b I).inv ≫
      (GroupScheme.baseChange b).map (exponentIso S I e).hom ≫
        (GroupScheme.baseChange b).map i
  have he : (baseChangeIso b I).inv ≫
      (GroupScheme.baseChange b).map (exponentIso S I e).hom =
      (exponentIso S' I e).hom ≫ (baseChangeIso b I).inv := by
    apply (cancel_mono (baseChangeIso b I).hom).mp
    rw [Category.assoc, ← exponentIso_baseChange S I b e,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]
  exact hn

end splitTorus

/-- An affine pointed etale lift with an involutive prescribed action has
its square in the actual pullback torus. -/
theorem PointedEtaleNormalizerData.exists_sq_eq
    {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {σ : T ≅ T} {s : Spec R}
    {n₀ : Over.mk ((Spec R).fromSpecResidueField s) ⟶ G.X}
    (d : PointedEtaleNormalizerData i σ s n₀)
    (hσ : σ ≪≫ σ = Iso.refl T) (hG : IsReductive G)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i) :
    ∃ z : Over.mk (𝟙 d.neighbourhood) ⟶
        ((CommGroupScheme.baseChange d.projection).obj T).X,
      d.sectionPoint * d.sectionPoint =
        z ≫ ((GroupScheme.baseChange d.projection).map i).hom.hom := by
  let : Smooth G.X.hom := hG.smooth
  have hσ' : (CommGroupScheme.baseChange d.projection).mapIso σ ≪≫
      (CommGroupScheme.baseChange d.projection).mapIso σ = Iso.refl _ := by
    rw [← Functor.mapIso_trans, hσ]
    exact Functor.mapIso_refl _ _
  exact d.isNormalizing.exists_sq_eq_of_fibrewiseMaximal hσ'
    (hG.baseChange d.projection) (hT.baseChange d.projection)
    (hi.baseChange d.projection) (hmax.baseChange d.projection)

/-- A lift of a specified nonzero residue product, with exact recovery and
prescribed torus action. The product is supplied as a family of fibre points. -/
structure PointedEtaleProductNormalizerData
    {R : CommRingCat.{u}} {T : CommGroupScheme (Spec R)}
    {G : GroupScheme (Spec R)} (i : T.toGrp ⟶ G) (σ : T ≅ T)
    (s : Spec R)
    (n : (Spec R).residueField s →
      (Over.mk (𝟙 (Spec ((Spec R).residueField s))) ⟶
        ((GroupScheme.baseChange ((Spec R).fromSpecResidueField s)).obj G).X)) where
  scalar : (Spec R).residueField s
  scalar_ne_zero : scalar ≠ 0
  lift : PointedEtaleNormalizerData i σ s (residueNormalizerPoint (G := G) s (n scalar))

namespace LocalRankOneEtaleWeylData

/-- Transport a base-changed section along equality of the actual base maps. -/
def baseChangePointOfEq {S U : Scheme.{u}} {G : GroupScheme S}
    {b c : U ⟶ S} (h : b = c)
    (n : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange b).obj G).X) :
    Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange c).obj G).X := h ▸ n

/-- The prescribed normalizer action is unchanged by transport along equal
base maps. -/
theorem baseChangePointOfEq_isNormalizing {S U : Scheme.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S} (i : T.toGrp ⟶ G)
    (σ : T ≅ T) {b c : U ⟶ S} (h : b = c)
    (n : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange b).obj G).X)
    (hn : IsNormalizingPoint ((GroupScheme.baseChange b).map i) n
      ((CommGroupScheme.baseChange b).mapIso σ)) :
    IsNormalizingPoint ((GroupScheme.baseChange c).map i) (baseChangePointOfEq h n)
      ((CommGroupScheme.baseChange c).mapIso σ) := by
  cases h
  exact hn

/-- The algebra on an actual scheme residue field induced by its canonical
map to the affine base. -/
abbrev residueFieldAlgebra (R : Type u) [CommRing R]
    (s : Spec (CommRingCat.of R)) :
    Algebra R ((Spec (CommRingCat.of R)).residueField s) :=
  (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)).hom.toAlgebra

/-- This residue algebra has exactly the canonical residue-field base map. -/
theorem residueFieldAlgebra_baseMap (R : Type u) [CommRing R]
    (s : Spec (CommRingCat.of R)) :
    letI := residueFieldAlgebra R s
    algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s :=
  Spec.map_preimage _

end LocalRankOneEtaleWeylData

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (ha : ∑ j, P.root a j * mu j = 0)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)

include hG hmax hP

/-- On each supplied field fibre the product of the actual lifted opposite
root maps realizes the original root reflection inside the centralizer. -/
theorem exists_fieldReflection (k : Type u) [Field k] [Algebra R k] :
    ∃ d : k, d ≠ 0 ∧ IsNormalizingPoint (T := commGroupScheme _ I)
      (baseChangeHom (K := k) (groupScheme I G i mu) I (torusHom I G i mu))
      (weylPoint (baseChangeRoot k (rootLift i mu hp ha))
        (scaleHom d ≫ baseChangeRoot k (rootLift i mu hm (by
          simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
            congrArg Neg.neg ha))))
      (exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a)) := by
  let : Smooth G.X.hom := hG.smooth
  have hm' : IsRootParametrization i (P.root (P.reflectionPerm a a)) xm := by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] using hm
  obtain ⟨d, hd, -, hn⟩ :=
    LocalSplitCell.fieldWeylNormalization R G hG I i hmax J P hP a xp xm hp hm' k
  refine ⟨d, hd, ?_⟩
  let j := (GroupScheme.baseChange (algebraBaseMap R k)).map (inclusion I G i mu)
  have hj : IsClosedSubgroup j := (isClosedSubgroup_inclusion I G i mu).baseChange _
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  apply IsNormalizingPoint.of_comp j
  have ht : baseChangeHom (K := k) (groupScheme I G i mu) I (torusHom I G i mu) ≫ j =
      baseChangeHom (K := k) G I i := by
    dsimp only [baseChangeHom, j]
    rw [Category.assoc, ← Functor.map_comp, torusHom_comp]
  rw [ht, ← weylPoint_comp]
  have hpj : baseChangeRoot k (rootLift i mu hp ha) ≫ j = baseChangeRoot k xp := by
    rw [← baseChangeRoot_comp, rootLift_comp]
  have hmj : (scaleHom d ≫ baseChangeRoot k (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))) ≫ j = scaleHom d ≫ baseChangeRoot k xm := by
    rw [Category.assoc, ← baseChangeRoot_comp, rootLift_comp]
  rw [hpj, hmj]
  exact hn.isNormalizingPoint

/-- The actual residue-fibre Weyl product of the two lifted root maps,
with its base map identified with the canonical residue map. -/
def residueReflectionPoint (s : Spec (CommRingCat.of R))
    (d : (Spec (CommRingCat.of R)).residueField s) :
    Over.mk (𝟙 (Spec ((Spec (CommRingCat.of R)).residueField s))) ⟶
      ((GroupScheme.baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).obj
        (groupScheme I G i mu)).X := by
  letI := LocalRankOneEtaleWeylData.residueFieldAlgebra R s
  exact LocalRankOneEtaleWeylData.baseChangePointOfEq (G := groupScheme I G i mu)
    (LocalRankOneEtaleWeylData.residueFieldAlgebra_baseMap R s)
    (weylPoint (baseChangeRoot ((Spec (CommRingCat.of R)).residueField s)
        (rootLift i mu hp ha))
      (scaleHom d ≫ baseChangeRoot ((Spec (CommRingCat.of R)).residueField s) (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))))

/-- The residue Weyl product normalizes the actual fibre torus through the
pullback of the actual root-coroot reflection over the local base. -/
theorem exists_residueReflection [IsLocalRing R] (s : Spec (CommRingCat.of R)) :
    ∃ d : (Spec (CommRingCat.of R)).residueField s, d ≠ 0 ∧
      IsNormalizingPoint
        ((GroupScheme.baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).map
          (torusHom I G i mu))
        (residueReflectionPoint i mu a ha hp hm s d)
        ((CommGroupScheme.baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField s)).mapIso
          (LocalRankOneWeylData.corootReflectionIso hP a)) := by
  let := LocalRankOneEtaleWeylData.residueFieldAlgebra R s
  obtain ⟨d, hd, hn⟩ := exists_fieldReflection i mu hG hmax hP a ha hp hm
    ((Spec (CommRingCat.of R)).residueField s)
  refine ⟨d, hd, ?_⟩
  unfold residueReflectionPoint
  apply LocalRankOneEtaleWeylData.baseChangePointOfEq_isNormalizing
  change IsNormalizingPoint _ _
    ((CommGroupScheme.baseChange (algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s))).mapIso
      (RingRootCell.reflectionIso _ _ (LocalRankOneWeylData.coroot_comp_root hP a)))
  rw [LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a]
  exact splitTorus.isNormalizingPoint_baseChange_of_coordinates
    (torusHom I G i mu) (algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s)) (P.reflection a) hn

/-- Lift the actual residue reflection with its prescribed whole-base action
and exact residue recovery over an affine pointed etale neighbourhood. -/
def pointedEtaleReflection [IsLocalRing R] (s : Spec (CommRingCat.of R)) :
    PointedEtaleProductNormalizerData (T := commGroupScheme (Spec (CommRingCat.of R)) I)
      (G := groupScheme I G i mu) (torusHom I G i mu)
      (LocalRankOneWeylData.corootReflectionIso hP a) s
      (residueReflectionPoint i mu a ha hp hm s) := Classical.choice <| by
  obtain ⟨d, hd, hn⟩ := exists_residueReflection i mu hG hmax hP a ha hp hm s
  let hC := isReductive i mu hG
  let : Smooth (groupScheme I G i mu).X.hom := hC.smooth
  let : IsAffine (groupScheme I G i mu).X.left :=
    isAffine_of_isAffineHom (groupScheme I G i mu).X.hom
  exact ⟨{ scalar := d, scalar_ne_zero := hd
           lift := pointedEtaleNormalizerOfNormalizing
             (T := commGroupScheme (Spec (CommRingCat.of R)) I)
             (G := groupScheme I G i mu) (torusHom I G i mu)
             (LocalRankOneWeylData.corootReflectionIso hP a)
             (isSplitTorus_splitTorus I) hC.smooth s _ hn }⟩

omit [DecidableEq I] in
/-- Every such lift of the actual residue reflection has square in the
actual pullback of the inherited torus, when the ambient torus is closed. -/
theorem pointedEtaleReflection_sq [IsLocalRing R] (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of R))
    (d : PointedEtaleProductNormalizerData
      (T := commGroupScheme (Spec (CommRingCat.of R)) I)
      (G := groupScheme I G i mu) (torusHom I G i mu)
      (LocalRankOneWeylData.corootReflectionIso hP a) s
      (residueReflectionPoint i mu a ha hp hm s)) :
    ∃ z : Over.mk (𝟙 d.lift.neighbourhood) ⟶
        ((CommGroupScheme.baseChange d.lift.projection).obj
          (commGroupScheme (Spec (CommRingCat.of R)) I)).X,
      d.lift.sectionPoint * d.lift.sectionPoint =
        z ≫ ((GroupScheme.baseChange d.lift.projection).map
          (torusHom I G i mu)).hom.hom := by
  apply d.lift.exists_sq_eq
  · exact RingRootCell.reflectionIso_trans_self _ _ (LocalRankOneWeylData.coroot_comp_root hP a)
  · exact isReductive i mu hG
  · exact isSplitTorus_splitTorus I
  · apply IsClosedSubgroup.of_comp (isClosedSubgroup_inclusion I G i mu)
    rw [torusHom_comp]
    exact hi
  · exact isFibrewiseMaximalTorus i mu hmax

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
