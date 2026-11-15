import Langlands.GroupScheme.RelativeLevi.ParabolicLocalSectionConjugacy
import Langlands.GroupScheme.RelativeLevi.GeometricBorelNormalizerTransitivity
import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.RelativeLevi.ParabolicLieContainmentProof
import Langlands.GroupScheme.Reductive.SplitNormalizerLocalLiftingStatement

/-! # Local normalizer conjugacy from geometric lifting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open SubgroupFunctor

section GeometricConjugacy

variable {S : Scheme.{u}} {G B B' : GroupScheme S}
  {T : CommGroupScheme S} {i : B ⟶ G} {j : B' ⟶ G}

/-- Geometric Borel conjugacy containing a fixed maximal torus, expressed by an
original-base point in the full normalizer and the all-test conjugacy relation. -/
theorem IsRelativeBorelSubgroup.exists_fieldPoint_normalizer_conjugacy
    (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j)
    (hG : IsReductive G) (t : T.toGrp ⟶ G) (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j)
    {k : Type u} [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ S) :
    ∃ n : Over.mk x ⟶ G.X,
      n ∈ (range t).normalizer.carrier (Over.mk x) ∧
        IsConjugatingPoint (range i) (range j) n := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hred := hG.isConnectedReductive_baseChange x
  let : Smooth ((GroupScheme.baseChange x).obj G).X.hom := hred.smooth
  let : IsAffineHom ((GroupScheme.baseChange x).obj G).X.hom := hred.isAffineHom
  let : ConnectedSpace ((GroupScheme.baseChange x).obj G).X.left := hred.connectedSpace
  have hti' : range ((GroupScheme.baseChange x).map t) ≤ range ((GroupScheme.baseChange x).map i) := by
    simpa only [range_baseChangeHom] using baseChange_mono x hti
  have htj' : range ((GroupScheme.baseChange x).map t) ≤ range ((GroupScheme.baseChange x).map j) := by
    simpa only [range_baseChangeHom] using baseChange_mono x htj
  obtain ⟨n, hn, hc⟩ := (hi.fieldPoint hG x).1.exists_normalizer_range_conjugacy
    (T := (CommGroupScheme.baseChange x).obj T) (hj.fieldPoint hG x).1 ((GroupScheme.baseChange x).map t) (hmax.fieldPoint x) hti' htj'
  refine ⟨baseChangeBasePointsEquiv x G n, ?_, ?_⟩
  · apply isConjugatingPoint_self_iff.mp
    apply (isConjugatingPoint_baseChangeBasePointsEquiv_iff x n).mp
    rw [← range_baseChangeHom]
    exact isConjugatingPoint_self_iff.mpr hn
  · apply (isConjugatingPoint_baseChangeBasePointsEquiv_iff x n).mp
    rw [← range_baseChangeHom, ← range_baseChangeHom]
    exact (isConjugatingPoint_iff_range_innerIso _ _ n).mpr hc

end GeometricConjugacy

section LocalConjugacy

variable {S : Scheme.{u}} {G B B' : GroupScheme S}
  (i : B ⟶ G) (j : B' ⟶ G) (T : CommGroupScheme S) (t : T.toGrp ⟶ G)

/-- Geometric normalizer lifting modulo the common torus implies Zariski-local
normalizer conjugacy of two relative Borels containing that torus. -/
theorem relativeBorel_exists_open_normalizer_conjugacy_of_geometric_lifting
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j) (s : S)
    (hLift : ∀ n : Over.mk (geometricPoint S s) ⟶ G.X,
      n ∈ (range t).normalizer.carrier (Over.mk (geometricPoint S s)) →
      ∃ V : S.Opens, geometricPoint S s
          (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) ∈ V ∧
        ∃ (a : Over.mk (geometricPoint S s) ⟶ Over.mk V.ι)
          (nV : Over.mk V.ι ⟶ G.X),
          nV ∈ (range t).normalizer.carrier (Over.mk V.ι) ∧
            (a ≫ nV) * n⁻¹ ∈ (range t).carrier (Over.mk (geometricPoint S s))) :
    ∃ U : S.Opens, s ∈ U ∧
      ∃ n : Over.mk (𝟙 U.toScheme) ⟶ ((GroupScheme.baseChange U.ι).obj G).X,
        n ∈ (range ((GroupScheme.baseChange U.ι).map t)).normalizer.carrier
          (Over.mk (𝟙 U.toScheme)) ∧
        range ((GroupScheme.baseChange U.ι).map i ≫ (((GroupScheme.baseChange U.ι).obj G).innerIso n).hom) =
          range ((GroupScheme.baseChange U.ι).map j) := by
  obtain ⟨n, hn, hc⟩ := hi.exists_fieldPoint_normalizer_conjugacy hj hG t hmax
    hti htj (geometricPoint S s)
  obtain ⟨V, _, a, nV, hnV, hdiff⟩ := hLift n hn
  have hcV : IsConjugatingPoint (range i) (range j) (a ≫ nV) :=
    hc.of_mul_inv_mem_target (htj _ hdiff)
  obtain ⟨U, hu, nU, hnU, hcU⟩ :=
    relativeParabolic_exists_open_conjugatingPoint_of_local_fieldPoint
      i j T t relativeParabolicLieContainment hG hi.isRelativeParabolicSubgroup
      hj.isRelativeParabolicSubgroup hT ht hmax hti htj (geometricPoint S s) V a nV hnV hcV
  have hs : s ∈ U := by
    change S.fromSpecResidueField s
      ((toAlgebraicClosure _) (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s)))) ∈ U at hu
    simpa only [Scheme.fromSpecResidueField_apply] using hu
  let n' := (baseChangeBasePointsEquiv U.ι G).symm nU
  refine ⟨U, hs, n', ?_, (isConjugatingPoint_iff_baseChange_range i j nU).mp hcU⟩
  apply isConjugatingPoint_self_iff.mp
  rw [range_baseChangeHom]
  apply (isConjugatingPoint_baseChangeBasePointsEquiv_iff U.ι n').mpr
  simpa only [n', MulEquiv.apply_symm_apply] using isConjugatingPoint_self_iff.mpr hnU

/-- Choose the actual local normalizer-conjugacy witness under geometric lifting. -/
def relativeBorelLocalNormalizerConjugacyOfGeometricLifting
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i) (hj : IsRelativeBorelSubgroup j)
    (hT : RelativeTorus.IsTorus T.toGrp) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus t)
    (hti : range t ≤ range i) (htj : range t ≤ range j) (s : S)
    (hLift : ∀ n : Over.mk (geometricPoint S s) ⟶ G.X,
      n ∈ (range t).normalizer.carrier (Over.mk (geometricPoint S s)) →
      ∃ V : S.Opens, geometricPoint S s
          (IsLocalRing.closedPoint (AlgebraicClosure (S.residueField s))) ∈ V ∧
        ∃ (a : Over.mk (geometricPoint S s) ⟶ Over.mk V.ι)
          (nV : Over.mk V.ι ⟶ G.X),
          nV ∈ (range t).normalizer.carrier (Over.mk V.ι) ∧
            (a ≫ nV) * n⁻¹ ∈ (range t).carrier (Over.mk (geometricPoint S s))) :
    Σ U : S.Opens,
      {n : Over.mk (𝟙 U.toScheme) ⟶ ((GroupScheme.baseChange U.ι).obj G).X //
        s ∈ U ∧
        n ∈ (range ((GroupScheme.baseChange U.ι).map t)).normalizer.carrier
          (Over.mk (𝟙 U.toScheme)) ∧
        range ((GroupScheme.baseChange U.ι).map i ≫ (((GroupScheme.baseChange U.ι).obj G).innerIso n).hom) =
          range ((GroupScheme.baseChange U.ι).map j)} :=
  let h := relativeBorel_exists_open_normalizer_conjugacy_of_geometric_lifting
    i j T t hG hi hj hT ht hmax hti htj s hLift
  ⟨h.choose, h.choose_spec.2.choose, h.choose_spec.1, h.choose_spec.2.choose_spec⟩

end LocalConjugacy

/-- Part (2) of split Borel local conjugacy follows from the exact published
geometric normalizer-lifting statement, with all original split data retained. -/
theorem splitBorel_exists_open_normalizer_conjugacy_of_lifting
    (hLift : SplitNormalizerGeometricLocalLiftingStatement.{u})
    (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (I : Type u) [Fintype I]
    (t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) :
    haveI := hG.isAffineHom
    IsClosedSubgroup t →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t →
    IsFibrewiseRootDatumOf I G t P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G t (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ (B B' : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G) (j : B' ⟶ G),
      IsRelativeBorelSubgroup i → IsRelativeBorelSubgroup j →
      range t ≤ range i → range t ≤ range j →
      ∀ s : Spec (CommRingCat.of R), ∃ U : (Spec (CommRingCat.of R)).Opens, s ∈ U ∧
        ∃ n : Over.mk (𝟙 U.toScheme) ⟶ ((GroupScheme.baseChange U.ι).obj G).X,
          n ∈ (range ((GroupScheme.baseChange U.ι).map t)).normalizer.carrier
            (Over.mk (𝟙 U.toScheme)) ∧
          range ((GroupScheme.baseChange U.ι).map i ≫
              (((GroupScheme.baseChange U.ι).obj G).innerIso n).hom) =
            range ((GroupScheme.baseChange U.ι).map j) := by
  intro ht hmax hroot hfree B B' i j hi hj hti htj s
  exact relativeBorel_exists_open_normalizer_conjugacy_of_geometric_lifting
    i j (splitTorus.commGroupScheme _ I) t hG hi hj
    (RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)) ht hmax hti htj s
    (hLift R G hG I t J P ht hmax hroot hfree
      (AlgebraicClosure ((Spec (CommRingCat.of R)).residueField s)) (geometricPoint _ s))

end Langlands.GroupScheme
