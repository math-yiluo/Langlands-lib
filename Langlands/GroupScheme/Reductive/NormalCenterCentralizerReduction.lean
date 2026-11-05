import Langlands.GroupScheme.Reductive.NormalCenterDescent
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Full-centre containment from algebraically closed maximal-torus centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, self-centralization of maximal tori puts
the full centre of a connected reductive group in a closed split torus. -/
theorem exists_splitTorus_containing_center_of_algClosedMaximalTorusCentralizer
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hH : IsConnectedReductive H) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ H),
      IsSplitTorus T.toGrp ∧ IsClosedSubgroup t ∧
        center H ≤ SubgroupFunctor.range t := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  obtain ⟨T, t, ht⟩ := maximalTorusExistence k H
  refine ⟨T, t, ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting,
    ht.2.1, ?_⟩
  rw [← hCentralizer k H hH T t ht]
  exact center_le_torusCentralizer t

/-- Algebraically closed maximal-torus self-centralization supplies the split
embedding needed for full-centre containment under a closed normal inclusion. -/
theorem center_le_comap_of_normal_of_algClosedMaximalTorusCentralizer
    (hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (hH : IsConnectedReductive H)
    (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (hn : (SubgroupFunctor.range i).IsNormal) :
    center H ≤ (center G).comap i := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k H hH
  let : IsClosedImmersion z.hom.hom.left := hz.1
  let : IsAffineHom Z.X.hom := by
    rw [← z.hom.hom.w]
    infer_instance
  let : IsAffine Z.X.left := isAffine_of_isAffineHom Z.X.hom
  obtain ⟨T, t, hT, ht, hc⟩ :=
    exists_splitTorus_containing_center_of_algClosedMaximalTorusCentralizer hCentralizer H hH
  let : IsClosedImmersion t.hom.hom.left := ht
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  have htrep : (SubgroupFunctor.range t).IsRepresentedBy t := ⟨inferInstance, rfl⟩
  let j := htrep.factorHom z (hz.2 ▸ hc)
  have hj : IsClosedSubgroup j := IsClosedSubgroup.of_comp ht (by
    rw [SubgroupFunctor.IsRepresentedBy.factorHom_comp]
    exact hz.1)
  exact center_le_comap_of_normal_of_center_split_embedding
    i hn z hz.isRepresentedBy hT j hj

/-- Algebraically closed maximal-torus self-centralization suffices for the
full normal-reductive-centre theorem over every field. -/
def NormalReductiveCenterCentralizerReductionStatement : Prop :=
  AlgClosedMaximalTorusCentralizerStatement.{u} → NormalReductiveCenterStatement.{u}

/-- Choose the maximal torus after passage to the algebraic closure, apply
full-centre rigidity there, and descend the containment by the fpqc comparison. -/
theorem normalReductiveCenterCentralizerReduction :
    NormalReductiveCenterCentralizerReductionStatement.{u} := by
  intro hCentralizer k _ G H hG hH i hi hn
  let b := toAlgebraicClosure k
  obtain ⟨Z, z, hz⟩ := schemeTheoreticCenterExistence k G hG
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  let : Surjective b := hsurj
  let : Flat b := hflat
  let : QuasiCompact b := hqc
  apply center_le_comap_of_baseChange_le b i z hz
  apply center_le_comap_of_normal_of_algClosedMaximalTorusCentralizer
    hCentralizer hG.baseChange_toAlgebraicClosure hH.baseChange_toAlgebraicClosure
    ((GroupScheme.baseChange b).map i) (hi.baseChange b)
  rw [SubgroupFunctor.range_baseChangeHom]
  exact hn.baseChange b

/-- In particular, the full-field maximal-torus centralizer proposition implies
the exact normal-reductive-centre proposition. -/
theorem normalReductiveCenter_of_maximalTorusCentralizer
    (hCentralizer : MaximalTorusCentralizerStatement.{u}) :
    NormalReductiveCenterStatement.{u} :=
  normalReductiveCenterCentralizerReduction
    (fun k _ _ H hH T t ht => hCentralizer k H hH T t ht)

end Langlands.GroupScheme
