import Langlands.BruhatTits.RationalPoints.NormKernelCompactnessReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Rational.MaximalSplitQuotientAnisotropy
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.AnisotropicCompactnessStatement
import Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapProof
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup

/-! # Actual central maximal split-torus quotients and norm-kernel compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.BruhatTits.RationalPoints

/-- The actual smooth affine quotient by a central maximal split torus is
anisotropic, and its projection is smooth. No reductivity of the quotient is asserted. -/
theorem exists_smooth_anisotropic_central_split_quotient
    {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {j : A.toGrp ⟶ G}
    (hj : IsMaximalSplitTorus j) (hc : IsCentral j) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧ IsAnisotropic Q ∧
      Smooth q.hom.hom.left ∧
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨Q, q, hs, ha, hq⟩ :=
    normalSubgroupQuotient k G A.toGrp j hj.1.2 hc.range_isNormal
  let : IsAffineHom Q.X.hom := ha
  let : IsClosedImmersion j.hom.hom.left := hj.1.2
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  exact ⟨Q, q, hs, ha, hj.isAnisotropic_quotient hc q hq,
    hq.smooth_of_smooth_kernel hjrep hj.1.1.smooth, hq⟩

/-- Anisotropic compactness gives actual norm-kernel compactness through any
specified connected reductive quotient by a central maximal split torus. -/
def CentralSplitQuotientNormKernelCompactnessStatement : Prop :=
  AnisotropicCompactnessStatement.{u} →
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (A : CommGroupScheme (Spec (CommRingCat.of F))) (j : A.toGrp ⟶ G),
      IsMaximalSplitTorus j → IsCentral j →
      ∀ (Q : GroupScheme (Spec (CommRingCat.of F))) (q : G ⟶ Q),
      IsConnectedReductive Q →
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) q →
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsCompact (rationalCommonNormKernel G : Set (rationalPoints G))

/-- The smooth-kernel projection is open on local-field points. Its kernel
is central; anisotropy makes its connected reductive target compact. -/
theorem centralSplitQuotientNormKernelCompactness :
    CentralSplitQuotientNormKernelCompactnessStatement.{u} := by
  intro hcompact F _ _ _ _ G hG A j hj hc Q q hQ hq
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : IsAffine Q.X.left := isAffine_of_isAffineHom Q.X.hom
  let : Smooth Q.X.hom := hQ.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.1.2
  have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
    rw [Over.w q.hom.hom]
    infer_instance
  let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
  let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
  let : Smooth q.hom.hom.left := hq.smooth_of_smooth_kernel hjrep hj.1.1.smooth
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  let : TopologicalSpace (rationalPoints Q) := rationalPointTopology F Q.X
  let : IsTopologicalGroup (rationalPoints Q) := rationalPoint_isTopologicalGroup F Q
  let : T2Space F := BruhatTits.localField_t2Space F
  let : T2Space (rationalPoints Q) := rationalPoint_t2Space F Q
  have hani : IsAnisotropic Q := hj.isAnisotropic_quotient hc q hq
  let : CompactSpace (rationalPoints Q) := ⟨(hcompact F Q hQ).mpr hani⟩
  let qpt : rationalPoints G →ₜ* rationalPoints Q :=
    { rationalPoints.map q with
      continuous_toFun := continuous_rationalPointMap F q.hom.hom }
  have hopen : IsOpenMap qpt :=
    smoothRationalPointOpenMap F G.X Q.X q.hom.hom
  have hker : qpt.ker ≤ Subgroup.center (rationalPoints G) := by
    intro g hg
    have hg' : g ∈ (SubgroupFunctor.range (kernelι q)).carrier (Over.mk (𝟙 _)) :=
      (mem_range_kernelι_iff q g).mpr hg
    rw [hq.2.2.2] at hg'
    obtain ⟨a, rfl⟩ := SubgroupFunctor.mem_range.mp hg'
    exact hc.map_mem_center a
  exact isCompact_rationalCommonNormKernel_of_open_central_quotient G hG qpt hopen hker

end Langlands.BruhatTits.RationalPoints
