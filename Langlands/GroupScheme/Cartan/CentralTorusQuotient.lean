import Langlands.GroupScheme.Nilpotent.CentralExtension
import Langlands.GroupScheme.Torus.CentralizerConnected
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Torus.NoTorusUnipotentStatement
import Langlands.GroupScheme.Cartan.StructureStatement

/-! # The central maximal torus quotient of a Cartan subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- A central maximal torus and its actual smooth connected affine quotient,
without any assumed nilpotence or asserted unipotence. -/
structure CentralMaximalTorusQuotientData
    (G : GroupScheme (Spec (CommRingCat.of k))) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ G
  quotient : GroupScheme (Spec (CommRingCat.of k))
  projection : G ⟶ quotient
  maximal_torus : IsMaximalTorus inclusion
  central : IsCentral inclusion
  smooth_quotient : Smooth quotient.X.hom
  affine_quotient : IsAffineHom quotient.X.hom
  connected_quotient : ConnectedSpace quotient.X.left
  smooth_projection : Smooth projection.hom.hom.left
  fppf_quotient : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range inclusion) projection
  no_tori : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))), IsTorus T.toGrp →
    ∀ g : T.toGrp ⟶ quotient, SubgroupFunctor.range g = ⊥

variable {G C : GroupScheme (Spec (CommRingCat.of k))}

/-- Construct the actual affine quotient of any smooth connected affine group
by a specified central maximal torus. -/
def IsMaximalTorus.centralQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalTorus i) (hc : IsCentral i) :
    CentralMaximalTorusQuotientData G :=
  Classical.choice (by
    obtain ⟨Q, q, hs, ha, hq⟩ :=
      normalSubgroupQuotient k G T.toGrp i hi.2.1 hc.range_isNormal
    let : Smooth Q.X.hom := hs
    let : IsAffineHom Q.X.hom := ha
    let : IsClosedImmersion i.hom.hom.left := hi.2.1
    have hr : (SubgroupFunctor.range i).IsRepresentedBy i :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    have hqc : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    let : QuasiCompact (q.hom.hom.left ≫ Q.X.hom) := hqc
    let : QuasiCompact q.hom.hom.left := QuasiCompact.of_comp _ Q.X.hom
    exact ⟨{
      torus := T
      inclusion := i
      quotient := Q
      projection := q
      maximal_torus := hi
      central := hc
      smooth_quotient := hs
      affine_quotient := ha
      connected_quotient := hq.connectedSpace
      smooth_projection := hq.smooth_of_smooth_kernel hr hi.1.smooth
      fppf_quotient := hq
      no_tori := centralMaximalTorusQuotientStatement k G T i hc hi Q q hq }⟩)

/-- The actual kernel of the quotient projection is central. -/
theorem CentralMaximalTorusQuotientData.central_kernel
    (D : CentralMaximalTorusQuotientData G) : IsCentral (kernelι D.projection) := by
  apply (isCentral_iff_range_le_center _).2
  rw [D.fppf_quotient.2.2.2]
  exact (isCentral_iff_range_le_center _).1 D.central

/-- A Cartan subgroup contains its witnessing maximal torus centrally. Its
actual quotient is smooth connected affine and receives no nontrivial torus
homomorphisms. No nilpotence premise is used. -/
def IsCartanSubgroup.centralTorusQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : C ⟶ G} (hj : IsCartanSubgroup j) :
    CentralMaximalTorusQuotientData C := Classical.choice (by
  obtain ⟨hs, hc⟩ := hj.smooth_connected
  let : Smooth C.X.hom := hs
  let : ConnectedSpace C.X.left := hc
  let : IsClosedImmersion j.hom.hom.left := hj.1
  let : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨T, i, hi, hrep⟩ := hj.exists_centralizer_representation
  exact ⟨(hi.isMaximalTorus_torusCentralizerFactor hrep hj.1).centralQuotient
    (isCentral_torusCentralizerFactor i hrep)⟩)

/-- If its central maximal torus quotient is unipotent, the group has a
uniform nilpotence bound on every relative scheme test. -/
theorem CentralMaximalTorusQuotientData.exists_hasUniformNilpotentPoints
    (D : CentralMaximalTorusQuotientData G) (hQ : IsUnipotent D.quotient) :
    ∃ d, HasUniformNilpotentPoints G d := by
  let := D.affine_quotient
  let := D.smooth_quotient
  exact exists_hasUniformNilpotentPoints_of_isCentral_kernelι_of_isUnipotent
    D.projection D.central_kernel hQ

/-- Conditional only on the exact no-torus unipotence statement, a central
maximal torus quotient supplies geometric nilpotence. -/
theorem CentralMaximalTorusQuotientData.isNilpotentGroupScheme
    (D : CentralMaximalTorusQuotientData G)
    (hunip : NoTorusUnipotentStatement.{u}) : IsNilpotentGroupScheme G := by
  let := D.smooth_quotient
  let := D.affine_quotient
  let := D.connected_quotient
  obtain ⟨d, hd⟩ := D.exists_hasUniformNilpotentPoints
    (hunip k D.quotient D.no_tori)
  exact hd.isNilpotentGroupScheme

/-- Cartan structure follows from the exact no-torus theorem. This is a
conditional reduction, not a proof of that structural input. -/
theorem cartanStructure_of_noTorusUnipotent
    (hunip : NoTorusUnipotentStatement.{u}) : CartanStructureStatement.{u} := by
  intro k _ G _ _ _ C j hj
  obtain ⟨hs, hc⟩ := hj.smooth_connected
  exact ⟨hs, hc, hj.centralTorusQuotient.isNilpotentGroupScheme hunip⟩

end Langlands.GroupScheme
