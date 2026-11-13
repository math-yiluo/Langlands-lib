import Langlands.GroupScheme.Quaternionic.SpinKernelBinaryReduction
import Langlands.GroupScheme.BaseChangeReflection

/-! # The binary diagonal as a morphism to the actual spin kernel -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- The original binary diagonal, factored through the full scheme-theoretic kernel. -/
def diagonalKernel : BinaryKernel.muTwo (K := K) ⟶ kernel π :=
  pullback.lift (diagonalSpin σ hdim hsym h hπ hsc) 0 (by
    apply (Grp.forget _).map_injective
    change (diagonalSpin σ hdim hsym h hπ hsc).hom.hom ≫ π.hom.hom = _
    rw [diagonalSpin_comp]
    exact (MonObj.comp_one _).symm)

/-- The factorization preserves the original morphism into the supplied spin group. -/
@[reassoc]
theorem diagonalKernel_comp :
    diagonalKernel σ hdim hsym h hπ hsc ≫ kernelι π =
      diagonalSpin σ hdim hsym h hπ hsc :=
  pullback.lift_fst _ _ _

/-- An isomorphism with the actual kernel gives both geometric inputs used by the
binary kernel-generation reduction. -/
theorem mono_and_coverage_of_isIso_diagonalKernel
    [IsIso (diagonalKernel σ hdim hsym h hπ hsc)] :
    Mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom ∧
      SubgroupFunctor.range (kernelι π) ≤
        SubgroupFunctor.range (productHom σ hdim hsym h hπ hsc) := by
  have hc : (diagonalKernel σ hdim hsym h hπ hsc).hom.hom ≫ (kernelι π).hom.hom =
      (diagonalSpin σ hdim hsym h hπ hsc).hom.hom := by
    change (diagonalKernel σ hdim hsym h hπ hsc ≫ kernelι π).hom.hom = _
    rw [diagonalKernel_comp]
  refine ⟨?_, ?_⟩
  · rw [← hc]
    infer_instance
  · intro T s hs
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hs
    have hd : y ≫ (kernelι π).hom.hom ∈
        (SubgroupFunctor.range (diagonalSpin σ hdim hsym h hπ hsc)).carrier T := by
      refine SubgroupFunctor.mem_range.mpr
        ⟨y ≫ (inv (diagonalKernel σ hdim hsym h hπ hsc)).hom.hom, ?_⟩
      rw [← hc, Category.assoc,
        ← Category.assoc (inv (diagonalKernel σ hdim hsym h hπ hsc)).hom.hom,
        ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom, Category.id_comp]
    rw [diagonalSpin_range] at hd
    exact hd.1

/-- The two geometric inputs identify the actual diagonal-kernel factorization
as an isomorphism of group schemes. -/
theorem isIso_diagonalKernel_of_mono_and_coverage
    (hm : Mono (diagonalSpin σ hdim hsym h hπ hsc).hom.hom)
    (hcover : SubgroupFunctor.range (kernelι π) ≤
      SubgroupFunctor.range (productHom σ hdim hsym h hπ hsc)) :
    IsIso (diagonalKernel σ hdim hsym h hπ hsc) := by
  have hr : SubgroupFunctor.range (diagonalSpin σ hdim hsym h hπ hsc) =
      SubgroupFunctor.range (kernelι π) := by
    rw [diagonalSpin_range]
    ext T x
    constructor
    · exact fun hx => hx.2
    · exact fun hx => ⟨hcover T hx, hx⟩
  let hi : (SubgroupFunctor.range (kernelι π)).IsRepresentedBy
      (diagonalSpin σ hdim hsym h hπ hsc) := ⟨hm, hr⟩
  let hj : (SubgroupFunctor.range (kernelι π)).IsRepresentedBy (kernelι π) :=
    ⟨inferInstance, rfl⟩
  have he : (hi.isoOfIsRepresentedBy hj).hom =
      diagonalKernel σ hdim hsym h hπ hsc := by
    apply hj.hom_ext
    rw [SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp,
      diagonalKernel_comp]
  rw [← he]
  infer_instance

end Langlands.GroupScheme.Quaternionic.BinarySpinLift

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] [Infinite K]
  (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- A scheme-theoretic identification of the binary diagonal with the full kernel
implies kernel generation for every Levi lift pair. -/
theorem kernelGenerator_of_isIso_diagonalKernel
    [IsIso (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc)]
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      π mu psi := by
  obtain ⟨hm, hc⟩ :=
    BinarySpinLift.mono_and_coverage_of_isIso_diagonalKernel σ hdim hsym h hπ hsc
  exact kernelGenerator_of_binary σ hdim hsym h hπ hsc hm hc hl

/-- The full kernel comparison may be checked after any fpqc change of base. -/
theorem kernelGenerator_of_isIso_diagonalKernel_baseChange
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of K))
    [Surjective b] [Flat b] [QuasiCompact b]
    [IsIso ((GroupScheme.baseChange b).map
      (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc))]
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      π mu psi := by
  let := isIso_of_baseChange b (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc)
  exact kernelGenerator_of_isIso_diagonalKernel σ hdim hsym h hπ hsc hl

/-- In particular, it suffices to identify the full kernel after one field extension. -/
theorem kernelGenerator_of_isIso_diagonalKernel_fieldExtension
    (L : Type u) [Field L] [Algebra K L]
    [IsIso ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map
        (BinarySpinLift.diagonalKernel σ hdim hsym h hπ hsc))]
    {mu : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
    {psi : CentralSimpleUnits.normOne K D ⟶ S}
    (hl : IsLeviLift h π mu psi) :
    KernelGenerator (FirstKindInvolution.reducedDegree_eq_two_of_finrank_four hdim)
      π mu psi := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc K L
  let := hs
  let := hf
  let := hq
  exact kernelGenerator_of_isIso_diagonalKernel_baseChange σ hdim hsym h hπ hsc
    (Spec.map (CommRingCat.ofHom (algebraMap K L))) hl

end Langlands.GroupScheme.Quaternionic.SpinKernel
