import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneProof
import Langlands.GroupScheme.CentralSimpleNormOneDivisionModel
import Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankProof
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Actual division norm-one models for anisotropic inner type A

The simply connected inner-type-A presentation route does not need a separate
absolute almost-simplicity hypothesis. Anisotropy then forces the Wedderburn
matrix size to be one and retains the exact reduced degree.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- An actual norm-one presentation by a finite-dimensional central division
algebra, together with its exact reduced degree. -/
def HasCentralDivisionNormOnePresentation {K : Type u} [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) (degree : ℕ) : Prop :=
  ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
    (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
    Langlands.CentralSimple.reducedDegree K D = degree ∧
      Nonempty (G ≅ CentralSimpleUnits.normOne K D)

open InnerTypeANormOneReduction

/-- The finite-stage pinning route supplies an actual central-simple
norm-one presentation from simply connectedness and actual inner type A. -/
theorem normOnePresentation_of_simplyConnected_innerTypeA
    {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (n : ℕ) (hsc : IsSimplyConnected G)
    (hA : d.HasInnerTypeA n) :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A)
      (_ : FiniteDimensional K A) (_ : Algebra.IsCentral K A) (_ : IsSimpleRing A),
      Langlands.CentralSimple.reducedDegree K A = n + 1 ∧
        Nonempty (G ≅ CentralSimpleUnits.normOne K A) := by
  obtain ⟨-, ⟨eA, hcart⟩, hstarKs⟩ := hA
  obtain ⟨L, _, _, _, _, ι, d', e, hbase, hcomp⟩ := starActionFiniteStage K G d.pinning
  have hscL := isSimplyConnectedFieldExtension K L G hsc
  have hspan' : d'.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan L _ hscL _ d'.isSplitTorus _ d'.isMaximalTorus _ _
      d'.isRootDatum d'.isReduced
  have hstar' : ∀ σ : L ≃ₐ[K] L, d'.starAction σ = 1 := by
    intro σ
    refine finiteStage_starAction_eq_one d.pinning d' ι e hbase hcomp hspan' ?_ σ
    intro τ a
    exact congrArg Subtype.val (hstarKs τ a)
  have := SpecialLinear.isAffineHom_groupScheme (Fin (n + 1)) (CommRingCat.of K)
  obtain ⟨p, hpspan, e1, hp1⟩ := specialLinearSimplyConnectedPinning K n
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let pL := p.baseChange (F := L)
  have hpLspan : pL.rootDatum.corootSpan ℤ = ⊤ :=
    Langlands.LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv
      (p.baseChangeRootDatumEquiv (F := L)) hpspan
  let e2 : pL.base.support ≃ d'.toSplitPinning.base.support :=
    (p.baseChangeSimpleEquiv (F := L)).symm.trans
      (e1.trans (eA.symm.trans (Equiv.subtypeEquiv e.indexEquiv hbase).symm))
  have he2 : ∀ i : pL.base.support,
      e.indexEquiv (e2 i).val = (eA.symm (e1 ((p.baseChangeSimpleEquiv (F := L)).symm i))).val :=
    fun i => congrArg Subtype.val ((Equiv.subtypeEquiv e.indexEquiv hbase).apply_symm_apply _)
  have hpair : ∀ i j : pL.base.support,
      d'.toSplitPinning.rootDatum.pairing (e2 i) (e2 j) = pL.rootDatum.pairing i j := by
    intro i j
    rw [← RootPairing.Hom.pairing e.toHom, he2, he2]
    change d.cartan _ _ = _
    rw [hcart, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← hp1]
    exact (RootPairing.Hom.pairing (p.baseChangeRootDatumEquiv (F := L)).toHom).symm
  have : pL.rootDatum.IsReduced := pL.isReduced
  have : d'.toSplitPinning.rootDatum.IsReduced := d'.isReduced
  obtain ⟨f, hf⟩ := Langlands.LinearAlgebra.corootSpanCartanEquiv _ _ _ _ _ _ pL.rootDatum d'.toSplitPinning.rootDatum pL.base
    d'.toSplitPinning.base hpLspan hspan' e2 hpair
  have hiff : ∀ a, a ∈ pL.base.support ↔ f.indexEquiv a ∈ d'.toSplitPinning.base.support := by
    intro a
    constructor
    · intro ha
      rw [hf ⟨a, ha⟩]
      exact (e2 ⟨a, ha⟩).property
    · intro ha
      have h := hf (e2.symm ⟨_, ha⟩)
      rw [Equiv.apply_symm_apply] at h
      have := f.indexEquiv.injective h
      rw [← this]
      exact (e2.symm ⟨_, ha⟩).property
  obtain ⟨E, -⟩ := pinnedIsomorphism L _ _ pL d'.toSplitPinning f hiff
  obtain ⟨A, q, hq⟩ := adjointQuotientExistence K _ p.isConnectedReductive
  have hs := p.isQuasiSplit
  have hAq := adjointQuotientQuasiSplitStatement K _ A q hq hs
  refine specialLinearInnerFormNormOne K G n (QuasiSplitInnerForm.ofInnerDiscrepancy hs q hq hAq L
    (LocalGroupIso.ofBaseChangeIso E.groupIso) ?_) ⟨Iso.refl _⟩
  intro T
  exact TrivialStarInnerTwist.hasInnerDiscrepancy p d' E hstar' hq


namespace CentralSimpleUnits

/-- Split rank zero forces an actual central-simple algebra to be a
central division algebra up to algebra isomorphism. -/
theorem exists_division_algEquiv_of_splitRank_zero
    (K A : Type u) [Field K] [Ring A] [Algebra K A]
    [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    (hA : splitRank (normOne K A) = 0) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (A ≃ₐ[K] D) := by
  obtain ⟨m, hm, D, hD, hKD, hfd, hcentral, e, ⟨f⟩⟩ := exists_matrix_division_model K A
  have h : ((m - 1 : ℕ) : ℕ∞) = 0 :=
    (matrixNormOneSplitRank K D m).symm.trans ((splitRank_eq_of_iso f).symm.trans hA)
  have hm' : m - 1 = 0 := ENat.natCast_inj.mp h
  have hm0 : m ≠ 0 := NeZero.ne m
  have hm1 : m = 1 := by omega
  subst m
  let e1 : Matrix (Fin 1) (Fin 1) D ≃ₐ[K] D :=
    { toFun := fun x => x 0 0
      invFun := fun x => Matrix.of fun _ _ => x
      left_inv := by
        intro x
        ext i j
        simp only [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.of_apply]
      right_inv := fun _ => rfl
      map_mul' := by intro x y; simp [Matrix.mul_apply]
      map_add' := fun _ _ => rfl
      commutes' := by intro c; rfl }
  exact ⟨D, hD, hKD, hfd, hcentral, ⟨e.trans e1⟩⟩

end CentralSimpleUnits

/-- A simply connected anisotropic group with actual inner Cartan type A_n
has an actual central division norm-one model of reduced degree n + 1. -/
theorem centralDivisionNormOnePresentation_of_anisotropic_innerTypeA
    {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (n : ℕ) (hsc : IsSimplyConnected G)
    (han : IsAnisotropic G) (hA : d.HasInnerTypeA n) :
    HasCentralDivisionNormOnePresentation G (n + 1) := by
  obtain ⟨A, hRing, hAlg, hfd, hcentral, hsimple, hdegree, ⟨e⟩⟩ :=
    normOnePresentation_of_simplyConnected_innerTypeA d n hsc hA
  have hA0 : splitRank (CentralSimpleUnits.normOne K A) = 0 :=
    (splitRank_eq_of_iso e).symm.trans han
  obtain ⟨D, hD, hKD, hfdD, hcentralD, ⟨f⟩⟩ :=
    CentralSimpleUnits.exists_division_algEquiv_of_splitRank_zero K A hA0
  exact ⟨D, hD, hKD, hfdD, hcentralD,
    (Langlands.CentralSimple.reducedDegree_algEquiv f).symm.trans hdegree,
    ⟨e.trans (CentralSimpleUnits.normOneAlgEquivIso f)⟩⟩

end Langlands.GroupScheme
