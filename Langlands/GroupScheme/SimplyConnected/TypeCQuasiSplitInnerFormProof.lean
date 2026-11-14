import Langlands.LinearAlgebra.CartanCNumbering
import Langlands.GroupScheme.SimplyConnected.TypeCQuasiSplitInnerFormStatement
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.Reductive.PinnedGeometricBorel
import Langlands.GroupScheme.Adjoint.QuasiSplitProof
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.LinearAlgebra.CorootSpanCartanEquivProof
import Langlands.GroupScheme.SymplecticMatrix.TypeCPinning
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.LinearAlgebra.SimplyConnectedRootDatum

/-! # Simply connected groups of type `C_n` are inner forms of `Sp_{2n}`: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace TypeCQuasiSplitInnerFormProof

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The full star action preserves every actual Cartan entry. -/
theorem cartan_star (d : TitsIndexData G) (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (a b : d.Vertex) : d.cartan (d.star σ a) (d.star σ b) = d.cartan a b :=
  (d.pinning.starAction σ).val.toHom.pairing

/-- **Trivial star action in type `C_n`.** -/
theorem star_eq_self (d : TitsIndexData G) {n : ℕ} (hn : 2 ≤ n) (e : d.Vertex ≃ Fin n)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.C n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) : d.star σ a = a := by
  let f : Fin n → Fin n := fun i => e (d.star σ (e.symm i))
  have hf : ∀ i j, CartanMatrix.C n (f i) (f j) = CartanMatrix.C n i j := by
    intro i j
    rw [← hcart, cartan_star, hcart, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply e.injective
  have h := Langlands.CartanCNumbering.rigid hn f hf (e a)
  simpa [f] using h

end TypeCQuasiSplitInnerFormProof

open TypeCQuasiSplitInnerFormProof in
/-- **Simply connected groups of type `C_n` are inner forms of `Sp_{2n}`.** -/
theorem typeCQuasiSplitInnerForm : TypeCQuasiSplitInnerFormStatement.{u} := by
  intro K _ G _ _ d n eC hn hsc hcart
  obtain ⟨L, _, _, _, _, ι, d', e, hbase, hcomp⟩ := starActionFiniteStage K G d.pinning
  have hscL := isSimplyConnectedFieldExtension K L G hsc
  have hspan' : d'.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan L _ hscL _ d'.isSplitTorus _ d'.isMaximalTorus _ _
      d'.isRootDatum d'.isReduced
  have hstar' : ∀ σ : L ≃ₐ[K] L, d'.starAction σ = 1 := by
    intro σ
    refine InnerTypeANormOneReduction.finiteStage_starAction_eq_one d.pinning d' ι e hbase hcomp
      hspan' ?_ σ
    intro τ a
    exact congrArg Subtype.val (star_eq_self d hn eC hcart τ a)
  obtain ⟨p, hpspan, e1, hp1⟩ := SymplecticMatrix.TypeCPinning.exists_splitPinning n K
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let pL := p.baseChange (F := L)
  have hpLspan : pL.rootDatum.corootSpan ℤ = ⊤ :=
    LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv
      (p.baseChangeRootDatumEquiv (F := L)) hpspan
  let e2 : pL.base.support ≃ d'.toSplitPinning.base.support :=
    (p.baseChangeSimpleEquiv (F := L)).symm.trans
      (e1.trans (eC.symm.trans (Equiv.subtypeEquiv e.indexEquiv hbase).symm))
  have he2 : ∀ i : pL.base.support,
      e.indexEquiv (e2 i).val = (eC.symm (e1 ((p.baseChangeSimpleEquiv (F := L)).symm i))).val :=
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
  obtain ⟨f, hf⟩ := Langlands.LinearAlgebra.corootSpanCartanEquiv _ _ _ _ _ _ pL.rootDatum
    d'.toSplitPinning.rootDatum pL.base d'.toSplitPinning.base hpLspan hspan' e2 hpair
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
  refine ⟨QuasiSplitInnerForm.ofInnerDiscrepancy hs q hq hAq L
    (LocalGroupIso.ofBaseChangeIso E.groupIso) ?_, ⟨SymplecticMatrix.comparisonIso K n⟩⟩
  intro T
  exact TrivialStarInnerTwist.hasInnerDiscrepancy p d' E hstar' hq

end Langlands.GroupScheme
