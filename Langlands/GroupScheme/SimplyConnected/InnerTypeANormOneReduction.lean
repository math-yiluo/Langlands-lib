import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneStatement
import Langlands.GroupScheme.SimplyConnected.SpecialLinearInnerFormNormOneStatement
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.Reductive.StarActionFiniteStageStatement
import Langlands.GroupScheme.Reductive.SpecialLinearPinningStatement
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.Reductive.PinnedGeometricBorel
import Langlands.GroupScheme.Adjoint.QuasiSplitProof
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.LinearAlgebra.CorootSpanCartanEquivStatement
import Langlands.LinearAlgebra.RootDatumSimpleCorootEquiv
import Langlands.LinearAlgebra.SimplyConnectedRootDatum

/-! # Reduction of reduced-norm-one presentations of inner type A to four inputs -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace InnerTypeANormOneReduction

section RootData

variable {ι ι₂ M N M₂ N₂ : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M₂]
  [AddCommGroup N₂]

/-- A root-datum automorphism fixing every simple index of a base is trivial when the coroots
span the coweight lattice. -/
theorem aut_eq_one_of_simple {P : RootDatum ι M N} (b : P.Base) (hP : P.corootSpan ℤ = ⊤)
    (f : P.Aut) (hf : ∀ i : b.support, f.indexEquiv i = i) : f = 1 := by
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  intro x
  rw [map_one]
  apply Langlands.RootDatumSimpleCorootEquiv.eq_of_pairing_simpleCoroot b hP
  intro j
  have h1 := LinearMap.congr_fun
    (RootPairing.Hom.weight_coweight_transpose_apply P P (P.coroot j) f.toHom) x
  have h2 : f.coweightMap (P.coroot j) = P.coroot j := by
    rw [RootPairing.Hom.coroot_coweightMap_apply]
    congr 1
    rw [Equiv.symm_apply_eq]
    exact (hf j).symm
  rw [h2] at h1
  change P.toLinearMap (f.toHom.weightMap x) (P.coroot j) = P.toLinearMap x (P.coroot j)
  simpa using h1

end RootData

local instance innerTypeABaseChangeAffine (k E : Type u) [Field k] [Field E] [Algebra k E]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- The star action over the finite stage is trivial when the absolute star action fixes every
simple vertex. -/
theorem finiteStage_starAction_eq_one {K L : Type u} [Field K] [Field L] [Algebra K L]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (d : GaloisPinningData K (SeparableClosure K) G) (d' : GaloisPinningData K L G)
    (ι : L →ₐ[K] SeparableClosure K)
    (e : RootPairing.Equiv d'.toSplitPinning.rootDatum d.toSplitPinning.rootDatum)
    (hbase : ∀ a, a ∈ d'.toSplitPinning.base.support ↔
      e.indexEquiv a ∈ d.toSplitPinning.base.support)
    (hcomp : ∀ (σ : L ≃ₐ[K] L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
      (∀ x, τ (ι x) = ι (σ x)) →
        RootPairing.Equiv.comp e (d'.starAction σ).val =
          RootPairing.Equiv.comp (d.starAction τ).val e)
    (hspan : d'.toSplitPinning.rootDatum.corootSpan ℤ = ⊤)
    (hstar : ∀ (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.toSplitPinning.base.support),
      (d.starAction τ).val.indexEquiv a = a)
    (σ : L ≃ₐ[K] L) : d'.starAction σ = 1 := by
  let : Algebra L (SeparableClosure K) := ι.toRingHom.toAlgebra
  have : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (ι.commutes x).symm)
  let τ : SeparableClosure K ≃ₐ[K] SeparableClosure K := σ.liftNormal (SeparableClosure K)
  have hτ : ∀ x, τ (ι x) = ι (σ x) := fun x => σ.liftNormal_commutes (SeparableClosure K) x
  have hc := hcomp σ τ hτ
  apply Subtype.ext
  apply aut_eq_one_of_simple d'.toSplitPinning.base hspan
  intro i
  have h3 : e.indexEquiv ((d'.starAction σ).val.indexEquiv i) =
      (d.starAction τ).val.indexEquiv (e.indexEquiv i) :=
    congrArg (fun f => f.indexEquiv i.val) hc
  rw [hstar τ ⟨e.indexEquiv i, (hbase i).mp i.property⟩] at h3
  exact e.indexEquiv.injective h3

/-- The reduction: the four inputs imply reduced-norm-one presentations of simply connected
groups of inner type `A`. -/
theorem innerTypeANormOne_of_inputs
    (h1 : SpecialLinearSimplyConnectedPinningStatement.{u})
    (h2 : Langlands.LinearAlgebra.CorootSpanCartanEquivStatement.{u})
    (h4 : SpecialLinearInnerFormNormOneStatement.{u})
    (h5 : StarActionFiniteStageStatement.{u}) : InnerTypeANormOneStatement.{u} := by
  intro K _ G _ _ d n hsc _ hA
  obtain ⟨-, ⟨eA, hcart⟩, hstarKs⟩ := hA
  obtain ⟨L, _, _, _, _, ι, d', e, hbase, hcomp⟩ := h5 K G d.pinning
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
  obtain ⟨p, hpspan, e1, hp1⟩ := h1 K n
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
  obtain ⟨f, hf⟩ := h2 _ _ _ _ _ _ pL.rootDatum d'.toSplitPinning.rootDatum pL.base
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
  refine h4 K G n (QuasiSplitInnerForm.ofInnerDiscrepancy hs q hq hAq L
    (LocalGroupIso.ofBaseChangeIso E.groupIso) ?_) ⟨Iso.refl _⟩
  intro T
  exact TrivialStarInnerTwist.hasInnerDiscrepancy p d' E hstar' hq

end InnerTypeANormOneReduction

end Langlands.GroupScheme
