import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyPresentationStatement
import Langlands.GroupScheme.Composition.SplitCayleyAutomorphismPinningStatement
import Langlands.GroupScheme.SimplyConnected.TypeG2CayleyDescent
import Langlands.GroupScheme.SimplyConnected.TrivialStarInnerTwist
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.Reductive.StarActionFiniteStageProof
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof
import Langlands.GroupScheme.Reductive.PinnedGeometricBorel
import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.LinearAlgebra.CorootSpanCartanEquivProof
import Langlands.GroupScheme.SimplyConnected.InnerTypeANormOneReduction
import Langlands.LinearAlgebra.SimplyConnectedRootDatum
import Langlands.GroupScheme.Adjoint.CompactNormalizer
import Langlands.GroupScheme.Adjoint.Assembly

/-! # Type-`G₂` Cayley presentations from the pinned split Cayley automorphism group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace TypeG2CayleyPresentationReduction

open Langlands.AlgebraicGeometry.PointTopology

/-- The Cartan matrix of type `G₂` admits no nontrivial renumbering of its two vertices. -/
theorem cartanG2_rigid (f : Fin 2 → Fin 2)
    (hf : ∀ i j, CartanMatrix.G₂ (f i) (f j) = CartanMatrix.G₂ i j) (i : Fin 2) : f i = i := by
  have key : f 0 = 0 ∧ f 1 = 1 := by
    have h := hf 0 1
    generalize f 0 = a at h ⊢
    generalize f 1 = b at h ⊢
    fin_cases a <;> fin_cases b <;> simp [CartanMatrix.G₂] at h ⊢
  fin_cases i
  · exact key.1
  · exact key.2

/-- Precomposing an automorphism representation with a group-scheme isomorphism gives an
automorphism representation. -/
theorem isAutomorphismRepresentation_iso_comp {K : Type u} [Field K] (c : CayleyDatum K)
    {H H' : GroupScheme (Spec (CommRingCat.of K))} (φ : H' ≅ H)
    {i : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)}
    (hi : c.IsAutomorphismRepresentation i) : c.IsAutomorphismRepresentation (φ.hom ≫ i) := by
  refine ⟨?_, fun T g => ?_⟩
  · have : IsClosedImmersion i.hom.hom.left := hi.1
    let φ' : H'.X ≅ H.X :=
      { hom := φ.hom.hom.hom
        inv := φ.inv.hom.hom
        hom_inv_id := by rw [← Grp.comp_hom_hom, φ.hom_inv_id, Grp.id_hom_hom]
        inv_hom_id := by rw [← Grp.comp_hom_hom, φ.inv_hom_id, Grp.id_hom_hom] }
    have : IsIso φ.hom.hom.hom.left :=
      (inferInstance : IsIso ((Over.forget _).mapIso φ').hom)
    change IsClosedImmersion (φ.hom ≫ i).hom.hom.left
    rw [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  · rw [SubgroupFunctor.range_iso_comp]
    exact hi.2 T g

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- The full star action preserves every actual Cartan entry. -/
theorem cartan_star (d : TitsIndexData G) (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K)
    (a b : d.Vertex) : d.cartan (d.star σ a) (d.star σ b) = d.cartan a b :=
  (d.pinning.starAction σ).val.toHom.pairing

/-- **Trivial star action in type `G₂`.** -/
theorem star_eq_self (d : TitsIndexData G) (e : d.Vertex ≃ Fin 2)
    (hcart : ∀ a b, d.cartan a b = CartanMatrix.G₂ (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex) : d.star σ a = a := by
  let f : Fin 2 → Fin 2 := fun i => e (d.star σ (e.symm i))
  have hf : ∀ i j, CartanMatrix.G₂ (f i) (f j) = CartanMatrix.G₂ i j := by
    intro i j
    rw [← hcart, cartan_star, hcart, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply e.injective
  have h := cartanG2_rigid f hf (e a)
  simpa [f] using h

end TypeG2CayleyPresentationReduction

open TypeG2CayleyPresentationReduction in
/-- **Reduction of the type-`G₂` Cayley presentation to the split model.** If the
automorphism group scheme of the split Cayley datum is pinned split simply connected of type
`G₂` with trivial centre over every field, then every simply connected group with a
type-`G₂` Tits index is the automorphism group scheme of an actual Cayley datum. -/
theorem typeG2CayleyPresentation_of_splitCayleyAutomorphismPinning
    (hsplit : SplitCayleyAutomorphismPinningStatement.{u}) :
    TypeG2CayleyPresentationStatement.{u} := by
  intro K _ G _ _ d eG hsc _ hcart
  obtain ⟨hc, p, hpspan, e1, hp1⟩ := hsplit K
  obtain ⟨L, _, _, _, _, ι, d', ε, hbase, hcomp⟩ := starActionFiniteStage K G d.pinning
  have hscL := isSimplyConnectedFieldExtension K L G hsc
  have hspan' : d'.toSplitPinning.rootDatum.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan L _ hscL _ d'.isSplitTorus _ d'.isMaximalTorus _ _
      d'.isRootDatum d'.isReduced
  have hstar' : ∀ σ : L ≃ₐ[K] L, d'.starAction σ = 1 := by
    intro σ
    refine InnerTypeANormOneReduction.finiteStage_starAction_eq_one d.pinning d' ι ε hbase
      hcomp hspan' ?_ σ
    intro τ a
    exact congrArg Subtype.val (star_eq_self d eG hcart τ a)
  have : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let pL := p.baseChange (F := L)
  have hpLspan : pL.rootDatum.corootSpan ℤ = ⊤ :=
    LinearAlgebra.SimplyConnectedRootDatum.corootSpan_eq_top_of_equiv
      (p.baseChangeRootDatumEquiv (F := L)) hpspan
  let e2 : pL.base.support ≃ d'.toSplitPinning.base.support :=
    (p.baseChangeSimpleEquiv (F := L)).symm.trans
      (e1.trans (eG.symm.trans (Equiv.subtypeEquiv ε.indexEquiv hbase).symm))
  have he2 : ∀ i : pL.base.support,
      ε.indexEquiv (e2 i).val = (eG.symm (e1 ((p.baseChangeSimpleEquiv (F := L)).symm i))).val :=
    fun i => congrArg Subtype.val ((Equiv.subtypeEquiv ε.indexEquiv hbase).apply_symm_apply _)
  have hpair : ∀ i j : pL.base.support,
      d'.toSplitPinning.rootDatum.pairing (e2 i) (e2 j) = pL.rootDatum.pairing i j := by
    intro i j
    rw [← RootPairing.Hom.pairing ε.toHom, he2, he2]
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
  have hq : IsAdjointQuotient (𝟙 (CayleyDatum.split K).automorphismGroup) :=
    (isAdjoint_of_isConnectedReductive_of_center_eq_bot p.isConnectedReductive hc).identityQuotient
  have he : (LocalGroupIso.ofBaseChangeIso
      (U := Langlands.AlgebraicGeometry.PointTopology.ringTest K L) E.groupIso).HasInnerDiscrepancy
      hq.innerAction := by
    intro T
    exact TrivialStarInnerTwist.hasInnerDiscrepancy p d' E hstar' hq
  obtain ⟨c, ⟨φ⟩⟩ := TypeG2CayleyDescent.exists_iso_automorphismGroup hq _ _
    (LocalGroupIso.innerCocycle_hasDiscrepancy _ hq.innerAction hq.innerAction_isFaithful he)
  exact ⟨c, φ.hom ≫ c.automorphismInclusion,
    isAutomorphismRepresentation_iso_comp c φ c.isAutomorphismRepresentation_automorphismInclusion⟩

end Langlands.GroupScheme
