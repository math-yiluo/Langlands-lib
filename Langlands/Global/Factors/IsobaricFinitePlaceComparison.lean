import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.LocalComponentFinitePlace
import Langlands.Global.Factors.IsobaricAutomorphicRepresentation
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof

/-! # Finite-place comparison for isobaric automorphic subquotients -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

universe u uV uW uP uP'

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.CompactSplitting
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

attribute [local instance] subquotientRationalGroup subquotientContinuousGroup
  subquotientSmoothGroup subquotientFormGroup subquotientStableGroup subquotientRealizationGroup

variable {F : Type u} [Field F] [NumberField F]

namespace OperatorSubquotient

variable {n : ℕ} (Q : OperatorSubquotient F n) (v : FinitePlace F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (FiniteLocalGL F n v) V)

/-- A supplied irreducible local embedding makes the whole restriction isotypic. -/
theorem isFinitePlaceIsotypic_of_injective (hQ : Q.IsIrreducible) (hρ : ρ.IsIrreducible)
    (f : ρ.IntertwiningMap (Q.localRepresentation v)) (hf : Function.Injective f) :
    Q.IsFinitePlaceIsotypic v ρ := by
  have : ρ.IsIrreducible := hρ
  have : Nontrivial ρ.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteLocalGL F n v)) ρ.asModule
  have : Nontrivial V := ρ.asModuleEquiv.symm.toEquiv.nontrivial
  have hne : isotypicPart ρ (Q.localRepresentation v) ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hmem := range_le_isotypicPart ρ (Q.localRepresentation v) f
      (show f x ∈ LinearMap.range f.toLinearMap from ⟨x, rfl⟩)
    rw [hbot, Submodule.mem_bot] at hmem
    exact hx (hf (hmem.trans (map_zero f).symm))
  rcases Q.isJointlyIrreducible_localCentralizerOperators hQ v
      (isotypicPart ρ (Q.localRepresentation v))
      (fun g _ hx => apply_mem_isotypicPart ρ (Q.localRepresentation v) g hx)
      (fun c hc _ hx => intertwiner_mem_isotypicPart ρ
        (JointIsotypic.commutingHom c (Q.commutesWith_localCentralizerOperators v c hc)) hx)
    with hbot | htop
  · exact (hne hbot).elim
  · exact htop

/-- Two irreducible local representations embedded in the same irreducible operator
subquotient are equivalent. -/
theorem nonempty_local_equiv_of_injective (hQ : Q.IsIrreducible)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (FiniteLocalGL F n v) W)
    (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (f : ρ.IntertwiningMap (Q.localRepresentation v)) (hf : Function.Injective f)
    (g : σ.IntertwiningMap (Q.localRepresentation v)) (hg : Function.Injective g) :
    Nonempty (ρ.Equiv σ) := by
  have htop : isotypicPart ρ (Q.localRepresentation v) = ⊤ :=
    Q.isFinitePlaceIsotypic_of_injective v ρ hQ hρ f hf
  have : ρ.IsIrreducible := hρ
  have : σ.IsIrreducible := hσ
  apply nonempty_equiv_of_isotypicPart_eq_top
  rw [← isotypicPart_comap_of_injective ρ σ (Q.localRepresentation v) g hg,
    htop, Submodule.comap_top]

end OperatorSubquotient

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {S T : CuspidalOperatorRealization F r}

/-- At a given rank a full cuspidal equivalence identifies the local components
of any two irreducible spectral presentations. -/
theorem nonempty_localComponent_equiv_of_equivalence
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (P' : CuspidalSpectralPresentation.{u, uP'} T)
    (e : S.Equivalence T) (v : FinitePlace F)
    (hP : (P.localComponent v).IsIrreducible)
    (hP' : (P'.localComponent v).IsIrreducible) :
    Nonempty ((P.localComponent v).representation.Equiv
      (P'.localComponent v).representation) := by
  let ev : (S.realization.localRepresentation v).Equiv (T.realization.localRepresentation v) :=
    Representation.Equiv.mk e.toLinearEquiv
      (fun g => e.toIntertwiningMap.isIntertwining' (finiteOperator F (r + 1)
        (localInclusion F (r + 1) v g)))
  let f := S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v)
  let g := T.realization.localSubspaceInclusion v _ (P'.localComponent_le_full v)
  have : T.realization.IsIrreducible := T.irreducible
  have : (P.localComponent v).representation.IsIrreducible := hP
  have : (P'.localComponent v).representation.IsIrreducible := hP'
  exact T.realization.nonempty_local_equiv_of_injective v _ _ (ev.toIntertwiningMap.comp f)
    (ev.injective.comp (S.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v)))
    g (T.realization.localSubspaceInclusion_injective v _ (P'.localComponent_le_full v))

end CuspidalSpectralPresentation

section IsobaricSums

open CategoryTheory

local instance (v : FinitePlace F) (n : ℕ) :
    TopologicalSpace (GeneralLinear n (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology n

variable [CompactSpace (AdeleQuotient F)]

private theorem inducing_multisegment_eq {r r' : ℕ}
    (S : CuspidalOperatorRealization F r) (S' : CuspidalOperatorRealization F r')
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (P' : CuspidalSpectralPresentation.{u, uP'} S')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (hc : (⟨r, S.isoClass⟩ : PositiveRankCuspidalClass F) = ⟨r', S'.isoClass⟩)
    (v : FinitePlace F)
    (a a' : (padicField v).canonicalTopologicalData.Multisegment.{u, u})
    (ha : a.IsLanglandsHead ((P.localComponent v).padicObject (h v).1 (h v).2).obj)
    (ha' : a'.IsLanglandsHead ((P'.localComponent v).padicObject (h' v).1 (h' v).2).obj) :
    a = a' := by
  have hr : r = r' := congrArg PositiveRankCuspidalClass.rankIndex hc
  subst r'
  obtain ⟨e⟩ := (PositiveRankCuspidalClass.ofFixedRank_isoClass_eq_iff S S').mp hc
  obtain ⟨ev⟩ := P.nonempty_localComponent_equiv_of_equivalence P' e v (h v).1 (h' v).1
  exact (Classification.multisegmentHeadClassification.{u, u} (padicField v)
    (padicField v).canonicalTopologicalData _ _ _ _ _ ha ha').mpr ⟨SmoothRep.mkIso ev⟩

/-- A bijection of positive-rank cuspidal classes identifies the local isobaric sums
of any two sets of irreducible admissible spectral presentations. -/
theorem nonempty_finitePlace_isobaricSum_iso {r k k' : ℕ} {m : Fin k → ℕ} {m' : Fin k' → ℕ}
    {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {T' : ∀ j, CuspidalOperatorRealization F (m' j)}
    {P : ∀ i, CuspidalSpectralPresentation.{u, uP} (T i)}
    {P' : ∀ j, CuspidalSpectralPresentation.{u, uP'} (T' j)}
    {h : ∀ i, HasIrreducibleAdmissibleComponents (P i)}
    {h' : ∀ j, HasIrreducibleAdmissibleComponents (P' j)}
    (e : Fin k ≃ Fin k')
    (hc : ∀ i, (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F) =
      ⟨m' (e i), (T' (e i)).isoClass⟩)
    (v : FinitePlace F) {A A' : AutomorphicObject.{u, u} (padicField v) r.succPNat}
    (hA : (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
      (fun i => (((P i).localComponent v).padicObject (h i v).1 (h i v).2).obj) A.obj)
    (hA' : (padicField v).canonicalTopologicalData.IsIsobaricSum.{u, u}
      (fun j => (((P' j).localComponent v).padicObject (h' j v).1 (h' j v).2).obj) A'.obj) :
    Nonempty (A.obj ≅ A'.obj) := by
  obtain ⟨a, ha, hsum⟩ := hA
  obtain ⟨a', ha', hsum'⟩ := hA'
  apply (Classification.multisegmentHeadClassification.{u, u} (padicField v)
    (padicField v).canonicalTopologicalData _ _ _ _ _ hsum hsum').mp
  exact Fintype.sum_equiv e a a' fun i =>
    inducing_multisegment_eq (T i) (T' (e i)) (P i) (P' (e i)) (h i) (h' (e i))
      (hc i) v (a i) (a' (e i)) (ha i) (ha' (e i))

namespace IrreducibleOperatorSubquotient

/-- Matched cuspidal classes give a common finite-place isotypic type for the two
isobaric operator subquotients. -/
theorem exists_common_finitePlace_isotypic_of_isobaricSum {r k k' : ℕ}
    {Q Q' : IrreducibleOperatorSubquotient F r} {m : Fin k → ℕ} {m' : Fin k' → ℕ}
    {T : ∀ i, CuspidalOperatorRealization F (m i)}
    {T' : ∀ j, CuspidalOperatorRealization F (m' j)}
    {P : ∀ i, CuspidalSpectralPresentation.{u, uP} (T i)}
    {P' : ∀ j, CuspidalSpectralPresentation.{u, uP'} (T' j)}
    {h : ∀ i, HasIrreducibleAdmissibleComponents (P i)}
    {h' : ∀ j, HasIrreducibleAdmissibleComponents (P' j)}
    (hQ : Q.IsCuspidalIsobaricSum T P h) (hQ' : Q'.IsCuspidalIsobaricSum T' P' h')
    (e : Fin k ≃ Fin k')
    (hc : ∀ i, (⟨m i, (T i).isoClass⟩ : PositiveRankCuspidalClass F) =
      ⟨m' (e i), (T' (e i)).isoClass⟩)
    (v : FinitePlace F) :
    ∃ A : AutomorphicObject.{u, u} (padicField v) r.succPNat,
      Q.subquotient.IsFinitePlaceIsotypic v A.obj.representation ∧
        Q'.subquotient.IsFinitePlaceIsotypic v A.obj.representation := by
  obtain ⟨A, hA, f, hf⟩ := hQ.1 v
  obtain ⟨A', hA', g, hg⟩ := hQ'.1 v
  obtain ⟨i⟩ := nonempty_finitePlace_isobaricSum_iso (h := h) (h' := h') e hc v hA hA'
  let ev := SmoothRep.equivOfIso i
  exact ⟨A, Q.subquotient.isFinitePlaceIsotypic_of_injective v _ Q.irreducible hA.isIrreducible f hf,
    Q'.subquotient.isFinitePlaceIsotypic_of_injective v _ Q'.irreducible hA.isIrreducible
      (g.comp ev.toIntertwiningMap) (hg.comp ev.injective)⟩

end IrreducibleOperatorSubquotient

end IsobaricSums

end Langlands.Automorphic
