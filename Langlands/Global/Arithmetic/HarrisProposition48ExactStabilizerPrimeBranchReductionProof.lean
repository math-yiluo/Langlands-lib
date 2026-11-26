import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerPrimeBranchReductionStatement
import Langlands.Global.Arithmetic.CyclicNormKernelCharacterProof
import Langlands.Global.Arithmetic.HarrisProposition48StabilizerComparison
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Langlands.Automorphic.Unramified.CyclicTransferInputsTCStatement

/-!
# Proof of the reduction of the exact-stabilizer prime branch of Proposition 4.8

Proves `Proposition48ExactStabilizerPrimeBranchReductionStatement`, following the
prime-orbit argument of Harris (1998), Proposition 4.8 (printed p.203): from the
child of the trivial double coset, its constituent over the step field `D` is
induced to `E` by Arthur–Clozel (B2), its Galois conjugates are kept apart by
`HasDistinctMackeyComponents`, the induced class is supercuspidal at the
auxiliary place by B4, and restricted B7(2) gives its complex-place parameters.
The common argument `proposition48ExactStabilizerPrimeBranch_of_inputs` uses only
the totally complex forms of B2 and B4; the totally complex reduction is proved
from it in `HarrisProposition48ExactStabilizerPrimeBranchReductionTCProof`.
-/

noncomputable section

universe uF uV

set_option autoImplicit false

namespace Langlands.Global.Harris

open NumberField IsDedekindDomain Langlands.Automorphic Langlands.Automorphic.Unramified
open AdelicFunctoriality Langlands.LocalFactor.Archimedean LocalFactor.CommonClosure
open CuspidalOperatorRealization (IsoClass)

/-- Pulling a finite place back along `e.symm` and then along `e` returns it. -/
private theorem finitePlaceEquiv_apply_symm_apply {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (v : FinitePlace K) : finitePlaceEquiv e (finitePlaceEquiv e.symm v) = v := by
  change ((finitePlaceEquiv e.symm).trans (finitePlaceEquiv e)) v = v
  rw [← finitePlaceEquiv_trans, e.self_trans_symm, finitePlaceEquiv_refl, Equiv.refl_apply]

/-- The prime-orbit argument common to both reductions. Besides interfaces 1–6 and
8–12, restricted B7 and the bridge, it takes the totally complex forms of B2 and
B4 (applied only over the CM field `Q.E`) and the conclusion of the conjugate
self-duality input after its rigidity premise has been discharged (`hcsd`). -/
theorem proposition48ExactStabilizerPrimeBranch_of_inputs
    (h1 : Proposition48MackeyFibreStatement.{uF})
    (h2 : Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV})
    (h3 : Proposition48MackeyChildTransportStatement.{uF, uV})
    (h4 : Proposition48PrimeInducedParameterStagesStatement.{uF})
    (h5 : Proposition48PrimeInductionStagesStatement.{uF, uV})
    (h6 : Proposition48InducedParameterRegularAlgebraicStatement.{uF})
    (h8 : ArithmeticComapUnitaryCentralCharacterStatement.{0, 0})
    (h9 : ArithmeticComapSupercuspidalComponentStatement.{0, 0, uV})
    (h10 : ConjugateSelfDualUnitaryCentralCharacterStatement.{0})
    (h11 : ConjugateSelfDualSupercuspidalConjPlaceStatement.{0, uV})
    (h12 : SplitPlaceNeConjPlaceStatement.{0})
    (hcsd : ∀ (E : Type) (E' : Type) [Field E] [NumberField E] [IsCMField E]
      [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E']
      [CompactSpace (AdeleQuotient E)] (ξ : HeckeCharacter E') (r : ℕ)
      (c : IsoClass E r),
      IsConjugateInverse ξ → c.IsWeakAutomorphicInductionOf.{0, 0, uV} ξ →
        c.IsConjugateSelfDual)
    (hB2 : CyclicRegularInductionTCStatement.{0, 0, uV, uV})
    (hB4 : CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV})
    (hB7 : RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV})
    (hBridge : CuspidalComplexParameterBridgeTCStatement.{0})
    (Q : Proposition48Problem.{uF}) (D : IntermediateField Q.E Q.L)
    (hQ : Q.IsAuxiliaryExactStabilizerValid) (hstep : Q.IsPrimeCyclicStep D)
    (hcard : Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D)
    (hdist : Q.HasDistinctMackeyComponents.{uF, uV} D)
    (hchild : ∀ a : Q.L ≃ₐ[Q.E] Q.L,
        ∃ (R : Proposition48Problem.{uF}) (ν : HeckeCharacter R.E)
          (χs : FieldCharacter R.F R.F') (r : ℕ)
          (S T : CuspidalOperatorRealization R.E r),
          Q.IsAuxiliaryMackeyChild D a R ∧
          R.IsAuxiliaryExactStabilizerValidAtParity (Module.finrank Q.E Q.E' - 1) ∧
          Module.finrank R.E R.E' = Q.mackeyRank D a ∧
          R.inductionDegree < Q.inductionDegree ∧
          R.IsAuxiliaryParityNormalization (Module.finrank Q.E Q.E' - 1) ν χs ∧
          R.IsUntwistedSolution.{uF, uV} ν S T ∧
          R.HasInducedComplexPlaceParameters S.isoClass) :
    Q.HasParameterSolution.{uF, uV} := by
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  obtain ⟨_, hsplit, _, hnormal, hpv, _, hunique, hconjunique, _, halg, hreg, hinv, _⟩ := hQ
  obtain ⟨hgal, hcyc, hprime⟩ := hstep
  let : IsGalois Q.E D := hgal
  let : IsCyclic (D ≃ₐ[Q.E] D) := hcyc
  let : IsNormalClosure Q.E Q.E' Q.L := hnormal
  let : Normal Q.E Q.L := IsNormalClosure.normal (K := Q.E')
  -- Step 1: the double cosets are the fibres of restriction to `D`, and `D ⊆ E'`.
  obtain ⟨hDle, hfib⟩ := h1 Q D hnormal ⟨hgal, hcyc, hprime⟩ hcard
  -- Step 2: the child of the trivial double coset.
  obtain ⟨R, ν, χs, r, S, T, hR, -, -, -, -, hsol, hpar⟩ := hchild 1
  obtain ⟨e, e', j, -, he, -, -, hξ, -, hPs⟩ :
      ∃ (e : R.E ≃+* D) (e' : R.E' ≃+* Q.mackeyField D 1) (j : R.L →+* Q.L),
        R.p = Q.p ∧
        (∀ x : R.E, (e' (algebraMap R.E R.E' x) : Q.L) = (e x : Q.L)) ∧
        (∀ x : R.E', j (algebraMap R.E' R.L x) = (e' x : Q.L)) ∧
        Set.range (fun x : R.K₀ ↦ ((e (x : R.E) : D) : Q.L)) =
          Set.range (fun x : Q.K₀ ↦ algebraMap Q.E Q.L (x : Q.E)) ∧
        R.ξ = (Q.mackeyCharacter D 1).comp
          (ContinuousMonoidHom.toContinuousMonoidHom (ideleClassEquiv e')) ∧
        (finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal ∧
        (finitePlaceEquiv e.symm R.Ps.v).asIdeal.LiesOver Q.Ps.v.asIdeal := hR
  obtain ⟨hSind, hScsd, hSsc, -⟩ := hsol
  -- Step 3: the constituent `T₀` over `D`.
  let T₀ : CuspidalOperatorRealization D r := S.arithmeticComap e.symm
  obtain ⟨h3a, h3b⟩ := h3 Q D 1 R e e' he hξ r S
  have hT₀mc : Q.IsMackeyConstituent.{uF, uV} D 1 T₀.isoClass := h3a hSind
  have hT₀u := h8 D R.E e.symm r S (h10 R.E r S hScsd)
  have hT₀sc : T₀.isoClass.HasSupercuspidalComponent.{0, uV}
      (finitePlaceEquiv e.symm R.Ps.v) := h9 D R.E e.symm r S.isoClass R.Ps.v hSsc
  have : Subsingleton (FinitePlacesAbove D Q.Ps.v) :=
    finitePlacesAbove_subsingleton (L := Q.L) Q.Ps.v hunique
  have : Subsingleton (FinitePlacesAbove D (conjPlace Q.E Q.Ps.v)) :=
    finitePlacesAbove_subsingleton (L := Q.L) _ hconjunique
  let w₀ : FinitePlacesAbove D Q.Ps.v := ⟨finitePlaceEquiv e.symm R.Ps.v, hPs⟩
  let : Algebra Q.E R.E := (e.symm.toRingHom.comp (algebraMap Q.E D)).toAlgebra
  have hRv : R.Ps.v.asIdeal.LiesOver Q.Ps.v.asIdeal := by
    have h := finitePlaceEquiv_liesOver (K := Q.E) (L := R.E) (K' := Q.E) (L' := D)
      (RingEquiv.refl Q.E) e (fun x => e.apply_symm_apply (algebraMap Q.E D x))
      Q.Ps.v (finitePlaceEquiv e.symm R.Ps.v) (hw := hPs)
    rwa [finitePlaceEquiv_apply_symm_apply, finitePlaceEquiv_refl, Equiv.refl_apply] at h
  have hRc : (conjPlace R.E R.Ps.v).asIdeal.LiesOver (conjPlace Q.E Q.Ps.v).asIdeal :=
    HarrisDatum.conjPlace_liesOver (E := Q.E) (E' := R.E) Q.Ps.v R.Ps.v
  have hwc : (finitePlaceEquiv e.symm (conjPlace R.E R.Ps.v)).asIdeal.LiesOver
      (conjPlace Q.E Q.Ps.v).asIdeal := by
    have h := finitePlaceEquiv_liesOver (K := Q.E) (L := D) (K' := Q.E) (L' := R.E)
      (RingEquiv.refl Q.E) e.symm (fun x => rfl) (conjPlace Q.E Q.Ps.v)
      (conjPlace R.E R.Ps.v) (hw := hRc)
    rwa [finitePlaceEquiv_refl, Equiv.refl_apply] at h
  let wc : FinitePlacesAbove D (conjPlace Q.E Q.Ps.v) := ⟨_, hwc⟩
  have hT₀scc : T₀.isoClass.HasSupercuspidalComponent.{0, uV} wc.1 :=
    h9 D R.E e.symm r S.isoClass _ (h11 R.E r S.isoClass R.Ps.v hScsd hSsc)
  -- Step 4: `T₀` is stable under no nontrivial element of `Gal(D/E)`.
  have hlift : ∀ σ' : D ≃ₐ[Q.E] D, ∃ τ : Q.L ≃ₐ[Q.E] Q.L,
      ∀ x : D, ((σ' x : D) : Q.L) = τ x :=
    fun σ' => ⟨σ'.liftNormal Q.L, fun x => (σ'.liftNormal_commutes Q.L x).symm⟩
  have hcoset : ∀ (σ' : D ≃ₐ[Q.E] D) (τ : Q.L ≃ₐ[Q.E] Q.L), σ' ≠ 1 →
      (∀ x : D, ((σ' x : D) : Q.L) = τ x) →
      DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup 1 ≠
        DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup (τ * 1) := by
    intro σ' τ hσ' hτ heq
    apply hσ'
    have hagree := (hfib 1 (τ * 1)).mp heq
    refine AlgEquiv.ext fun x => Subtype.ext ?_
    rw [hτ x]
    have hx := hagree x x.2
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply] at hx
    exact hx.symm
  obtain ⟨P, hP⟩ := (IsoClass.hasSupercuspidalComponent_iff T₀ _).mp hT₀sc
  have hns : ∀ σ' : D ≃ₐ[Q.E] D, σ' ≠ 1 → ¬ T₀.isoClass.IsGaloisStable σ' := by
    intro σ' hσ' hst
    obtain ⟨τ, hτ⟩ := hlift σ'
    have hmc := h2 Q D 1 τ σ' hτ r T₀.isoClass hT₀mc
    rw [(IsoClass.isGaloisStable_iff σ' _).mp hst] at hmc
    exact hdist 1 (τ * 1) (hcoset σ' τ hσ' hτ) r T₀ T₀ hT₀u hT₀u hT₀mc hmc w₀ P P rfl
  -- Step 5: the class `Π` over `E` (B2).
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := D ≃ₐ[Q.E] D)
  have horder : orderOf σ = Module.finrank Q.E D := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hpow : ∀ i : ℕ, 0 < i → i < Module.finrank Q.E D → σ ^ i ≠ 1 :=
    fun i hi hil => pow_ne_one_of_lt_orderOf hi.ne' (horder ▸ hil)
  obtain ⟨η, hη⟩ := (HeckeCharacter.cyclicNormKernelCharacter.{0, 0} Q.E D).1
  obtain ⟨r', cPi, -, hind, -, -⟩ :=
    hB2 Q.E D σ hσ η hη r T₀ hT₀u fun i hi hil => hns _ (hpow i hi hil)
  obtain ⟨SPi, rfl⟩ := cPi.exists_representative
  -- Step 6: weak induction of `ξ`.
  have hPiind := h5 Q D hDle r' r SPi.isoClass T₀.isoClass hind hT₀mc
  -- Step 7: conjugate self-duality.
  have hPicsd := hcsd Q.E Q.E' Q.ξ r' SPi.isoClass hinv hPiind
  -- Step 8: supercuspidal at `Ps.v` (B4).
  have hPisc : SPi.isoClass.HasSupercuspidalComponent.{0, uV} Q.Ps.v := by
    refine hB4 Q.E D hprime σ hσ Q.Ps.v w₀ (fun _ => Subsingleton.elim _ _) r' r SPi T₀ P
      hT₀u hP (fun i hi hil => ?_) hind
    let g : D ≃+* D := (σ ^ i).toRingEquiv.symm
    let U : CuspidalOperatorRealization D r := T₀.arithmeticComap g
    have hUu := h8 D D g r T₀ hT₀u
    have hUsc := h9 D D g r T₀.isoClass w₀.1 hT₀sc
    have hgw : finitePlaceEquiv g w₀.1 = w₀.1 := by
      have hlo : (finitePlaceEquiv g w₀.1).asIdeal.LiesOver Q.Ps.v.asIdeal := by
        have h := finitePlaceEquiv_liesOver (K := Q.E) (L := D) (K' := Q.E) (L' := D)
          (RingEquiv.refl Q.E) g (fun x => (σ ^ i).symm.commutes x) Q.Ps.v w₀.1 (hw := hPs)
        rwa [finitePlaceEquiv_refl, Equiv.refl_apply] at h
      exact congrArg Subtype.val
        (Subsingleton.elim (⟨_, hlo⟩ : FinitePlacesAbove D Q.Ps.v) w₀)
    rw [hgw] at hUsc
    obtain ⟨PU, hPU⟩ := (IsoClass.hasSupercuspidalComponent_iff U _).mp hUsc
    obtain ⟨τ, hτ⟩ := hlift (σ ^ i)
    have hUmc : Q.IsMackeyConstituent.{uF, uV} D (τ * 1) U.isoClass :=
      h2 Q D 1 τ (σ ^ i) hτ r T₀.isoClass hT₀mc
    refine ⟨U, PU, IsoClass.isGaloisConjugate_galoisConj (σ ^ i) T₀.isoClass, hPU, ?_⟩
    exact hdist (τ * 1) 1 (hcoset (σ ^ i) τ (hpow i hi hil) hτ).symm r U T₀ hUu hT₀u
      hUmc hT₀mc w₀ PU P
  -- Step 9: the auxiliary conjugate pair.
  have hPiu := h10 Q.E r' SPi hPicsd
  have hPiscc := h11 Q.E r' SPi.isoClass Q.Ps.v hPicsd hPisc
  have hne := h12 Q.p Q.E Q.K₀ Q.Ps.v hsplit hpv
  -- Step 10: parameters (restricted B7(2)).
  have hB7' := (hB7 Q.E D hprime Q.Ps.v hne w₀ wc (fun _ => Subsingleton.elim _ _)
    (fun _ => Subsingleton.elim _ _)).2 r' r SPi T₀ hPiu hT₀u hPisc hPiscc hT₀sc hT₀scc hns hind
  have hpars : Q.HasInducedComplexPlaceParameters SPi.isoClass := by
    intro v
    choose dsf hdsf hdsf' using h3b hpar
    let en := (Fintype.equivFin (InfinitePlacesAbove D v.1)).symm
    let ds : InfinitePlacesAbove D v.1 → List ComplexCharacterData :=
      fun w => dsf (complexPlaceAbove v w)
    exact ⟨complexPlaceLanglandsSum v en ds, hB7' v _ en ds fun w => hdsf _,
      h4 Q D hDle v _ en ds fun w => hdsf' _⟩
  -- Step 11: regular algebraicity.
  have hPireg := h6 hBridge Q halg hreg hinv r' SPi.isoClass hpars
  exact ⟨r', SPi.isoClass, ⟨hPiind, hPireg, hPicsd, hPisc⟩, hpars⟩

/-- The exact target `Proposition48ExactStabilizerPrimeBranchReductionStatement`:
the twelve named interfaces imply the exact-stabilizer prime branch. The general
forms of B2 and B4 give their totally complex forms by forgetting the instance
`[NumberField.IsTotallyComplex F]`; Theorem 1.2, isobaric invariance and B3 are
not used. -/
theorem proposition48ExactStabilizerPrimeBranchReduction :
    Proposition48ExactStabilizerPrimeBranchReductionStatement.{uF, uV} := by
  intro h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 _ hRig _ hB2 _ hB4 hB7 hBridge
  exact proposition48ExactStabilizerPrimeBranch_of_inputs h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12
    (h7 hRig) (fun F E _ _ _ _ _ _ _ _ _ => hB2 F E) (fun F E _ _ _ _ _ _ _ _ _ => hB4 F E)
    hB7 hBridge

end Langlands.Global.Harris
