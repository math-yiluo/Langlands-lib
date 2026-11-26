import Langlands.BaseChange.TwistedPaleyWiener
import Langlands.BaseChange.TwistedCharacterSeparation
import Langlands.Representation.Hecke.FiniteSampling
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
import Langlands.Representation.Unitary.CornerFormGluing
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Twisted traces of smooth induction evaluated by common inducing-group tests -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis MeasureTheory Induction
open Hecke (HeckeAlgebra)

universe uG uM uX

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {M : Type uM} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
  [T2Space M] [LocallyCompactSpace M] [TotallyDisconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

/-- For a smooth induction from a compact quotient, a single test of the inducing group
computes the induced twisted trace on every admissible inducing pair. -/
def TwistedInducedTestStatement
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ν : Measure M) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (θ : MulAut G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    (P : Subgroup G) (hP : ∀ g, θ g ∈ P ↔ g ∈ P)
    (p : P →* M) (θM : MulAut M)
    (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x)) : Prop :=
  ∀ f : SchwartzBruhat G, ∃ fM : SchwartzBruhat M,
    ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X]
      (Ξ : Representation ℂ M X) (hΞ : IsAdmissible Ξ)
      (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom))
      (hI : IsAdmissible (smoothInduced P (Ξ.comp p))),
      twistedDistribution μ _ hI
          (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B).toLinearMap f =
        twistedDistribution ν Ξ hΞ B.toLinearMap fM

private theorem twistedDistribution_rightTranslate_indicator
    (ν : Measure M) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (θM : MulAut M) (Ξ : Representation ℂ M X) (hΞ : IsAdmissible Ξ)
    (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom)) (J : OpenSubgroup M) (hJ : IsCompact (J : Set M))
    (m : M) :
    twistedDistribution ν Ξ hΞ B.toLinearMap
        (Hecke.TestFunction.rightTranslate (θM m)⁻¹
          (HeckeAlgebra.toTestFunction ν (HeckeAlgebra.normalizedIndicator ν J hJ))) =
      LinearMap.trace ℂ (fixedVectors Ξ J.toSubgroup)
        ((Hecke.fixedProjection ν Ξ hΞ.1 J hJ).comp
          (B.toLinearMap.comp ((Ξ m).comp (fixedVectors Ξ J.toSubgroup).subtype))) := by
  let e := HeckeAlgebra.toTestFunction ν (HeckeAlgebra.normalizedIndicator ν J hJ)
  let g := Hecke.TestFunction.rightTranslate (θM m)⁻¹ e
  have heval (v : X) :
      Hecke.integratedAction ν Ξ hΞ.1 g (B v) =
        (Hecke.fixedProjection ν Ξ hΞ.1 J hJ (B (Ξ m v)) : X) := by
    calc
      _ = Hecke.integratedAction ν Ξ hΞ.1 e (Ξ (θM m) (B v)) := by
        simpa only [g, inv_inv] using
          Hecke.integratedAction_rightTranslate_of_isMulRightInvariant ν Ξ hΞ.1 (θM m)⁻¹ e (B v)
      _ = _ := congrArg (Hecke.integratedAction ν Ξ hΞ.1 e)
        (LinearMap.congr_fun (B.isIntertwining' m) v).symm
  have hrange : ((Hecke.integratedAction ν Ξ hΞ.1 g).comp B.toLinearMap).range ≤
      fixedVectors Ξ J.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    change Hecke.integratedAction ν Ξ hΞ.1 g (B v) ∈ _
    rw [heval]
    exact (Hecke.fixedProjection ν Ξ hΞ.1 J hJ _).property
  let := hΞ.2 J
  change twistedDistribution ν Ξ hΞ B.toLinearMap g = _
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ _ hrange]
  congr 1
  ext v
  exact heval v.val

set_option maxHeartbeats 1100000 in
/-- The common test is the sum of translated normalized indicators from the diagonal
of the finite double-coset model of the induced action. -/
theorem twistedInducedTest
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ν : Measure M) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (θ : MulAut G) (hθ : Continuous θ) (hθ' : Continuous θ.symm)
    {d : ℕ} (hd : 0 < d) (hθd : θ ^ d = 1)
    (P : Subgroup G) (hcl : IsClosed (P : Set G)) [CompactSpace (LeftQuotient P)]
    (hP : ∀ g, θ g ∈ P ↔ g ∈ P) (p : P →* M) (hpc : Continuous p) (hpo : IsOpenMap p)
    (θM : MulAut M) (hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x)) :
    TwistedInducedTestStatement.{uG,uM,uX} μ ν θ hθ hθ' P hP p θM hp := by
  classical
  intro f
  obtain ⟨K₀, _, hK₀, hf₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  obtain ⟨K, hK, hKK₀, hθK⟩ := exists_invariantCompactOpen_le θ hθ hd hθd K₀ hK₀
  have hf : f ∈ Hecke.TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
    Hecke.TestFunction.biInvariant_antitone hKK₀ hKK₀ (hf₀ f (Finset.mem_singleton_self f))
  obtain ⟨t, hcover, hdistinct⟩ := exists_finset_doubleCoset_representatives P K
  have hfactor := hcover
  choose r hr q hq k hk he using hfactor
  let H (i : t) := conjOpenSubgroup P K i
  let J (i : t) : OpenSubgroup M := ⟨(H i).toSubgroup.map p, hpo _ (H i).isOpen⟩
  have hJ (i : t) : IsCompact (J i : Set M) :=
    (isCompact_conjOpenSubgroup P hcl K hK i).image hpc
  let S := Hecke.fixedLevelActionSamples μ K f hf.2
  let x (i : t) (a : Fin S.size) : G := θ.symm ((i : G) * S.points a)
  let rep (i : t) (a : Fin S.size) : t := ⟨r (x i a), hr _⟩
  let par (i : t) (a : Fin S.size) : P := ⟨q (x i a), hq _⟩
  let m (i : t) (a : Fin S.size) := p (par i a)
  let test (i : t) (a : Fin S.size) : SchwartzBruhat M :=
    Hecke.TestFunction.rightTranslate (θM (m i a))⁻¹
      (HeckeAlgebra.toTestFunction ν (HeckeAlgebra.normalizedIndicator ν (J i) (hJ i)))
  refine ⟨∑ i : t, ∑ a : Fin S.size,
    S.coefficients a • (if rep i a = i then test i a else 0), ?_⟩
  intro X _ _ Ξ hΞ B hI
  let ρ := Ξ.comp p
  let U (i : t) := fixedVectors Ξ (J i).toSubgroup
  let (i : t) : Module.Finite ℂ (U i) := hΞ.2 (J i)
  let e : fixedVectors (smoothInduced P ρ) K.toSubgroup ≃ₗ[ℂ] ((i : t) → U i) :=
    (fixedEvaluationEquiv P ρ K hK t hcover hdistinct).trans
      (LinearEquiv.piCongrRight fun i => LinearEquiv.ofEq _ _ (fixedVectors_comp_eq_map Ξ p (H i)))
  have heval (w : fixedVectors (smoothInduced P ρ) K.toSubgroup) (i : t) :
      (e w i : X) = eval P ρ w.val i := rfl
  let A := inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B
  let Aₖ := fixedVectorsTwistEquiv hθK A
  let T := (Hecke.integratedActionToFixed μ (smoothInduced P ρ) hI.1 hf).comp
    ((fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.comp Aₖ.toLinearMap)
  let project (i : t) := Hecke.fixedProjection ν Ξ hΞ.1 (J i) (hJ i)
  let O (i : t) (a : Fin S.size) : ((j : t) → U j) →ₗ[ℂ] U i :=
    (project i).comp (B.toLinearMap.comp ((Ξ (m i a)).comp
      ((U (rep i a)).subtype.comp (LinearMap.proj (rep i a)))))
  have hrow (v : (j : t) → U j) (i : t) :
      (e.conj T) v i = ∑ a : Fin S.size, S.coefficients a • O i a v := by
    let w := e.symm v
    have hw : A w.val ∈ fixedVectors (smoothInduced P ρ) K.toSubgroup := (Aₖ w).property
    let L := (project i).comp (FiniteProductTensorBijective.evalLinear P ρ (i : G))
    calc
      (e.conj T) v i = L (Hecke.integratedAction μ (smoothInduced P ρ) hI.1 f (A w.val)) := by
        change e (T w) i = project i (eval P ρ (T w).val i)
        rw [← heval]
        exact (Hecke.fixedProjection_fixed ν Ξ hΞ.1 _ _ _).symm
      _ = ∑ a : Fin S.size, S.coefficients a • O i a v := by
        rw [Hecke.fixedLevelActionSamples_action μ K f hf.2 _ hI.1 _ hw, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_smul]
        change S.coefficients a • project i
          (eval P ρ (A w.val) ((i : G) * S.points a)) = _
        rw [eval_inducedTwistedIntertwiner]
        have hpoint : x i a = (par i a : G) * (rep i a : G) *
            (⟨k (x i a), hk (x i a)⟩ : K) := he (x i a)
        change S.coefficients a • project i (B (eval P ρ w.val (x i a))) = _
        rw [hpoint, eval_mul_of_mem_fixedVectors P ρ K.toSubgroup w.property, eval_covariant,
          ← heval, show e w = v from e.apply_symm_apply v]
        rfl
  have hT : e.conj T = ∑ i : t, ∑ a : Fin S.size,
      S.coefficients a • ((LinearMap.single ℂ (fun j : t => U j) i).comp (O i a)) := by
    apply LinearMap.ext
    intro v
    funext i
    rw [hrow]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
      LinearMap.comp_apply, LinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      exact Finset.sum_eq_zero fun a _ => by simp [Pi.single_eq_of_ne hji.symm]
    · exact fun hi => (hi (Finset.mem_univ i)).elim
  have hdiag (i : t) (a : Fin S.size) :
      LinearMap.trace ℂ ((j : t) → U j)
          ((LinearMap.single ℂ (fun j : t => U j) i).comp (O i a)) =
        twistedDistribution ν Ξ hΞ B.toLinearMap (if rep i a = i then test i a else 0) := by
    rw [LinearMap.trace_comp_comm']
    by_cases hi : rep i a = i
    · rw [ite_eq_left hi, twistedDistribution_rightTranslate_indicator]
      congr 1
      apply LinearMap.ext
      intro v
      have hv :
          ((LinearMap.single ℂ (fun j : t => U j) i v) (rep i a) : X) = v.val := by
        rw [hi]
        simp [LinearMap.single_apply]
      simp only [O, project, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.subtype_apply, hv]
    · rw [ite_eq_right hi, map_zero]
      have hop : (O i a).comp (LinearMap.single ℂ (fun j : t => U j) i) = 0 := by
        apply LinearMap.ext
        intro v
        simp [O, Pi.single_eq_of_ne hi]
      rw [hop, map_zero]
  have hrange : ((Hecke.integratedAction μ (smoothInduced P ρ) hI.1 f).comp A.toLinearMap).range
      ≤ fixedVectors (smoothInduced P ρ) K.toSubgroup := by
    rintro _ ⟨v, rfl⟩
    exact Hecke.integratedAction_mem_fixedVectors μ _ hI.1 hf (A v)
  let := hI.2 K
  change twistedDistribution μ _ hI A.toLinearMap f = _
  rw [twistedDistribution_apply, FiniteRankEnd.trace_eq_subspace _ _ hrange]
  change LinearMap.trace ℂ _ T = _
  rw [← LinearMap.trace_conj' T e, hT]
  simp only [map_sum, map_smul, hdiag]

/-- Any finite linear relation between inducing twisted distributions remains a relation
after smooth induction along the given equivariant homomorphism. -/
theorem TwistedInducedTestStatement.exists_traceTransfer
    {μ : Measure G} [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    {ν : Measure M} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {θ : MulAut G} {hθ : Continuous θ} {hθ' : Continuous θ.symm}
    {P : Subgroup G} {hP : ∀ g, θ g ∈ P ↔ g ∈ P}
    {p : P →* M} {θM : MulAut M} {hp : ∀ x : P, p ⟨θ x, (hP x).2 x.2⟩ = θM (p x)}
    (h : TwistedInducedTestStatement.{uG,uM,uX} μ ν θ hθ hθ' P hP p θM hp) :
    ∃ T : Distribution M →ₗ[ℂ] Distribution G,
      ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X]
        (Ξ : Representation ℂ M X) (hΞ : IsAdmissible Ξ)
        (B : Ξ.Equiv (Ξ.comp θM.toMonoidHom))
        (hI : IsAdmissible (smoothInduced P (Ξ.comp p))),
        T (twistedDistribution ν Ξ hΞ B.toLinearMap) =
          twistedDistribution μ _ hI
            (inducedTwistedIntertwiner θ hθ hθ' P hP p θM hp Ξ B).toLinearMap := by
  classical
  let b := Module.Free.chooseBasis ℂ (SchwartzBruhat G)
  choose fM hfM using fun i => h (b i)
  let C := b.constr ℂ fM
  refine ⟨Module.Dual.transpose C, fun X _ _ Ξ hΞ B hI => b.ext fun i => ?_⟩
  change twistedDistribution ν Ξ hΞ B.toLinearMap (C (b i)) = _
  rw [b.constr_basis ℂ fM i]
  exact (hfM i X Ξ hΞ B hI).symm

end Langlands.BaseChange
