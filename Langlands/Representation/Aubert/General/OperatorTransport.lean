import Langlands.Representation.Aubert.General.GroupTransport
import Langlands.Representation.Smooth.FiniteLengthGrothendieckIso

/-! # Aubert's unadjusted operator across an equivalence of ambient groups -/

noncomputable section

open CategoryTheory Langlands.SmoothRep

namespace Langlands.Aubert.General

universe uI uJ uG uV

namespace GroupTransport

section Pullback

variable {G H : Type uG} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

/-- Pulling back along an equivalence after its inverse is the identity on the
actual carrier. -/
def pullbackPullbackSymmIso (e : H ≃ₜ* G) (A : SmoothRep.{0, uG, uV} ℂ H) :
    SmoothRep.pullback e (SmoothRep.pullback e.symm A) ≅ A :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun g => by
    ext v
    change A.representation (e.symm (e g)) v = A.representation g v
    rw [e.symm_apply_apply])

end Pullback

section Projection

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  {P M U : Subgroup G} {P' M' U' : Subgroup H}

/-- Continuity of the actual Levi projection transfers along the equivalence. -/
theorem continuous_projection_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hproj : Continuous h.projection) : Continuous h'.projection := by
  have heq : (h'.projection : P' → M') =
      (subgroupEquiv e hMM').symm ∘ h.projection ∘ subgroupEquiv e hPP' := by
    funext p
    change h'.projection p = (subgroupEquiv e hMM').symm (h.projection (subgroupEquiv e hPP' p))
    rw [← projection_transport h h' e hPP' hMM' hUU' p, ContinuousMulEquiv.symm_apply_apply]
  rw [heq]
  exact (subgroupEquiv e hMM').symm.continuous.comp
    (hproj.comp (subgroupEquiv e hPP').continuous)

end Projection

section FiniteLength

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {P M U : Subgroup G} {P' M' U' : Subgroup H}

/-- Finite-length preservation by normalized induction transfers along the
equivalence. -/
theorem inductionPreservesFiniteLength_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hPP' : ∀ x : H, x ∈ P' ↔ e x ∈ P)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU)) :
    PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h' hU') := by
  intro A hA
  let eM := subgroupEquiv e hMM'
  let A₀ := SmoothRep.pullback eM.symm A
  have hA₀ : A₀.HasFiniteLength := pullbackFunctor_preservesFiniteLength eM.symm A hA
  have hI : ((normalizedInductionFunctor.{uG, uV} h hU).obj A₀).HasFiniteLength := hl A₀ hA₀
  have hpI := pullbackFunctor_preservesFiniteLength e _ hI
  have h₁ := hasFiniteLength_of_iso (inductionIsoApp h h' e hPP' hMM' hUU' hU hU' A₀) hpI
  exact hasFiniteLength_of_iso
    ((normalizedInductionFunctor.{uG, uV} h' hU').mapIso (pullbackPullbackSymmIso eM A)) h₁

/-- Finite-length preservation by normalized Jacquet restriction transfers along
the equivalence. -/
theorem jacquetPreservesFiniteLength_transport (h : IsSemidirectDecomposition P M U)
    (h' : IsSemidirectDecomposition P' M' U') (e : H ≃ₜ* G)
    (hMM' : ∀ x : H, x ∈ M' ↔ e x ∈ M)
    (hUU' : ∀ x : H, x ∈ U' ↔ e x ∈ U)
    (hU : IsClosed (U : Set G)) (hU' : IsClosed (U' : Set H))
    (hl : PreservesFiniteLength (jacquetFunctor.{uG, uV} h hU)) :
    PreservesFiniteLength (jacquetFunctor.{uG, uV} h' hU') := by
  intro A hA
  let A₀ := SmoothRep.pullback e.symm A
  have hA₀ : A₀.HasFiniteLength := pullbackFunctor_preservesFiniteLength e.symm A hA
  have hJ : ((jacquetFunctor.{uG, uV} h hU).obj A₀).HasFiniteLength := hl A₀ hA₀
  have hpJ := pullbackFunctor_preservesFiniteLength (subgroupEquiv e hMM') _ hJ
  have h₁ := hasFiniteLength_of_iso (jacquetIsoApp h h' e hMM' hUU' hU hU' A₀) hpJ
  exact hasFiniteLength_of_iso
    ((jacquetFunctor.{uG, uV} h' hU').mapIso (pullbackPullbackSymmIso e A)) h₁

end FiniteLength

section Operator

open SmoothRep.FiniteLengthGrothendieckGroup

variable {G H : Type uG} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  [NonarchimedeanGroup G] [NonarchimedeanGroup H]
  {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
  (P M U : Finset ι → Subgroup G) (P' M' U' : Finset κ → Subgroup H)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (h' : ∀ J, IsSemidirectDecomposition (P' J) (M' J) (U' J))
  (hU : ∀ I, IsClosed (U I : Set G)) (hU' : ∀ J, IsClosed (U' J : Set H))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))
  (hfl' : ∀ J, ParabolicFiniteLength.{uG, max uG uV} (h' J) (hU' J))

/-- Aubert's unadjusted operator commutes with pullback along an equivalence of
ambient groups, when the subgroup families correspond under an equivalence of
the index types. -/
theorem alternatingOperator_transport (e : H ≃ₜ* G) (σ : κ ≃ ι)
    (hPP' : ∀ J x, x ∈ P' J ↔ e x ∈ P (σ.finsetCongr J))
    (hMM' : ∀ J x, x ∈ M' J ↔ e x ∈ M (σ.finsetCongr J))
    (hUU' : ∀ J x, x ∈ U' J ↔ e x ∈ U (σ.finsetCongr J)) :
    (FiniteLengthGrothendieckGroup.pullback.{uG, uG, max uG uV} e).comp
        (alternatingOperator.{uI, uG, uV} P M U h hU hfl) =
      (alternatingOperator.{uJ, uG, uV} P' M' U' h' hU' hfl').comp
        (FiniteLengthGrothendieckGroup.pullback e) := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, alternatingOperator_apply,
    alternatingOperator_apply, map_sum]
  symm
  refine Fintype.sum_equiv σ.finsetCongr _ _ fun J => ?_
  rw [map_zsmul, Equiv.finsetCongr_apply, Finset.card_map]
  congr 1
  exact (LinearMap.congr_fun (inductionJacquetK0_transport (h _) (h' J) e (hPP' J) (hMM' J)
    (hUU' J) (hU _) (hU' J) (hfl _) (hfl' J)) x).symm

end Operator

end GroupTransport

end Langlands.Aubert.General
