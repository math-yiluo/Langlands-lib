import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Jacquet.LocalizationTransport

/-!
# Transport of the derivatives along representation equivalences

An actual equivalence between two smooth representations, whose carriers may lie
in different universes, induces an actual equivalence between their images under
each of the published functors `Res`, unnormalized and normalized `Ψ⁻` and `Φ⁻`,
`(Φ⁻)^k`, the mirabolic derivatives, the rank transports and the general-linear
derivatives. Finite group-algebra length is transported along every such
equivalence.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

universe uF uV uW uG uH uK

section General

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] {K : Type uK} [Group K] [TopologicalSpace K]

/-- A pair of functors, at carrier universes `uV` and `uW`, sends equivalent
representations to equivalent representations. -/
def TransportsEquiv
    (J : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H)
    (J' : SmoothRep.{0, uG, uW} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H) : Prop :=
  ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (B : SmoothRep.{0, uG, uW} ℂ G),
    Nonempty (A.representation.Equiv B.representation) →
      Nonempty ((J.obj A).representation.Equiv (J'.obj B).representation)

/-- An actual linear equivalence commuting with the two actions is an equivalence of
representations. -/
def equivOfLinearEquiv {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : V ≃ₗ[ℂ] W) (he : ∀ (g : G) (v : V), e (ρ g v) = σ g (e v)) : ρ.Equiv σ :=
  Representation.Equiv.mk e fun g => LinearMap.ext fun v => he g v

theorem transportsEquiv_id :
    TransportsEquiv (𝟭 (SmoothRep.{0, uG, uV} ℂ G)) (𝟭 (SmoothRep.{0, uG, uW} ℂ G)) :=
  fun _ _ h => h

theorem transportsEquiv_comp
    {J₁ : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uH, uV} ℂ H}
    {J₁' : SmoothRep.{0, uG, uW} ℂ G ⥤ SmoothRep.{0, uH, uW} ℂ H}
    {J₂ : SmoothRep.{0, uH, uV} ℂ H ⥤ SmoothRep.{0, uK, uV} ℂ K}
    {J₂' : SmoothRep.{0, uH, uW} ℂ H ⥤ SmoothRep.{0, uK, uW} ℂ K}
    (h₁ : TransportsEquiv J₁ J₁') (h₂ : TransportsEquiv J₂ J₂') :
    TransportsEquiv (J₁ ⋙ J₂) (J₁' ⋙ J₂') :=
  fun A B e => h₂ _ _ (h₁ A B e)

/-- Finite group-algebra length passes along an actual equivalence of
representations, across carrier universes. -/
theorem hasFiniteLength_of_equiv {A : SmoothRep.{0, uG, uV} ℂ G}
    {B : SmoothRep.{0, uG, uW} ℂ G} (e : A.representation.Equiv B.representation)
    (hA : A.HasFiniteLength) : B.HasFiniteLength :=
  IsFiniteLength.of_surjective hA
    (f := Representation.IntertwiningMap.equivLinearMapAsModule A.representation
      B.representation e.toIntertwiningMap) e.surjective

theorem hasFiniteLength_iff_of_equiv {A : SmoothRep.{0, uG, uV} ℂ G}
    {B : SmoothRep.{0, uG, uW} ℂ G} (e : A.representation.Equiv B.representation) :
    A.HasFiniteLength ↔ B.HasFiniteLength :=
  ⟨hasFiniteLength_of_equiv e, hasFiniteLength_of_equiv e.symm⟩

/-- Restriction along a continuous homomorphism keeps the linear equivalence. -/
theorem continuousPullbackFunctor_transportsEquiv (φ : H →* G) (hφ : Continuous φ) :
    TransportsEquiv (Mirabolic.continuousPullbackFunctor.{0, uG, uH, uV} φ hφ)
      (Mirabolic.continuousPullbackFunctor.{0, uG, uH, uW} φ hφ) := by
  rintro A B ⟨e⟩
  exact ⟨equivOfLinearEquiv e.toLinearEquiv fun h v =>
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (φ h) v⟩

/-- Twisting by a character keeps the linear equivalence. -/
theorem twistFunctor_transportsEquiv (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) :
    TransportsEquiv (SmoothRep.twistFunctor.{0, uG, uV} χ hχ)
      (SmoothRep.twistFunctor.{0, uG, uW} χ hχ) := by
  rintro A B ⟨e⟩
  refine ⟨equivOfLinearEquiv e.toLinearEquiv fun g v => ?_⟩
  change e.toLinearEquiv ((χ g : ℂ) • A.representation g v) =
    (χ g : ℂ) • B.representation g (e.toLinearEquiv v)
  rw [map_smul]
  exact congrArg ((χ g : ℂ) • ·)
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)

/-- Localization at a subgroup and character, with the descended action of a
normalizing subgroup, transports equivalences by `Jacquet.Localization.representationEquiv`. -/
theorem localizationSmoothFunctor_transportsEquiv (U : Subgroup G) (θ : U →* ℂˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U)
    (hθ : Jacquet.Localization.IsInvariant U M hMU θ) :
    TransportsEquiv (Jacquet.Localization.smoothFunctor.{0, uG, uV} U θ M hMU hθ)
      (Jacquet.Localization.smoothFunctor.{0, uG, uW} U θ M hMU hθ) := by
  rintro A B ⟨e⟩
  refine ⟨equivOfLinearEquiv (Jacquet.Localization.representationEquiv U θ e) fun m w => ?_⟩
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U θ w
  change Jacquet.Localization.mk B.representation U θ (e (A.representation m v)) =
    Jacquet.Localization.mk B.representation U θ (B.representation m (e v))
  exact congrArg (Jacquet.Localization.mk B.representation U θ)
    (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap m v)

end General

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## The minus functors -/

theorem psiMinusUnnormalized_transportsEquiv (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    TransportsEquiv (Mirabolic.psiMinusUnnormalized.{uV} T n)
      (Mirabolic.psiMinusUnnormalized.{uW} T n) := by
  let _ := T.topology
  exact transportsEquiv_comp (localizationSmoothFunctor_transportsEquiv _ _ _ _ _)
    (continuousPullbackFunctor_transportsEquiv _ _)

theorem phiMinusUnnormalized_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    TransportsEquiv (Mirabolic.phiMinusUnnormalized.{uV} T ψ n)
      (Mirabolic.phiMinusUnnormalized.{uW} T ψ n) := by
  let _ := T.topology
  exact transportsEquiv_comp (localizationSmoothFunctor_transportsEquiv _ _ _ _ _)
    (continuousPullbackFunctor_transportsEquiv _ _)

theorem psiMinus_transportsEquiv (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    TransportsEquiv (Mirabolic.psiMinus.{uV} T n) (Mirabolic.psiMinus.{uW} T n) := by
  let _ := T.topology
  exact transportsEquiv_comp (psiMinusUnnormalized_transportsEquiv T n)
    (twistFunctor_transportsEquiv _ _)

theorem phiMinus_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    TransportsEquiv (Mirabolic.phiMinus.{uV} T ψ n) (Mirabolic.phiMinus.{uW} T ψ n) := by
  let _ := T.topology
  exact transportsEquiv_comp (phiMinusUnnormalized_transportsEquiv T ψ n)
    (twistFunctor_transportsEquiv _ _)

/-! ## Iterates and derivatives -/

theorem phiMinusIterate_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    ∀ k : ℕ, letI := T.topology
      TransportsEquiv (phiMinusIterate.{uF, uV} T ψ n k) (phiMinusIterate.{uF, uW} T ψ n k) := by
  let _ := T.topology
  intro k
  induction k with
  | zero => exact transportsEquiv_id
  | succ k ih => exact transportsEquiv_comp (phiMinus_transportsEquiv T ψ (n + k)) ih

theorem mirabolicDerivative_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    TransportsEquiv (mirabolicDerivative.{uF, uV} T ψ n k)
      (mirabolicDerivative.{uF, uW} T ψ n k) := by
  let _ := T.topology
  exact transportsEquiv_comp (phiMinusIterate_transportsEquiv T ψ n k)
    (psiMinus_transportsEquiv T n)

theorem generalLinearRestriction_transportsEquiv (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    TransportsEquiv (generalLinearRestriction.{uF, uV} T n)
      (generalLinearRestriction.{uF, uW} T n) := by
  let _ := T.topology
  exact continuousPullbackFunctor_transportsEquiv _ _

theorem generalLinearDerivativePositive_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    TransportsEquiv (generalLinearDerivativePositive.{uF, uV} T ψ n k)
      (generalLinearDerivativePositive.{uF, uW} T ψ n k) := by
  let _ := T.topology
  exact transportsEquiv_comp (generalLinearRestriction_transportsEquiv T (n + k))
    (mirabolicDerivative_transportsEquiv T ψ n k)

theorem generalLinearRankCast_transportsEquiv (T : F.TopologicalData) {a b : ℕ}
    (h : a = b) :
    letI := T.topology
    TransportsEquiv (generalLinearRankCast.{uF, uV} T h) (generalLinearRankCast.{uF, uW} T h) := by
  let _ := T.topology
  subst h
  exact transportsEquiv_id

theorem generalLinearDerivative_transportsEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N) :
    letI := T.topology
    TransportsEquiv (generalLinearDerivative.{uF, uV} T ψ N k hk)
      (generalLinearDerivative.{uF, uW} T ψ N k hk) := by
  let _ := T.topology
  cases k with
  | zero => exact transportsEquiv_id
  | succ k =>
    exact transportsEquiv_comp (generalLinearRankCast_transportsEquiv T _)
      (generalLinearDerivativePositive_transportsEquiv T ψ (N - (k + 1)) k)

/-- Finite length of the derivative is invariant under an actual equivalence of the
inputs, whose carriers may lie in different universes. -/
theorem generalLinearDerivative_hasFiniteLength_iff_of_equiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear N F.Carrier))
    (e : letI := T.topology; A.representation.Equiv B.representation) :
    letI := T.topology
    ((generalLinearDerivative.{uF, uV} T ψ N k hk).obj A).HasFiniteLength ↔
      ((generalLinearDerivative.{uF, uW} T ψ N k hk).obj B).HasFiniteLength := by
  let _ := T.topology
  obtain ⟨e'⟩ := generalLinearDerivative_transportsEquiv T ψ N k hk A B ⟨e⟩
  exact hasFiniteLength_iff_of_equiv e'

end Langlands.Derivative
