import Langlands.Representation.Filtration.MixedBilinear
import Langlands.Representation.RankinSelberg.UnequalRankBilinearForms

/-!
# Unequal-rank mirabolic covariance as mixed covariance tests

The two unequal-rank covariance laws of `IsUnequalRankMirabolicCovariant`
are expressed as one family of tests for `Langlands.MixedBilinear`: a test is
either an element `g` of `GL_(n+1)`, acting through `diag(g, I_(r-n))` and `g`,
or an element `u` of the actual group `U_(n+2,r+1)`, acting through its lift to
the mirabolic group and through `1`. The mixed form space is then exactly
`unequalRankMirabolicForms`. No uniqueness or pairing result is proved here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

/-- The tests of the unequal-rank covariance: an element of `GL_(n+1)`, or an
element of the actual subgroup `U_(n+2,r+1)` of the upper unipotent group of
`GL_(r+1)`. At adjacent ranks the second summand is the trivial subgroup. -/
abbrev UnequalRankMixedTest (n r : ℕ) (F : Type uF) [Field F] : Type uF :=
  Langlands.GeneralLinear (n + 1) F ⊕ unequalRankCovarianceSubgroup n r F

variable {F : Type uF} [Field F] {n r : ℕ}

/-- The mirabolic test map: `g ↦ diag(g, I_(r-n))` and `u ↦ u`. -/
def unequalRankMixedLeft (hnr : n < r) : UnequalRankMixedTest n r F → mirabolic r F :=
  Sum.elim (unequalRankEmbedding hnr) fun u => unequalRankUnipotentLift u.val

/-- The `GL_(n+1)` test map: `g ↦ g` and `u ↦ 1`. -/
def unequalRankMixedRight :
    UnequalRankMixedTest n r F → Langlands.GeneralLinear (n + 1) F :=
  Sum.elim id fun _ => 1

@[simp] theorem unequalRankMixedLeft_inl (hnr : n < r)
    (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankMixedLeft hnr (Sum.inl g) = unequalRankEmbedding hnr g :=
  rfl

@[simp] theorem unequalRankMixedLeft_inr (hnr : n < r)
    (u : unequalRankCovarianceSubgroup n r F) :
    unequalRankMixedLeft hnr (Sum.inr u) = unequalRankUnipotentLift u.val :=
  rfl

@[simp] theorem unequalRankMixedRight_inl (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankMixedRight (Sum.inl g : UnequalRankMixedTest n r F) = g :=
  rfl

@[simp] theorem unequalRankMixedRight_inr (u : unequalRankCovarianceSubgroup n r F) :
    unequalRankMixedRight (Sum.inr u : UnequalRankMixedTest n r F) = 1 :=
  rfl

section Weight

variable [TopologicalSpace F]

/-- The scalar of each test: `|det g|^((r-n)/2-s)` for `g` and the standard
character value `ψ_(r+1)(u)` for `u`. It is an arbitrary function on tests;
no multiplicativity is claimed. -/
def unequalRankMixedWeight (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (s : ℂ) : UnequalRankMixedTest n r F → ℂ :=
  Sum.elim (fun g => determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s))
    fun u => (standardCharacter ψ r u.val : ℂ)

@[simp] theorem unequalRankMixedWeight_inl (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (s : ℂ) (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankMixedWeight ψ abv s (Sum.inl g : UnequalRankMixedTest n r F) =
      determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s) :=
  rfl

@[simp] theorem unequalRankMixedWeight_inr (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (s : ℂ) (u : unequalRankCovarianceSubgroup n r F) :
    unequalRankMixedWeight ψ abv s (Sum.inr u : UnequalRankMixedTest n r F) =
      (standardCharacter ψ r u.val : ℂ) :=
  rfl

end Weight

section Forms

variable [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The mixed covariance laws over `UnequalRankMixedTest` are exactly the two
unequal-rank mirabolic covariance laws. -/
theorem isCovariant_unequalRankMixed_iff (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (s : ℂ) (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) :
    MixedBilinear.IsCovariant (unequalRankMixedLeft hnr) unequalRankMixedRight
        (unequalRankMixedWeight ψ abv s) ξ η B ↔
      IsUnequalRankMirabolicCovariant hnr ψ abv ξ η s B := by
  constructor
  · intro h
    refine ⟨fun g v w => h (Sum.inl g) v w, fun u hu v w => ?_⟩
    have h' := h (Sum.inr ⟨u, hu⟩) v w
    simp only [unequalRankMixedLeft_inr, unequalRankMixedRight_inr,
      unequalRankMixedWeight_inr, map_one, Module.End.one_apply] at h'
    exact h'
  · rintro ⟨h₁, h₂⟩ (g | ⟨u, hu⟩) v w
    · exact h₁ g v w
    · simp only [unequalRankMixedLeft_inr, unequalRankMixedRight_inr,
        unequalRankMixedWeight_inr, map_one, Module.End.one_apply]
      exact h₂ u hu v w

/-- The mixed form space over `UnequalRankMixedTest` is the actual submodule
`unequalRankMirabolicForms`. -/
theorem forms_unequalRankMixed_eq (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (s : ℂ) :
    MixedBilinear.forms (unequalRankMixedLeft hnr) unequalRankMixedRight
        (unequalRankMixedWeight ψ abv s) ξ η =
      unequalRankMirabolicForms hnr ψ abv ξ η s := by
  ext B
  exact isCovariant_unequalRankMixed_iff hnr ψ abv ξ η s B

/-- The mixed length over `UnequalRankMixedTest` is the complex module length
of `unequalRankMirabolicForms`. -/
theorem length_unequalRankMixed_eq (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (ξ : Representation ℂ (mirabolic r F) V)
    (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (s : ℂ) :
    MixedBilinear.length (unequalRankMixedLeft hnr) unequalRankMixedRight
        (unequalRankMixedWeight ψ abv s) ξ η =
      Module.length ℂ (unequalRankMirabolicForms hnr ψ abv ξ η s) :=
  (LinearEquiv.ofEq _ _ (forms_unequalRankMixed_eq hnr ψ abv ξ η s)).length_eq

/-- On actual coefficient models, with the first model restricted to the
mirabolic subgroup, membership in the mixed form space is the published
`IsUnequalRankBilinearCovariant`. Neither functional needs to be nonzero. -/
theorem mem_forms_unequalRankMixed_restrict_iff (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) (s : ℂ)
    (B : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ) :
    B ∈ MixedBilinear.forms (V := (coefficientModel π ℓ).toSubmodule)
        (W := (coefficientModel σ ℓ').toSubmodule)
        (unequalRankMixedLeft hnr) unequalRankMixedRight
        (unequalRankMixedWeight ψ abv s)
        ((modelRepresentation π ℓ).comp (mirabolic r F).subtype)
        (modelRepresentation σ ℓ') ↔
      IsUnequalRankBilinearCovariant hnr ψ abv π σ ℓ ℓ' s B := by
  rw [forms_unequalRankMixed_eq]
  exact mem_unequalRankMirabolicForms_restrict_iff hnr ψ abv π σ ℓ ℓ' s B

end Forms

end Langlands.RankinSelberg
