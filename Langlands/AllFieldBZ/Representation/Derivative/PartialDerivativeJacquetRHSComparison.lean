import Langlands.AllFieldBZ.Representation.Derivative.PartialDerivativeJacquetRHS
import Langlands.AllFieldBZ.Representation.Derivative.PartialLocalizationData
import Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison

/-!
# All-field port of `Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Derivative.JacquetRHSComparison
open Langlands.Derivative.JacquetRHSComparison hiding Direct backward backward_forward backward_mk directMk_radical firstToDirect firstToDirect_covariant firstToDirect_mk forward forward_backward forward_rhsMk linearEquiv linearEquiv_rhsMk linearEquiv_symm_mk linearEquiv_symm_natural rhsMk_covariant
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
open Langlands.Derivative.JacquetRHS hiding inverseHalf_leviModulus_upperUnipotent jacquetMk jacquetMk_surjective jacquet_action_mk jacquet_map_mk leviModulus_upperUnipotent rhsMk rhsMk_natural rhsMk_radical rhsMk_surjective rhsMk_unipotentSubgroup rhsMk_upperUnipotent rhs_action_mk
open Langlands.AllFieldBZ.Derivative.JacquetRHS
universe uF uV

variable {F : LocalFieldPackage.{uF}}

/-- The actual direct quotient, with no change of carrier universe. -/
abbrev Direct (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier) → Type uV := by
  letI := T.topology
  intro A
  exact Jacquet.Localization.Coinvariants A.representation
    (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m)

/-- The composite quotient satisfies the exact combined-character relation. -/
theorem rhsMk_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier) (v : A),
      Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A (A.representation u.val v) =
        (Langlands.Derivative.PartialLocalization.character ψ.complex k m u : ℂ) •
          Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  let U := (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F.Carrier
  let W := Langlands.Derivative.PartialLocalization.finalLeviRange k m F.Carrier
  have he : Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier = U ⊔ W :=
    Langlands.Derivative.PartialLocalization.partialUpper_eq_parabolicRadical_sup hk hm
  let Θ : ↥(U ⊔ W) →* ℂˣ :=
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m).comp (Subgroup.inclusion he.ge)
  apply Jacquet.Localization.covariant_sup A.representation Θ
    (Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A)
    (fun a w => ?_) (fun b w => ?_) ⟨u.val, he.le u.property⟩ v
  · change Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A (A.representation a.val w) =
      (Langlands.Derivative.PartialLocalization.character ψ.complex k m ⟨a.val, _⟩ : ℂ) • _
    rw [Langlands.Derivative.PartialLocalization.character_radical hk hm]
    simpa using Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk_unipotentSubgroup T ψ k m hk hm A a w
  · obtain ⟨a, ha⟩ := b.property
    have hb : b = ⟨(Langlands.Derivative.PartialLocalization.finalLevi (k := k) a).val, ⟨a, rfl⟩⟩ :=
      Subtype.ext ha.symm
    subst b
    change Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A
        (A.representation (blockSum (1, a.val)) w) =
      (Langlands.Derivative.PartialLocalization.character ψ.complex k m (Langlands.Derivative.PartialLocalization.finalLevi a) : ℂ) • _
    rw [Langlands.Derivative.PartialLocalization.character_finalLevi]
    exact Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk_upperUnipotent T ψ k m hk hm A a w

/-- Lift the actual composite quotient through the direct character quotient. -/
def backward (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      Direct T ψ k m A →ₗ[ℂ]
        ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
          partialDerivative T ψ k m).obj A := by
  letI := T.topology
  intro A
  exact Jacquet.Localization.lift A.representation _ _
    (Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A) (rhsMk_covariant T ψ k m hk hm A)

@[simp] theorem backward_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      backward T ψ k m hk hm A
        (Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v) =
        Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A v := by
  intros
  rfl

/-- Direct localization kills every actual ambient parabolic-radical relation. -/
theorem directMk_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F.Carrier) (v : A),
      Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m)
          (A.representation u.val v) =
        Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v := by
  let := T.topology
  intro A u v
  have h := Jacquet.Localization.mk_apply_subgroup A.representation
    (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m)
    ⟨u.val, Langlands.Derivative.PartialLocalization.parabolicRadical_le_partialUpper hk hm u.property⟩ v
  rw [Langlands.Derivative.PartialLocalization.character_radical hk hm] at h
  simpa using h

/-- First descend through the actual Jacquet quotient, keeping its carrier. -/
def firstToDirect (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      (positiveTwoBlockNormalizedJacquet T k m hk hm).obj A →ₗ[ℂ] Direct T ψ k m A := by
  letI := T.topology
  intro A
  exact Jacquet.lift
    (A.representation.comp ((Shahidi.twoBlocks k m hk hm).parabolic F.Carrier).subtype)
    ((Shahidi.twoBlocks k m hk hm).unipotentRadical F.Carrier)
    (Jacquet.Localization.mk A.representation
      (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
      (Langlands.Derivative.PartialLocalization.character ψ.complex k m))
    (fun u => LinearMap.ext fun v =>
      directMk_radical T ψ k m hk hm A ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩ v)

@[simp] theorem firstToDirect_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      firstToDirect T ψ k m hk hm A (Langlands.AllFieldBZ.Derivative.JacquetRHS.jacquetMk T k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v := by
  intros
  rfl

/-- The first lift satisfies the second quotient's original character relation. -/
theorem firstToDirect_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : Langlands.Derivative.Partial.unipotent F.Carrier k m)
      (v : (positiveTwoBlockNormalizedJacquet T k m hk hm).obj A),
      firstToDirect T ψ k m hk hm A
          (((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A).representation u.val v) =
        (Langlands.Derivative.Partial.character ψ.complex k m u : ℂ) • firstToDirect T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  obtain ⟨w, rfl⟩ := Langlands.AllFieldBZ.Derivative.JacquetRHS.jacquetMk_surjective T k m hk hm A v
  have hu : u.val = (1, (Langlands.Derivative.Partial.second F.Carrier k m u).val) :=
    Prod.ext u.property.1 rfl
  rw [hu, Langlands.AllFieldBZ.Derivative.JacquetRHS.jacquet_action_mk, Langlands.AllFieldBZ.Derivative.JacquetRHS.inverseHalf_leviModulus_upperUnipotent]
  simp only [Units.val_one, one_smul, firstToDirect_mk]
  have h := Jacquet.Localization.mk_apply_subgroup A.representation
    (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m)
    (Langlands.Derivative.PartialLocalization.finalLevi (Langlands.Derivative.Partial.second F.Carrier k m u)) w
  rw [Langlands.Derivative.PartialLocalization.character_finalLevi] at h
  exact h

/-- Descend through the actual second quotient into the direct partial quotient. -/
def forward (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A →ₗ[ℂ] Direct T ψ k m A := by
  letI := T.topology
  intro A
  exact Jacquet.Localization.lift
    ((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A).representation
    (Langlands.Derivative.Partial.unipotent F.Carrier k m) (Langlands.Derivative.Partial.character ψ.complex k m)
    (firstToDirect T ψ k m hk hm A) (firstToDirect_covariant T ψ k m hk hm A)

@[simp] theorem forward_rhsMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      forward T ψ k m hk hm A (Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v := by
  intros
  rfl

/-- The two actual quotient lifts are inverse on every RHS vector. -/
@[simp] theorem backward_forward (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (x : ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A),
      backward T ψ k m hk hm A (forward T ψ k m hk hm A x) = x := by
  let := T.topology
  intro A x
  obtain ⟨v, rfl⟩ := Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk_surjective T ψ k m hk hm A x
  rfl

/-- The two actual quotient lifts are inverse on every direct class. -/
@[simp] theorem forward_backward (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (x : Direct T ψ k m A),
      forward T ψ k m hk hm A (backward T ψ k m hk hm A x) = x := by
  let := T.topology
  intro A x
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation
    (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m) x
  rfl

/-- The actual RHS double quotient is linearly equivalent to direct localization. -/
def linearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier),
      ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A ≃ₗ[ℂ] Direct T ψ k m A := by
  letI := T.topology
  intro A
  exact LinearEquiv.ofLinearMap
    (forward T ψ k m hk hm A) (backward T ψ k m hk hm A)
    (LinearMap.ext (forward_backward T ψ k m hk hm A))
    (LinearMap.ext (backward_forward T ψ k m hk hm A))

@[simp] theorem linearEquiv_rhsMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      linearEquiv T ψ k m hk hm A (Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v := by
  intros
  rfl

@[simp] theorem linearEquiv_symm_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      (linearEquiv T ψ k m hk hm A).symm
        (Jacquet.Localization.mk A.representation
          (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
          (Langlands.Derivative.PartialLocalization.character ψ.complex k m) v) =
        Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk T ψ k m hk hm A v := by
  intros
  rfl

/-- The inverse naturality formula, on every direct quotient vector. -/
theorem linearEquiv_symm_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)}
      (f : A ⟶ B) (x : Direct T ψ k m A),
      SmoothRep.hom (((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
          partialDerivative T ψ k m).map f)
          ((linearEquiv T ψ k m hk hm A).symm x) =
        (linearEquiv T ψ k m hk hm B).symm
          (Jacquet.Localization.mapLinear
            (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
            (Langlands.Derivative.PartialLocalization.character ψ.complex k m) (SmoothRep.hom f) x) := by
  let := T.topology
  intro A B f x
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation
    (Langlands.Derivative.PartialLocalization.partialUpper k m F.Carrier)
    (Langlands.Derivative.PartialLocalization.character ψ.complex k m) x
  rw [linearEquiv_symm_mk, Langlands.AllFieldBZ.Derivative.JacquetRHS.rhsMk_natural]
  rfl

end Langlands.AllFieldBZ.Derivative.JacquetRHSComparison
