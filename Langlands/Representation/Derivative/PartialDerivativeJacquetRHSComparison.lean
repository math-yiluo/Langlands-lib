import Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
import Langlands.Representation.Derivative.PartialLocalizationData
import Langlands.Representation.Jacquet.LocalizationTower

/-!
# The actual right-hand double quotient and direct partial localization

The two quotient maps are compared on the same original vectors. The combined
subgroup and character are the published concrete partial-upper data.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.JacquetRHSComparison

open GeneralLinear HarmonicAnalysis
open JacquetRHS

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual direct quotient, with no change of carrier universe. -/
abbrev Direct (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier) → Type uV := by
  letI := T.topology
  intro A
  exact Jacquet.Localization.Coinvariants A.representation
    (PartialLocalization.partialUpper k m F.Carrier)
    (PartialLocalization.character ψ.complex k m)

/-- The composite quotient satisfies the exact combined-character relation. -/
theorem rhsMk_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : PartialLocalization.partialUpper k m F.Carrier) (v : A),
      rhsMk T ψ k m hk hm A (A.representation u.val v) =
        (PartialLocalization.character ψ.complex k m u : ℂ) •
          rhsMk T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  let U := (Shahidi.twoBlocks k m hk hm).unipotentSubgroup F.Carrier
  let W := PartialLocalization.finalLeviRange k m F.Carrier
  have he : PartialLocalization.partialUpper k m F.Carrier = U ⊔ W :=
    PartialLocalization.partialUpper_eq_parabolicRadical_sup hk hm
  let Θ : ↥(U ⊔ W) →* ℂˣ :=
    (PartialLocalization.character ψ.complex k m).comp (Subgroup.inclusion he.ge)
  apply Jacquet.Localization.covariant_sup A.representation Θ
    (rhsMk T ψ k m hk hm A)
    (fun a w => ?_) (fun b w => ?_) ⟨u.val, he.le u.property⟩ v
  · change rhsMk T ψ k m hk hm A (A.representation a.val w) =
      (PartialLocalization.character ψ.complex k m ⟨a.val, _⟩ : ℂ) • _
    rw [PartialLocalization.character_radical hk hm]
    simpa using rhsMk_unipotentSubgroup T ψ k m hk hm A a w
  · obtain ⟨a, ha⟩ := b.property
    have hb : b = ⟨(PartialLocalization.finalLevi (k := k) a).val, ⟨a, rfl⟩⟩ :=
      Subtype.ext ha.symm
    subst b
    change rhsMk T ψ k m hk hm A
        (A.representation (blockSum (1, a.val)) w) =
      (PartialLocalization.character ψ.complex k m (PartialLocalization.finalLevi a) : ℂ) • _
    rw [PartialLocalization.character_finalLevi]
    exact rhsMk_upperUnipotent T ψ k m hk hm A a w

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
    (rhsMk T ψ k m hk hm A) (rhsMk_covariant T ψ k m hk hm A)

@[simp] theorem backward_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      backward T ψ k m hk hm A
        (Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v) =
        rhsMk T ψ k m hk hm A v := by
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
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m)
          (A.representation u.val v) =
        Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v := by
  let := T.topology
  intro A u v
  have h := Jacquet.Localization.mk_apply_subgroup A.representation
    (PartialLocalization.partialUpper k m F.Carrier)
    (PartialLocalization.character ψ.complex k m)
    ⟨u.val, PartialLocalization.parabolicRadical_le_partialUpper hk hm u.property⟩ v
  rw [PartialLocalization.character_radical hk hm] at h
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
      (PartialLocalization.partialUpper k m F.Carrier)
      (PartialLocalization.character ψ.complex k m))
    (fun u => LinearMap.ext fun v =>
      directMk_radical T ψ k m hk hm A ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩ v)

@[simp] theorem firstToDirect_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      firstToDirect T ψ k m hk hm A (jacquetMk T k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v := by
  intros
  rfl

/-- The first lift satisfies the second quotient's original character relation. -/
theorem firstToDirect_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (u : Partial.unipotent F.Carrier k m)
      (v : (positiveTwoBlockNormalizedJacquet T k m hk hm).obj A),
      firstToDirect T ψ k m hk hm A
          (((positiveTwoBlockNormalizedJacquet T k m hk hm).obj A).representation u.val v) =
        (Partial.character ψ.complex k m u : ℂ) • firstToDirect T ψ k m hk hm A v := by
  let := T.topology
  intro A u v
  obtain ⟨w, rfl⟩ := jacquetMk_surjective T k m hk hm A v
  have hu : u.val = (1, (Partial.second F.Carrier k m u).val) :=
    Prod.ext u.property.1 rfl
  rw [hu, jacquet_action_mk, inverseHalf_leviModulus_upperUnipotent]
  simp only [Units.val_one, one_smul, firstToDirect_mk]
  have h := Jacquet.Localization.mk_apply_subgroup A.representation
    (PartialLocalization.partialUpper k m F.Carrier)
    (PartialLocalization.character ψ.complex k m)
    (PartialLocalization.finalLevi (Partial.second F.Carrier k m u)) w
  rw [PartialLocalization.character_finalLevi] at h
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
    (Partial.unipotent F.Carrier k m) (Partial.character ψ.complex k m)
    (firstToDirect T ψ k m hk hm A) (firstToDirect_covariant T ψ k m hk hm A)

@[simp] theorem forward_rhsMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      forward T ψ k m hk hm A (rhsMk T ψ k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v := by
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
  obtain ⟨v, rfl⟩ := rhsMk_surjective T ψ k m hk hm A x
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
    (PartialLocalization.partialUpper k m F.Carrier)
    (PartialLocalization.character ψ.complex k m) x
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
      linearEquiv T ψ k m hk hm A (rhsMk T ψ k m hk hm A v) =
        Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v := by
  intros
  rfl

@[simp] theorem linearEquiv_symm_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)) (v : A),
      (linearEquiv T ψ k m hk hm A).symm
        (Jacquet.Localization.mk A.representation
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) v) =
        rhsMk T ψ k m hk hm A v := by
  intros
  rfl

/-- Naturality for the actual RHS functor and the induced direct quotient map. -/
theorem linearEquiv_natural (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier)}
      (f : A ⟶ B)
      (x : ((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
        partialDerivative T ψ k m).obj A),
      Jacquet.Localization.mapLinear
          (PartialLocalization.partialUpper k m F.Carrier)
          (PartialLocalization.character ψ.complex k m) (SmoothRep.hom f)
          (linearEquiv T ψ k m hk hm A x) =
        linearEquiv T ψ k m hk hm B
          (SmoothRep.hom (((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
            partialDerivative T ψ k m).map f) x) := by
  let := T.topology
  intro A B f x
  obtain ⟨v, rfl⟩ := rhsMk_surjective T ψ k m hk hm A x
  rw [linearEquiv_rhsMk, rhsMk_natural, linearEquiv_rhsMk]
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
            (PartialLocalization.partialUpper k m F.Carrier)
            (PartialLocalization.character ψ.complex k m) (SmoothRep.hom f) x) := by
  let := T.topology
  intro A B f x
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation
    (PartialLocalization.partialUpper k m F.Carrier)
    (PartialLocalization.character ψ.complex k m) x
  rw [linearEquiv_symm_mk, rhsMk_natural]
  rfl

/-- The comparison keeps the exact first-factor inverse-half normalization. -/
theorem linearEquiv_action_rhsMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + m) F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : A),
      linearEquiv T ψ k m hk hm A
        ((((positiveTwoBlockNormalizedJacquet T k m hk hm) ⋙
          partialDerivative T ψ k m).obj A).representation g
            (rhsMk T ψ k m hk hm A v)) =
        (Jacquet.inverseHalfCharacter (T.leviModulus (Shahidi.twoBlocks k m hk hm))
          ((Shahidi.twoBlockLeviContinuousEquiv hk hm F.Carrier).symm (g, 1)) : ℂ) •
          Jacquet.Localization.mk A.representation
            (PartialLocalization.partialUpper k m F.Carrier)
            (PartialLocalization.character ψ.complex k m)
            (A.representation (blockSum (g, 1)) v) := by
  let := T.topology
  intro A g v
  rw [rhs_action_mk, map_smul, linearEquiv_rhsMk]

end Langlands.Derivative.JacquetRHSComparison
