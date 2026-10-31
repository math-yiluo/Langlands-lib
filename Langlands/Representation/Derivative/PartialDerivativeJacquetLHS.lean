import Langlands.Representation.Derivative.PartialLocalizationCharacter
import Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
import Langlands.Representation.Jacquet.LocalizationTower
import Langlands.Representation.Jacquet.LocalizationTransport

/-! # Iterated minus quotients as partial character localizations -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.JacquetLHS

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis
open PartialLocalization Jacquet.Localization

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual combined character in the mirabolic realization. -/
def mirabolicCharacter (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    mirabolicPartialUpper k j F.Carrier →* ℂˣ := by
  letI := T.topology
  exact (character ψ.complex k (j + 1)).comp fromMirabolic

/-- A single nonterminal step of the partial localization tower. -/
def stepDatum (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    TowerDatum ℂ (mirabolic (k + j + 1) F.Carrier) := by
  letI := T.topology
  exact
    { U := radical (k + j + 1) F.Carrier
      M := successorSubgroup (k + j) F.Carrier
      W := partialLeviSubgroup k (j + 1) F.Carrier
      H := ⊥
      W_le_M := partialLeviSubgroup_le_successor
      H_le_M := bot_le
      M_le_normalizer := successorSubgroup_le_normalizer
      H_le_normalizer := bot_le
      θ := T.mirabolicTheta ψ (k + j)
      η := (mirabolicCharacter T ψ k (j + 1)).comp
        (Subgroup.inclusion partialLeviSubgroup_le_partialUpper)
      θ_invariant := Mirabolic.theta_isInvariant ψ (k + j)
      η_invariant := by
        intro h w
        have hh : h = 1 := Subsingleton.elim _ _
        subst h
        simp [conjugate]
      Θ := (mirabolicCharacter T ψ k (j + 1)).comp
        (Subgroup.inclusion (partialUpper_eq_radical_sup (k := k)
          (m := j + 1) (F := F.Carrier)).ge)
      Θ_comp_left := by
        exact character_recursiveRadical_succ (k := k) (m := j) ψ
      Θ_comp_right := rfl }

/-- The normalization transported to the actual successor range. -/
def stepTwist (T : F.TopologicalData) (k j : ℕ) :
    successorSubgroup (k + j) F.Carrier →* ℂˣ :=
  (Mirabolic.phiMinusCharacter T (k + j)).comp successorEquiv.symm.toMonoidHom

/-- The actual smaller partial group, with both subgroup certificates. -/
def stepInnerEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    mirabolicPartialUpper k j F.Carrier ≃* (stepDatum T ψ k j).innerSubgroup := by
  letI := T.topology
  exact mirabolicEquiv.trans successorPartialEquiv

@[simp] theorem stepInnerEquiv_val (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ u : mirabolicPartialUpper k j F.Carrier,
      (stepInnerEquiv T ψ k j u).val = successorEquiv u.val := by
  intros
  rfl

/-- Every actual partial upper matrix has determinant one. -/
theorem determinant_partialUpper {k m : ℕ} (u : partialUpper k m F.Carrier) :
    GeneralLinear.determinant u.val = 1 := by
  apply Units.ext
  change Matrix.det u.val.val = 1
  rw [Matrix.det_of_isUpperTriangular u.property.1.1]
  simp only [u.property.1.2, Finset.prod_const_one]

/-- The actual inverse-half determinant twist is trivial on the second subgroup. -/
theorem stepTwist_inner (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ w : (stepDatum T ψ k j).innerSubgroup, stepTwist T k j w.val = 1  := by
  let := T.topology
  intro w
  obtain ⟨u, rfl⟩ := (stepInnerEquiv T ψ k j).surjective w
  change Mirabolic.phiMinusCharacter T (k + j)
    (successorEquiv.symm ((stepInnerEquiv T ψ k j u).val)) = 1
  rw [stepInnerEquiv_val, MulEquiv.symm_apply_apply]
  apply ker_le_realPowerCharacter_ker
  change T.normalizedAbsUnits (GeneralLinear.determinant u.val.val) = 1
  change T.normalizedAbsUnits (GeneralLinear.determinant (fromMirabolic u).val) = 1
  rw [determinant_partialUpper (fromMirabolic u), map_one]

/-- The second tower character is the unchanged smaller partial character. -/
theorem stepInnerEquiv_character (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ u : mirabolicPartialUpper k j F.Carrier,
      mirabolicCharacter T ψ k j u =
        (stepDatum T ψ k j).innerCharacter (stepInnerEquiv T ψ k j u) := by
  let := T.topology
  intro u
  exact (DFunLike.congr_fun (character_recursiveLevi (k := k) (m := j + 1)
    ψ.complex) (fromMirabolic u)).symm

/-- Transport the second quotient using the actual normalized Phi action. -/
def stepIteratedEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j + 1) F.Carrier)) →
      Coinvariants ((Mirabolic.phiMinus T ψ (k + j)).obj A).representation
        (mirabolicPartialUpper k j F.Carrier) (mirabolicCharacter T ψ k j) ≃ₗ[ℂ]
      (stepDatum T ψ k j).TwistedIteratedCoinvariants (stepTwist T k j)
        A.representation := by
  letI := T.topology
  intro A
  refine transportEquiv _ _ _ _ _ _ (stepInnerEquiv T ψ k j)
    (LinearEquiv.refl ℂ _) ?_ (stepInnerEquiv_character T ψ k j)
  intro u x
  change (Mirabolic.phiMinusCharacter T (k + j) u.val : ℂ) •
      (stepDatum T ψ k j).firstAction A.representation (successorEquiv u.val) x =
    (stepTwist T k j (stepInnerEquiv T ψ k j u).val : ℂ) •
      (stepDatum T ψ k j).firstAction A.representation
        (stepInnerEquiv T ψ k j u).val x
  rw [stepInnerEquiv_val]
  change _ = (Mirabolic.phiMinusCharacter T (k + j)
    (successorEquiv.symm (successorEquiv u.val)) : ℂ) • _
  rw [MulEquiv.symm_apply_apply]

/-- Identify the actual tower join with the larger partial group. -/
def stepDirectEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j + 1) F.Carrier)) →
      Coinvariants A.representation ((stepDatum T ψ k j).U ⊔ (stepDatum T ψ k j).W)
        (stepDatum T ψ k j).Θ ≃ₗ[ℂ]
      Coinvariants A.representation (mirabolicPartialUpper k (j + 1) F.Carrier)
        (mirabolicCharacter T ψ k (j + 1)) := by
  letI := T.topology
  intro A
  exact transportEquiv _ _ _ _ _ _
    (MulEquiv.subgroupCongr (partialUpper_eq_radical_sup (k := k)
      (m := j + 1) (F := F.Carrier)).symm)
    (LinearEquiv.refl ℂ _) (fun _ _ => rfl) (fun _ => rfl)

/-- One normalized Phi quotient followed by smaller partial localization. -/
def stepLinearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j + 1) F.Carrier)) →
      Coinvariants ((Mirabolic.phiMinus T ψ (k + j)).obj A).representation
        (mirabolicPartialUpper k j F.Carrier) (mirabolicCharacter T ψ k j) ≃ₗ[ℂ]
      Coinvariants A.representation (mirabolicPartialUpper k (j + 1) F.Carrier)
        (mirabolicCharacter T ψ k (j + 1)) := by
  letI := T.topology
  intro A
  exact (stepIteratedEquiv T ψ k j A).trans
    (((stepDatum T ψ k j).twistedEquiv (stepTwist T k j)
      (stepTwist_inner T ψ k j) 1 A.representation).toLinearEquiv.trans
        (stepDirectEquiv T ψ k j A))

@[simp] theorem stepLinearEquiv_mk_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j + 1) F.Carrier)) (v : A),
      stepLinearEquiv T ψ k j A
        (mk ((Mirabolic.phiMinus T ψ (k + j)).obj A).representation
          (mirabolicPartialUpper k j F.Carrier) (mirabolicCharacter T ψ k j)
          (JacquetNormalization.phiStepMk T ψ (k + j) A v)) =
      mk A.representation (mirabolicPartialUpper k (j + 1) F.Carrier)
        (mirabolicCharacter T ψ k (j + 1)) v := by
  intros
  rfl

/-- At the terminal Psi step the partial group is the actual final-column radical. -/
theorem mirabolicPartialUpper_zero (k : ℕ) :
    mirabolicPartialUpper k 0 F.Carrier = radical k F.Carrier := by
  apply le_antisymm
  · intro g hg i j
    exact hg.2 i j
  · exact radical_le_partialUpper (k := k) (m := 0) (F := F.Carrier)

/-- Transport the normalized terminal Psi carrier, whose character is trivial. -/
def terminalLinearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic k F.Carrier)) →
      (Mirabolic.psiMinus T k).obj A ≃ₗ[ℂ]
      Coinvariants A.representation (mirabolicPartialUpper k 0 F.Carrier)
        (mirabolicCharacter T ψ k 0) := by
  letI := T.topology
  intro A
  refine transportEquiv A.representation A.representation _ _ 1 _
    (MulEquiv.subgroupCongr (mirabolicPartialUpper_zero k).symm)
    (LinearEquiv.refl ℂ _) (fun _ _ => rfl) ?_
  intro u
  simp [mirabolicCharacter, character]

/-- The actual iterated-minus carrier is the direct partial character quotient. -/
def mirabolicLinearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k : ℕ) :
    (j : ℕ) → letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j) F.Carrier)) →
      (mirabolicDerivative T ψ k j).obj A ≃ₗ[ℂ]
      Coinvariants A.representation (mirabolicPartialUpper k j F.Carrier)
        (mirabolicCharacter T ψ k j)
  | 0 => terminalLinearEquiv T ψ k
  | j + 1 => by
      letI := T.topology
      intro A
      exact (mirabolicLinearEquiv T ψ k j ((Mirabolic.phiMinus T ψ (k + j)).obj A)).trans
        (stepLinearEquiv T ψ k j A)

@[simp] theorem mirabolicLinearEquiv_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (k + j) F.Carrier)) (v : A),
      mirabolicLinearEquiv T ψ k j A
        (JacquetNormalization.mirabolicDerivativeMk T ψ k j A v) =
      mk A.representation (mirabolicPartialUpper k j F.Carrier)
        (mirabolicCharacter T ψ k j) v := by
  let := T.topology
  induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro A v
    change stepLinearEquiv T ψ k j A
      (mirabolicLinearEquiv T ψ k j ((Mirabolic.phiMinus T ψ (k + j)).obj A)
        (JacquetNormalization.mirabolicDerivativeMk T ψ k j
          ((Mirabolic.phiMinus T ψ (k + j)).obj A)
          (JacquetNormalization.phiStepMk T ψ (k + j) A v))) = _
    rw [ih, stepLinearEquiv_mk_mk]

/-- Forget the redundant mirabolic certificate in the direct quotient. -/
def ambientLinearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + j + 1) F.Carrier)) →
      Coinvariants ((generalLinearRestriction T (k + j)).obj A).representation
        (mirabolicPartialUpper k j F.Carrier) (mirabolicCharacter T ψ k j) ≃ₗ[ℂ]
      Coinvariants A.representation (partialUpper k (j + 1) F.Carrier)
        (character ψ.complex k (j + 1)) := by
  letI := T.topology
  intro A
  exact transportEquiv _ _ _ _ _ _ mirabolicEquiv
    (LinearEquiv.refl ℂ _) (fun _ _ => rfl) (fun _ => rfl)

/-- The actual positive derivative carrier, without changes to the published functor. -/
def generalLinearLinearEquiv (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + j + 1) F.Carrier)) →
      (generalLinearDerivativePositive T ψ k j).obj A ≃ₗ[ℂ]
      Coinvariants A.representation (partialUpper k (j + 1) F.Carrier)
        (character ψ.complex k (j + 1)) := by
  letI := T.topology
  intro A
  exact (mirabolicLinearEquiv T ψ k j
    ((generalLinearRestriction T (k + j)).obj A)).trans (ambientLinearEquiv T ψ k j A)

@[simp] theorem generalLinearLinearEquiv_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + j + 1) F.Carrier)) (v : A),
      generalLinearLinearEquiv T ψ k j A
        (JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v) =
      mk A.representation (partialUpper k (j + 1) F.Carrier)
        (character ψ.complex k (j + 1)) v := by
  let := T.topology
  intro A v
  change ambientLinearEquiv T ψ k j A
    (mirabolicLinearEquiv T ψ k j ((generalLinearRestriction T (k + j)).obj A)
      (JacquetNormalization.mirabolicDerivativeMk T ψ k j
        ((generalLinearRestriction T (k + j)).obj A) v)) = _
  erw [mirabolicLinearEquiv_mk]
  rfl

@[simp] theorem generalLinearLinearEquiv_symm_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (k j : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear (k + j + 1) F.Carrier)) (v : A),
      (generalLinearLinearEquiv T ψ k j A).symm
        (mk A.representation (partialUpper k (j + 1) F.Carrier)
          (character ψ.complex k (j + 1)) v) =
      JacquetNormalization.generalLinearDerivativePositiveMk T ψ k j A v := by
  let := T.topology
  intro A v
  apply (generalLinearLinearEquiv T ψ k j A).injective
  rw [LinearEquiv.apply_symm_apply, generalLinearLinearEquiv_mk]

end Langlands.Derivative.JacquetLHS
