import Langlands.Representation.Derivative.TopLocalizationData
import Langlands.Representation.Derivative.TopLocalizationRestriction
import Langlands.Representation.Jacquet.LocalizationTower

/-! # One normalized minus step in full upper localization -/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.TopLocalization

open GeneralLinear GeneralLinear.Mirabolic Jacquet.Localization

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The actual radical, successor and smaller upper group for one minus step. -/
def stepDatum (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    TowerDatum ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  exact
    { U := radical (n + 1) F.Carrier
      M := successorSubgroup n F.Carrier
      W := upperLeviSubgroup (n + 1) F.Carrier
      H := ⊥
      W_le_M := upperLeviSubgroup_le_successor
      H_le_M := bot_le
      M_le_normalizer := successorSubgroup_le_normalizer
      H_le_normalizer := bot_le
      θ := T.mirabolicTheta ψ n
      η := (mirabolicUpperCharacter ψ.complex (n + 1)).comp
        (Subgroup.inclusion upperLeviSubgroup_le_upper)
      θ_invariant := Mirabolic.theta_isInvariant ψ n
      η_invariant := by
        intro h w
        have hh : h = 1 := Subsingleton.elim _ _
        subst h
        simp [conjugate]
      Θ := (mirabolicUpperCharacter ψ.complex (n + 1)).comp
        (Subgroup.inclusion upper_eq_radical_sup.ge)
      Θ_comp_left := by
        ext u
        exact congrArg Units.val (DFunLike.congr_fun (entrywiseCharacter_radical ψ) u)
      Θ_comp_right := rfl }

/-- The twist on the actual successor subgroup, before the second quotient. -/
def stepTwist (T : F.TopologicalData) (n : ℕ) :
    successorSubgroup n F.Carrier →* ℂˣ :=
  (Mirabolic.phiMinusCharacter T n).comp successorEquiv.symm.toMonoidHom

/-- The actual smaller mirabolic upper group is the tower's inner subgroup. -/
def stepInnerEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    Mirabolic.upperUnipotent n F.Carrier ≃* (stepDatum T ψ n).innerSubgroup := by
  letI := T.topology
  exact Mirabolic.upperUnipotentEquiv.trans successorUpperEquiv

/-- The subgroup-copy map is the successor embedding on actual group elements. -/
theorem stepInnerEquiv_val (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ u : Mirabolic.upperUnipotent n F.Carrier,
      (stepInnerEquiv T ψ n u).val = successorEquiv u.val := by
  intros
  rfl

/-- The determinant normalization is trivial on the tower's inner subgroup. -/
theorem stepTwist_inner (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ w : (stepDatum T ψ n).innerSubgroup, stepTwist T n w.val = 1 := by
  let := T.topology
  intro w
  obtain ⟨u, rfl⟩ := (stepInnerEquiv T ψ n).surjective w
  change Mirabolic.phiMinusCharacter T n
    (successorEquiv.symm ((stepInnerEquiv T ψ n u).val)) = 1
  rw [stepInnerEquiv_val, MulEquiv.symm_apply_apply]
  exact realPowerCharacter_mirabolicUpper T _ u

/-- The tower character on the second subgroup is precisely the smaller upper character. -/
theorem stepInnerEquiv_character (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ u : Mirabolic.upperUnipotent n F.Carrier,
      mirabolicUpperCharacter ψ.complex n u =
        (stepDatum T ψ n).innerCharacter (stepInnerEquiv T ψ n u) := by
  let := T.topology
  intro u
  exact (DFunLike.congr_fun (entrywiseCharacter_levi ψ.complex)
    (Mirabolic.upperUnipotentEquiv u)).symm

/-- Transport the second actual quotient to the tower's subgroup copy. -/
def stepIteratedEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      Coinvariants ((Mirabolic.phiMinus T ψ n).obj A).representation
        (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n) ≃ₗ[ℂ]
      (stepDatum T ψ n).TwistedIteratedCoinvariants (stepTwist T n) A.representation := by
  letI := T.topology
  intro A
  refine transportEquiv _ _ _ _ _ _ (stepInnerEquiv T ψ n)
    (LinearEquiv.refl ℂ _) ?_ (stepInnerEquiv_character T ψ n)
  intro u x
  change (Mirabolic.phiMinusCharacter T n u.val : ℂ) •
      (stepDatum T ψ n).firstAction A.representation (successorEquiv u.val) x =
    (stepTwist T n (stepInnerEquiv T ψ n u).val : ℂ) •
      (stepDatum T ψ n).firstAction A.representation (stepInnerEquiv T ψ n u).val x
  rw [stepInnerEquiv_val]
  change _ = (Mirabolic.phiMinusCharacter T n
    (successorEquiv.symm (successorEquiv u.val)) : ℂ) • _
  rw [MulEquiv.symm_apply_apply]

/-- Identify the tower's join with the actual full upper group. -/
def stepDirectEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      Coinvariants A.representation ((stepDatum T ψ n).U ⊔ (stepDatum T ψ n).W)
        (stepDatum T ψ n).Θ ≃ₗ[ℂ]
      Coinvariants A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
        (mirabolicUpperCharacter ψ.complex (n + 1)) := by
  letI := T.topology
  intro A
  exact transportEquiv _ _ _ _ _ _ (MulEquiv.subgroupCongr upper_eq_radical_sup.symm)
    (LinearEquiv.refl ℂ _) (fun _ _ => rfl) (fun _ => rfl)

/-- The normalized minus step followed by full upper localization is the full
upper localization at the original rank. -/
def stepLinearEquiv (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) →
      Coinvariants ((Mirabolic.phiMinus T ψ n).obj A).representation
        (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n) ≃ₗ[ℂ]
      Coinvariants A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
        (mirabolicUpperCharacter ψ.complex (n + 1)) := by
  letI := T.topology
  intro A
  exact (stepIteratedEquiv T ψ n A).trans
    (((stepDatum T ψ n).twistedEquiv (stepTwist T n) (stepTwist_inner T ψ n) 1
      A.representation).toLinearEquiv.trans (stepDirectEquiv T ψ n A))


@[simp] theorem stepLinearEquiv_mk_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) (v : A),
      stepLinearEquiv T ψ n A
        (mk ((Mirabolic.phiMinus T ψ n).obj A).representation
          (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n)
          (mk A.representation (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n) v)) =
      mk A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
        (mirabolicUpperCharacter ψ.complex (n + 1)) v := by
  intros
  rfl

@[simp] theorem stepLinearEquiv_symm_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) (v : A),
      (stepLinearEquiv T ψ n A).symm
        (mk A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
          (mirabolicUpperCharacter ψ.complex (n + 1)) v) =
      mk ((Mirabolic.phiMinus T ψ n).obj A).representation
        (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n)
        (mk A.representation (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n) v) := by
  intros
  rfl

/-- The one-step comparison is natural in every smooth mirabolic intertwiner. -/
def stepIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    Mirabolic.phiMinus.{uV} T ψ n ⋙ mirabolicUpperCoinvariantsFunctor ψ.complex n ≅
      mirabolicUpperCoinvariantsFunctor ψ.complex (n + 1) := by
  letI := T.topology
  refine NatIso.ofComponents (fun A => SmoothRep.mkIso
    { toLinearEquiv := stepLinearEquiv T ψ n A
      isIntertwining' := fun _ => rfl }) ?_
  intro A B f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply hom_ext
  apply hom_ext
  ext v
  rfl

@[simp] theorem stepIso_hom_app_mk_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) (v : A),
      SmoothRep.hom ((stepIso T ψ n).hom.app A)
        (mk ((Mirabolic.phiMinus T ψ n).obj A).representation
          (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n)
          (mk A.representation (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n) v)) =
      mk A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
        (mirabolicUpperCharacter ψ.complex (n + 1)) v := by
  intros
  rfl

@[simp] theorem stepIso_inv_app_mk (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0,uF,uV} ℂ (mirabolic (n + 1) F.Carrier)) (v : A),
      SmoothRep.hom ((stepIso T ψ n).inv.app A)
        (mk A.representation (Mirabolic.upperUnipotent (n + 1) F.Carrier)
          (mirabolicUpperCharacter ψ.complex (n + 1)) v) =
      mk ((Mirabolic.phiMinus T ψ n).obj A).representation
        (Mirabolic.upperUnipotent n F.Carrier) (mirabolicUpperCharacter ψ.complex n)
        (mk A.representation (radical (n + 1) F.Carrier) (T.mirabolicTheta ψ n) v) := by
  intros
  rfl

end Langlands.Derivative.TopLocalization
