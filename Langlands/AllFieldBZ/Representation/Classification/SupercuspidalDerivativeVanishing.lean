import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.AllFieldBZ.Representation.Derivative.Iteration
import Langlands.Representation.Classification.SupercuspidalDerivativeVanishing

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalDerivativeVanishing`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalDerivativeVanishing` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing
open Langlands.Classification.SupercuspidalDerivativeVanishing hiding isSupercuspidal_rankCast iterateQuotient iterateQuotient_surjective phiMinusCharacter_eq_one psiMinusQuotient_iterateQuotient_invariant subsingleton_generalLinearDerivative subsingleton_generalLinearDerivativePositive
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
open Langlands.AllFieldBZ.Derivative
open Langlands.Derivative.Mirabolic hiding isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter ker_psiMinusQuotient phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient
open Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.HarmonicAnalysis
universe uF uV u

/-! ## Block unipotent matrices -/

section Matrices
variable {R : Type u} [CommRing R]

end Matrices
/-! ## The iterated quotient map -/

variable {F : LocalFieldPackage.{uF}}

/-- The composite quotient map `X → (Φ⁻)^j X`, applying the largest-rank quotient first. -/
def iterateQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    (j : ℕ) → letI := T.topology
      (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier)) →
        X →ₗ[ℂ] (Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj X
  | 0 => fun _ => LinearMap.id
  | j + 1 => fun X => letI := T.topology
      iterateQuotient T ψ m j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X) ∘ₗ Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (m + j) X

theorem iterateQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    ∀ (j : ℕ), letI := T.topology
      ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier),
        Function.Surjective (iterateQuotient T ψ m j X)
  | 0 => fun _ => Function.surjective_id
  | j + 1 => fun X => by
      let _ := T.topology
      exact (iterateQuotient_surjective T ψ m j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X)).comp
        (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient_surjective T ψ (m + j) X)

/-- The `Φ⁻` normalization character is trivial on block unipotent elements. -/
theorem phiMinusCharacter_eq_one (T : F.TopologicalData) {n m : ℕ} (g : mirabolic n F.Carrier)
    (hg : IsBlockUnipotent m g.val) :
    realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
      (-(1 / 2 : ℝ)) g = 1 := by
  have hdet : GeneralLinear.determinant g.val = 1 := by
    have hu := mem_upperUnipotent_of_isBlockUnipotent hg
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        Matrix.det_of_isUpperTriangular hu.1, Finset.prod_eq_one fun i _ => hu.2 i])
  have hnorm : (T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype g = 1 := by
    change T.normalizedAbsUnits (GeneralLinear.determinant g.val) = 1
    rw [hdet, map_one]
  unfold realPowerCharacter
  rw [MonoidHom.comp_apply, hnorm, map_one]

/-- The composite quotient `X → Ψ⁻ (Φ⁻)^j X` is invariant under every block unipotent
`[[I_m, Y], [0, I_(j+1)]]` in `P_(m+j+1)`. -/
theorem psiMinusQuotient_iterateQuotient_invariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    ∀ (j : ℕ), letI := T.topology
      ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + j) F.Carrier))
        (g : mirabolic (m + j) F.Carrier), IsBlockUnipotent m g.val → ∀ v : X,
          Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T m ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj X)
              (iterateQuotient T ψ m j X (X.representation g v)) =
            Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T m ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj X)
              (iterateQuotient T ψ m j X v)
  | 0 => fun X g hg v => by
      let _ := T.topology
      exact Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient_radical T m X ⟨g, mem_radical_of_isBlockUnipotent hg⟩ v
  | j + 1 => fun X g hg v => by
      let _ := T.topology
      obtain ⟨g', c, hc, hg', rfl⟩ :=
        exists_radical_mul_successor (n := m + j) (Nat.le_add_right m j) g hg
      have hq : ∀ w : X,
          Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (m + j) X (X.representation
              (((radicalElement c : radical (m + j + 1) F.Carrier) :
                mirabolic (m + j + 1) F.Carrier) * successor g') w) =
            ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X).representation g'
              (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (m + j) X w) := by
        intro w
        rw [map_mul, Module.End.mul_apply, Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient_radical, Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus_action,
          phiMinusCharacter_eq_one T g' hg', Units.val_one, one_smul]
        have ht : (T.mirabolicTheta ψ (m + j) (radicalElement c) : ℂ) = 1 := by
          change (Derivative.Mirabolic.theta ψ (m + j) (radicalElement c) : ℂ) = 1
          rw [theta_radicalElement, hc, AddChar.map_zero_eq_one]
        rw [ht, one_smul]
      change Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T m ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X))
          (iterateQuotient T ψ m j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X)
            (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (m + j) X (X.representation _ v))) =
        Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T m ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X))
          (iterateQuotient T ψ m j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + j)).obj X)
            (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (m + j) X v))
      rw [hq]
      exact psiMinusQuotient_iterateQuotient_invariant T ψ m j _ g' hg' _

/-! ## Vanishing of the intermediate derivatives -/

/-- A positive derivative `GL_(m+j+1) → GL_m` with `m > 0` of a supercuspidal
representation is zero. -/
theorem subsingleton_generalLinearDerivativePositive (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m j : ℕ) (hm : 0 < m) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + j + 1) F.Carrier),
      IsSupercuspidal A.representation →
        Subsingleton ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ m j).obj A) := by
  let _ := T.topology
  intro A hA
  let X := (Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (m + j)).obj A
  let tot : A →ₗ[ℂ] (Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ m j).obj A :=
    Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T m ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj X) ∘ₗ iterateQuotient T ψ m j X
  have hsurj : Function.Surjective tot :=
    (Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient_surjective T m _).comp (iterateQuotient_surjective T ψ m j X)
  let B : BlockShape (m + j + 1) := BlockShape.binary m (j + 1) hm (Nat.succ_pos j)
  have hJ := hA.2 B (binary_parabolic_ne_top (R := F.Carrier) hm (Nat.succ_pos j)) 1
  have hinv : ∀ u : B.conjugateUnipotent 1, tot ∘ₗ A.representation u.val = tot := by
    rintro ⟨u, hu⟩
    apply LinearMap.ext
    intro v
    have hu' : u ∈ B.unipotentSubgroup F.Carrier := by
      obtain ⟨u', hu', rfl⟩ := hu
      simpa using hu'
    have hb := isBlockUnipotent_of_mem_binary (c := j + 1) hm (Nat.succ_pos j) hu'
    have hP : u ∈ mirabolic (m + j) F.Carrier :=
      mem_mirabolic_of_isBlockUnipotent (Nat.le_add_right m j) hb
    exact psiMinusQuotient_iterateQuotient_invariant T ψ m j X ⟨u, hP⟩ hb v
  refine ⟨fun x y => ?_⟩
  obtain ⟨v, rfl⟩ := hsurj x
  obtain ⟨w, rfl⟩ := hsurj y
  have hl := Jacquet.lift_mk A.representation (B.conjugateUnipotent 1) tot hinv
  rw [← hl v, ← hl w,
    Subsingleton.elim (Jacquet.mk A.representation (B.conjugateUnipotent 1) v)
      (Jacquet.mk A.representation (B.conjugateUnipotent 1) w)]

/-- Rank transport preserves supercuspidality. -/
theorem isSupercuspidal_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      IsSupercuspidal A.representation →
        IsSupercuspidal ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A).representation := by
  subst h
  intro A hA
  exact hA

/-- BZ77 §4.4, vanishing part: for `0 < k < N`, the derivative of order `k` of a
supercuspidal representation of `GL_N` is zero. -/
theorem subsingleton_generalLinearDerivative (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (N k : ℕ) (hk : k ≤ N)
    (hpos : 0 < k) (hlt : k < N) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier),
      IsSupercuspidal A.representation →
        Subsingleton ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ N k hk).obj A) := by
  let _ := T.topology
  intro A hA
  rw [Langlands.AllFieldBZ.Derivative.generalLinearDerivative_of_pos T ψ N k hk hpos]
  exact subsingleton_generalLinearDerivativePositive T ψ (N - k) (k - 1) (by omega) _
    (isSupercuspidal_rankCast T (rank_eq_of_pos_le hk hpos) A hA)

end Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing
