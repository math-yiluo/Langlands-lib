import Langlands.AllFieldBZ.Representation.Classification.SupercuspidalDerivativeVanishing
import Langlands.AllFieldBZ.Representation.Derivative.MinusVanishing
import Langlands.Representation.Classification.SupercuspidalTopDerivative

/-!
# All-field port of `Langlands.Representation.Classification.SupercuspidalTopDerivative`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Classification.SupercuspidalTopDerivative` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
namespace Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative
open Langlands.Classification.SupercuspidalTopDerivative hiding comp_topQuotient_mem_glFunctionals generalLinearRestriction_rankCast_heq isIrreducible_rankCast nontrivial_generalLinearDerivativePositive_top nontrivial_generalLinearDerivative_top nontrivial_phiMinusIterate nontrivial_rankCast phiMinusCharacter_eq_one_of_upper phiMinusIterate_obj_succ_bottom phiMinusQuotient_eq_of_eq_radical_mul_successor phiMinus_obj_heq psiMinusQuotient_iterateQuotient_upper psiMinusQuotient_zero_injective topQuotient topQuotient_surjective
open Langlands.GeneralLinear
open Langlands.GeneralLinear.Mirabolic
open Langlands.Derivative hiding generalLinearDerivative generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_succ phiMinusIterate_zero
open Langlands.AllFieldBZ.Derivative
open Langlands.Derivative.Mirabolic hiding character_dotProduct_eq_one character_mul_eq_one coe_latticeBox coordinateCharacter coordinateCharacter_apply coordinateCharacter_eq_of_sub_mem coordinateCharacter_eq_one coordinateCharacter_zero eq_zero_of_forall_characterAverage_eq_zero exists_forall_characterAverage_eq_zero exists_latticeBox_subset exists_mem_latticeBox exists_ne_zero_mem_additiveLattice finite_latticeBox_quotient inv_mem_additiveLattice_of_notMem isCompact_latticeBox isCompact_radicalBox isOpen_ker_coordinateCharacter isOpen_ker_phiMinusCharacter isOpen_ker_psiMinusCharacter isOpen_latticeBox ker_psiMinusQuotient latticeBox latticeBox_mono levi_inv_mem_relations mem_latticeBox mem_latticeBox_of_forall_character_eq_one mem_radicalBox phiMinus phiMinusCharacter phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinus_action phiMinus_map_quotient psiMinus psiMinusCharacter psiMinusQuotient psiMinusQuotient_radical psiMinusQuotient_surjective psiMinusUnnormalized psiMinus_action psiMinus_action_eq_smul psiMinus_map_quotient radicalBox radicalBox_mono subsingleton_of_psiMinus_phiMinus
open Langlands.AllFieldBZ.Derivative.Mirabolic
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
open Langlands.Classification.SupercuspidalDerivativeVanishing hiding isSupercuspidal_rankCast iterateQuotient iterateQuotient_surjective phiMinusCharacter_eq_one psiMinusQuotient_iterateQuotient_invariant subsingleton_generalLinearDerivative subsingleton_generalLinearDerivativePositive
open Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing
universe uF uV u

/-! ## Upper unipotent mirabolic elements -/

section Matrices
variable {R : Type u} [CommRing R]

end Matrices
/-! ## Whittaker equivariance of the top quotient -/

variable {F : LocalFieldPackage.{uF}}

/-- The `Φ⁻` normalization character is trivial on upper unipotent elements. -/
theorem phiMinusCharacter_eq_one_of_upper (T : F.TopologicalData) {n : ℕ}
    (g : mirabolic n F.Carrier) (hg : g.val ∈ GeneralLinear.upperUnipotent (n + 1) F.Carrier) :
    realPowerCharacter ((T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype)
      (-(1 / 2 : ℝ)) g = 1 := by
  have hdet : GeneralLinear.determinant g.val = 1 := by
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        Matrix.det_of_isUpperTriangular hg.1, Finset.prod_eq_one fun i _ => hg.2 i])
  have hnorm : (T.determinantNorm (n + 1)).comp (mirabolic n F.Carrier).subtype g = 1 := by
    change T.normalizedAbsUnits (GeneralLinear.determinant g.val) = 1
    rw [hdet, map_one]
  unfold realPowerCharacter
  rw [MonoidHom.comp_apply, hnorm, map_one]

/-- The `Φ⁻` quotient map at `g = r(c) · successor g'` with `g'` upper unipotent: the
radical factor contributes `ψ(c_n)` and `g'` acts on the quotient. -/
theorem phiMinusQuotient_eq_of_eq_radical_mul_successor (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {n : ℕ} :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (n + 1) F.Carrier))
      (g : mirabolic (n + 1) F.Carrier) (c : Fin (n + 1) → F.Carrier)
      (g' : mirabolic n F.Carrier), g'.val ∈ GeneralLinear.upperUnipotent (n + 1) F.Carrier →
      g = ((radicalElement c : radical (n + 1) F.Carrier) : mirabolic (n + 1) F.Carrier) *
        successor g' → ∀ w : X,
        Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ n X (X.representation g w) =
          ψ.complex (c (Fin.last n)) •
            ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ n).obj X).representation g' (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ n X w) := by
  let _ := T.topology
  intro X g c g' hg' hdec w
  subst hdec
  rw [map_mul, Module.End.mul_apply, Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient_radical, Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus_action,
    phiMinusCharacter_eq_one_of_upper T g' hg', Units.val_one, one_smul]
  have ht : (T.mirabolicTheta ψ n (radicalElement c) : ℂ) = ψ.complex (c (Fin.last n)) := by
    change (Derivative.Mirabolic.theta ψ n (radicalElement c) : ℂ) = _
    rw [theta_radicalElement]
  rw [ht]
  rfl

set_option maxHeartbeats 400000 in
/-- The composite quotient `X → Ψ⁻ (Φ⁻)^j X` with target `GL_0` transforms under the
upper unipotent elements of `P_(j+1)` by the standard Whittaker character. -/
theorem psiMinusQuotient_iterateQuotient_upper (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (j : ℕ) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (mirabolic (0 + j) F.Carrier))
      (u : mirabolic (0 + j) F.Carrier)
      (hu : u.val ∈ GeneralLinear.upperUnipotent (0 + j + 1) F.Carrier) (v : X),
        Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj X)
            (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j X (X.representation u v)) =
          (Whittaker.standardCharacter ψ (0 + j) ⟨u.val, hu⟩ : ℂ) •
            Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj X)
              (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j X v) := by
  let _ := T.topology
  induction j with
  | zero =>
      intro X u hu v
      have hr : u ∈ radical 0 F.Carrier := fun _ j => j.elim0
      have h1 : (Whittaker.standardCharacter ψ (0 + 0) ⟨u.val, hu⟩ : ℂ) = 1 := by
        change (Whittaker.standardCharacter ψ 0 ⟨u.val, hu⟩ : ℂ) = 1
        rw [Whittaker.standardCharacter_rankOne]
        rfl
      rw [h1, one_smul]
      exact Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient_radical T 0 X ⟨u, hr⟩ v
  | succ j ih =>
      intro X u hu v
      obtain ⟨u', hu', he, hdec⟩ := exists_radical_mul_successor_upper (n := 0 + j) u hu
      have hq : Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (0 + j) X (X.representation u v) =
          ψ.complex (u.val.val (Fin.last (0 + j)).castSucc (Fin.last (0 + j + 1))) •
            ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X).representation u'
              (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (0 + j) X v) :=
        phiMinusQuotient_eq_of_eq_radical_mul_successor T ψ (n := 0 + j) X u _ u' hu' hdec v
      have hsum : (∑ i : Fin (0 + j + 1), u.val.val i.castSucc i.succ) =
          (∑ i : Fin (0 + j), u'.val.val i.castSucc i.succ) +
            u.val.val (Fin.last (0 + j)).castSucc (Fin.last (0 + j + 1)) := by
        rw [Fin.sum_univ_castSucc, Fin.succ_last]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [he, Fin.succ_castSucc]
      change Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0
          ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X))
          (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X)
            (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (0 + j) X (X.representation u v))) =
        (Whittaker.standardCharacter ψ (0 + j + 1) ⟨u.val, hu⟩ : ℂ) •
          Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0
            ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X))
            (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X)
              (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (0 + j) X v))
      have h2 := ih ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X) u' hu' (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinusQuotient T ψ (0 + j) X v)
      have h3 : ∀ (c : ℂ) (w : (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X),
          Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X))
              (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X) (c • w)) =
            c • Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0
              ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 j).obj ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X))
              (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 j ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (0 + j)).obj X) w) := fun c w => by
        rw [LinearMap.map_smul, LinearMap.map_smul]
      rw [hq]
      refine (h3 _ _).trans ((congrArg
        (ψ.complex (u.val.val (Fin.last (0 + j)).castSucc (Fin.last (0 + j + 1))) • ·) h2).trans
          ((smul_smul _ _ _).trans ?_))
      congr 1
      rw [Whittaker.standardCharacter_apply, Whittaker.standardCharacter_apply]
      change _ = ψ.complex (∑ i : Fin (0 + j + 1), u.val.val i.castSucc i.succ)
      rw [hsum, AddChar.map_add_eq_mul, mul_comm]

/-- The quotient map `A → Ψ⁻ (Φ⁻)^n (A|P)` onto the top derivative `GL_(0+n+1) → GL_0`. -/
def topQuotient (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier)) →
      A →ₗ[ℂ] (Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A := fun A =>
  letI := T.topology
  Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ 0 n).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (0 + n)).obj A))
    ∘ₗ Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 n ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (0 + n)).obj A)

theorem topQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      Function.Surjective (topQuotient T ψ n A) := by
  let _ := T.topology
  intro A
  exact (Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient_surjective T 0 _).comp (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient_surjective T ψ 0 n _)

/-- Every functional on the top derivative pulls back to a standard Whittaker functional. -/
theorem comp_topQuotient_mem_glFunctionals (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier))
      (f : Module.Dual ℂ ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A)),
        f ∘ₗ topQuotient T ψ n A ∈ Whittaker.glFunctionals ψ (0 + n) A.representation := by
  let _ := T.topology
  intro A f u v
  have hP : (u : GeneralLinear (0 + n + 1) F.Carrier) ∈ mirabolic (0 + n) F.Carrier :=
    upperUnipotent_le_mirabolic u.property
  have key := psiMinusQuotient_iterateQuotient_upper T ψ n
    ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (0 + n)).obj A) ⟨u.val, hP⟩ u.property v
  change f (Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 _ (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.iterateQuotient T ψ 0 n _
      (((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (0 + n)).obj A).representation ⟨u.val, hP⟩ v))) =
    (Whittaker.standardCharacter ψ (0 + n) u : ℂ) * f (topQuotient T ψ n A v)
  rw [key]
  exact f.map_smul _ _

/-! ## Nonvanishing of the top derivative -/

theorem phiMinus_obj_heq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (a + 1) F.Carrier))
      (Y' : SmoothRep.{0, uF, uV} ℂ (mirabolic (b + 1) F.Carrier)),
      HEq Y Y' → HEq ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ a).obj Y) ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ b).obj Y') := by
  subst h
  intro Y Y' hY
  obtain rfl := eq_of_heq hY
  exact HEq.rfl

/-- `(Φ⁻)^(j+1)` from rank `m + j + 1` is `Φ⁻` at rank `m` after `(Φ⁻)^j` down to rank
`m + 1`. -/
theorem phiMinusIterate_obj_succ_bottom (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    ∀ (j m : ℕ), letI := T.topology
      ∀ (Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + (j + 1)) F.Carrier))
        (Y' : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1 + j) F.Carrier)),
        HEq Y Y' →
          (Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m (j + 1)).obj Y =
            (Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ m).obj ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ (m + 1) j).obj Y')
  | 0 => fun m Y Y' hY => by
      let _ := T.topology
      obtain rfl := eq_of_heq hY
      rfl
  | j + 1 => fun m Y Y' hY => by
      let _ := T.topology
      exact phiMinusIterate_obj_succ_bottom T ψ j m ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + (j + 1))).obj Y)
        ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ (m + 1 + j)).obj Y')
        (phiMinus_obj_heq T ψ (a := m + (j + 1)) (b := m + 1 + j) (by omega) Y Y' hY)

theorem generalLinearRestriction_rankCast_heq (T : F.TopologicalData) {a b : ℕ} (h : a = b)
    (h' : a + 1 = b + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      HEq ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T a).obj A)
        ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T b).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h').obj A)) := by
  subst h
  intro A
  exact HEq.rfl

theorem nontrivial_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Nontrivial A → Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A) := by
  subst h
  intro A hA
  exact hA

theorem isIrreducible_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      A.IsIrreducible → ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A).IsIrreducible := by
  subst h
  intro A hA
  exact hA

/-- For supercuspidal nonzero `A` on `GL_(m+j+1)`, `(Φ⁻)^j (A|P)` is nonzero. -/
theorem nontrivial_phiMinusIterate (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    ∀ (j m : ℕ), letI := T.topology
      ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + j + 1) F.Carrier),
        IsSupercuspidal A.representation → Nontrivial A →
          Nontrivial ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ m j).obj ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (m + j)).obj A))
  | 0 => fun _ _ _ hA => by
      let _ := T.topology
      exact hA
  | j + 1 => fun m A hsc hA => by
      let _ := T.topology
      have h' : m + (j + 1) + 1 = m + 1 + j + 1 := by omega
      have hsc' := Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.isSupercuspidal_rankCast T h' A hsc
      have hA' := nontrivial_rankCast T h' A hA
      have hZ := nontrivial_phiMinusIterate T ψ j (m + 1) _ hsc' hA'
      have hΨ : Subsingleton ((Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinus T (m + 1)).obj ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ (m + 1) j).obj
          ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (m + 1 + j)).obj
            ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h').obj A)))) :=
        Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.subsingleton_generalLinearDerivativePositive T ψ (m + 1) j (Nat.succ_pos m) _ hsc'
      have hΦ : Nontrivial ((Langlands.AllFieldBZ.Derivative.Mirabolic.phiMinus T ψ m).obj ((Langlands.AllFieldBZ.Derivative.phiMinusIterate T ψ (m + 1) j).obj
          ((Langlands.AllFieldBZ.Derivative.generalLinearRestriction T (m + 1 + j)).obj
            ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h').obj A)))) := by
        rw [← not_subsingleton_iff_nontrivial] at hZ ⊢
        exact fun hs => hZ (Langlands.AllFieldBZ.Derivative.Mirabolic.subsingleton_of_psiMinus_phiMinus T ψ m _ hΨ hs)
      rw [phiMinusIterate_obj_succ_bottom T ψ j m _ _
        (generalLinearRestriction_rankCast_heq T (a := m + (j + 1)) (b := m + 1 + j)
          (by omega) h' A)]
      exact hΦ

/-- `Ψ⁻` at `P_1`, the trivial group, is injective. -/
theorem psiMinusQuotient_zero_injective (T : F.TopologicalData) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier),
      Function.Injective (Langlands.AllFieldBZ.Derivative.Mirabolic.psiMinusQuotient T 0 X) := by
  let _ := T.topology
  intro X
  rw [← LinearMap.ker_eq_bot, Langlands.AllFieldBZ.Derivative.Mirabolic.ker_psiMinusQuotient, eq_bot_iff,
    Jacquet.Localization.relations, Submodule.span_le]
  rintro _ ⟨⟨u, v⟩, rfl⟩
  have hu : ((u : mirabolic 0 F.Carrier)) = 1 := Langlands.GeneralLinear.Mirabolic.rankOne_eq_one _
  have hu' : u = 1 := Subtype.ext hu
  subst hu'
  simp

/-- The top derivative `GL_(0+n+1) → GL_0` of a nonzero supercuspidal representation is
nonzero. -/
theorem nontrivial_generalLinearDerivativePositive_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      IsSupercuspidal A.representation → Nontrivial A →
        Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ 0 n).obj A) := by
  let _ := T.topology
  intro A hsc hA
  have := nontrivial_phiMinusIterate T ψ n 0 A hsc hA
  exact (psiMinusQuotient_zero_injective T _).nontrivial

/-- BZ77 §4.4, nonvanishing half: the derivative of order `n + 1` of a nonzero supercuspidal
representation of `GL_(n+1)` is nonzero. -/
theorem nontrivial_generalLinearDerivative_top (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier),
      IsSupercuspidal A.representation → Nontrivial A →
        Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) := by
  let _ := T.topology
  intro A hsc hA
  have key : ∀ (m : ℕ) (hm : m = 0) (h : n + 1 = m + n + 1),
      Nontrivial ((Langlands.AllFieldBZ.Derivative.generalLinearDerivativePositive T ψ m n).obj
        ((Langlands.AllFieldBZ.Derivative.generalLinearRankCast T h).obj A)) := by
    intro m hm h
    subst hm
    exact nontrivial_generalLinearDerivativePositive_top T ψ n _
      (Langlands.AllFieldBZ.Classification.SupercuspidalDerivativeVanishing.isSupercuspidal_rankCast T h A hsc) (nontrivial_rankCast T h A hA)
  exact key (n + 1 - (n + 1)) (Nat.sub_self _) (rank_eq_of_succ_le le_rfl)

end Langlands.AllFieldBZ.Classification.SupercuspidalTopDerivative
