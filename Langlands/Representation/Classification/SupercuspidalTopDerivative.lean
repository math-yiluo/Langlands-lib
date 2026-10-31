import Langlands.Representation.Classification.SupercuspidalDerivativeVanishing
import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Representation.Whittaker.GeneralLinear

/-!
# The top derivative of a supercuspidal representation

Two unconditional facts about the top derivative `Ψ⁻ (Φ⁻)^n (A|P)` of a smooth
representation `A` of `GL_(n+1)`:

* The quotient map `A → Ψ⁻ (Φ⁻)^n (A|P)` is surjective and transforms under the upper
  unipotent group by the standard Whittaker character, so every linear functional on the
  top derivative pulls back to a standard Whittaker functional on `A`.
* If `A` is nonzero and supercuspidal, the top derivative is nonzero: by induction on the
  number of `Φ⁻` steps, the intermediate derivatives vanish, so the published lemma
  `Ψ⁻ X = 0 ∧ Φ⁻ X = 0 → X = 0` keeps `Φ⁻` nonzero at each step.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Classification.SupercuspidalTopDerivative

open GeneralLinear GeneralLinear.Mirabolic Derivative Derivative.Mirabolic HarmonicAnalysis
  SupercuspidalDerivativeVanishing

universe uF uV u

/-! ## Upper unipotent mirabolic elements -/

section Matrices

variable {R : Type u} [CommRing R]

/-- An upper unipotent element of `P_(n+2)` is the radical element of its last column times
the successor image of an upper unipotent element of `P_(n+1)` with the same upper-left
block. -/
theorem exists_radical_mul_successor_upper {n : ℕ} (g : mirabolic (n + 1) R)
    (hg : g.val ∈ GeneralLinear.upperUnipotent (n + 1 + 1) R) :
    ∃ g' : mirabolic n R, g'.val ∈ GeneralLinear.upperUnipotent (n + 1) R ∧
      (∀ i j : Fin (n + 1), g'.val.val i j = g.val.val i.castSucc j.castSucc) ∧
      g = ((radicalElement (fun i : Fin (n + 1) => g.val.val i.castSucc (Fin.last (n + 1))) :
        radical (n + 1) R) : mirabolic (n + 1) R) * successor g' := by
  let c : Fin (n + 1) → R := fun i => g.val.val i.castSucc (Fin.last (n + 1))
  let r : mirabolic (n + 1) R := (radicalElement c : radical (n + 1) R)
  let r' : mirabolic (n + 1) R := (radicalElement (-c) : radical (n + 1) R)
  have hrr' : r * r' = 1 := by
    have h := radicalElement_add c (-c)
    rw [add_neg_cancel, radicalElement_zero] at h
    exact congrArg Subtype.val h.symm
  let s := r' * g
  have hs : ∀ (i : Fin (n + 1)) (j : Fin (n + 2)),
      s.val.val i.castSucc j =
        g.val.val i.castSucc j + (-c i) * g.val.val (Fin.last (n + 1)) j := by
    intro i j
    change ((radicalElement (-c)).val.val.val * g.val.val) i.castSucc j = _
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    simp only [radicalElement_first, radicalElement_last, Pi.neg_apply, ite_mul, one_mul,
      zero_mul, Fin.castSucc_inj, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hs' : ∀ i j : Fin (n + 1), s.val.val i.castSucc j.castSucc =
      g.val.val i.castSucc j.castSucc := by
    intro i j
    rw [hs, g.property j.castSucc, ite_eq_right (Fin.castSucc_ne_last j), mul_zero, add_zero]
  have hcol : ∀ i : Fin (n + 1), s.val.val i.castSucc (Fin.last (n + 1)) = 0 := by
    intro i
    rw [hs, g.property (Fin.last (n + 1)), ite_eq_left rfl, mul_one]
    exact add_neg_cancel _
  have hrow : ∀ j : Fin (n + 1),
      s.val.val (Fin.last n).castSucc j.castSucc = if j = Fin.last n then 1 else 0 := by
    intro j
    rw [hs']
    by_cases hj : j = Fin.last n
    · subst hj
      rw [ite_eq_left rfl]
      exact hg.2 _
    · rw [ite_eq_right hj]
      have hlt : j.castSucc < (Fin.last n).castSucc :=
        Fin.castSucc_lt_castSucc_iff.mpr (lt_of_le_of_ne (Fin.le_last j) hj)
      exact hg.1 hlt
  obtain ⟨g', hg'⟩ := exists_successor_eq s hcol hrow
  have he : ∀ i j : Fin (n + 1), g'.val.val i j = g.val.val i.castSucc j.castSucc := by
    intro i j
    rw [← hs' i j, ← hg', successor_first]
  refine ⟨g', ⟨fun i j hji => ?_, fun i => ?_⟩, he, ?_⟩
  · rw [he]
    exact hg.1 (Fin.castSucc_lt_castSucc_iff.mpr hji)
  · rw [he]
    exact hg.2 _
  · rw [hg']
    change g = r * (r' * g)
    rw [← mul_assoc, hrr', one_mul]

end Matrices

/-! ## Whittaker equivariance of the top quotient -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

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
        phiMinusQuotient T ψ n X (X.representation g w) =
          ψ.complex (c (Fin.last n)) •
            ((phiMinus T ψ n).obj X).representation g' (phiMinusQuotient T ψ n X w) := by
  let _ := T.topology
  intro X g c g' hg' hdec w
  subst hdec
  rw [map_mul, Module.End.mul_apply, phiMinusQuotient_radical, phiMinus_action,
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
        psiMinusQuotient T 0 ((phiMinusIterate T ψ 0 j).obj X)
            (iterateQuotient T ψ 0 j X (X.representation u v)) =
          (Whittaker.standardCharacter ψ (0 + j) ⟨u.val, hu⟩ : ℂ) •
            psiMinusQuotient T 0 ((phiMinusIterate T ψ 0 j).obj X)
              (iterateQuotient T ψ 0 j X v) := by
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
      exact psiMinusQuotient_radical T 0 X ⟨u, hr⟩ v
  | succ j ih =>
      intro X u hu v
      obtain ⟨u', hu', he, hdec⟩ := exists_radical_mul_successor_upper (n := 0 + j) u hu
      have hq : phiMinusQuotient T ψ (0 + j) X (X.representation u v) =
          ψ.complex (u.val.val (Fin.last (0 + j)).castSucc (Fin.last (0 + j + 1))) •
            ((phiMinus T ψ (0 + j)).obj X).representation u'
              (phiMinusQuotient T ψ (0 + j) X v) :=
        phiMinusQuotient_eq_of_eq_radical_mul_successor T ψ (n := 0 + j) X u _ u' hu' hdec v
      have hsum : (∑ i : Fin (0 + j + 1), u.val.val i.castSucc i.succ) =
          (∑ i : Fin (0 + j), u'.val.val i.castSucc i.succ) +
            u.val.val (Fin.last (0 + j)).castSucc (Fin.last (0 + j + 1)) := by
        rw [Fin.sum_univ_castSucc, Fin.succ_last]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [he, Fin.succ_castSucc]
      change psiMinusQuotient T 0
          ((phiMinusIterate T ψ 0 j).obj ((phiMinus T ψ (0 + j)).obj X))
          (iterateQuotient T ψ 0 j ((phiMinus T ψ (0 + j)).obj X)
            (phiMinusQuotient T ψ (0 + j) X (X.representation u v))) =
        (Whittaker.standardCharacter ψ (0 + j + 1) ⟨u.val, hu⟩ : ℂ) •
          psiMinusQuotient T 0
            ((phiMinusIterate T ψ 0 j).obj ((phiMinus T ψ (0 + j)).obj X))
            (iterateQuotient T ψ 0 j ((phiMinus T ψ (0 + j)).obj X)
              (phiMinusQuotient T ψ (0 + j) X v))
      have h2 := ih ((phiMinus T ψ (0 + j)).obj X) u' hu' (phiMinusQuotient T ψ (0 + j) X v)
      have h3 : ∀ (c : ℂ) (w : (phiMinus T ψ (0 + j)).obj X),
          psiMinusQuotient T 0 ((phiMinusIterate T ψ 0 j).obj ((phiMinus T ψ (0 + j)).obj X))
              (iterateQuotient T ψ 0 j ((phiMinus T ψ (0 + j)).obj X) (c • w)) =
            c • psiMinusQuotient T 0
              ((phiMinusIterate T ψ 0 j).obj ((phiMinus T ψ (0 + j)).obj X))
              (iterateQuotient T ψ 0 j ((phiMinus T ψ (0 + j)).obj X) w) := fun c w => by
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
      A →ₗ[ℂ] (generalLinearDerivativePositive T ψ 0 n).obj A := fun A =>
  letI := T.topology
  psiMinusQuotient T 0 ((phiMinusIterate T ψ 0 n).obj ((generalLinearRestriction T (0 + n)).obj A))
    ∘ₗ iterateQuotient T ψ 0 n ((generalLinearRestriction T (0 + n)).obj A)

theorem topQuotient_surjective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier),
      Function.Surjective (topQuotient T ψ n A) := by
  let _ := T.topology
  intro A
  exact (psiMinusQuotient_surjective T 0 _).comp (iterateQuotient_surjective T ψ 0 n _)

/-- Every functional on the top derivative pulls back to a standard Whittaker functional. -/
theorem comp_topQuotient_mem_glFunctionals (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (0 + n + 1) F.Carrier))
      (f : Module.Dual ℂ ((generalLinearDerivativePositive T ψ 0 n).obj A)),
        f ∘ₗ topQuotient T ψ n A ∈ Whittaker.glFunctionals ψ (0 + n) A.representation := by
  let _ := T.topology
  intro A f u v
  have hP : (u : GeneralLinear (0 + n + 1) F.Carrier) ∈ mirabolic (0 + n) F.Carrier :=
    upperUnipotent_le_mirabolic u.property
  have key := psiMinusQuotient_iterateQuotient_upper T ψ n
    ((generalLinearRestriction T (0 + n)).obj A) ⟨u.val, hP⟩ u.property v
  change f (psiMinusQuotient T 0 _ (iterateQuotient T ψ 0 n _
      (((generalLinearRestriction T (0 + n)).obj A).representation ⟨u.val, hP⟩ v))) =
    (Whittaker.standardCharacter ψ (0 + n) u : ℂ) * f (topQuotient T ψ n A v)
  rw [key]
  exact f.map_smul _ _

/-! ## Nonvanishing of the top derivative -/

/-- An irreducible representation is nonzero. -/
theorem nontrivial_of_isIrreducible {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) : Nontrivial V := by
  have := (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
  exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule

theorem phiMinus_obj_heq (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (Y : SmoothRep.{0, uF, uV} ℂ (mirabolic (a + 1) F.Carrier))
      (Y' : SmoothRep.{0, uF, uV} ℂ (mirabolic (b + 1) F.Carrier)),
      HEq Y Y' → HEq ((phiMinus T ψ a).obj Y) ((phiMinus T ψ b).obj Y') := by
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
          (phiMinusIterate T ψ m (j + 1)).obj Y =
            (phiMinus T ψ m).obj ((phiMinusIterate T ψ (m + 1) j).obj Y')
  | 0 => fun m Y Y' hY => by
      let _ := T.topology
      obtain rfl := eq_of_heq hY
      rfl
  | j + 1 => fun m Y Y' hY => by
      let _ := T.topology
      exact phiMinusIterate_obj_succ_bottom T ψ j m ((phiMinus T ψ (m + (j + 1))).obj Y)
        ((phiMinus T ψ (m + 1 + j)).obj Y')
        (phiMinus_obj_heq T ψ (a := m + (j + 1)) (b := m + 1 + j) (by omega) Y Y' hY)

theorem generalLinearRestriction_rankCast_heq (T : F.TopologicalData) {a b : ℕ} (h : a = b)
    (h' : a + 1 = b + 1) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (a + 1) F.Carrier),
      HEq ((generalLinearRestriction T a).obj A)
        ((generalLinearRestriction T b).obj ((generalLinearRankCast T h').obj A)) := by
  subst h
  intro A
  exact HEq.rfl

theorem nontrivial_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      Nontrivial A → Nontrivial ((generalLinearRankCast T h).obj A) := by
  subst h
  intro A hA
  exact hA

theorem isIrreducible_rankCast (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier),
      A.IsIrreducible → ((generalLinearRankCast T h).obj A).IsIrreducible := by
  subst h
  intro A hA
  exact hA

/-- For supercuspidal nonzero `A` on `GL_(m+j+1)`, `(Φ⁻)^j (A|P)` is nonzero. -/
theorem nontrivial_phiMinusIterate (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    ∀ (j m : ℕ), letI := T.topology
      ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + j + 1) F.Carrier),
        IsSupercuspidal A.representation → Nontrivial A →
          Nontrivial ((phiMinusIterate T ψ m j).obj ((generalLinearRestriction T (m + j)).obj A))
  | 0 => fun _ _ _ hA => by
      let _ := T.topology
      exact hA
  | j + 1 => fun m A hsc hA => by
      let _ := T.topology
      have h' : m + (j + 1) + 1 = m + 1 + j + 1 := by omega
      have hsc' := isSupercuspidal_rankCast T h' A hsc
      have hA' := nontrivial_rankCast T h' A hA
      have hZ := nontrivial_phiMinusIterate T ψ j (m + 1) _ hsc' hA'
      have hΨ : Subsingleton ((psiMinus T (m + 1)).obj ((phiMinusIterate T ψ (m + 1) j).obj
          ((generalLinearRestriction T (m + 1 + j)).obj
            ((generalLinearRankCast T h').obj A)))) :=
        subsingleton_generalLinearDerivativePositive T ψ (m + 1) j (Nat.succ_pos m) _ hsc'
      have hΦ : Nontrivial ((phiMinus T ψ m).obj ((phiMinusIterate T ψ (m + 1) j).obj
          ((generalLinearRestriction T (m + 1 + j)).obj
            ((generalLinearRankCast T h').obj A)))) := by
        rw [← not_subsingleton_iff_nontrivial] at hZ ⊢
        exact fun hs => hZ (subsingleton_of_psiMinus_phiMinus T ψ m _ hΨ hs)
      rw [phiMinusIterate_obj_succ_bottom T ψ j m _ _
        (generalLinearRestriction_rankCast_heq T (a := m + (j + 1)) (b := m + 1 + j)
          (by omega) h' A)]
      exact hΦ

/-- `Ψ⁻` at `P_1`, the trivial group, is injective. -/
theorem psiMinusQuotient_zero_injective (T : F.TopologicalData) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier),
      Function.Injective (psiMinusQuotient T 0 X) := by
  let _ := T.topology
  intro X
  rw [← LinearMap.ker_eq_bot, ker_psiMinusQuotient, eq_bot_iff,
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
        Nontrivial ((generalLinearDerivativePositive T ψ 0 n).obj A) := by
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
        Nontrivial ((generalLinearDerivative T ψ (n + 1) (n + 1) le_rfl).obj A) := by
  let _ := T.topology
  intro A hsc hA
  have key : ∀ (m : ℕ) (hm : m = 0) (h : n + 1 = m + n + 1),
      Nontrivial ((generalLinearDerivativePositive T ψ m n).obj
        ((generalLinearRankCast T h).obj A)) := by
    intro m hm h
    subst hm
    exact nontrivial_generalLinearDerivativePositive_top T ψ n _
      (isSupercuspidal_rankCast T h A hsc) (nontrivial_rankCast T h A hA)
  exact key (n + 1 - (n + 1)) (Nat.sub_self _) (rank_eq_of_succ_le le_rfl)

end Langlands.Classification.SupercuspidalTopDerivative
