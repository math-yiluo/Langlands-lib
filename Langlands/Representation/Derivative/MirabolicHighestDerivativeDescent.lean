import Langlands.Representation.Derivative.MirabolicDerivativeVanishing
import Langlands.Representation.Filtration.InvariantBilinear

/-!
# Radical triviality and `Ψ⁻` descent of pairings

Two inputs to Bernstein–Zelevinsky (1977), Proposition 3.8.

* If `Φ⁻ X = 0` for a smooth representation `X` of `P_(m+2)`, the radical `V_(m+2)` acts
  trivially on `X`: each difference `ρ(u) x - x` lies in the relations of every coordinate
  character, so the finite Fourier inversion of `MinusVanishing` kills it.
* If the radical acts trivially on `A`, a left-nondegenerate pairing of `A` and `B` with
  covariance `|det|` descends to a left-nondegenerate invariant pairing of the normalized
  `Ψ⁻` quotients; the two `|det|^(-1/2)` twists cancel the covariance.

See the paired Markdown.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis Topology Jacquet.Localization
open scoped Matrix NNReal

universe uF uV uW

/-! ## Radical triviality from vanishing `Φ⁻` -/

section Radical

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A vector of a smooth representation of `P_(m+2)` lying in the relations of every
coordinate character of the radical is zero. -/
theorem eq_zero_of_forall_mem_relations (m : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) :
    letI := T.topology
    haveI := T.generalLinearTopologicalGroup (m + 1 + 1)
    IsSmooth ρ → ∀ x : V,
      (∀ a : Fin (m + 1) → F.Carrier,
        x ∈ relations ρ (radical (m + 1) F.Carrier) (coordinateCharacter T ψ m a)) →
      x = 0 := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro hρ x hall
  -- A radical lattice box fixing `x`.
  obtain ⟨K, hK⟩ := hρ x
  have hfix : ∀ k ∈ K, ρ k x = x := fun k hk =>
    (Representation.mem_invariants _ x).mp hK ⟨k, hk⟩
  have hrad0 : {d : Fin (m + 1) → F.Carrier |
      (radicalElement d : mirabolic (m + 1) F.Carrier) ∈ K} ∈ 𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  have hx : ∀ u : radical (m + 1) F.Carrier,
      radicalCoordinates u ∈ latticeBox T (m + 1) l → ρ u x = x := by
    intro u hu
    have h := hfix _ (hl hu)
    rwa [radicalElement_coordinates] at h
  -- Each coordinate character eventually kills `x` along the radical boxes.
  have hcover : ∀ n : radical (m + 1) F.Carrier, ∃ k : ℕ, n ∈ radicalBox T m k := by
    intro n
    obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates n)
    exact ⟨M.toNat, radicalBox_mono T m (Int.self_le_toNat M) hM⟩
  have hev : ∀ a : Fin (m + 1) → F.Carrier, ∃ M : ℤ,
      characterAverage hρ (isOpen_ker_coordinateCharacter T ψ m a) (radicalBox T m M)
        (isCompact_radicalBox T m M) x = 0 := by
    intro a
    obtain ⟨k₀, hk₀⟩ := eventually_characterAverage_eq_zero hρ
      (isOpen_ker_coordinateCharacter T ψ m a) (fun k : ℕ => radicalBox T m k)
      (fun k => isCompact_radicalBox T m k)
      (fun j k hjk => radicalBox_mono T m (Nat.cast_le.mpr hjk)) hcover (hall a)
    exact ⟨k₀, hk₀ k₀ le_rfl⟩
  obtain ⟨M, hM⟩ := exists_forall_characterAverage_eq_zero T ψ m ρ x
    (T.additiveConductor ψ - l) hρ hev
  exact eq_zero_of_forall_characterAverage_eq_zero T ψ m ρ x l M hρ hx hM

/-- BZ77 §3.2(e): if `Φ⁻ X = 0` for a smooth representation `X` of `P_(m+2)`, the
radical `V_(m+2)` acts trivially on `X`. -/
theorem radical_acts_trivially_of_phiMinus (m : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier),
      Subsingleton ((Mirabolic.phiMinus T ψ m).obj X) →
      ∀ (u : radical (m + 1) F.Carrier) (v : X),
        X.representation (u : mirabolic (m + 1) F.Carrier) v = v := by
  let := T.topology
  have := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro X h2 u v
  let ρ := X.representation
  change Subsingleton (Coinvariants ρ (radical (m + 1) F.Carrier) (T.mirabolicTheta ψ m)) at h2
  have hrelθ := Submodule.Quotient.subsingleton_iff.mp h2
  have hall : ∀ a : Fin (m + 1) → F.Carrier,
      ρ u v - v ∈ relations ρ (radical (m + 1) F.Carrier) (coordinateCharacter T ψ m a) := by
    intro a
    by_cases ha : a = 0
    · rw [ha, coordinateCharacter_zero]
      have h := sub_mem_relations ρ (radical (m + 1) F.Carrier) 1 u v
      simpa using h
    · obtain ⟨g, hg⟩ := exists_lastRow_eq_of_ne_zero a ha
      have hv := levi_inv_mem_relations T ψ m ρ g (v := ρ (levi g) (ρ u v - v))
        (by rw [hrelθ]; exact Submodule.mem_top)
      rw [hg, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
        Module.End.one_apply] at hv
      exact hv
  exact sub_eq_zero.mp (eq_zero_of_forall_mem_relations T ψ m ρ X.isSmooth _ hall)

end Radical

/-! ## Descent of pairings through `Ψ⁻` -/

section PsiDescent

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The Levi embedding `g ↦ diag(g, 1)` preserves the normalized determinant norm. -/
theorem determinantNorm_levi (n : ℕ) (g : GeneralLinear n F.Carrier) :
    T.determinantNorm (n + 1) (levi g : mirabolic n F.Carrier).val = T.determinantNorm n g := by
  have h : GeneralLinear.determinant (levi g : mirabolic n F.Carrier).val =
      GeneralLinear.determinant g := by
    apply Units.ext
    change Matrix.det (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks g.val 0 0 (1 : GeneralLinear 1 F.Carrier).val)) = Matrix.det g.val
    rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Units.val_one, Matrix.det_one,
      mul_one]
  change T.normalizedAbsUnits (GeneralLinear.determinant (levi g : mirabolic n F.Carrier).val) =
    T.normalizedAbsUnits (GeneralLinear.determinant g)
  rw [h]

/-- Radical elements have normalized determinant norm one. -/
theorem determinantNorm_radical (n : ℕ) (u : radical n F.Carrier) :
    T.determinantNorm (n + 1) (u : mirabolic n F.Carrier).val = 1 := by
  have h : GeneralLinear.determinant (u : mirabolic n F.Carrier).val = 1 := by
    apply Units.ext
    exact RankinSelberg.unipotent_det (radicalToUpperUnipotent u)
  change T.normalizedAbsUnits (GeneralLinear.determinant (u : mirabolic n F.Carrier).val) = 1
  rw [h, map_one]

/-- `r^(-1/2) · r^(-1/2) · r = 1` for `r > 0`, in `ℂ`. -/
theorem half_power_mul_half_power_mul_self {r : ℝ} (hr : 0 < r) :
    ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ((r ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (r : ℂ) = 1 := by
  have h : r ^ (-(1 / 2 : ℝ)) * r ^ (-(1 / 2 : ℝ)) * r = 1 := by
    rw [← Real.rpow_add hr, show (-(1 / 2 : ℝ)) + -(1 / 2) = -1 by norm_num, Real.rpow_neg_one,
      inv_mul_cancel₀ hr.ne']
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at h'
  exact h'

/-- The bilinear form on trivial-character coinvariants induced by `β`, when the radical
acts trivially on the first factor and `β` is radical-invariant. -/
def psiMinusDescendedForm (n : ℕ) {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (mirabolic n F.Carrier) V)
    (σ : Representation ℂ (mirabolic n F.Carrier) W)
    (hρ : ∀ (u : radical n F.Carrier) (v : V), ρ (u : mirabolic n F.Carrier) v = v)
    (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hβ : ∀ (u : radical n F.Carrier) (v : V) (w : W),
      β (ρ (u : mirabolic n F.Carrier) v) (σ (u : mirabolic n F.Carrier) w) = β v w) :
    Coinvariants ρ (radical n F.Carrier) 1 →ₗ[ℂ]
      Coinvariants σ (radical n F.Carrier) 1 →ₗ[ℂ] ℂ :=
  lift ρ (radical n F.Carrier) 1
    (lift σ (radical n F.Carrier) 1 β.flip (fun u w => by
      ext v
      simp only [LinearMap.flip_apply, MonoidHom.one_apply, Units.val_one, one_smul]
      rw [← hβ u v w, hρ u v])).flip
    (fun u v => by
      ext w
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.flip_apply,
        MonoidHom.one_apply, Units.val_one, one_smul, Submodule.mkQ_apply]
      rw [hρ u v])

theorem psiMinusDescendedForm_mk (n : ℕ) {V : Type uV} {W : Type uW} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (mirabolic n F.Carrier) V)
    (σ : Representation ℂ (mirabolic n F.Carrier) W)
    (hρ : ∀ (u : radical n F.Carrier) (v : V), ρ (u : mirabolic n F.Carrier) v = v)
    (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (hβ : ∀ (u : radical n F.Carrier) (v : V) (w : W),
      β (ρ (u : mirabolic n F.Carrier) v) (σ (u : mirabolic n F.Carrier) w) = β v w)
    (v : V) (w : W) :
    psiMinusDescendedForm n ρ σ hρ β hβ (mk ρ (radical n F.Carrier) 1 v)
      (mk σ (radical n F.Carrier) 1 w) = β v w :=
  rfl

/-- BZ77 3.7(a) for a representation on which the radical acts trivially: a
left-nondegenerate pairing with covariance `|det|` descends to a left-nondegenerate
invariant pairing of the normalized `Ψ⁻` quotients. -/
theorem psiMinus_nondegeneratePairing (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (B : SmoothRep.{0, uF, uW} ℂ (mirabolic n F.Carrier)),
      (∀ (u : radical n F.Carrier) (v : A),
        A.representation (u : mirabolic n F.Carrier) v = v) →
      ∀ β : InvariantBilinear.forms A.representation B.representation
          (fun g => ((((T.determinantNorm (n + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
        ∃ γ : InvariantBilinear.forms ((Mirabolic.psiMinus T n).obj A).representation
            ((Mirabolic.psiMinus T n).obj B).representation (fun _ => (1 : ℂ)),
          ∀ v : (Mirabolic.psiMinus T n).obj A,
            (∀ w : (Mirabolic.psiMinus T n).obj B, γ.val v w = 0) → v = 0 := by
  let := T.topology
  intro A B hA β hβ
  have hinv : ∀ (u : radical n F.Carrier) (v : A) (w : B),
      β.val (A.representation (u : mirabolic n F.Carrier) v)
        (B.representation (u : mirabolic n F.Carrier) w) = β.val v w := by
    intro u v w
    rw [β.property (u : mirabolic n F.Carrier) v w]
    dsimp only
    rw [determinantNorm_radical]
    simp
  let γ₀ := psiMinusDescendedForm n A.representation B.representation hA β.val hinv
  refine ⟨⟨γ₀, ?_⟩, ?_⟩
  · intro g x y
    obtain ⟨v, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T n A x
    obtain ⟨w, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T n B y
    rw [Mirabolic.psiMinus_action, Mirabolic.psiMinus_action]
    change γ₀ (_ • mk _ _ 1 _) (_ • mk _ _ 1 _) = 1 * γ₀ (mk _ _ 1 v) (mk _ _ 1 w)
    simp only [map_smul, LinearMap.smul_apply]
    change _ • _ • β.val (A.representation (levi g) v) (B.representation (levi g) w) =
      1 * β.val v w
    rw [β.property (levi g) v w]
    dsimp only
    rw [determinantNorm_levi, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
      coe_realPowerCharacter]
    have hr : 0 < (((T.determinantNorm n g : ℝ≥0ˣ) : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (T.determinantNorm n g).ne_zero)
    rw [half_power_mul_half_power_mul_self hr]
  · intro x hx
    obtain ⟨v, rfl⟩ := Mirabolic.psiMinusQuotient_surjective T n A x
    have hv : v = 0 := by
      refine hβ v fun w => ?_
      exact hx (Mirabolic.psiMinusQuotient T n B w)
    subst hv
    exact map_zero _

end PsiDescent

end Langlands.Derivative.Mirabolic
