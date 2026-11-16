import Langlands.GroupScheme.Reductive.RankOneRingSquareRoots
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Fppf covers adjoining roots of finitely many units -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.UnitPowerExtension

variable {R : Type u} [CommRing R]

/-- The monic equation adjoining an `n`-th root of a unit. -/
def polynomial (n : ℕ) (a : Rˣ) : Polynomial R := Polynomial.X ^ n - Polynomial.C (a : R)

/-- The finite free extension defined by the unit-root equation. -/
abbrev Ring (n : ℕ) (a : Rˣ) := AdjoinRoot (polynomial n a)

/-- The coefficient map to the unit-root extension. -/
def inclusion (n : ℕ) (a : Rˣ) : R →+* Ring n a := AdjoinRoot.of (polynomial n a)

theorem inclusion_injective (n : ℕ) (hn : n ≠ 0) (a : Rˣ) :
    Function.Injective (inclusion n a) := by
  cases subsingleton_or_nontrivial R with
  | inl h => exact Function.injective_of_subsingleton _
  | inr h =>
    apply AdjoinRoot.of.injective_of_monic_of_degree_pos
    · exact Polynomial.monic_X_pow_sub_C _ hn
    · rw [polynomial, Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.pos_of_ne_zero hn

/-- The coefficient map is faithfully flat, including over the zero ring. -/
theorem inclusion_faithfullyFlat (n : ℕ) (hn : n ≠ 0) (a : Rˣ) :
    (inclusion n a).FaithfullyFlat := by
  cases subsingleton_or_nontrivial R with
  | inl h =>
    have : Subsingleton (Ring n a) := subsingleton_of_zero_eq_one (by
      rw [← (inclusion n a).map_zero, ← (inclusion n a).map_one, Subsingleton.elim (0 : R) 1])
    apply RingHom.FaithfullyFlat.of_bijective
    refine ⟨Function.injective_of_subsingleton _, fun x => ⟨0, ?_⟩⟩
    exact Subsingleton.elim _ _
  | inr h =>
    have : Module.Free R (Ring n a) := (Polynomial.monic_X_pow_sub_C (a : R) hn).free_adjoinRoot
    have : Nontrivial (Ring n a) := Function.Injective.nontrivial (inclusion_injective n hn a)
    exact RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance

/-- The coefficient map is finitely presented. -/
theorem inclusion_finitePresentation (n : ℕ) (a : Rˣ) :
    (inclusion n a).FinitePresentation :=
  RingHom.finitePresentation_algebraMap.mpr inferInstance

theorem root_pow (n : ℕ) (a : Rˣ) :
    AdjoinRoot.root (polynomial n a) ^ n = inclusion n a (a : R) := by
  have h := AdjoinRoot.eval₂_root (polynomial n a)
  change (Polynomial.X ^ n - Polynomial.C (a : R)).eval₂ (inclusion n a)
    (AdjoinRoot.root (polynomial n a)) = 0 at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The adjoined root of a unit is itself a unit. -/
def rootUnit (n : ℕ) (hn : n ≠ 0) (a : Rˣ) : (Ring n a)ˣ :=
  ((isUnit_pow_iff hn).mp ((root_pow n a).symm ▸ a.isUnit.map (inclusion n a))).unit

theorem rootUnit_pow (n : ℕ) (hn : n ≠ 0) (a : Rˣ) :
    rootUnit n hn a ^ n = Units.map (inclusion n a).toMonoidHom a := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, rootUnit, IsUnit.unit_spec, Units.coe_map]
  exact root_pow n a

/-- Finitely many units admit simultaneous roots in a faithfully flat finitely
presented extension. -/
theorem exists_roots (n : ℕ) (hn : n ≠ 0) {m : ℕ} (a : Fin m → Rˣ) :
    ∃ (B : Type u) (_ : CommRing B) (f : R →+* B),
      f.FaithfullyFlat ∧ f.FinitePresentation ∧
      ∃ r : Fin m → Bˣ, ∀ j, r j ^ n = Units.map f.toMonoidHom (a j) := by
  induction m with
  | zero =>
    exact ⟨R, inferInstance, RingHom.id R,
      RingHom.FaithfullyFlat.of_bijective Function.bijective_id,
      RingHom.FinitePresentation.id R, Fin.elim0, fun j => Fin.elim0 j⟩
  | succ m ih =>
    obtain ⟨B, hB, f, hf, hfp, r, hr⟩ := ih (Fin.tail a)
    let b := Units.map f.toMonoidHom (a 0)
    let g := inclusion n b
    refine ⟨Ring n b, inferInstance, g.comp f,
      RingHom.FaithfullyFlat.stableUnderComposition f g hf (inclusion_faithfullyFlat n hn b),
      (inclusion_finitePresentation n b).comp hfp,
      Fin.cons (rootUnit n hn b) (fun j => Units.map g.toMonoidHom (r j)), ?_⟩
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact rootUnit_pow n hn b
    · change Units.map g.toMonoidHom (r i) ^ n = _
      rw [← map_pow, hr]
      rfl

end Langlands.GroupScheme.UnitPowerExtension

namespace Langlands.GroupScheme.UnitPowerExtension

/-- An affine test admits a surjective fppf refinement on which a finite list
of units has simultaneous prescribed positive roots. -/
theorem exists_roots_test {S : Scheme.{u}} (Z : Over S) [IsAffine Z.left]
    (n : ℕ) (hn : n ≠ 0) {m : ℕ} (a : Fin m → Γ(Z.left, ⊤)ˣ) :
    ∃ (W : Over S) (j : W ⟶ Z), IsAffine W.left ∧
      Flat j.left ∧ Surjective j.left ∧ LocallyOfFinitePresentation j.left ∧
      ∃ r : Fin m → Γ(W.left, ⊤)ˣ,
        ∀ i, r i ^ n = Units.map j.left.appTop.hom.toMonoidHom (a i) := by
  obtain ⟨B, hB, f, hf, hfp, r, hr⟩ := exists_roots n hn a
  let φ : Γ(Z.left, ⊤) ⟶ CommRingCat.of B := CommRingCat.ofHom f
  let j₀ : Spec (CommRingCat.of B) ⟶ Z.left := Spec.map φ ≫ Z.left.isoSpec.inv
  let W : Over S := Over.mk (j₀ ≫ Z.hom)
  let j : W ⟶ Z := Over.homMk j₀
  have hflat := (flat_and_surjective_SpecMap_iff φ).mpr hf
  have : Flat (Spec.map φ) := hflat.1
  have : Surjective (Spec.map φ) := hflat.2
  have : LocallyOfFinitePresentation (Spec.map φ) :=
    (LocallyOfFinitePresentation.SpecMap_iff φ).mpr hfp
  have hj : j.left.appTop = φ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv :=
    RingRootCell.appTop_specMap_isoSpec_inv φ
  refine ⟨W, j, inferInstanceAs (IsAffine (Spec (CommRingCat.of B))), inferInstanceAs (Flat j₀),
    inferInstanceAs (Surjective j₀), inferInstanceAs (LocallyOfFinitePresentation j₀),
    fun i => Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom (r i), ?_⟩
  intro i
  rw [← map_pow, hr, hj]
  rfl

end Langlands.GroupScheme.UnitPowerExtension
