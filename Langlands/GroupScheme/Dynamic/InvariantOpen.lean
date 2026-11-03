import Langlands.GroupScheme.Dynamic.AffineExtension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-! # Scalar invariant open subsets of the affine line -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.GroupScheme.AffineLine

variable {k : Type u} [Field k]

/-- The point of the affine line defined by evaluation at an element of a field extension. -/
def fieldPoint {K : Type u} [Field K] (f : k →+* K) (x : K) :
    PrimeSpectrum (Polynomial k) :=
  PrimeSpectrum.comap (Polynomial.eval₂RingHom f x) ⊥

/-- Scalar invariance on points over every field extension, including nonclosed points. -/
def IsScalarInvariantOpen (W : Opens (PrimeSpectrum (Polynomial k))) : Prop :=
  ∀ (K : Type u) [Field K] (f : k →+* K) (x : K) (a : Kˣ),
    fieldPoint f ((a : K) * x) ∈ W ↔ fieldPoint f x ∈ W

/-- A rational affine-line point has the same underlying point after extending the field. -/
theorem fieldPoint_map {K : Type u} [Field K] (f : k →+* K) (x : k) :
    fieldPoint f (f x) = fieldPoint (RingHom.id k) x := by
  have he : Polynomial.eval₂RingHom f (f x) = f.comp (Polynomial.evalRingHom x) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  have hb : PrimeSpectrum.comap f (⊥ : PrimeSpectrum K) = (⊥ : PrimeSpectrum k) :=
    Subsingleton.elim _ _
  rw [fieldPoint, he, PrimeSpectrum.comap_comp_apply, hb]
  rfl

/-- Every scheme point is obtained by evaluation in its own residue field. -/
theorem exists_fieldPoint (p : PrimeSpectrum (Polynomial k)) :
    ∃ (K : Type u) (_ : Field K) (f : k →+* K) (x : K), fieldPoint f x = p := by
  let K := p.asIdeal.ResidueField
  let g : Polynomial k →+* K := algebraMap (Polynomial k) K
  let f : k →+* K := g.comp Polynomial.C
  have he : Polynomial.eval₂RingHom f (g Polynomial.X) = g := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [f]
    · simp
  refine ⟨K, inferInstance, f, g Polynomial.X, ?_⟩
  change PrimeSpectrum.comap (Polynomial.eval₂RingHom f (g Polynomial.X)) ⊥ = p
  rw [he]
  exact Set.mem_singleton_iff.1 ((PrimeSpectrum.residueField_comap p) ▸
    Set.mem_range_self (⊥ : PrimeSpectrum K))

/-- The generic affine-line point is evaluation at a nonzero element of the fraction field. -/
theorem exists_unit_fieldPoint_eq_generic :
    ∃ (K : Type u) (_ : Field K) (f : k →+* K) (a : Kˣ),
      fieldPoint f (a : K) = (⊥ : PrimeSpectrum (Polynomial k)) := by
  let K := FractionRing (Polynomial k)
  let g : Polynomial k →+* K := algebraMap (Polynomial k) K
  let f : k →+* K := g.comp Polynomial.C
  have hx : g Polynomial.X ≠ 0 := by
    exact (map_ne_zero_iff g (IsFractionRing.injective (Polynomial k) K)).2 Polynomial.X_ne_zero
  let a : Kˣ := Units.mk0 (g Polynomial.X) hx
  refine ⟨K, inferInstance, f, a, ?_⟩
  change PrimeSpectrum.comap (Polynomial.eval₂RingHom f (g Polynomial.X)) ⊥ = ⊥
  have he : Polynomial.eval₂RingHom f (g Polynomial.X) = g := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [f]
    · simp
  rw [he]
  apply PrimeSpectrum.ext
  exact (RingHom.ker_eq_comap_bot g).symm.trans
    ((RingHom.ker_eq_bot_iff_eq_zero g).2 fun x hx =>
      (IsFractionRing.injective (Polynomial k) K) (hx.trans (map_zero g).symm))

/-- An open subset containing zero and invariant under all nonzero scalar multiplications
is the whole affine line, over finite and infinite fields alike. -/
theorem eq_top_of_isScalarInvariantOpen
    (W : Opens (PrimeSpectrum (Polynomial k)))
    (hW : IsScalarInvariantOpen W) (h0 : fieldPoint (RingHom.id k) 0 ∈ W) : W = ⊤ := by
  have hgen : IsGenericPoint (⊥ : PrimeSpectrum (Polynomial k)) Set.univ := by
    rw [isGenericPoint_def, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      PrimeSpectrum.vanishingIdeal_singleton, ← PrimeSpectrum.zeroLocus_singleton_zero]
    rfl
  have hη : (⊥ : PrimeSpectrum (Polynomial k)) ∈ W :=
    (hgen.mem_open_set_iff W.isOpen).2 ⟨_, Set.mem_univ _, h0⟩
  obtain ⟨K, hK, f, a, ha⟩ := exists_unit_fieldPoint_eq_generic (k := k)
  let := hK
  have h1 : fieldPoint (RingHom.id k) 1 ∈ W := by
    have hh : fieldPoint f (1 : K) ∈ W :=
      (hW K f 1 a).1 (by simpa [mul_one, ha] using hη)
    simpa only [← map_one f, fieldPoint_map] using hh
  apply top_unique
  intro p _
  obtain ⟨L, hL, g, x, rfl⟩ := exists_fieldPoint p
  let := hL
  by_cases hx : x = 0
  · simpa only [hx, ← map_zero g, fieldPoint_map] using h0
  · simpa only [Units.val_mk0, mul_one] using (hW L g 1 (Units.mk0 x hx)).2
      (by simpa only [← map_one g, fieldPoint_map] using h1)

/-- A map whose pullback of an open immersion is scalar invariant and contains zero
has its entire image in that open immersion. -/
theorem range_subset_of_isScalarInvariantOpen {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (e : Spec (CommRingCat.of (Polynomial k)) ⟶ X)
    (hinv : IsScalarInvariantOpen (e ⁻¹ᵁ j.opensRange))
    (h0 : e (fieldPoint (RingHom.id k) 0) ∈ j.opensRange) :
    Set.range e ⊆ Set.range j := by
  have htop : e ⁻¹ᵁ j.opensRange = ⊤ :=
    eq_top_of_isScalarInvariantOpen _ hinv h0
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ e ⁻¹ᵁ j.opensRange := by
    rw [htop]
    trivial
  exact hp

/-- The actual lift through an open immersion of a scalar-invariant affine-line map
whose value at zero lies in the open. -/
def invariantOpenLift {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (e : Spec (CommRingCat.of (Polynomial k)) ⟶ X)
    (hinv : IsScalarInvariantOpen (e ⁻¹ᵁ j.opensRange))
    (h0 : e (fieldPoint (RingHom.id k) 0) ∈ j.opensRange) :
    Spec (CommRingCat.of (Polynomial k)) ⟶ U :=
  IsOpenImmersion.lift j e (range_subset_of_isScalarInvariantOpen j e hinv h0)

@[reassoc]
theorem invariantOpenLift_fac {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (e : Spec (CommRingCat.of (Polynomial k)) ⟶ X)
    (hinv : IsScalarInvariantOpen (e ⁻¹ᵁ j.opensRange))
    (h0 : e (fieldPoint (RingHom.id k) 0) ∈ j.opensRange) :
    invariantOpenLift j e hinv h0 ≫ j = e :=
  IsOpenImmersion.lift_fac j e _

end Langlands.GroupScheme.AffineLine
