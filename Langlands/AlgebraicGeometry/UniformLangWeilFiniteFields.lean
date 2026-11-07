import Langlands.AlgebraicGeometry.UniformLangWeilFieldPoints
import Langlands.AlgebraicGeometry.SchemePureDimensionProof
import Mathlib.FieldTheory.Finite.Basic

/-! # Uniform lifting over all sufficiently large finite fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A finite field is a quotient of the integer polynomial ring in one variable. -/
theorem exists_surjective_integer_polynomial_map (K : Type u) [Field K] [Finite K] :
    ∃ φ : Polynomial (ULift.{u} ℤ) →+* K, Function.Surjective φ := by
  classical
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  let c : ULift.{u} ℤ →+* K := (Int.castRingHom K).comp ULift.ringEquiv.toRingHom
  refine ⟨Polynomial.eval₂RingHom c (a : K), ?_⟩
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  · have hpow : ∀ y : Kˣ, y ∈ Submonoid.powers a := by
      simpa only [mem_powers_iff_mem_zpowers] using ha
    obtain ⟨n, hn⟩ := hpow (Units.mk0 x hx)
    refine ⟨Polynomial.X ^ n, ?_⟩
    simpa using congrArg (fun y : Kˣ => (y : K)) hn

/-- A surjective affine coordinate map forces the image residue field of the
field-valued point to be the entire field of values. -/
theorem surjective_descResidueField_of_affine_coordinate
    {B : Scheme.{u}} {A K : Type u} [CommRing A] [Field K]
    (p : Spec (CommRingCat.of K) ⟶ B) (g : B ⟶ Spec (CommRingCat.of A))
    (φ : A →+* K) (hφ : Function.Surjective φ)
    (h : p ≫ g = Spec.map (CommRingCat.ofHom φ)) :
    Function.Surjective (B.descResidueField (Scheme.stalkClosedPointTo p)) := by
  let b := p (IsLocalRing.closedPoint K)
  let ρ := B.descResidueField (Scheme.stalkClosedPointTo p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (B.fromSpecResidueField b ≫ g)
  have heq : ψ ≫ ρ = CommRingCat.ofHom φ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, ← Category.assoc,
      Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    exact h
  have hsurj : Function.Surjective (ψ ≫ ρ) := by
    rw [heq]
    exact hφ
  exact Function.Surjective.of_comp hsurj

/-- Enlarge the base once by the integer affine line. A generating coordinate
then identifies the image residue field with any prescribed finite field. The
constant is uniform in that field and in its point of the original base. -/
def uniformLangWeilLargeFiniteFieldPointLifts
    (hLW : UniformLangWeilStatement.{u})
    (B Y : Scheme.{u}) (f : Y ⟶ B) (d : ℕ)
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (hBqc : CompactSpace B) (hsmooth : Smooth f)
    (hsep : _root_.AlgebraicGeometry.IsSeparated f) (hsurj : Surjective f)
    (hft : LocallyOfFiniteType f) (hqc : QuasiCompact f)
    (hconn : GeometricallyConnected f)
    (hdim : ∀ b : B, SchemeFiberGeometry.HasPureDimension (f.fiber b) d) :
    Σ C : {C : ℝ // 0 < C},
      (K : Type u) → [Field K] → [Finite K] →
        (p : Spec (CommRingCat.of K) ⟶ B) →
        C.1 ^ 2 < (Nat.card K : ℝ) →
        {q : Spec (CommRingCat.of K) ⟶ Y // q ≫ f = p} := by
  classical
  let := hBft
  let := hBqc
  let := hsmooth
  let := hsep
  let := hsurj
  let := hft
  let := hqc
  let := hconn
  let A := Polynomial (ULift.{u} ℤ)
  let π := specULiftZIsTerminal.{u}.from B
  let t : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ULift.{u} ℤ) A))
  have htft : LocallyOfFiniteType t := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := ULift.{u} ℤ) (B := A)).mpr inferInstance
  let := htft
  let B' := pullback π t
  let g : B' ⟶ B := pullback.fst π t
  let h : B' ⟶ Spec (CommRingCat.of A) := pullback.snd π t
  let Y' := pullback f g
  let f' : Y' ⟶ B' := pullback.snd f g
  have hB'ft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B') := by
    have : LocallyOfFiniteType (g ≫ π) := inferInstance
    convert this using 1
    exact specULiftZIsTerminal.{u}.hom_ext _ _
  have hdim' : ∀ b : B', SchemeFiberGeometry.HasPureDimension (f'.fiber b) d := by
    intro b
    exact (SchemeFiberGeometry.hasPureDimension_locallyFiniteType_fiberBaseChange_iff
      (IsPullback.of_hasPullback f g) b d).mpr (hdim (g b))
  let lifts := uniformLangWeilLargeResidueFieldPointLifts hLW B' Y' f' d hB'ft
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance hdim'
  refine ⟨lifts.1, fun K _ _ p hlarge => ?_⟩
  let φ := (exists_surjective_integer_polynomial_map K).choose
  have hφ : Function.Surjective φ :=
    (exists_surjective_integer_polynomial_map K).choose_spec
  let p' : Spec (CommRingCat.of K) ⟶ B' :=
    pullback.lift p (Spec.map (CommRingCat.ofHom φ))
      (specULiftZIsTerminal.{u}.hom_ext _ _)
  have hρ : Function.Surjective
      (B'.descResidueField (Scheme.stalkClosedPointTo p')) :=
    surjective_descResidueField_of_affine_coordinate p' h φ hφ
      (pullback.lift_snd _ _ _)
  have hcard : Nat.card (B'.residueField (p' (IsLocalRing.closedPoint K))) =
      Nat.card K :=
    Nat.card_congr (Equiv.ofBijective
      (B'.descResidueField (Scheme.stalkClosedPointTo p')).hom
      ⟨RingHom.injective _, hρ⟩)
  let q' := lifts.2 K p' (by simpa only [hcard] using hlarge)
  refine ⟨q'.1 ≫ pullback.fst f g, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, q'.2]
  exact pullback.lift_fst _ _ _

end Langlands.AlgebraicGeometry
