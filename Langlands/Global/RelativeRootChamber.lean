import Langlands.Global.PositiveRealTorusEmbedding
import Langlands.GroupScheme.Rational.StandardParabolic

/-! # Actual positive-torus chambers for restricted relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Topology

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
variable (T₀ T : CommGroupScheme (Spec (CommRingCat.of F)))

local instance (G : GroupScheme (Spec (CommRingCat.of F)))
    (A : Type u) [CommRing A] [Algebra F A] [TopologicalSpace A] :
    TopologicalSpace (Lie.AffinePoints G A) :=
  GroupScheme.affinePointsTopologicalSpace G (CommAlgCat.of F A)

/-- The normalized adelic norm of an actual rational torus character. -/
def normCharacter (χ : characterLattice T) :
    Lie.AffinePoints T.toGrp (Adeles F) →ₜ* ℝ≥0ˣ :=
  (IdeleAbsoluteValue.full F).comp (continuousCharacter F T (Adeles F) χ)

@[simp]
theorem normCharacter_apply (χ : characterLattice T)
    (a : Lie.AffinePoints T.toGrp (Adeles F)) :
    normCharacter F T χ a = IdeleAbsoluteValue.full F (Lie.characterValue χ a) := rfl

/-- Restrict an actual character along the supplied torus morphism before taking its norm. -/
theorem normCharacter_pullback (j : T₀ ⟶ T) (χ : characterLattice T)
    (a : Lie.AffinePoints T₀.toGrp (Adeles F)) :
    normCharacter F T₀ (j ≫ χ) a =
      normCharacter F T χ
        (pointMap F T₀.toGrp T.toGrp (Adeles F) (CommGroupScheme.groupHom j) a) := by
  simp only [normCharacter_apply, Lie.characterValue_comp, pointMap_apply]

variable (j : T₀ ⟶ T)
variable (Δ : Set (characterLattice T)) (b : characterLattice T → ℝ≥0ˣ)

/-- Weak inequalities on the actual intrinsic positive subgroup of `T₀`. -/
def weakCharacterChamber : Set (intrinsicSubgroup F T₀) :=
  {a | ∀ χ ∈ Δ, b χ ≤ normCharacter F T₀ (j ≫ χ) a}

/-- Strict inequalities on the same actual positive subgroup. -/
def strictCharacterChamber : Set (intrinsicSubgroup F T₀) :=
  {a | ∀ χ ∈ Δ, b χ < normCharacter F T₀ (j ≫ χ) a}

theorem strictCharacterChamber_subset_weak :
    strictCharacterChamber F T₀ T j Δ b ⊆ weakCharacterChamber F T₀ T j Δ b :=
  fun _ ha χ hχ => (ha χ hχ).le

/-- Arbitrary weak character chambers are closed in the intrinsic positive subgroup. -/
theorem isClosed_weakCharacterChamber :
    IsClosed (weakCharacterChamber F T₀ T j Δ b) := by
  have h : weakCharacterChamber F T₀ T j Δ b = ⋂ χ ∈ Δ,
      {a : intrinsicSubgroup F T₀ |
        (b χ : ℝ≥0) ≤ (normCharacter F T₀ (j ≫ χ) a : ℝ≥0)} := by
    ext a
    simp [weakCharacterChamber]
  rw [h]
  exact isClosed_iInter fun χ => isClosed_iInter fun _ =>
    isClosed_le continuous_const
      (Units.continuous_val.comp
        ((normCharacter F T₀ (j ≫ χ)).continuous.comp continuous_subtype_val))

/-- Finitely many strict inequalities are open in the intrinsic positive subgroup. -/
theorem isOpen_strictCharacterChamber (hΔ : Δ.Finite) :
    IsOpen (strictCharacterChamber F T₀ T j Δ b) := by
  have h : strictCharacterChamber F T₀ T j Δ b = ⋂ χ ∈ Δ,
      {a : intrinsicSubgroup F T₀ |
        (b χ : ℝ≥0) < (normCharacter F T₀ (j ≫ χ) a : ℝ≥0)} := by
    ext a
    simp [strictCharacterChamber]
  rw [h]
  exact hΔ.isOpen_biInter fun χ _ =>
    isOpen_lt continuous_const
      (Units.continuous_val.comp
        ((normCharacter F T₀ (j ≫ χ)).continuous.comp continuous_subtype_val))

theorem weakCharacterChamber_empty :
    weakCharacterChamber F T₀ T j ∅ b = Set.univ := by
  ext a
  simp [weakCharacterChamber]

theorem strictCharacterChamber_empty :
    strictCharacterChamber F T₀ T j ∅ b = Set.univ := by
  ext a
  simp [strictCharacterChamber]

theorem weakCharacterChamber_antitone {Δ' : Set (characterLattice T)}
    (h : Δ ⊆ Δ') :
    weakCharacterChamber F T₀ T j Δ' b ⊆ weakCharacterChamber F T₀ T j Δ b :=
  fun _ ha χ hχ => ha χ (h hχ)

theorem strictCharacterChamber_antitone {Δ' : Set (characterLattice T)}
    (h : Δ ⊆ Δ') :
    strictCharacterChamber F T₀ T j Δ' b ⊆ strictCharacterChamber F T₀ T j Δ b :=
  fun _ ha χ hχ => ha χ (h hχ)

section Coordinates

variable (I : Type u) [Fintype I]
variable (e : T₀.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)

/-- The existing scalar parametrization, with codomain the same intrinsic subgroup. -/
def fullIntrinsic : (I → ℝ≥0ˣ) →* intrinsicSubgroup F T₀ where
  toFun x := ⟨full F I T₀ e x,
    (subgroup_eq_intrinsicSubgroup F I T₀ e).le ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (map_one (full F I T₀ e))
  map_mul' x y := Subtype.ext (map_mul (full F I T₀ e) x y)

@[simp]
theorem coe_fullIntrinsic (x : I → ℝ≥0ˣ) :
    (fullIntrinsic F T₀ I e x : Lie.AffinePoints T₀.toGrp (Adeles F)) =
      full F I T₀ e x := rfl

theorem fullIntrinsic_surjective : Function.Surjective (fullIntrinsic F T₀ I e) := by
  rintro ⟨a, ha⟩
  have ha' : a ∈ subgroup F I T₀ e := by
    rwa [subgroup_eq_intrinsicSubgroup]
  obtain ⟨x, hx⟩ := ha'
  exact ⟨x, Subtype.ext hx⟩

/-- The root restriction is taken before computing its genuine coordinate monomial. -/
@[simp]
theorem normCharacter_fullIntrinsic (χ : characterLattice T) (x : I → ℝ≥0ˣ) :
    normCharacter F T₀ (j ≫ χ) (fullIntrinsic F T₀ I e x) =
      positiveCharacter F I T₀ e (j ≫ χ) x ^ Module.finrank ℚ F :=
  absoluteValue_characterValue_full F I T₀ e (j ≫ χ) x

theorem mem_weakCharacterChamber_fullIntrinsic (x : I → ℝ≥0ˣ) :
    fullIntrinsic F T₀ I e x ∈ weakCharacterChamber F T₀ T j Δ b ↔
      ∀ χ ∈ Δ, b χ ≤ positiveCharacter F I T₀ e (j ≫ χ) x ^ Module.finrank ℚ F := by
  simp only [weakCharacterChamber, Set.mem_ofPred_eq, normCharacter_fullIntrinsic]

theorem mem_strictCharacterChamber_fullIntrinsic (x : I → ℝ≥0ˣ) :
    fullIntrinsic F T₀ I e x ∈ strictCharacterChamber F T₀ T j Δ b ↔
      ∀ χ ∈ Δ, b χ < positiveCharacter F I T₀ e (j ≫ χ) x ^ Module.finrank ℚ F := by
  simp only [strictCharacterChamber, Set.mem_ofPred_eq, normCharacter_fullIntrinsic]

/-- Every splitting computes exactly the same intrinsic weak chamber. -/
theorem weakCharacterChamber_eq_image :
    weakCharacterChamber F T₀ T j Δ b =
      fullIntrinsic F T₀ I e ''
        {x | ∀ χ ∈ Δ,
          b χ ≤ positiveCharacter F I T₀ e (j ≫ χ) x ^ Module.finrank ℚ F} := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, rfl⟩ := fullIntrinsic_surjective F T₀ I e a
    exact ⟨x, (mem_weakCharacterChamber_fullIntrinsic F T₀ T j Δ b I e x).mp ha, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_weakCharacterChamber_fullIntrinsic F T₀ T j Δ b I e x).mpr hx

theorem strictCharacterChamber_eq_image :
    strictCharacterChamber F T₀ T j Δ b =
      fullIntrinsic F T₀ I e ''
        {x | ∀ χ ∈ Δ,
          b χ < positiveCharacter F I T₀ e (j ≫ χ) x ^ Module.finrank ℚ F} := by
  ext a
  constructor
  · intro ha
    obtain ⟨x, rfl⟩ := fullIntrinsic_surjective F T₀ I e a
    exact ⟨x, (mem_strictCharacterChamber_fullIntrinsic F T₀ T j Δ b I e x).mp ha, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_strictCharacterChamber_fullIntrinsic F T₀ T j Δ b I e x).mpr hx

end Coordinates

section RelativeRoots

variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The weak simple-root chamber with a common positive normalized threshold. -/
def weakSimpleRootChamber (t : ℝ≥0ˣ) : Set (intrinsicSubgroup F T₀) :=
  weakCharacterChamber F T₀ T j (simpleRelativeRoots i ν) (fun _ => t)

/-- The strict simple-root chamber with explicitly indexed positive thresholds. -/
def strictSimpleRootChamber : Set (intrinsicSubgroup F T₀) :=
  strictCharacterChamber F T₀ T j (simpleRelativeRoots i ν) b

/-- Thresholds may be computed from an actual reference torus point. -/
def basedStrictSimpleRootChamber (a₀ : Lie.AffinePoints T.toGrp (Adeles F)) :
    Set (intrinsicSubgroup F T₀) :=
  strictSimpleRootChamber F T₀ T j (fun χ => normCharacter F T χ a₀) G i ν

theorem isClosed_weakSimpleRootChamber (t : ℝ≥0ˣ) :
    IsClosed (weakSimpleRootChamber F T₀ T j G i ν t) :=
  isClosed_weakCharacterChamber F T₀ T j (simpleRelativeRoots i ν) (fun _ => t)

theorem isOpen_strictSimpleRootChamber (hΔ : (simpleRelativeRoots i ν).Finite) :
    IsOpen (strictSimpleRootChamber F T₀ T j b G i ν) :=
  isOpen_strictCharacterChamber F T₀ T j (simpleRelativeRoots i ν) b hΔ

end RelativeRoots

end Langlands.Global.PositiveRealTorus
