import Langlands.AllFieldBZ.Group.GL.BlockModulus
import Langlands.AllFieldBZ.Group.GL.Maps
import Langlands.Representation.Geometric.RefinementDefinitions

/-!
# All-field port of `Langlands.Representation.Geometric.RefinementDefinitions`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.RefinementDefinitions` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric
open Langlands.GeneralLinear
universe u
variable (R : Type u) [CommRing R] {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

private theorem _root_.Langlands.Geometric.block_mem_radical (i : Fin B.length) (g : (S i).parabolic R) :
    g.val ∈ (S i).unipotentSubgroup R ↔ (S i).leviProjection R g = 1 := by
  constructor
  · rintro ⟨h, hh, he⟩
    have e : h = g := Subtype.ext he
    subst h
    exact hh
  · intro h
    exact ⟨g, h, rfl⟩

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
end Langlands.AllFieldBZ.Geometric
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.Geometric
open scoped BigOperators
open scoped NNReal
universe u
variable {F : LocalFieldPackage.{u}}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : BlockRefinement B)

/-- The inner block coordinates of one actual refined Levi element. -/
def refinedLeviBlock (i : Fin B.length) :
    refinedLevi F.Carrier B S →* (S i).Levi F.Carrier :=
  ((S i).leviEquiv F.Carrier).symm.toMonoidHom.comp (refinedLeviEval F.Carrier B S i)

/-- Product of the published explicit positive moduli of the inner parabolics. -/
def refinedLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  ∏ i : Fin B.length, (T.leviModulus (S i)).comp (refinedLeviBlock B S i)

theorem refinedLeviModulus_apply (m : refinedLevi F.Carrier B S) :
    T.refinedLeviModulus B S m =
      ∏ i : Fin B.length, T.leviModulus (S i) (refinedLeviBlock B S i m) := by
  simp [refinedLeviModulus]

/-- Inflation through the actual subgroup-valued projection. -/
def refinedParabolicModulus : refinedParabolic F.Carrier B S →* ℝ≥0ˣ :=
  (T.refinedLeviModulus B S).comp (refinedLeviProjection F.Carrier B S)

@[simp] theorem refinedParabolicModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicModulus B S g =
      T.refinedLeviModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviModulus B S m := by simp

@[simp] theorem refinedParabolicModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

/-- Positive complex half of the full product modulus, for induction. -/
def refinedLeviHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (T.refinedLeviModulus B S))

/-- Canonical inverse half of the same full modulus, for Jacquet normalization. -/
def refinedLeviInverseHalfModulus : refinedLevi F.Carrier B S →* ℂˣ :=
  Jacquet.inverseHalfCharacter (T.refinedLeviModulus B S)

/-- The positive half on the refined parabolic. -/
def refinedParabolicHalfModulus : refinedParabolic F.Carrier B S →* ℂˣ :=
  (T.refinedLeviHalfModulus B S).comp (refinedLeviProjection F.Carrier B S)

/-- The inverse half on the refined parabolic. -/
def refinedParabolicInverseHalfModulus : refinedParabolic F.Carrier B S →* ℂˣ :=
  (T.refinedLeviInverseHalfModulus B S).comp (refinedLeviProjection F.Carrier B S)

@[simp] theorem refinedLeviHalfModulus_apply (m : refinedLevi F.Carrier B S) :
    (T.refinedLeviHalfModulus B S m : ℂ) =
      ((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ) := rfl

@[simp] theorem refinedLeviInverseHalfModulus_apply (m : refinedLevi F.Carrier B S) :
    (T.refinedLeviInverseHalfModulus B S m : ℂ) =
      (((NNReal.sqrt (T.refinedLeviModulus B S m : ℝ≥0) : ℝ) : ℂ))⁻¹ :=
  Jacquet.inverseHalfCharacter_apply _ _

theorem refinedLeviHalfModulus_sq (m : refinedLevi F.Carrier B S) :
    T.refinedLeviHalfModulus B S m ^ 2 =
      Jacquet.complexCharacter (T.refinedLeviModulus B S) m := by
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, refinedLeviHalfModulus_apply,
    Jacquet.complexCharacter_apply]
  norm_cast
  exact NNReal.sq_sqrt _

theorem refinedLeviInverseHalfModulus_eq_inv :
    T.refinedLeviInverseHalfModulus B S = (T.refinedLeviHalfModulus B S)⁻¹ := rfl

@[simp] theorem refinedParabolicHalfModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicHalfModulus B S g =
      T.refinedLeviHalfModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicInverseHalfModulus_apply (g : refinedParabolic F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S g =
      T.refinedLeviInverseHalfModulus B S (refinedLeviProjection F.Carrier B S g) := rfl

@[simp] theorem refinedParabolicHalfModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicHalfModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviHalfModulus B S m := by simp

@[simp] theorem refinedParabolicInverseHalfModulus_section (m : refinedLevi F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S (refinedLeviSection F.Carrier B S m) =
      T.refinedLeviInverseHalfModulus B S m := by simp

@[simp] theorem refinedParabolicHalfModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicHalfModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

@[simp] theorem refinedParabolicInverseHalfModulus_unipotent
    (u : refinedUnipotentRadical F.Carrier B S) :
    T.refinedParabolicInverseHalfModulus B S u = 1 := by
  have hu : refinedLeviProjection F.Carrier B S u.val = 1 := u.property
  simp [hu]

theorem refinedLeviHalfModulus_ker :
    (T.refinedLeviHalfModulus B S).ker = (T.refinedLeviModulus B S).ker := by
  ext m
  simpa only [MonoidHom.mem_ker, Jacquet.inverseHalfCharacter, MonoidHom.inv_apply,
    inv_eq_one, refinedLeviHalfModulus] using
    Jacquet.inverseHalfCharacter_eq_one (T.refinedLeviModulus B S) m

/-- The compatible field topology makes inner-block evaluation continuous. -/
theorem continuous_refinedLeviBlock (i : Fin B.length) :
    let := T.topology
    Continuous (refinedLeviBlock (F := F) B S i) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact ((S i).leviEquivContinuous F.Carrier).symm.continuous.comp
    (continuous_refinedLeviEval F.Carrier B S i)

/-- The finite intersection of factor kernels is an open subgroup of the full kernel. -/
theorem isOpen_ker_refinedLeviModulus :
    let := T.topology
    IsOpen ((T.refinedLeviModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  let := T.leviTopologicalGroup B
  let K : Subgroup (refinedLevi F.Carrier B S) :=
    ⨅ i : Fin B.length, ((T.leviModulus (S i)).comp (refinedLeviBlock B S i)).ker
  have hK : IsOpen (K : Set (refinedLevi F.Carrier B S)) := by
    have h : ∀ i : Fin B.length,
        IsOpen {m : refinedLevi F.Carrier B S |
          T.leviModulus (S i) (refinedLeviBlock B S i m) = 1} := fun i =>
      (T.isOpen_ker_leviModulus (S i)).preimage (T.continuous_refinedLeviBlock B S i)
    convert isOpen_iInter_of_finite h using 1
    ext m
    simp [K]
  apply Subgroup.isOpen_mono (show K ≤ (T.refinedLeviModulus B S).ker from ?_) hK
  intro m hm
  have h : ∀ i, T.leviModulus (S i) (refinedLeviBlock B S i m) = 1 := by
    simpa only [K, Subgroup.mem_iInf, MonoidHom.mem_ker, MonoidHom.comp_apply] using hm
  change T.refinedLeviModulus B S m = 1
  simp [T.refinedLeviModulus_apply B S, h]

theorem isOpen_ker_refinedLeviHalfModulus :
    let := T.topology
    IsOpen ((T.refinedLeviHalfModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  rw [T.refinedLeviHalfModulus_ker]
  exact T.isOpen_ker_refinedLeviModulus B S

theorem isOpen_ker_refinedParabolicHalfModulus :
    let := T.topology
    IsOpen ((T.refinedParabolicHalfModulus B S).ker : Set (refinedParabolic F.Carrier B S)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (T.isOpen_ker_refinedLeviHalfModulus B S).preimage
    (refinedLeviProjectionContinuous F.Carrier B S).continuous

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
