import Langlands.Representation.Parabolic.OppositeRefinementDefinitions
import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Jacquet.Normalized

/-! Actual opposite Jacquet quotients inside a product Levi and in GL_n,
with the same refined Levi and the inverse full upper modulus. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric CategoryTheory
open scoped NNReal

universe uF uV uW

namespace Jacquet

/-- Inverting the full positive character changes the inverse half to the positive half. -/
theorem inverseHalfCharacter_inv {H : Type*} [Group H] (δ : H →* ℝ≥0ˣ) :
    inverseHalfCharacter δ⁻¹ = complexCharacter (positiveHalfCharacter δ) := by
  apply MonoidHom.ext
  intro h
  simp [inverseHalfCharacter, complexCharacter, positiveHalfCharacter]

end Jacquet

namespace Geometric

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Coinvariants by the actual refined opposite radical. -/
abbrev RefinedOppositeJacquetModule (ρ : Representation ℂ (B.Levi F) V) :=
  Jacquet.Coinvariants ρ (refinedOppositeUnipotent F B S)

/-- The actual quotient map. -/
abbrev refinedOppositeJacquetMk (ρ : Representation ℂ (B.Levi F) V) :
    V →ₗ[ℂ] RefinedOppositeJacquetModule B S ρ :=
  Jacquet.mk ρ (refinedOppositeUnipotent F B S)

/-- Every quotient vector has a representative in the source. -/
theorem refinedOppositeJacquetMk_surjective (ρ : Representation ℂ (B.Levi F) V) :
    Function.Surjective (refinedOppositeJacquetMk B S ρ) :=
  Jacquet.mk_surjective _ _

/-- The common refined Levi acts through its actual radical-normalizer map. -/
def refinedOppositeJacquetAction (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (refinedLevi F B S) (RefinedOppositeJacquetModule B S ρ) :=
  (Jacquet.action ρ (refinedOppositeUnipotent F B S)
    (Subgroup.normalizer (refinedOppositeUnipotent F B S)) le_rfl).comp
      (refinedOppositeLeviNormalizer F B S)

@[simp] theorem refinedOppositeJacquetAction_mk (ρ : Representation ℂ (B.Levi F) V)
    (m : refinedLevi F B S) (v : V) :
    refinedOppositeJacquetAction B S ρ m (refinedOppositeJacquetMk B S ρ v) =
      refinedOppositeJacquetMk B S ρ (ρ (m.val) v) := rfl

/-- Every ambient intertwiner descends to the opposite quotient. -/
def refinedOppositeJacquetMap {ρ : Representation ℂ (B.Levi F) V}
    {τ : Representation ℂ (B.Levi F) W} (f : ρ.IntertwiningMap τ) :
    (refinedOppositeJacquetAction B S ρ).IntertwiningMap (refinedOppositeJacquetAction B S τ) where
  toLinearMap := (Jacquet.map (refinedOppositeUnipotent F B S)
    (Subgroup.normalizer (refinedOppositeUnipotent F B S)) le_rfl f).toLinearMap
  isIntertwining' m := (Jacquet.map (refinedOppositeUnipotent F B S)
    (Subgroup.normalizer (refinedOppositeUnipotent F B S)) le_rfl f).isIntertwining'
      (refinedOppositeLeviNormalizer F B S m)

@[simp] theorem refinedOppositeJacquetMap_mk
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    refinedOppositeJacquetMap B S f (refinedOppositeJacquetMk B S ρ v) =
      refinedOppositeJacquetMk B S τ (f v) := rfl

/-- Pullback along the continuous normalizer map preserves quotient smoothness. -/
theorem isSmooth_refinedOppositeJacquetAction [TopologicalSpace F] [IsTopologicalRing F]
    {ρ : Representation ℂ (B.Levi F) V} (hρ : IsSmooth ρ) :
    IsSmooth (refinedOppositeJacquetAction B S ρ) :=
  isSmooth_comp (refinedOppositeLeviNormalizer F B S)
    (refinedOppositeLeviNormalizerContinuous F B S).continuous
    (Jacquet.isSmooth_action _ _ _ le_rfl hρ)

end Geometric

namespace Parabolic

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Coinvariants by the actual composed opposite radical. -/
abbrev ComposedOppositeJacquetModule (ρ : Representation ℂ (GeneralLinear n F) V) :=
  Jacquet.Coinvariants ρ (composedOppositeUnipotent F B S)

/-- The actual quotient map. -/
abbrev composedOppositeJacquetMk (ρ : Representation ℂ (GeneralLinear n F) V) :
    V →ₗ[ℂ] ComposedOppositeJacquetModule B S ρ :=
  Jacquet.mk ρ (composedOppositeUnipotent F B S)

/-- Every quotient vector has a representative in the source. -/
theorem composedOppositeJacquetMk_surjective (ρ : Representation ℂ (GeneralLinear n F) V) :
    Function.Surjective (composedOppositeJacquetMk B S ρ) :=
  Jacquet.mk_surjective _ _

/-- The common refined Levi acts through its actual radical-normalizer map. -/
def composedOppositeJacquetAction (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (refinedLevi F B S) (ComposedOppositeJacquetModule B S ρ) :=
  (Jacquet.action ρ (composedOppositeUnipotent F B S)
    (Subgroup.normalizer (composedOppositeUnipotent F B S)) le_rfl).comp
      (composedOppositeLeviNormalizer F B S)

@[simp] theorem composedOppositeJacquetAction_mk (ρ : Representation ℂ (GeneralLinear n F) V)
    (m : refinedLevi F B S) (v : V) :
    composedOppositeJacquetAction B S ρ m (composedOppositeJacquetMk B S ρ v) =
      composedOppositeJacquetMk B S ρ (ρ (B.leviEmbedding F m.val) v) := rfl

/-- Every ambient intertwiner descends to the opposite quotient. -/
def composedOppositeJacquetMap {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (composedOppositeJacquetAction B S ρ).IntertwiningMap (composedOppositeJacquetAction B S τ) where
  toLinearMap := (Jacquet.map (composedOppositeUnipotent F B S)
    (Subgroup.normalizer (composedOppositeUnipotent F B S)) le_rfl f).toLinearMap
  isIntertwining' m := (Jacquet.map (composedOppositeUnipotent F B S)
    (Subgroup.normalizer (composedOppositeUnipotent F B S)) le_rfl f).isIntertwining'
      (composedOppositeLeviNormalizer F B S m)

@[simp] theorem composedOppositeJacquetMap_mk
    {ρ : Representation ℂ (GeneralLinear n F) V} {τ : Representation ℂ (GeneralLinear n F) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    composedOppositeJacquetMap B S f (composedOppositeJacquetMk B S ρ v) =
      composedOppositeJacquetMk B S τ (f v) := rfl

/-- Pullback along the continuous normalizer map preserves quotient smoothness. -/
theorem isSmooth_composedOppositeJacquetAction [TopologicalSpace F] [IsTopologicalRing F]
    {ρ : Representation ℂ (GeneralLinear n F) V} (hρ : IsSmooth ρ) :
    IsSmooth (composedOppositeJacquetAction B S ρ) :=
  isSmooth_comp (composedOppositeLeviNormalizer F B S)
    (composedOppositeLeviNormalizerContinuous F B S).continuous
    (Jacquet.isSmooth_action _ _ _ le_rfl hρ)

end Parabolic

namespace PadicField.TopologicalData

open Parabolic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The explicit opposite full character is the inverse of the upper full character. -/
def refinedOppositeLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  (T.refinedLeviModulus B S)⁻¹

@[simp] theorem refinedOppositeLeviModulus_apply (m : refinedLevi F.Carrier B S) :
    T.refinedOppositeLeviModulus B S m = (T.refinedLeviModulus B S m)⁻¹ := rfl

/-- The canonical inverse half of the opposite full character is the upper positive half. -/
theorem inverseHalf_refinedOppositeLeviModulus :
    Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S) =
      T.refinedLeviHalfModulus B S :=
  Jacquet.inverseHalfCharacter_inv (T.refinedLeviModulus B S)

/-- Inversion preserves the full character's kernel. -/
theorem refinedOppositeLeviModulus_ker :
    (T.refinedOppositeLeviModulus B S).ker = (T.refinedLeviModulus B S).ker := by
  ext m
  simp [MonoidHom.mem_ker, refinedOppositeLeviModulus]

theorem isOpen_ker_refinedOppositeLeviModulus :
    letI := T.topology
    IsOpen ((T.refinedOppositeLeviModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  rw [T.refinedOppositeLeviModulus_ker B S]
  exact T.isOpen_ker_refinedLeviModulus B S

/-- Normalize the actual lower-radical quotient by the inverse half of the opposite full character. -/
def normalizedRefinedOppositeJacquet (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (RefinedOppositeJacquetModule B S ρ) :=
  twist (Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S))
    (refinedOppositeJacquetAction B S ρ)

/-- On quotient classes the scalar is the positive half of the upper full character. -/
theorem normalizedRefinedOppositeJacquet_mk (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedRefinedOppositeJacquet B S ρ m (refinedOppositeJacquetMk B S ρ v) =
      (T.refinedLeviHalfModulus B S m : ℂ) •
        refinedOppositeJacquetMk B S ρ (ρ (m.val) v) := by
  change (Jacquet.inverseHalfCharacter (T.refinedOppositeLeviModulus B S) m : ℂ) •
    refinedOppositeJacquetMk B S ρ (ρ m.val v) = _
  rw [T.inverseHalf_refinedOppositeLeviModulus B S]

/-- The descended intertwiner keeps the same quotient representative formula. -/
def normalizedRefinedOppositeJacquetMap
    {ρ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ) :
    (T.normalizedRefinedOppositeJacquet B S ρ).IntertwiningMap
      (T.normalizedRefinedOppositeJacquet B S τ) :=
  twistIntertwining _ (refinedOppositeJacquetMap B S f)

@[simp] theorem normalizedRefinedOppositeJacquetMap_mk
    {ρ : Representation ℂ (B.Levi F.Carrier) V} {τ : Representation ℂ (B.Levi F.Carrier) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    T.normalizedRefinedOppositeJacquetMap B S f (refinedOppositeJacquetMk B S ρ v) =
      refinedOppositeJacquetMk B S τ (f v) := rfl

/-- The explicit normalizing character has open kernel, so smoothness is preserved. -/
theorem isSmooth_normalizedRefinedOppositeJacquet
    {ρ : Representation ℂ (B.Levi F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedRefinedOppositeJacquet B S ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ
  exact (isSmooth_twist_iff _ _ (Jacquet.isOpen_ker_inverseHalfCharacter _
    (T.isOpen_ker_refinedOppositeLeviModulus B S))).mpr
      (isSmooth_refinedOppositeJacquetAction B S hρ)

/-- The actual normalized opposite Jacquet functor, with intrinsic identity and composition laws. -/
def normalizedRefinedOppositeJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := by
  letI := T.topology
  exact {
    obj := fun A => SmoothRep.of (T.normalizedRefinedOppositeJacquet B S A.representation)
      (T.isSmooth_normalizedRefinedOppositeJacquet B S A.isSmooth)
    map := fun f => SmoothRep.ofHom (T.normalizedRefinedOppositeJacquetMap B S (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl }

/-- The explicit opposite full character is the inverse of the upper full character. -/
def composedOppositeLeviModulus : refinedLevi F.Carrier B S →* ℝ≥0ˣ :=
  (T.composedLeviModulus B S)⁻¹

@[simp] theorem composedOppositeLeviModulus_apply (m : refinedLevi F.Carrier B S) :
    T.composedOppositeLeviModulus B S m = (T.composedLeviModulus B S m)⁻¹ := rfl

/-- The canonical inverse half of the opposite full character is the upper positive half. -/
theorem inverseHalf_composedOppositeLeviModulus :
    Jacquet.inverseHalfCharacter (T.composedOppositeLeviModulus B S) =
      T.composedLeviHalfModulus B S :=
  Jacquet.inverseHalfCharacter_inv (T.composedLeviModulus B S)

/-- Inversion preserves the full character's kernel. -/
theorem composedOppositeLeviModulus_ker :
    (T.composedOppositeLeviModulus B S).ker = (T.composedLeviModulus B S).ker := by
  ext m
  simp [MonoidHom.mem_ker, composedOppositeLeviModulus]

theorem isOpen_ker_composedOppositeLeviModulus :
    letI := T.topology
    IsOpen ((T.composedOppositeLeviModulus B S).ker : Set (refinedLevi F.Carrier B S)) := by
  let := T.topology
  rw [T.composedOppositeLeviModulus_ker B S]
  exact T.isOpen_ker_composedLeviModulus B S

/-- Normalize the actual lower-radical quotient by the inverse half of the opposite full character. -/
def normalizedComposedOppositeJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (ComposedOppositeJacquetModule B S ρ) :=
  twist (Jacquet.inverseHalfCharacter (T.composedOppositeLeviModulus B S))
    (composedOppositeJacquetAction B S ρ)

/-- On quotient classes the scalar is the positive half of the upper full character. -/
theorem normalizedComposedOppositeJacquet_mk (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedComposedOppositeJacquet B S ρ m (composedOppositeJacquetMk B S ρ v) =
      (T.composedLeviHalfModulus B S m : ℂ) •
        composedOppositeJacquetMk B S ρ (ρ (B.leviEmbedding F.Carrier m.val) v) := by
  change (Jacquet.inverseHalfCharacter (T.composedOppositeLeviModulus B S) m : ℂ) •
    composedOppositeJacquetMk B S ρ (ρ (B.leviEmbedding F.Carrier m.val) v) = _
  rw [T.inverseHalf_composedOppositeLeviModulus B S]

/-- The descended intertwiner keeps the same quotient representative formula. -/
def normalizedComposedOppositeJacquetMap
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (f : ρ.IntertwiningMap τ) :
    (T.normalizedComposedOppositeJacquet B S ρ).IntertwiningMap
      (T.normalizedComposedOppositeJacquet B S τ) :=
  twistIntertwining _ (composedOppositeJacquetMap B S f)

@[simp] theorem normalizedComposedOppositeJacquetMap_mk
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    T.normalizedComposedOppositeJacquetMap B S f (composedOppositeJacquetMk B S ρ v) =
      composedOppositeJacquetMk B S τ (f v) := rfl

/-- The explicit normalizing character has open kernel, so smoothness is preserved. -/
theorem isSmooth_normalizedComposedOppositeJacquet
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedComposedOppositeJacquet B S ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ
  exact (isSmooth_twist_iff _ _ (Jacquet.isOpen_ker_inverseHalfCharacter _
    (T.isOpen_ker_composedOppositeLeviModulus B S))).mpr
      (isSmooth_composedOppositeJacquetAction B S hρ)

/-- The actual normalized opposite Jacquet functor, with intrinsic identity and composition laws. -/
def normalizedComposedOppositeJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := by
  letI := T.topology
  exact {
    obj := fun A => SmoothRep.of (T.normalizedComposedOppositeJacquet B S A.representation)
      (T.isSmooth_normalizedComposedOppositeJacquet B S A.isSmooth)
    map := fun f => SmoothRep.ofHom (T.normalizedComposedOppositeJacquetMap B S (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl }

end PadicField.TopologicalData
end Langlands
