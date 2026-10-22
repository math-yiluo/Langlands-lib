import Langlands.Representation.Geometric.RefinementDefinitions
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Normalized

/-! Actual normalized induction and Jacquet functors inside product Levis. -/

noncomputable section

open scoped NNReal

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV uW uX

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW} {X : Type uX}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X]

/-- The actual refined diagonal subgroup normalizes the ambient refined radical. -/
theorem refinedLevi_le_normalizer :
    refinedLevi F B S ≤ Subgroup.normalizer (refinedUnipotent F B S) := by
  intro m hm
  exact refinedParabolic_le_normalizer F B S
    (refinedLeviSection F B S ⟨m, hm⟩).property

/-- The ambient coinvariant quotient, also used in product-Levi cuspidality. -/
abbrev RefinedJacquetModule (ρ : Representation ℂ (B.Levi F) V) :=
  Jacquet.Coinvariants ρ (refinedUnipotent F B S)

/-- The quotient map onto the refined Jacquet carrier. -/
abbrev refinedJacquetMk (ρ : Representation ℂ (B.Levi F) V) :
    V →ₗ[ℂ] RefinedJacquetModule B S ρ :=
  Jacquet.mk ρ (refinedUnipotent F B S)

/-- The actual refined Levi acts on the quotient with inverse half modulus. -/
def normalizedRefinedJacquetOf (δ : refinedLevi F B S →* ℝ≥0ˣ)
    (ρ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (refinedLevi F B S) (RefinedJacquetModule B S ρ) :=
  Jacquet.normalizedActionOfModulus ρ (refinedUnipotent F B S)
    (refinedLevi F B S) (refinedLevi_le_normalizer B S) δ

theorem normalizedRefinedJacquetOf_mk (δ : refinedLevi F B S →* ℝ≥0ˣ)
    (ρ : Representation ℂ (B.Levi F) V) (m : refinedLevi F B S) (v : V) :
    normalizedRefinedJacquetOf B S δ ρ m (refinedJacquetMk B S ρ v) =
      (((NNReal.sqrt (δ m : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        refinedJacquetMk B S ρ (ρ m.val v) :=
  Jacquet.normalizedActionOfModulus_mk _ _ _ _ _ _ _

/-- An ambient intertwiner induces the same linear map on quotient classes. -/
def normalizedRefinedJacquetOfMap (δ : refinedLevi F B S →* ℝ≥0ˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) :
    (normalizedRefinedJacquetOf B S δ ρ).IntertwiningMap
      (normalizedRefinedJacquetOf B S δ τ) :=
  Jacquet.normalizedMapOfModulus _ _ (refinedLevi_le_normalizer B S) δ f

@[simp] theorem normalizedRefinedJacquetOfMap_mk
    (δ : refinedLevi F B S →* ℝ≥0ˣ)
    {ρ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    normalizedRefinedJacquetOfMap B S δ f (refinedJacquetMk B S ρ v) =
      refinedJacquetMk B S τ (f v) := rfl

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

omit [IsTopologicalRing F] in
/-- Smoothness follows from the open kernel of the full positive modulus. -/
theorem isSmooth_normalizedRefinedJacquetOf
    (δ : refinedLevi F B S →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (refinedLevi F B S)))
    {ρ : Representation ℂ (B.Levi F) V} (hρ : IsSmooth ρ) :
    IsSmooth (normalizedRefinedJacquetOf B S δ ρ) :=
  Jacquet.isSmooth_normalizedActionOfModulus _ _ _ _ _ hδ hρ

/-- The normalized quotient functor on the actual smooth categories. -/
def normalizedRefinedJacquetFunctorOf (δ : refinedLevi F B S →* ℝ≥0ˣ)
    (hδ : IsOpen (δ.ker : Set (refinedLevi F B S))) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) where
  obj A := SmoothRep.of (normalizedRefinedJacquetOf B S δ A.representation)
    (isSmooth_normalizedRefinedJacquetOf B S δ hδ A.isSmooth)
  map f := SmoothRep.ofHom (normalizedRefinedJacquetOfMap B S δ (SmoothRep.hom f))
  map_id A := by
    ext v
    rfl
  map_comp {A A' A''} f g := by
    ext v
    rfl

/-- Inflate the actual Levi action through the refined projection and twist. -/
abbrev refinedInducingRepresentation (χ : refinedLevi F B S →* ℂˣ)
    (σ : Representation ℂ (refinedLevi F B S) V) :
    Representation ℂ (refinedParabolic F B S) V :=
  twist (χ.comp (refinedLeviProjection F B S))
    (σ.comp (refinedLeviProjection F B S))

/-- Smooth normalized induction inside the ambient product Levi. -/
def normalizedRefinedInducedOf (χ : refinedLevi F B S →* ℂˣ)
    (σ : Representation ℂ (refinedLevi F B S) V) :
    Representation ℂ (B.Levi F)
      (Induction.SmoothFunctions (refinedParabolic F B S)
        (refinedInducingRepresentation B S χ σ)) :=
  Induction.smoothInduced _ (refinedInducingRepresentation B S χ σ)

omit [IsTopologicalRing F] in
/-- The defining left covariance, using the actual subgroup projection. -/
theorem normalizedRefinedInducedOf_covariant (χ : refinedLevi F B S →* ℂˣ)
    (σ : Representation ℂ (refinedLevi F B S) V)
    (f : Induction.SmoothFunctions (refinedParabolic F B S)
      (refinedInducingRepresentation B S χ σ))
    (q : refinedParabolic F B S) (g : B.Levi F) :
    Induction.eval _ (refinedInducingRepresentation B S χ σ) f (q.val * g) =
      (χ (refinedLeviProjection F B S q) : ℂ) •
        σ (refinedLeviProjection F B S q)
          (Induction.eval _ (refinedInducingRepresentation B S χ σ) f g) :=
  f.val.property q g

/-- The ambient product Levi acts by right translation. -/
@[simp] theorem normalizedRefinedInducedOf_apply (χ : refinedLevi F B S →* ℂˣ)
    (σ : Representation ℂ (refinedLevi F B S) V) (g x : B.Levi F)
    (f : Induction.SmoothFunctions (refinedParabolic F B S)
      (refinedInducingRepresentation B S χ σ)) :
    Induction.eval _ (refinedInducingRepresentation B S χ σ)
        (normalizedRefinedInducedOf B S χ σ g f) x =
      Induction.eval _ (refinedInducingRepresentation B S χ σ) f (x * g) := rfl

/-- Inflation and twisting of an actual intertwiner. -/
def refinedInducingMap (χ : refinedLevi F B S →* ℂˣ)
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ) :
    (refinedInducingRepresentation B S χ σ).IntertwiningMap
      (refinedInducingRepresentation B S χ τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun q => f.isIntertwining' (refinedLeviProjection F B S q) }

/-- Induction of an intertwiner by pointwise postcomposition. -/
def normalizedRefinedInducedOfMap (χ : refinedLevi F B S →* ℂˣ)
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ) :
    (normalizedRefinedInducedOf B S χ σ).IntertwiningMap
      (normalizedRefinedInducedOf B S χ τ) :=
  Induction.smoothInducedMap _ (refinedInducingMap B S χ f)

@[simp] theorem normalizedRefinedInducedOfMap_apply (χ : refinedLevi F B S →* ℂˣ)
    {σ : Representation ℂ (refinedLevi F B S) V}
    {τ : Representation ℂ (refinedLevi F B S) W} (f : σ.IntertwiningMap τ)
    (φ : Induction.SmoothFunctions (refinedParabolic F B S)
      (refinedInducingRepresentation B S χ σ)) (g : B.Levi F) :
    Induction.eval _ (refinedInducingRepresentation B S χ τ)
        (normalizedRefinedInducedOfMap B S χ f φ) g =
      f (Induction.eval _ (refinedInducingRepresentation B S χ σ) φ g) := rfl

/-- The normalized induction functor, with intrinsic identity and composition laws. -/
def normalizedRefinedInductionFunctorOf (χ : refinedLevi F B S →* ℂˣ) :
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F) where
  obj A := SmoothRep.of (normalizedRefinedInducedOf B S χ A.representation)
    (Induction.smoothInduced_smooth _ _)
  map f := SmoothRep.ofHom (normalizedRefinedInducedOfMap B S χ (SmoothRep.hom f))
  map_id _ := by ext φ x; rfl
  map_comp _ _ := by ext φ x; rfl

end Topology
end Langlands.Geometric

namespace Langlands.PadicField.TopologicalData

open Geometric CategoryTheory

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
  (S : BlockRefinement B) {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The actual p-adic refined Jacquet action, with the explicit full product modulus. -/
def normalizedRefinedJacquet (ρ : Representation ℂ (B.Levi F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (RefinedJacquetModule B S ρ) :=
  normalizedRefinedJacquetOf B S (T.refinedLeviModulus B S) ρ

/-- Its action on quotient classes uses the canonical inverse half. -/
theorem normalizedRefinedJacquet_mk (ρ : Representation ℂ (B.Levi F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedRefinedJacquet B S ρ m (refinedJacquetMk B S ρ v) =
      (T.refinedLeviInverseHalfModulus B S m : ℂ) •
        refinedJacquetMk B S ρ (ρ m.val v) :=
  by simpa only [normalizedRefinedJacquet, refinedLeviInverseHalfModulus_apply] using
    normalizedRefinedJacquetOf_mk B S (T.refinedLeviModulus B S) ρ m v

/-- Refined Jacquet maps preserve the actual quotient representatives. -/
def normalizedRefinedJacquetMap
    {ρ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedRefinedJacquet B S ρ).IntertwiningMap
      (T.normalizedRefinedJacquet B S τ) :=
  normalizedRefinedJacquetOfMap B S (T.refinedLeviModulus B S) f

/-- The p-adic normalized quotient of a smooth representation is smooth. -/
theorem isSmooth_normalizedRefinedJacquet
    {ρ : Representation ℂ (B.Levi F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedRefinedJacquet B S ρ) := by
  let := T.topology
  exact isSmooth_normalizedRefinedJacquetOf B S (T.refinedLeviModulus B S)
    (T.isOpen_ker_refinedLeviModulus B S)

/-- The actual normalized Jacquet functor of a refinement of a product Levi. -/
def normalizedRefinedJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedJacquetFunctorOf B S (T.refinedLeviModulus B S)
    (T.isOpen_ker_refinedLeviModulus B S)

/-- The normalized refined induction action uses the positive half of the same modulus. -/
def normalizedRefinedInduced (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    Representation ℂ (B.Levi F.Carrier)
      (Induction.SmoothFunctions (refinedParabolic F.Carrier B S)
        (twist (T.refinedParabolicHalfModulus B S)
          (σ.comp (refinedLeviProjection F.Carrier B S)))) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOf B S (T.refinedLeviHalfModulus B S) σ

/-- Smoothness of the actual normalized refined induced representation. -/
theorem isSmooth_normalizedRefinedInduced
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    IsSmooth (T.normalizedRefinedInduced B S σ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact Induction.smoothInduced_smooth _ _

/-- The normalized induced map is postcomposition by the original intertwiner. -/
def normalizedRefinedInducedMap
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    (T.normalizedRefinedInduced B S σ).IntertwiningMap
      (T.normalizedRefinedInduced B S τ) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInducedOfMap B S (T.refinedLeviHalfModulus B S) f

/-- Normalized induction between the actual smooth categories of product Levi subgroups. -/
def normalizedRefinedInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier) := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact normalizedRefinedInductionFunctorOf B S (T.refinedLeviHalfModulus B S)

end Langlands.PadicField.TopologicalData
