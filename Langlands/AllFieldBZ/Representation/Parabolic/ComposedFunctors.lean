import Langlands.AllFieldBZ.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Parabolic.ComposedFunctors

/-!
# All-field port of `Langlands.Representation.Parabolic.ComposedFunctors`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Parabolic.ComposedFunctors` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Parabolic
open Langlands.Parabolic
open Langlands.GeneralLinear
open Langlands.Geometric
universe uF uV uW

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Langlands.AllFieldBZ.Parabolic
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
open Langlands.GeneralLinear hiding SupercuspidalClass
open Langlands.Geometric
open Langlands.Parabolic
open CategoryTheory
universe uF uV uW

variable {F : LocalFieldPackage.{uF}}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Direct Jacquet normalization uses the inverse half of the full product modulus. -/
def normalizedComposedJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (ComposedJacquetModule B S ρ) :=
  twist (Jacquet.inverseHalfCharacter (T.composedLeviModulus B S))
    (composedJacquetAction B S ρ)

/-- The same quotient map on vectors descends every ambient intertwiner. -/
def normalizedComposedJacquetMap
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W} (f : ρ.IntertwiningMap τ) :
    (T.normalizedComposedJacquet B S ρ).IntertwiningMap
      (T.normalizedComposedJacquet B S τ) :=
  twistIntertwining _ (composedJacquetMap B S f)

@[simp] theorem normalizedComposedJacquetMap_mk
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear n F.Carrier) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    T.normalizedComposedJacquetMap B S f (composedJacquetMk B S ρ v) =
      composedJacquetMk B S τ (f v) := rfl

/-- Inflation through the actual composite projection, with the positive half. -/
abbrev composedInducingRepresentation
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    Representation ℂ (composedParabolic F.Carrier B S) V :=
  twist (T.composedParabolicHalfModulus B S)
    (σ.comp (composedLeviProjection F.Carrier B S))

/-- Direct smooth induction from the smaller actual matrix parabolic. -/
def normalizedComposedInduced (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (composedParabolic F.Carrier B S)
        (T.composedInducingRepresentation B S σ)) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.smoothInduced _ _

/-- Inflate and twist an intertwiner using the composite projection. -/
def composedInducingMap
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ) :
    (T.composedInducingRepresentation B S σ).IntertwiningMap
      (T.composedInducingRepresentation B S τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun q => f.isIntertwining' (composedLeviProjection F.Carrier B S q) }

/-- The direct induced intertwiner acts by pointwise postcomposition. -/
def normalizedComposedInducedMap
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedComposedInduced B S σ).IntertwiningMap
      (T.normalizedComposedInduced B S τ) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact Induction.smoothInducedMap _ (T.composedInducingMap B S f)

theorem isSmooth_normalizedComposedInduced
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedComposedInduced B S σ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact Induction.smoothInduced_smooth _ _

/-- Direct normalized induction between the actual smooth categories. -/
def normalizedComposedInductionFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  exact {
    obj := fun A => SmoothRep.of (T.normalizedComposedInduced B S A.representation)
      (T.isSmooth_normalizedComposedInduced B S A.representation)
    map := fun f => SmoothRep.ofHom (T.normalizedComposedInducedMap B S (SmoothRep.hom f))
    map_id := by intros; ext φ x; rfl
    map_comp := by intros; ext φ x; rfl }

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
