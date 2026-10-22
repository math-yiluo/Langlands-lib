import Langlands.Representation.Parabolic.RefinementComposition
import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Normalized

/-! Direct normalized functors for the actual composed matrix parabolic. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV uW

variable {F : Type uF} [CommRing F] {n : ℕ}
  (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The quotient by the actual full ambient radical of the composed parabolic. -/
abbrev ComposedJacquetModule (ρ : Representation ℂ (GeneralLinear n F) V) :=
  Jacquet.Coinvariants ρ (composedUnipotent F B S)

/-- The canonical quotient map for the full composed radical. -/
abbrev composedJacquetMk (ρ : Representation ℂ (GeneralLinear n F) V) :
    V →ₗ[ℂ] ComposedJacquetModule B S ρ :=
  Jacquet.mk ρ (composedUnipotent F B S)

/-- The actual refined Levi acts through its embedded normalizer map. -/
def composedJacquetAction (ρ : Representation ℂ (GeneralLinear n F) V) :
    Representation ℂ (refinedLevi F B S) (ComposedJacquetModule B S ρ) :=
  (Jacquet.action ρ (composedUnipotent F B S)
    (Subgroup.normalizer (composedUnipotent F B S)) le_rfl).comp
      (composedLeviNormalizer F B S)

@[simp] theorem composedJacquetAction_mk
    (ρ : Representation ℂ (GeneralLinear n F) V)
    (m : refinedLevi F B S) (v : V) :
    composedJacquetAction B S ρ m (composedJacquetMk B S ρ v) =
      composedJacquetMk B S ρ (ρ (B.leviEmbedding F m.val) v) := rfl

/-- Descent of an ambient intertwiner, with the actual embedded Levi action. -/
def composedJacquetMap {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W} (f : ρ.IntertwiningMap τ) :
    (composedJacquetAction B S ρ).IntertwiningMap (composedJacquetAction B S τ) where
  toLinearMap := (Jacquet.map (composedUnipotent F B S)
    (Subgroup.normalizer (composedUnipotent F B S)) le_rfl f).toLinearMap
  isIntertwining' m := (Jacquet.map (composedUnipotent F B S)
    (Subgroup.normalizer (composedUnipotent F B S)) le_rfl f).isIntertwining'
      (composedLeviNormalizer F B S m)

@[simp] theorem composedJacquetMap_mk
    {ρ : Representation ℂ (GeneralLinear n F) V}
    {τ : Representation ℂ (GeneralLinear n F) W}
    (f : ρ.IntertwiningMap τ) (v : V) :
    composedJacquetMap B S f (composedJacquetMk B S ρ v) =
      composedJacquetMk B S τ (f v) := rfl

theorem isSmooth_composedJacquetAction [TopologicalSpace F] [IsTopologicalRing F]
    {ρ : Representation ℂ (GeneralLinear n F) V} (hρ : IsSmooth ρ) :
    IsSmooth (composedJacquetAction B S ρ) :=
  isSmooth_comp (composedLeviNormalizer F B S)
    (composedLeviNormalizerContinuous F B S).continuous
    (Jacquet.isSmooth_action _ _ _ le_rfl hρ)

end Langlands.Parabolic

namespace Langlands.PadicField.TopologicalData

open GeneralLinear Geometric Parabolic CategoryTheory

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)
  {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Direct Jacquet normalization uses the inverse half of the full product modulus. -/
def normalizedComposedJacquet (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (refinedLevi F.Carrier B S) (ComposedJacquetModule B S ρ) :=
  twist (Jacquet.inverseHalfCharacter (T.composedLeviModulus B S))
    (composedJacquetAction B S ρ)

theorem normalizedComposedJacquet_mk
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
    (m : refinedLevi F.Carrier B S) (v : V) :
    T.normalizedComposedJacquet B S ρ m (composedJacquetMk B S ρ v) =
      (Jacquet.inverseHalfCharacter (T.composedLeviModulus B S) m : ℂ) •
        composedJacquetMk B S ρ (ρ (B.leviEmbedding F.Carrier m.val) v) := rfl

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

theorem isSmooth_normalizedComposedJacquet
    {ρ : Representation ℂ (GeneralLinear n F.Carrier) V} :
    letI := T.topology
    IsSmooth ρ → IsSmooth (T.normalizedComposedJacquet B S ρ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hρ
  exact (isSmooth_twist_iff _ _ (Jacquet.isOpen_ker_inverseHalfCharacter _
    (T.isOpen_ker_composedLeviModulus B S))).mpr
      (isSmooth_composedJacquetAction B S hρ)

/-- The direct normalized Jacquet functor of the full composed radical. -/
def normalizedComposedJacquetFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (refinedLevi F.Carrier B S) := by
  letI := T.topology
  exact {
    obj := fun A => SmoothRep.of (T.normalizedComposedJacquet B S A.representation)
      (T.isSmooth_normalizedComposedJacquet B S A.isSmooth)
    map := fun f => SmoothRep.ofHom (T.normalizedComposedJacquetMap B S (SmoothRep.hom f))
    map_id := by intros; ext v; rfl
    map_comp := by intros; ext v; rfl }

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

theorem normalizedComposedInduced_covariant
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (f : Induction.SmoothFunctions (composedParabolic F.Carrier B S)
        (T.composedInducingRepresentation B S σ))
      (q : composedParabolic F.Carrier B S) (g : GeneralLinear n F.Carrier),
      Induction.eval _ _ f (q.val * g) =
        (T.composedLeviHalfModulus B S (composedLeviProjection F.Carrier B S q) : ℂ) •
          σ (composedLeviProjection F.Carrier B S q) (Induction.eval _ _ f g) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact fun f q g => f.val.property q g

theorem normalizedComposedInduced_apply
    (σ : Representation ℂ (refinedLevi F.Carrier B S) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (g x : GeneralLinear n F.Carrier)
      (f : Induction.SmoothFunctions (composedParabolic F.Carrier B S)
        (T.composedInducingRepresentation B S σ)),
      Induction.eval _ _ (T.normalizedComposedInduced B S σ g f) x =
        Induction.eval _ _ f (x * g) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intros
  rfl

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

theorem normalizedComposedInducedMap_apply
    {σ : Representation ℂ (refinedLevi F.Carrier B S) V}
    {τ : Representation ℂ (refinedLevi F.Carrier B S) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (φ : Induction.SmoothFunctions (composedParabolic F.Carrier B S)
        (T.composedInducingRepresentation B S σ)) (g : GeneralLinear n F.Carrier),
      Induction.eval _ _ (T.normalizedComposedInducedMap B S f φ) g =
        f (Induction.eval _ _ φ g) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intros
  rfl

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

end Langlands.PadicField.TopologicalData
