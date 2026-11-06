import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Mathlib.RingTheory.Flat.Basic

/-! # Coefficient finiteness of actual universal normalized induction

Prop-valued targets from Renard VI.8.1–2 for the existing full rational-point
model. The structural comparisons in the universal target remain explicit.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

section FixedData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance inducedFinitenessAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance inducedFinitenessPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]

local instance inducedFinitenessModule
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) :
    Module (RegularAlgebra r) (Induced r h hU σ) :=
  Submodule.module _

/-- Flatness of the existing full normalized universal induced B-module. -/
abbrev UniversalInducedFlatness
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  Module.Flat (RegularAlgebra r) (Induced r h hU σ)

/-- Finite projectivity of every compact-open fixed submodule of the actual
right-translation action, the finiteness consequence of VI.8.2.1 and VI.8.1. -/
abbrev UniversalInducedFixedFiniteProjectivity
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  ∀ (K : OpenSubgroup (rationalPoints G)), IsCompact (K : Set (rationalPoints G)) →
    Module.Finite (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU σ) K.toSubgroup) ∧
    Module.Projective (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU σ) K.toSubgroup)

/-- The two coefficient-finiteness conclusions for the actual full model. -/
abbrev UniversalInducedCoefficientFiniteness
    (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  UniversalInducedFlatness r h hU σ ∧
    UniversalInducedFixedFiniteProjectivity r h hU σ

end FixedData

/-- Renard VI.8.1–2 on arbitrary connected-reductive rational points.
The literal parabolic quotient's compactness, closedness of the actual
unipotent image, and continuity of the actual semidirect projection are
retained structural comparisons. Flatness and fixed-space projectivity are
conclusions for the published full induced function space. -/
def UniversalInducedCoefficientFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (n : U ⟶ P)
      (r : ParabolicRootPresentation p l a)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
        (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
      (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))
      (_hr : Continuous h.projection)
      [CompactSpace (Induction.LeftQuotient (ParabolicPoints p))]
      (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)),
      π.IsAdmissible → UniversalInducedCoefficientFiniteness r h hU π.representation

end Langlands.Plancherel.RationalNormalized
