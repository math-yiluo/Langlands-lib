import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedSpecialization
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
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

local instance continuousBasesAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance continuousBasesPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

/-- A common finite index for actual fixed-space bases with continuous matrices. -/
abbrev InducedContinuousFixedBases
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (mHaar : Measure (rationalPoints G)) [mHaar.IsHaarMeasure] : Prop :=
  ∃ d : ℕ, ∃ e : ∀ χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r),
    Module.Basis (Fin d) ℂ
      (fixedVectors (complexInduced r h hU π χ).representation K.toSubgroup),
    ∀ (g : rationalPoints G) (i j : Fin d),
      Continuous (fun χ => UnitarizabilityContinuation.fixedMatrix mHaar
        (complexInduced r h hU π χ).isSmooth hK (e χ)
        (complexInduced r h hU π χ).representation g i j)

end FixedData

/-- Actual rational normalized induction admits continuous finite fixed matrices.
Literal quotient compactness and actual projection continuity remain explicit. -/
def RationalContinuousFixedBasesStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (M P U : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a) (n : U ⟶ P)
      (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
        (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
      (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G))),
      Continuous h.projection → CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) →
      ∀ (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)),
        π.IsAdmissible →
        ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
          (mHaar : Measure (rationalPoints G)) [mHaar.IsHaarMeasure],
          InducedContinuousFixedBases r h hU π K hK mHaar

end Langlands.Plancherel.RationalNormalized
