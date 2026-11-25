/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison

/-! # Uniqueness of the normalized finite Chern comparison image

Source: diagonal tower coefficient changes proof (1), reduction of the section class.
(blueprint: lem-diagonal-uniformizer-local-chern-finite-spec-unique-map).
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization Functor.mapDerivedCategory Functor.leftAdjoint
  Functor.rightAdjoint RestrictionSquare.mate CompletedRealization.singleUnit
  CompletedRealization.shiftedLine FiniteRealization.derivedUnit
  HasDerivedCategory.standard Etale.projectiveLineTraceDatum
  Scheme.finiteEtaleTateLine

variable (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
  [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)]
  [DiagonalTraceLocalizations l Y]
  [DiagonalTraceLocalizations l (ProjectiveLine Y)]

namespace UniformizerChernNormalizationData

/-- A finite normalized factor has the canonical comparison image.

Source: diagonal tower coefficient changes proof (1), finite Kummer normalization.
(blueprint: lem-diagonal-uniformizer-local-chern-finite-spec-unique-map).

The ordinary finite class comparison is bijective. Applying its uniqueness to
`hk` identifies the finite arrow with the canonical projective-line trace arrow;
functoriality of `geoP1Comparison` maps this equality to the displayed result. -/
theorem localChern_transport_finite_spec_unique_map
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hY : IsUnit (N : Γ(Y, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine Y, ⊤)))
    {k : Etale.ordinaryFiniteUnit A (ProjectiveLine Y) ⟶
      Etale.p1DecompositionTwist A N hA (ProjectiveLine Y) 1 2}
    (hk : LocalFiniteChernSpec A N hA Y hP k) :
    (geoP1Comparison A (ProjectiveLine Y)).map k =
      (geoP1Comparison A (ProjectiveLine Y)).map
        (geoP1EtaleChern A N hN hA Y hY) := by
  unfold LocalFiniteChernSpec at hk
  have hu := Etale.existsUnique_ordinaryFiniteP1Chern A N hA Y hP
  have huniq : k = geoP1EtaleChern A N hN hA Y hY :=
    hu.unique hk (Etale.projectiveLineTraceDatum N hN A hA Y hY).chern_spec
  exact congrArg (fun k => (geoP1Comparison A (ProjectiveLine Y)).map k) huniq

end UniformizerChernNormalizationData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients
