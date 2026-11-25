/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicRootEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicEvaluationTransport
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRootMap
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedFlat
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedOrdinaryScalars
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerFiniteModels
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarDiagramTransport
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedScalarSource
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteIntegralEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicClassRestriction

/-! # The cyclic projection of the completed diagonal class

Source: diagonal tower coefficient changes, paragraph (1), and the finite class
normalization in the diagonal limit theorem.
(blueprint: lem-diagonal-cyclic-cartier-projection).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary

attribute [local irreducible] cyclicLine cyclicLineMap derivedScalars

/-- Assemble only coefficient and endpoint data, independently of every diagonal class. -/
private theorem cyclicFrame_nonempty
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) : Nonempty (CyclicCartierFrame l Y n) := by
  obtain ⟨e, push⟩ := finiteDiscrete_realizations.{u} (ZMod (l ^ (n + 1)))
  let a := cyclicMap.{u} l n
  let units := regularEndpoint a
  obtain ⟨supported⟩ := endpoint_of_flat_ordinary_unit a (diagonalSurface Y)
    (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (source (Profinite.continuousMapRingObj.{u} (ZMod (l ^ (n + 1)))) Y)
    (supportMap a Y (units (ProjectiveLine Y)).semilinear.hom)
    (diagonal_supported_flat _ Y)
    (diagonal_supported_ordinary_scalars a Y (units (ProjectiveLine Y)).semilinear.hom
      (units (ProjectiveLine Y)).semilinear.underlying)
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    residueInvertible l (diagonalSurface Y) hW
  have line : Endpoint a (zlLine l (diagonalSurface Y))
      (cyclicLine l n (diagonalSurface Y)) (cyclicLineMap l n (diagonalSurface Y)) := by
    unfold cyclicLine cyclicLineMap
    exact flatExtensionEndpoint a (diagonalSurface Y) (zlLine l (diagonalSurface Y))
      (zlLine_flat l (diagonalSurface Y))
  let integralRoots := diagonalIntegralRoots l (diagonalSurface Y) (bottomField l)
  obtain ⟨finiteRoots⟩ := diagonalFiniteRoots_exists (diagonalSurface Y) (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n)
  obtain ⟨lineEndpoint⟩ := diagonalCyclicRootEndpoint l (diagonalSurface Y) hW n
    (e (diagonalSurface Y)) integralRoots finiteRoots
  obtain ⟨square⟩ := push _ _ (diagonalImmersion Y)
  obtain ⟨sourceComparison⟩ := finiteSource_of_pushSquare _ _ Y _ _ square
  exact ⟨{ eP := e (ProjectiveLine Y)
           eW := e (diagonalSurface Y)
           units := units
           supported := supported
           line := line
           integralRoots := integralRoots
           finiteRoots := finiteRoots
           lineEndpoint := lineEndpoint
           sourceComparison := sourceComparison }⟩

/-- Relative boundary uniqueness fixes the finite class with the positive sign. -/
private theorem residueClass_eq_canonical
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤))) (n : ℕ) :
    cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
        (diagonalImmersion Y) (diagonalImmersion_cartier Y)
        (diagonalSurface_power_unit l Y hY n) =
      geoCartierCanonicalClass (diagonalResidue.{u} l n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (cartierResidue_cast l (n + 1))
        (diagonalImmersion Y) (diagonalImmersion_cartier Y)
        (diagonalSurface_power_unit l Y hY n) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, unique⟩ :=
    cartier_reduction_site_comparison l (Fact.out : l.Prime) (n + 1) (Nat.succ_pos n)
      (diagonalResidue.{u} l n) (cartierResidue_cast l (n + 1))
      (diagonalImmersion Y) (diagonalImmersion_cartier Y)
      (diagonalSurface_power_unit l Y hY n)
  unfold cartierResidueReducedPro
  exact (unique _ ⟨_, (Etale.geoCartierEtaleClass_spec _ _ _ _ _ _ _).1,
    geoCartierCanonicalClass_comparison _ _ _ _ _ _ _⟩).symm

/-- Projection to the cyclic coefficient ring only, before any finite extension
of Q_l or any choice of uniformizer. The frame has no class equation in its data.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md (1), and diagonal-limit clause (3).
(blueprint: lem-diagonal-cyclic-cartier-projection).

Proof: construct the finite constant-ring realizations and their direct-image
comparison. The regular scalar unit, flat supported source and flat integral
Tate line give the frame's derived scalar Endpoints. The projection-normalized
integral and finite roots and the cyclic root endpoint give its LineEndpoint.
Unpack IsDiagonalLimit to obtain the strict class c, its normalized ordinary
source/root cones and the whole-limit equation for delta. Apply the generic
normalized finite-evaluation transport at n. It uses ArrowCompatibility and
the source/root cone normalizations to identify the cyclic scalar reduction after
restriction to discrete integral coefficients. The finite-cycle equation identifies
this image with the image
of cartierResidueReducedPro. The proved cyclic restriction-detection theorem
cancels restriction using the full supported integral-generator Ext bijection.
Finally relative-boundary uniqueness and the canonical comparison equation
identify cartierResidueReducedPro with the positive geoCartierCanonicalClass.
Reference.delta identifies the realized completed arrow with family.zl.delta.
The statement concerns only one cyclic quotient. It neither constructs nor
compares any uniformizer quotient, ramified coefficient extension, or trace.
At n=0 the exponent is one; the empty base has zero source and target. -/
theorem diagonalCompleted_cyclicCartier
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (hsystem : DiagonalCycleSystemSpec l Y hY D)
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (family : Family l Y) (reference : Reference l Y δ family) (n : ℕ) :
    ∃ p : CyclicCartierFrame l Y n,
      p.reduce l Y n family.zl.delta =
        geoCartierCanonicalClass (diagonalResidue.{u} l n) (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (cartierResidue_cast l (n + 1))
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit l Y hY n) := by
  obtain ⟨p⟩ := cyclicFrame_nonempty l Y hY n
  refine ⟨p, ?_⟩
  calc
    p.reduce l Y n family.zl.delta =
        cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit l Y hY n) :=
      by
        apply diagonalCyclicClass_restrict_injective l Y n
        exact diagonalCyclicEvaluation_transport l Y hY D δ family reference n p hδ
    _ = _ := residueClass_eq_canonical l Y hY n

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
