/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteArrowEquations
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierProjection
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicUniformizerSquare
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionScalar
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteCartierScalarCancellation
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteCartierClassToArrow

/-! # The finite image of the completed diagonal Cartier boundary

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-uniformizer-cartier-reduction).
 -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedScalars
  QuotientLineRealization finiteRealizedClass CyclicCartierFrame.reduce
  geoCartierConstant geoCartierLine

/-- Reduction of the completed diagonal arrow, after its finite source and
positive-root endpoint have already been supplied. This states no realization
existence, direct-image comparison or trace identity.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), reduction of delta.
(blueprint: lem-diagonal-uniformizer-cartier-reduction).

Proof: Use reference.delta to replace the family's whole Z_l arrow by the
realization of delta. The IsDiagonalLimit equation identifies that whole arrow
with the completion of the positive Cartier boundary, and hcompletion identifies
its reduction at n with the n-th cycle-system component of hsystem. Extend that
component from Z/l^(n+1) to the finite quotient A. The canonical Cartier boundary
commutes with this unital coefficient map. Associativity of derived scalar
extension, family.toIntegral E and scalar.delta identify this composite with the
finite realization of d.delta. The supported-source normalization fixes the
source comparison; the projection equation in lineW fixes the target comparison
and the positive sign. Conjugating by these endpoints gives the displayed full
arrow equality. The argument reduces the specified completed arrow itself; it
never infers equality of arbitrary derived arrows from their separate reductions.
Ramification is harmless because A is explicitly killed by l^(n+1). -/
theorem diagonalUniformizer_cartierReduction
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
    (family : Family l Y) (reference : Reference l Y δ family)
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    [hfinite : Finite (ULift.{u + 1} (completedResidue l E π n))]
    (hA : ((l ^ (n + 1) : ℕ) : ULift.{u + 1} (completedResidue l E π n)) = 0)
    (hYpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(Y, ⊤)))
    (hWpow : IsUnit ((l ^ (n + 1) : ℕ) : Γ(diagonalSurface Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) (family.integral E) d)
    (eP : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (ProjectiveLine Y))
    (eW : FiniteRealization
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) (diagonalSurface Y))
    (lineW : QuotientLineRealization l E π n n hA (diagonalSurface Y) eW)
    (sourceComparison : FiniteSourceComparison
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n)) Y eP eW) :
    FiniteCartierArrowEquation
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      (ULift.{u + 1} (completedResidue l E π n))
      (l ^ (n + 1)) (pow_pos (Fact.out : l.Prime).pos _) hA Y hWpow
      (quotientLine l E π n) d eW (lineW.iso l) sourceComparison.iso := by
  have _hπ := hπ
  have _hYpow := hYpow
  let A := ULift.{u + 1} (completedResidue l E π n)
  let R := diagonalResidue.{u} l n
  let N := l ^ (n + 1)
  let hN : 0 < N := pow_pos (Fact.out : l.Prime).pos _
  let hR : (N : R) = 0 := cartierResidue_cast l (n + 1)
  let φ : R →+* A := cartierResidueAlgebra l (n + 1) A hA
  let cA : GeoCartierClass A N hA (diagonalImmersion Y) :=
    finiteRealizedClass
      (R := Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) (A := A)
      (L := quotientLine l E π n) N hA Y eW
      (lineW.iso l) sourceComparison.iso d.delta
  have hcompat := geoCartierCanonicalClass_scalar R A N hN hR hA φ
    (diagonalImmersion Y) (diagonalImmersion_cartier Y) hWpow
  obtain ⟨p, hp⟩ := diagonalCompleted_cyclicCartier l Y hY D hcompletion hsystem
    δ hδ family reference n
  let route : CoefficientArrowRoute l Y (integralMap l E) (quotientMap l E π n)
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (integralLineMap l E) (quotientLineMap l E π n) :=
    ⟨family.zl, family.integral E, d, family.toIntegral E, scalar⟩
  let roots : UniformizerRootFrame l E π n A hA (diagonalSurface Y) eW := by
    unfold QuotientLineRealization at lineW
    exact ⟨lineW.1, lineW.2.1, lineW.2.2⟩
  have hc : cA = geoCartierCanonicalClass A N hN hA (diagonalImmersion Y)
      (diagonalImmersion_cartier Y) hWpow := by
    apply class_eq_of_scalar_square (R := R) (A := A) φ
      (N := N) (hR := hR) (hA := hA) (Y := Y) _ cA _ hcompat
    intro maps
    let q : UniformizerSquareData l Y E π n A hA :=
      ⟨route, eP, eW, roots, sourceComparison, p, maps⟩
    have ht := diagonalCyclic_uniformizerSquare l Y E π n A hA q
    unfold UniformizerSquareData.equation at ht
    dsimp only [q, route, roots, QuotientLineRealization.iso] at ht
    exact (congrArg
      (fun c : GeoCartierClass R N hR (diagonalImmersion Y) ↦ maps.Equation c cA) hp).mp ht
  exact finiteCartierArrowEquation_of_class
    (R := Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) (A := A)
    N hN hA Y hWpow (quotientLine l E π n) d eW
    (lineW.iso l) sourceComparison.iso hc

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
