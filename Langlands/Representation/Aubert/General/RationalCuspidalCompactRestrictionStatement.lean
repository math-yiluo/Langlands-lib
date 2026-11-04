import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.SupportCategory
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.CompactCoefficient.AmbientProjector
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.BruhatTits.SpecialCompact.Properties
import Langlands.BruhatTits.SpecialCompact.StandardBasisProperty
import Langlands.Geometry.Building.SpecialCompact
import Langlands.Geometry.Building.CocharacterUniformizer
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Renard VI.2.1, (a) implies (c), on the actual rational-point group

A smooth complex representation of the actual rational-point group whose normalized
Jacquet modules vanish along every proper actual standard parabolic has compact
smooth-dual coefficients after restriction to the actual common norm kernel.
The only structural antecedents are the standard-cocharacter comparisons, the
relative-root-system realization, the special compact and simultaneous basis
properties of one geometric `K₀`, and the covering clause of the Cartan
decomposition over that same `K₀`. Nothing is proved here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.SpecialCompact

/-- Only the covering clause of Renard V.5.1(4): a finite set `F₀` of actual torus
centralizer points such that every rational point lies in some `K₀ f a K₀` with
`f ∈ F₀` and `a` in the actual `C_A^+` of the simple relative roots. No disjointness,
lattice or representative law is included. -/
abbrev FiniteCartanCovering (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (K0 : Subgroup (rationalPoints G)) :
    Prop :=
  ∃ F0 : Finset (centralizerPoints i), ∀ g : rationalPoints G,
    ∃ (k₁ k₂ : rationalPoints G) (f : centralizerPoints i) (a : rationalPoints S.toGrp),
      k₁ ∈ K0 ∧ k₂ ∈ K0 ∧ f ∈ F0 ∧
        a ∈ CocharacterUniformizer.CAplus F S (simpleRelativeRoots i ν) ∧
        g = k₁ * (f : rationalPoints G) * rationalPoints.map i a * k₂

/-- Renard VI.2.1, (a) implies (c), for every smooth complex representation of the
actual rational-point group with the canonical topology. Cuspidality is vanishing of
the normalized Jacquet module for every proper subset of the actual simple roots. -/
def RationalCuspidalCompactRestrictionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (RationalPoint F G.X)]
      [NonarchimedeanGroup (RationalPoint F G.X)] [T2Space (RationalPoint F G.X)]
      (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint F G.X)))
      (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment),
      D.IsSpecialApartmentVertex x →
      let K0 := D.specialCompactSubgroup x
      SpecialCompactProperties F i ν K0 →
      SimultaneousStandardBasisAt i ν K0 →
      FiniteCartanCovering F i ν K0 →
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      let h := isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν
      ∀ A : SmoothRep.{0, u, v} ℂ (RationalPoint F G.X),
        IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
        HasCompactSmoothDualCoefficients
          (SmoothRep.restrictSubgroup (Plancherel.rationalCommonNormKernel G) A).representation

end Langlands.Aubert.General.RationalPointFamily
