import Langlands.Automorphic.GeneralLinearDiscreteCuspidalHeckeIsolationStatement
import Langlands.Automorphic.GroupSchemeRestrictionCanonicalCuspidalL2
import Langlands.Automorphic.IsobaricData
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # The spherical Hecke data of noncuspidal discrete general linear representations

The unramified consequence of the residual spectrum theorem of Mœglin and Waldspurger. A
noncuspidal irreducible closed subrepresentation of canonical `L²([GL_n])` has, at almost all
finite places, the Euler polynomials of a family of at least two actual cuspidal constituents.
Getz–Hahn, §10.8 and Theorem 10.8.1, give the split-centre formulation and the Euler factors. -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped BigOperators CategoryTheory.MonObj

set_option autoImplicit false

universe uV

namespace Langlands.Automorphic.DiscreteHeckeIsolation

open Langlands.Global Langlands.GroupScheme Langlands.Unramified
open RestrictionSplitCentre

local instance (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type) [Field F] (n : ℕ) :
    LocallyOfFiniteType (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  have := IsConnectedReductive.smooth (isConnectedReductive_generalLinear F (Fin n))
  inferInstance

/-- The normalized spherical Hecke data of a noncuspidal irreducible summand of
`L²([GL_{r+1}])` are isobaric data with at least two constituents. The finite-place systems of
these constituents are attached through actual cuspidal spectral presentations. -/
def GeneralLinearResidualIsobaricHeckeDataStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ),
    let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
    let hG := isConnectedReductive_generalLinear F (Fin (r + 1))
    ∀ (P : Submodule ℂ (Lp ℂ 2 (canonicalMeasure F G))),
      Langlands.Analysis.IsIrreducibleSubrepresentation
        (canonicalL2RightAction F G centralSplitTorusCharacter hG) P →
      ¬ P ≤ canonicalFullAEL2CuspidalSubmodule F G centralSplitTorusCharacter parabolicDynamic hG →
      ∃ (m : ℕ) (c : Fin m → PositiveRankCuspidalClass F)
        (t : ∀ j, SpectralSystem (Global.FinitePlace F) (c j).rank)
        (s : SpectralSystem (Global.FinitePlace F) (r + 1)),
        1 < m ∧ (∑ j, (c j).rank) = r + 1 ∧
        (∀ j, PositiveRankCuspidalClass.HasSpectralSystem.{0, uV} (c j) (t j)) ∧
        (SpectralSystem.finiteSum t).SameEulerPolynomials s ∧
        ∀ (p : Global.FinitePlace F) (hp : p ∉ s.exceptional),
          ∃ χ : SphericalHeckeAlgebra (CompletionPadic.padicField p) r →ₐ[ℂ] ℂ,
            HasSphericalHeckeCharacterOn (canonicalL2LocalAction F r p) P χ ∧
            ∀ i : Fin (r + 2),
              χ (standardHeckeElement (CompletionPadic.padicField p) r i) =
                standardHeckeScalar (CompletionPadic.padicField p) (s.eigenvalues p hp) i

end Langlands.Automorphic.DiscreteHeckeIsolation
