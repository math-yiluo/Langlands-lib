import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationStatement
import Langlands.Automorphic.OperatorLocalRestriction
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.AdelicRestrictionSplitCentreCanonical
import Langlands.Global.Factors.CuspidalPairPoleStatement
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Reductive.GeneralLinear
import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Unitary.DiscretePart
import Langlands.Representation.Unramified.HeckeOperators

/-! # Discrete automorphic representations of `GL_n` with the Hecke eigenvalues of a cuspidal one

Strong multiplicity one for the discrete spectrum of `GL_{r+1}` over a number field relative to a
cuspidal representation, with multiplicity one: an irreducible closed invariant subspace `Π` of
`L²([GL_{r+1}])` which at almost every finite place has nonzero spherical vectors on which the
spherical Hecke algebra acts by the character of a cuspidal realization `S` trivial on the positive
split centre is the closure `V_S` of the `L²` classes of the forms of `S`. The statement is derived
from Mœglin–Waldspurger, *Le spectre résiduel de `GL(n)`* (1989), Jacquet–Shalika, *On Euler
products and the classification of automorphic forms II* (1981), Theorem 4.4, and Getz–Hahn,
Theorems 10.8.1, 11.4.3 and 11.7.2 and Corollary 11.7.3; the paired Markdown gives the argument.

The module defines the spherical Hecke action on the spherical smooth vectors of an arbitrary
representation of `GL_{r+1}(F_p)`, the restriction of `L²([GL_{r+1}])` to `GL_{r+1}(F_p)`, the
`L²` class of a matrix-model form and the subspace `V_S`, and states the proposition. It contains
no proof. -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic.DiscreteHeckeIsolation

open Langlands.Global Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

local instance discreteHeckeGeneralLinearIsAffine (F : Type) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance discreteHeckeGeneralLinearLocallyOfFiniteType (F : Type) [Field F] (n : ℕ) :
    LocallyOfFiniteType (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  have := IsConnectedReductive.smooth (isConnectedReductive_generalLinear F (Fin n))
  inferInstance

local instance discreteHeckeRationalAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance discreteHeckeContinuousAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance discreteHeckeSmoothAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance discreteHeckeFormsAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance discreteHeckeStableAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance discreteHeckeRealizationAddCommGroup (F : Type) [Field F] [NumberField F] (n : ℕ)
    (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

section Local

variable {F : Type} [Field F] [NumberField F] {p : Langlands.Global.FinitePlace F}

local instance discreteHeckeLocalTopology (n : ℕ) : TopologicalSpace (FiniteLocalGL F n p) :=
  (CompletionPadic.padicField p).canonicalGeneralLinearTopology n
local instance discreteHeckeLocalTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F n p) :=
  (CompletionPadic.padicField p).canonicalGeneralLinearTopologicalGroup n
local instance discreteHeckeLocalMeasurable (n : ℕ) : MeasurableSpace (FiniteLocalGL F n p) :=
  borel _
local instance discreteHeckeLocalBorel (n : ℕ) : BorelSpace (FiniteLocalGL F n p) := ⟨rfl⟩
local instance discreteHeckeLocalHaar (r : ℕ) :
    (Unramified.sphericalHaar (CompletionPadic.padicField p) r).IsHaarMeasure :=
  Unramified.sphericalHaar_isHaar (CompletionPadic.padicField p) r

variable {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The spherical Hecke algebra of `GL_{r+1}(F_p)` (the Library's mass-one corner
`Unramified.SphericalHeckeAlgebra` for the subgroup `GL_{r+1}(𝒪_p)`) acting on the vectors of the
smooth part of `σ` fixed by `GL_{r+1}(𝒪_p)`, by the Library's `Hecke.cornerAction`. -/
def smoothSphericalHeckeAction (σ : Representation ℂ (FiniteLocalGL F (r + 1) p) V) :
    Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r →ₐ[ℂ]
      Module.End ℂ (Langlands.fixedVectors (Langlands.smoothPart σ)
        (Correspondence.sphericalSubgroup (CompletionPadic.padicField p) r)) :=
  Hecke.cornerAction (Unramified.sphericalHaar (CompletionPadic.padicField p) r)
    (Langlands.smoothPart σ) (Langlands.isSmooth_smoothPart σ)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField p) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField p) r)

/-- The subspace `W` of the space of `σ` has spherical Hecke character `χ` at `p`: some nonzero
vector of `W` is fixed by `GL_{r+1}(𝒪_p)`, and every element `h` of the spherical Hecke algebra
acts on every vector of `W` fixed by `GL_{r+1}(𝒪_p)` as multiplication by `χ h`. -/
def HasSphericalHeckeCharacterOn (σ : Representation ℂ (FiniteLocalGL F (r + 1) p) V)
    (W : Submodule ℂ V)
    (χ : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r →ₐ[ℂ] ℂ) : Prop :=
  (∃ x : Langlands.fixedVectors (Langlands.smoothPart σ)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField p) r),
    ((x : Langlands.smoothVectors σ) : V) ∈ W ∧ x ≠ 0) ∧
  ∀ (h : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r)
    (x : Langlands.fixedVectors (Langlands.smoothPart σ)
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField p) r)),
    ((x : Langlands.smoothVectors σ) : V) ∈ W → smoothSphericalHeckeAction σ h x = χ h • x

end Local

section Global

variable (F : Type) [Field F] [NumberField F] (r : ℕ)

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => isConnectedReductive_generalLinear F (Fin (r + 1))

/-- The right regular representation of `GL_{r+1}(𝔸_F)` on `L²([GL_{r+1}])` (canonical measure),
restricted to `GL_{r+1}(F_p)` in the matrix model: a matrix is sent to the local point of the group
scheme with that matrix (`GroupScheme.GeneralLinear.affinePointsEquiv`), which is inserted at the
place `p` (`AdelicGroupPoints.ofPlace`). -/
def canonicalL2LocalAction (p : Langlands.Global.FinitePlace F) :
    Representation ℂ (FiniteLocalGL F (r + 1) p)
      (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F GLG)) :=
  (RestrictionSplitCentre.canonicalL2RightAction F GLG centralSplitTorusCharacter hG).comp
    ((AdelicGroupPoints.ofPlace F GLG (.inr p)).comp
      (GroupScheme.GeneralLinear.affinePointsEquiv (Fin (r + 1)) (CommRingCat.of F)
        (placeCompletion F (.inr p))).symm.toMonoidHom)

/-- The class `φ ∈ L²([GL_{r+1}])` (canonical measure) is the class of the matrix-model continuous
function `f`: under the Library's identification `RestrictionSplitCentre.canonicalL2Equiv` of
`L²` of the positive quotient of the chosen split component of `GL_{r+1}` with `L²([GL_{r+1}])`,
`φ` corresponds to the class of `f` in the sense of `IsGeneralLinearFormClass`. -/
def IsCanonicalGeneralLinearFormClass (φ : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F GLG))
    (f : ContinuousRationalFunctions F (r + 1)) : Prop :=
  IsGeneralLinearFormClass F r (RestrictionSplitCentre.canonicalTorus F GLG)
    (RestrictionSplitCentre.canonicalComponent F GLG)
    ((RestrictionSplitCentre.canonicalL2Equiv F GLG).symm φ) f

variable [CompactSpace (AdeleQuotient F)]

/-- The subspace `V_S` of `L²([GL_{r+1}])` attached to a cuspidal realization `S`: the closure of
the span of the `L²` classes of the forms of `S`. -/
def cuspidalRealizationClosure (S : CuspidalOperatorRealization F r) :
    Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F GLG)) :=
  (Submodule.span ℂ {φ | ∃ f : S.Space,
    IsCanonicalGeneralLinearFormClass F r φ (S.realization.toContinuous f)}).topologicalClosure

end Global

/-- **An irreducible summand of `L²([GL_{r+1}])` with the Hecke eigenvalues of a cuspidal
representation at almost every place is that cuspidal representation.** Let `F` be a number field
whose adele quotient is compact, `r : ℕ`, and `S` a cuspidal realization of `GL_{r+1}` trivial on
the positive split centre. Let `P` be a nonzero closed `GL_{r+1}(𝔸_F)`-invariant subspace of
`L²([GL_{r+1}])` with no closed invariant subspace other than `0` and `P`. Suppose that for every
finite place `p` outside a finite set `E` there is a character `χ` of the spherical Hecke algebra
of `GL_{r+1}(F_p)` such that `P` and the space of `S` have nonzero vectors fixed by
`GL_{r+1}(𝒪_p)`, and the Hecke algebra acts on all such vectors of `P` and of `S` by `χ`. Then every
form of `S` has an `L²` class on `[GL_{r+1}]`, and `P` is the closure `V_S` of the span of these
classes. -/
def GeneralLinearDiscreteCuspidalHeckeIsolationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (S : CuspidalOperatorRealization F r),
    CuspidalPairPoles.IsTrivialOnSplitCentre S →
    ∀ P : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F
        (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))),
      Langlands.Analysis.IsIrreducibleSubrepresentation
        (RestrictionSplitCentre.canonicalL2RightAction F
          (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
          centralSplitTorusCharacter (isConnectedReductive_generalLinear F (Fin (r + 1)))) P →
      ∀ E : Finset (Langlands.Global.FinitePlace F),
        (∀ p ∉ E, ∃ χ : Unramified.SphericalHeckeAlgebra (CompletionPadic.padicField p) r →ₐ[ℂ] ℂ,
          HasSphericalHeckeCharacterOn (canonicalL2LocalAction F r p) P χ ∧
            HasSphericalHeckeCharacterOn (S.realization.localRepresentation p) ⊤ χ) →
        (∀ f : S.Space,
            ∃ φ, IsCanonicalGeneralLinearFormClass F r φ (S.realization.toContinuous f)) ∧
          P = cuspidalRealizationClosure F r S

end Langlands.Automorphic.DiscreteHeckeIsolation
