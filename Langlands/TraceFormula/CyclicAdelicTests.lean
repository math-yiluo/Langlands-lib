import Langlands.TraceFormula.GeneralLinearBaseChangeLocal
import Langlands.TraceFormula.GeneralLinearWeilAdelicTwistStatement
import Langlands.Automorphic.GroupSchemeInvariantForms
import Langlands.BaseChange.OrbitalIntegral
import Langlands.Global.ArchimedeanCompact

/-! # Factorizable tests for the prime cyclic discrete trace comparison -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj Langlands.TraceFormula.PlaceCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme Langlands.BaseChange
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.TraceFormula.AdelicGroupAutomorphism

/-- The base general linear group of the comparison. -/
abbrev cyclicBaseGroup (F : Type u) [Field F] (n : ℕ) : GroupScheme (Spec (CommRingCat.of F)) :=
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance cyclicBaseGroup_affine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (cyclicBaseGroup F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance cyclicBaseGroup_smooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (cyclicBaseGroup F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- The identity component whose `σ` component acts on the upper side. -/
abbrev cyclicWeilGroup (F E : Type u) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (n : ℕ) : GroupScheme (Spec (CommRingCat.of F)) :=
  weilGroup F E (cyclicBaseGroup F n)

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [FiniteDimensional F E] (n : ℕ)

/-- The underlying map of the adelic Weil-restriction comparison from Task 7340. -/
def cyclicWeilAdelicMap : AdelicGroupPoints F (cyclicWeilGroup F E n) → AdelicGL E n := fun g =>
  GeneralLinearGroupPoints.adelicHomeomorph E n
    (AdelicGroupPoints.map E (AffineWeil.unitBaseChange F E (cyclicBaseGroup F n))
      (cyclicBaseGroup E n)
      (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap F E)).hom
      (AdelicGaloisUnit.weilAdelicEquiv F E (cyclicBaseGroup F n) g))

/-- The standard infinite compact inside the full adelic matrix group, with finite coordinate
one. -/
def adelicInfiniteStandardCompact (K : Type u) [Field K] [NumberField K] (r : ℕ) :
    Subgroup (AdelicGL K r) :=
  (standardInfiniteCompact K r).comap (AdelicGL.infinite K r).toMonoidHom ⊓
    (AdelicGL.finite K r).toMonoidHom.ker

section Tests

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]

/-- A compactly supported smooth adelic test with finitely many left and right infinite compact
types. `κ` maps to the actual full adelic matrix points on the corresponding side. -/
def IsCyclicTraceTest (A : Type u) [Group A] (κ : AdelicGroupPoints F G → A) (K : Subgroup A)
    (h : AdelicGroupPoints F G → ℂ) : Prop :=
  HasCompactSupport h ∧ IsAdelicSmoothFunction F G h ∧
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun k : {g // κ g ∈ K} =>
      fun x => h (k.val * x))) ∧
    Module.Finite ℂ (Submodule.span ℂ (Set.range fun k : {g // κ g ∈ K} =>
      fun x => h (x * k.val)))

/-- A factorizable test has compact local factors, locally constant at the finite places.
All the infinite places are in `S` and the outside factors are the integral units. -/
def IsFactorizableCyclicTraceTest (A : Type u) [Group A] (κ : AdelicGroupPoints F G → A)
    (K : Subgroup A) (U : (v : Place F) → Subgroup (PlaceGroupPoints F G v))
    (S : Finset (Place F)) (h : AdelicGroupPoints F G → ℂ)
    (hlocal : (v : Place F) → PlaceGroupPoints F G v → ℂ) : Prop :=
  IsCyclicTraceTest F A κ K h ∧ (∀ v : NumberField.InfinitePlace F, .inl v ∈ S) ∧
    (∀ v ∈ S, Continuous (hlocal v) ∧ HasCompactSupport (hlocal v)) ∧
    (∀ v : Langlands.Global.FinitePlace F, .inr v ∈ S → IsLocallyConstant (hlocal (.inr v))) ∧
    (∀ v ∉ S, hlocal v = (U v : Set _).indicator (fun _ => 1)) ∧
    IsAdelicFactorization F S hlocal U h

end Tests

local instance cyclicMeasureSpace {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {r : ℕ} : MeasurableSpace (GeneralLinear r R) := borel _

local instance cyclicBorelSpace {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {r : ℕ} : BorelSpace (GeneralLinear r R) := ⟨rfl⟩

/-- The local Haar measures on the actual base completion and the local scalar extension. -/
structure CyclicLocalHaarData where
  base (v : Place F) : Measure (GeneralLinear n (placeCompletion F v))
  upper (v : Place F) : Measure (GeneralLinear n (LocalBaseChangeAlgebra F E v))
  base_haar (v : Place F) : (base v).IsHaarMeasure
  upper_haar (v : Place F) : (upper v).IsHaarMeasure

variable {F E n}

/-- The distinguished integral subgroups have volume one on both sides at every omitted
place. -/
def CyclicLocalHaarData.HasUnitTail (H : CyclicLocalHaarData F E n)
    (S : Finset (Place F)) : Prop :=
  ∀ v : Place F, v ∉ S →
    H.base v (localGLEquiv F n v '' (glIntegralFamily F n v : Set _)) = 1 ∧
    H.upper v (localPointsEquiv F E n v '' (localIntegralFamily F E n v : Set _)) = 1

/-- Regular concordance on the actual local points at every base place, including the unit
factors at places outside the common exceptional set. The global cyclic algebra condition
specifies the generator and the length of every local norm. -/
def CyclicLocalHaarData.Matches (H : CyclicLocalHaarData F E n) (σ : E ≃ₐ[F] E)
    (f : (v : Place F) → PlaceGroupPoints F (cyclicBaseGroup F n) v → ℂ)
    (φ : (v : Place F) → PlaceGroupPoints F (cyclicWeilGroup F E n) v → ℂ) : Prop :=
  IsCyclicAlgebra σ (Module.finrank F E) ∧
  ∀ v : Place F,
    AreConcordant (localGalois F E σ v) (Module.finrank F E) (H.base v) (H.upper v)
      (φ v ∘ (localPointsEquiv F E n v).symm) (f v ∘ (localGLEquiv F n v).symm)

/-- A factorizable associated pair for the discrete comparison. The maximal integral
subgroups have volume one outside the exceptional set. -/
def IsFactorizableCyclicMatch (H : CyclicLocalHaarData F E n) (σ : E ≃ₐ[F] E)
    (S : Finset (Place F)) (f : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ)
    (φ : AdelicGroupPoints F (cyclicWeilGroup F E n) → ℂ) : Prop :=
  ∃ (flocal : (v : Place F) → PlaceGroupPoints F (cyclicBaseGroup F n) v → ℂ)
    (φlocal : (v : Place F) → PlaceGroupPoints F (cyclicWeilGroup F E n) v → ℂ),
    IsFactorizableCyclicTraceTest F (AdelicGL F n) (GeneralLinearGroupPoints.adelicHomeomorph F n)
      (adelicInfiniteStandardCompact F n) (glIntegralFamily F n) S f flocal ∧
    IsFactorizableCyclicTraceTest F (AdelicGL E n) (cyclicWeilAdelicMap F E n)
      (adelicInfiniteStandardCompact E n) (localIntegralFamily F E n) S φ φlocal ∧
    H.Matches σ flocal φlocal ∧ H.HasUnitTail S

/-- Ambient Haar measures normalized to integrate factorizable tests as the product of their
local integrals. A common finite level of unit tail volumes exists, and the product formula
is required at every such level. -/
def CyclicLocalHaarData.IsCompatible (H : CyclicLocalHaarData F E n)
    (μF : Measure (AdelicGroupPoints F (cyclicBaseGroup F n)))
    (μE : Measure (AdelicGroupPoints F (cyclicWeilGroup F E n))) : Prop :=
  μF.IsHaarMeasure ∧ μE.IsHaarMeasure ∧ (∃ S, H.HasUnitTail S) ∧
    (∀ S f flocal,
      IsFactorizableCyclicTraceTest F (AdelicGL F n) (GeneralLinearGroupPoints.adelicHomeomorph F n)
        (adelicInfiniteStandardCompact F n) (glIntegralFamily F n) S f flocal →
      H.HasUnitTail S →
      ∫ g, f g ∂μF = ∏ v ∈ S, ∫ x, flocal v ((localGLEquiv F n v).symm x) ∂H.base v) ∧
    (∀ S φ φlocal,
      IsFactorizableCyclicTraceTest F (AdelicGL E n) (cyclicWeilAdelicMap F E n)
        (adelicInfiniteStandardCompact E n) (localIntegralFamily F E n) S φ φlocal →
      H.HasUnitTail S →
      ∫ g, φ g ∂μE = ∏ v ∈ S, ∫ x, φlocal v ((localPointsEquiv F E n v).symm x) ∂H.upper v)

/-- The linear span of the factorizable associated pairs, in base-then-upper order, for the
full cyclic norm. -/
def cyclicMatchedTests (H : CyclicLocalHaarData F E n) (σ : E ≃ₐ[F] E) :
    Submodule ℂ ((AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) ×
      (AdelicGroupPoints F (cyclicWeilGroup F E n) → ℂ)) :=
  Submodule.span ℂ {p | ∃ S, IsFactorizableCyclicMatch H σ S p.1 p.2}

end Langlands.TraceFormula
