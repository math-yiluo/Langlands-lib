import Langlands.Automorphic.FiniteTensorHilbertHeckeEigenspace
import Langlands.Automorphic.FiniteTensorHilbertPadic

/-! # Canonical spherical operators on full completed tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorPadicAux

universe uR uG uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {W : Type uW} [AddCommGroup W] [Module R W]

/-- Equal group topologies identify the smooth intersections by the identity
on the original ambient vectors and action. -/
def smoothInfTopologyEquiv (t t' : TopologicalSpace G) (heq : t = t')
    (ht : @IsTopologicalGroup G t _) (ht' : @IsTopologicalGroup G t' _)
    (τ : Representation R G W) (S : Subrepresentation τ) :
    (letI := t; letI := ht;
      (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation).Equiv
    (letI := t'; letI := ht';
      (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation) := by
  subst t'
  exact Representation.Equiv.refl _

theorem smoothInfTopologyEquiv_apply_val (t t' : TopologicalSpace G) (heq : t = t')
    (ht : @IsTopologicalGroup G t _) (ht' : @IsTopologicalGroup G t' _)
    (τ : Representation R G W) (S : Subrepresentation τ)
    (x : (letI := t; letI := ht;
      (S ⊓ Langlands.smoothSubrepresentation τ).toSubmodule)) :
    (smoothInfTopologyEquiv t t' heq ht ht' τ S x).val = x.val := by
  subst t'
  rfl

theorem smoothInfTopologyEquiv_symm_apply_val (t t' : TopologicalSpace G) (heq : t = t')
    (ht : @IsTopologicalGroup G t _) (ht' : @IsTopologicalGroup G t' _)
    (τ : Representation R G W) (S : Subrepresentation τ)
    (x : (letI := t'; letI := ht';
      (S ⊓ Langlands.smoothSubrepresentation τ).toSubmodule)) :
    ((smoothInfTopologyEquiv t t' heq ht ht' τ S).symm x).val = x.val := by
  subst t'
  rfl

/-- Smoothness is transported along equality of the group topologies. -/
theorem isSmoothOfTopologyEq (t t' : TopologicalSpace G) (heq : t = t')
    (τ : Representation R G W) (hs : @IsSmooth R G W _ _ _ _ t τ) :
    @IsSmooth R G W _ _ _ _ t' τ := heq ▸ hs

end Langlands.TensorPadicAux

namespace Langlands.Automorphic

open MeasureTheory
open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertSphericalRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertSphericalContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertSphericalSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertSphericalFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertSphericalFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertSphericalLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual smooth slice identifies with the ambient smooth intersection
for the canonical local topology, without a nonzero-tail hypothesis. -/
def sliceHilbertCanonicalSmoothEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  Langlands.TensorPadicAux.smoothInfTopologyEquiv _ _
    (localGL_topology_eq F v (r + 1)) inferInstance
    ((CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1))
    (b.completedRepresentation.comp (localInclusion F (r + 1) v).toMonoidHom)
    (P.sliceHilbertRange b v y)

/-- The same smooth slice is smooth for the canonical local topology. -/
theorem sliceHilbertSmoothRange_isSmooth_canonical (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    @IsSmooth ℂ (FiniteLocalGL F (r + 1) v)
      (P.sliceHilbertSmoothRange b v y).toSubmodule _ _ _ _
      ((CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1))
      (P.sliceHilbertSmoothRange b v y).toRepresentation :=
  Langlands.TensorPadicAux.isSmoothOfTopologyEq _ _
    (localGL_topology_eq F v (r + 1)) _
    (P.sliceHilbertSmoothRange_isSmooth b v y)

local instance tensorHilbertSphericalTopology (v : FinitePlace F) :
    TopologicalSpace (FiniteLocalGL F (r + 1) v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)
local instance tensorHilbertSphericalTopologicalGroup (v : FinitePlace F) :
    IsTopologicalGroup (FiniteLocalGL F (r + 1) v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)
local instance tensorHilbertSphericalMeasurable (v : FinitePlace F) :
    MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
local instance tensorHilbertSphericalBorel (v : FinitePlace F) :
    BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩
local instance tensorHilbertSphericalHaar (v : FinitePlace F) :
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r).IsHaarMeasure :=
  Unramified.sphericalHaar_isHaar (CompletionPadic.padicField v) r

/-- Canonical spherical fixed vectors of the whole closed slice. -/
abbrev SliceHilbertSphericalVectors (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  fixedVectors (P.sliceHilbertRange b v y).toRepresentation
    (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r)

/-- The mass-one canonical spherical corner acts on the entire fixed space. -/
def sliceHilbertSphericalAction (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  TensorHilbertHeckeAux.cornerAction
    _
    (P.sliceHilbertRange b v y)
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)

/-- The same action by bounded operators for the inherited global Hilbert norm. -/
def sliceHilbertSphericalContinuousAction (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  TensorHilbertHeckeAux.cornerContinuousAction
    (Unramified.sphericalHaar (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)
    (Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r)
    _
    (P.sliceHilbertRange b v y)
    (fun g x => b.completedRepresentation_norm (localInclusion F (r + 1) v g) x)

/-- The actual-vector equivalence from the original smooth-slice fixed space
onto the entire closed-slice spherical fixed space. -/
def sliceHilbertSphericalFixedEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  TensorHilbertFixedAux.factorFixedEquiv
    _
    (P.sliceHilbertRange b v y) (P.sliceHilbertCanonicalSmoothEquiv b v y)
    (Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r)

/-- The standard diagonal double-coset operator on the full closed slice. -/
def sliceHilbertStandardHeckeOperator (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (i : Fin (r + 2)) :
    Module.End ℂ (P.SliceHilbertSphericalVectors b v y) :=
  P.sliceHilbertSphericalAction b v y
    (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i)

/-- The unchanged standard operator as a continuous linear map. -/
def sliceHilbertStandardContinuousHeckeOperator (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (i : Fin (r + 2)) :
    P.SliceHilbertSphericalVectors b v y →L[ℂ] P.SliceHilbertSphericalVectors b v y :=
  P.sliceHilbertSphericalContinuousAction b v y
    (Unramified.standardHeckeElement (CompletionPadic.padicField v) r i)

/-- The actual joint eigenspace for the prescribed normalized standard scalars. -/
def sliceHilbertSphericalEigenspace (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (s : Unramified.Eigenvalues (r + 1)) :
    Submodule ℂ (P.SliceHilbertSphericalVectors b v y) :=
  TensorHilbertHeckeAux.jointEigenspace (P.sliceHilbertStandardHeckeOperator b v y)
    (Unramified.standardHeckeScalar (CompletionPadic.padicField v) s)

end FiniteTensorPresentation
end Langlands.Automorphic
