import Langlands.Automorphic.FiniteTensorHilbertSpherical

/-! # Whole scalar spectra and full-slice spherical comparison -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace Langlands.TensorHilbertHeckeAux

universe uA uB

variable {ι : Type uI}
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- A nonzero whole space on which every specified operator acts by its
specified scalar, rather than merely the existence of one joint eigenvector. -/
def HasScalarSpectrum (T : ι → Module.End ℂ A) (c : ι → ℂ) : Prop :=
  Nontrivial A ∧ ∀ i x, T i x = c i • x

/-- All scalar equations hold exactly when the actual joint eigenspace is top. -/
theorem jointEigenspace_eq_top_iff (T : ι → Module.End ℂ A) (c : ι → ℂ) :
    jointEigenspace T c = ⊤ ↔ ∀ i x, T i x = c i • x := by
  constructor
  · intro h i x
    exact (mem_jointEigenspace_iff T c x).mp (h ▸ Submodule.mem_top) i
  · intro h
    apply top_unique
    intro x _
    exact (mem_jointEigenspace_iff T c x).mpr (fun i => h i x)

theorem hasScalarSpectrum_iff_jointEigenspace (T : ι → Module.End ℂ A)
    (c : ι → ℂ) :
    HasScalarSpectrum T c ↔ Nontrivial A ∧ jointEigenspace T c = ⊤ := by
  rw [HasScalarSpectrum, jointEigenspace_eq_top_iff]

/-- A genuine intertwining equivalence transports nonzeroness and every
scalar equation, in independent carrier universes. -/
theorem hasScalarSpectrum_equiv_iff (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B) (c : ι → ℂ)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    HasScalarSpectrum U c ↔ HasScalarSpectrum T c := by
  constructor
  · rintro ⟨hne, hs⟩
    refine ⟨e.toEquiv.nontrivial_congr.mpr hne, ?_⟩
    intro i x
    apply e.injective
    rw [h, hs, map_smul]
  · rintro ⟨hne, hs⟩
    refine ⟨e.toEquiv.nontrivial_congr.mp hne, ?_⟩
    intro i z
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← h, hs, map_smul]

open MeasureTheory
universe uG uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ G W) (S : Subrepresentation τ)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Whole scalar spectra agree for the original smooth action and the
unchanged corner action on every full invariant-subspace fixed vector. -/
theorem hasScalarSpectrum_corner_iff {σ : Representation ℂ G A} (hσ : IsSmooth σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    HasScalarSpectrum (fun i => cornerAction τ S μ K hK (f i)) c ↔
      HasScalarSpectrum (fun i => Hecke.cornerAction μ σ hσ K hK (f i)) c :=
  hasScalarSpectrum_equiv_iff (TensorHilbertFixedAux.factorFixedEquiv τ S e K)
    _ _ c (fun i x => cornerAction_factor τ S μ K hK hσ e (f i) x)

end Langlands.TensorHilbertHeckeAux

namespace Langlands.TensorHilbertSphericalAux

open MeasureTheory
universe uA uW

variable {p : ℕ} [Fact p.Prime] (L : PadicField.{uF} p) (r : ℕ)

local instance sphericalComparisonTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopology n
local instance sphericalComparisonTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n L.Carrier) :=
  L.canonicalGeneralLinearTopologicalGroup n
local instance sphericalComparisonMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n L.Carrier) := borel _
local instance sphericalComparisonBorel (n : ℕ) :
    BorelSpace (GeneralLinear n L.Carrier) := ⟨rfl⟩
local instance sphericalComparisonHaar :
    (Unramified.sphericalHaar L r).IsHaarMeasure := Unramified.sphericalHaar_isHaar L r

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ (GeneralLinear (r + 1) L.Carrier) W)
variable (S : Subrepresentation τ)
variable (A : Correspondence.AutomorphicObject.{uF, uA} L r.succPNat)
variable (e : A.obj.representation.Equiv
  (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)

include e

/-- The actual canonical object's standard operators intertwine with the
full invariant-subspace corner operators through the existing fixed equivalence. -/
theorem objectStandardHeckeOperator_intertwine (i : Fin (r + 2))
    (x : fixedVectors A.obj.representation (Correspondence.sphericalSubgroup L r)) :
    TensorHilbertFixedAux.factorFixedEquiv τ S e (Unramified.sphericalOpenSubgroup L r)
        (Unramified.standardHeckeOperator L A i x) =
      TensorHilbertHeckeAux.cornerAction τ S (Unramified.sphericalHaar L r)
        (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r)
        (Unramified.standardHeckeElement L r i)
        (TensorHilbertFixedAux.factorFixedEquiv τ S e
          (Unramified.sphericalOpenSubgroup L r) x) :=
  TensorHilbertHeckeAux.cornerAction_factor τ S (Unramified.sphericalHaar L r)
    (Unramified.sphericalOpenSubgroup L r) (Unramified.sphericalOpenSubgroup_isCompact L r)
    A.obj.isSmooth e (Unramified.standardHeckeElement L r i) x

/-- Preserve the canonical object's actual joint eigenvectors and scalars in
the full invariant-subspace spherical fixed space. -/
def objectSphericalEigenspaceEquiv (s : Unramified.Eigenvalues (r + 1)) :
    TensorHilbertHeckeAux.jointEigenspace
      (Unramified.standardHeckeOperator L A) (Unramified.standardHeckeScalar L s) ≃ₗ[ℂ]
    TensorHilbertHeckeAux.cornerJointEigenspace τ S (Unramified.sphericalHaar L r)
      (Unramified.sphericalOpenSubgroup L r)
      (Unramified.sphericalOpenSubgroup_isCompact L r)
      (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s) :=
  TensorHilbertHeckeAux.factorJointCornerEquiv τ S (Unramified.sphericalHaar L r)
    (Unramified.sphericalOpenSubgroup L r) (Unramified.sphericalOpenSubgroup_isCompact L r)
    A.obj.isSmooth e (Unramified.standardHeckeElement L r) (Unramified.standardHeckeScalar L s)

/-- The existing whole-fixed-space spectrum relation is exactly the whole
scalar spectrum of the unchanged full invariant-subspace operators. -/
theorem objectHasSpectrum_iff (s : Unramified.Eigenvalues (r + 1)) :
    TensorHilbertHeckeAux.HasScalarSpectrum
      (fun i => TensorHilbertHeckeAux.cornerAction τ S (Unramified.sphericalHaar L r)
        (Unramified.sphericalOpenSubgroup L r)
        (Unramified.sphericalOpenSubgroup_isCompact L r)
        (Unramified.standardHeckeElement L r i))
      (Unramified.standardHeckeScalar L s) ↔
        Unramified.HasSphericalHeckeSpectrum L A s := by
  exact (TensorHilbertHeckeAux.hasScalarSpectrum_corner_iff τ S (Unramified.sphericalHaar L r)
    (Unramified.sphericalOpenSubgroup L r) (Unramified.sphericalOpenSubgroup_isCompact L r)
    A.obj.isSmooth e (Unramified.standardHeckeElement L r)
    (Unramified.standardHeckeScalar L s)).trans
      (and_congr Submodule.nontrivial_iff_ne_bot Iff.rfl)

end Langlands.TensorHilbertSphericalAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertComparisonRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertComparisonContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertComparisonSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertComparisonFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance tensorHilbertComparisonFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertComparisonLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Nonzero whole spherical fixed space with the actual standard operators
and the existing normalized scalars. Zero tails are allowed in the definition. -/
def HasHilbertSphericalSpectrum (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (s : Unramified.Eigenvalues (r + 1)) : Prop :=
  TensorHilbertHeckeAux.HasScalarSpectrum (P.sliceHilbertStandardHeckeOperator b v y)
    (Unramified.standardHeckeScalar (CompletionPadic.padicField v) s)

/-- The bundled canonical smooth object's actual joint eigenvectors identify
with those in the full closed Hilbert slice for the same normalized scalars. -/
def sliceHilbertPadicSphericalEigenspaceEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v))
    (s : Unramified.Eigenvalues (r + 1)) :
    TensorHilbertHeckeAux.jointEigenspace
      (Unramified.standardHeckeOperator (CompletionPadic.padicField v)
        (P.sliceHilbertPadicObject b v y hy hI hA))
      (Unramified.standardHeckeScalar (CompletionPadic.padicField v) s) ≃ₗ[ℂ]
        P.sliceHilbertSphericalEigenspace b v y s :=
  TensorHilbertSphericalAux.objectSphericalEigenspaceEquiv
    (CompletionPadic.padicField v) r _ (P.sliceHilbertRange b v y)
    (P.sliceHilbertPadicObject b v y hy hI hA)
    (P.sliceHilbertCanonicalSmoothEquiv b v y) s

/-- The canonical smooth-object spectrum is equivalent to the spectrum of
all spherical fixed vectors of the full closed Hilbert slice. -/
theorem sliceHilbertPadicObject_hasHilbertSpectrum_iff (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hI : (ρ v).IsIrreducible) (hA : IsAdmissible (ρ v))
    (s : Unramified.Eigenvalues (r + 1)) :
    P.HasHilbertSphericalSpectrum b v y s ↔
      Unramified.HasSphericalHeckeSpectrum (CompletionPadic.padicField v)
        (P.sliceHilbertPadicObject b v y hy hI hA) s :=
  TensorHilbertSphericalAux.objectHasSpectrum_iff
    (CompletionPadic.padicField v) r _ (P.sliceHilbertRange b v y)
    (P.sliceHilbertPadicObject b v y hy hI hA)
    (P.sliceHilbertCanonicalSmoothEquiv b v y) s

namespace UnramifiedData

variable {P} {hS : S.IsNonzero F (r + 1)} {T : Finset (FinitePlace F)}
variable (D : P.UnramifiedData hS T)

/-- Supplied unramified data govern all full closed-slice spherical fixed
vectors, preserving nonzeroness and the original eigenvalues. -/
theorem hasHilbertSpectrum (v : FinitePlace F) (hv : v ∉ T)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    P.HasHilbertSphericalSpectrum b v y (D.eigenvalues v hv) :=
  (P.sliceHilbertPadicObject_hasHilbertSpectrum_iff b v y hy
    (D.irreducible v hv) (D.admissible v hv) (D.eigenvalues v hv)).mpr
      (D.hasSpectrum_hilbertSmooth b v hv y hy)

end UnramifiedData
end FiniteTensorPresentation
end Langlands.Automorphic
