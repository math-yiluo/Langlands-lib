import Langlands.Automorphic.FiniteTensorHilbertFullSphericalProjection
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Data.Set.Finite.Lattice

/-! # Finite scalar spectral support of actual tensor Hilbert slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uA uB uG uH

variable {ι : Type uI}
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- Scalar systems with an actual nonzero common eigenvector for the specified
original operators. This is point spectral support, not whole-space spectrum. -/
def jointScalarSupport (T : ι → Module.End ℂ A) : Set (ι → ℂ) :=
  {c | jointEigenspace T c ≠ ⊥}

theorem mem_jointScalarSupport_iff (T : ι → Module.End ℂ A) (c : ι → ℂ) :
    c ∈ jointScalarSupport T ↔ ∃ x : A, x ≠ 0 ∧ ∀ i, T i x = c i • x := by
  constructor
  · intro hc
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    exact ⟨x, hx0, (mem_jointEigenspace_iff T c x).mp hx⟩
  · rintro ⟨x, hx0, hx⟩ hbot
    apply hx0
    exact (Submodule.mem_bot ℂ).mp
      (hbot ▸ (mem_jointEigenspace_iff T c x).mpr hx)

/-- A genuine intertwining equivalence preserves the entire scalar support,
including the empty support and independently sized carrier spaces. -/
theorem jointScalarSupport_equiv (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    jointScalarSupport U = jointScalarSupport T := by
  ext c
  exact jointEigenspace_ne_bot_iff e T U c h

/-- Every coordinate of an occurring scalar system is an actual eigenvalue. -/
theorem jointScalarSupport_subset (T : ι → Module.End ℂ A) :
    jointScalarSupport T ⊆ {c | ∀ i, (T i).HasEigenvalue (c i)} := by
  intro c hc i
  obtain ⟨x, hx0, hx⟩ := (mem_jointScalarSupport_iff T c).mp hc
  exact Module.End.hasEigenvalue_of_hasEigenvector
    ⟨(Module.End.mem_eigenspace_iff).mpr (hx i), hx0⟩

/-- A finite family on a finite-dimensional space has finite scalar support.
No commuting, normality or simultaneous diagonalization is required. -/
theorem finite_jointScalarSupport [Finite ι] [FiniteDimensional ℂ A]
    (T : ι → Module.End ℂ A) : (jointScalarSupport T).Finite := by
  refine (Set.Finite.pi (fun i => (T i).finite_hasEigenvalue)).subset ?_
  intro c hc i _
  exact jointScalarSupport_subset T hc i

/-- Whole-space scalar spectrum forces exactly one occurring scalar system,
with nonzeroness supplied by the original whole-spectrum relation. -/
theorem jointScalarSupport_eq_singleton (T : ι → Module.End ℂ A) (c : ι → ℂ)
    (hc : HasScalarSpectrum T c) : jointScalarSupport T = {c} := by
  ext d
  constructor
  · intro hd
    obtain ⟨x, hx0, hx⟩ := (mem_jointScalarSupport_iff T d).mp hd
    apply Set.mem_singleton_iff.mpr
    funext i
    exact smul_left_injective ℂ hx0 ((hx i).symm.trans (hc.2 i x))
  · intro hd
    have hd' : d = c := Set.mem_singleton_iff.mp hd
    subst d
    let : Nontrivial A := hc.1
    obtain ⟨x, hx0⟩ := exists_ne (0 : A)
    exact (mem_jointScalarSupport_iff T c).mpr ⟨x, hx0, fun i => hc.2 i x⟩

section Corner

open MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {W : Type uH} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ G W) (S : Subrepresentation τ)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- Point scalar support of the original corner operators on every fixed
vector of the invariant subspace. -/
def cornerScalarSupport (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) : Set (ι → ℂ) :=
  jointScalarSupport (fun i => cornerAction τ S μ K hK (f i))

theorem cornerScalarSupport_eq_model {σ : Representation ℂ G A} (hσ : IsSmooth σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) :
    cornerScalarSupport τ S μ K hK f =
      jointScalarSupport (fun i => Hecke.cornerAction μ σ hσ K hK (f i)) :=
  jointScalarSupport_equiv (TensorHilbertFixedAux.factorFixedEquiv τ S e K)
    _ _ (fun i x => cornerAction_factor τ S μ K hK hσ e (f i) x)

/-- Actual admissibility of a genuine smooth model supplies finite support
on the full invariant-subspace fixed vectors. -/
theorem finite_cornerScalarSupport [Finite ι] {σ : Representation ℂ G A}
    (hσ : IsAdmissible σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) :
    (cornerScalarSupport τ S μ K hK f).Finite := by
  rw [cornerScalarSupport_eq_model τ S μ K hK hσ.1 e f]
  let : FiniteDimensional ℂ (fixedVectors σ K.toSubgroup) := hσ.2 K
  exact finite_jointScalarSupport _

end Corner

section ProjectionSupport

variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (K : Submodule ℂ H) [CompleteSpace K]
variable (T : ι → K →L[ℂ] K) (c : ι → ℂ)

/-- The entire-domain projection vanishes exactly when its actual original
joint eigenspace is zero. -/
theorem ambientJointProjection_eq_zero_iff :
    ambientJointProjection K T c = 0 ↔
      jointEigenspace (fun i => (T i).toLinearMap) c = ⊥ := by
  constructor
  · intro hp
    apply bot_unique
    intro x hx
    change x = 0
    have hfix := (ambientJointProjection_eq_self_iff K T c (x : H)).mpr
      ⟨x, (mem_jointEigenspace_iff _ c x).mp hx, rfl⟩
    rw [hp, zero_apply] at hfix
    exact Subtype.ext hfix.symm
  · intro he
    have hr : (ambientJointProjection K T c).range = ⊥ := by
      rw [ambientJointProjection_range, ambientJointEigenspace, he, Submodule.map_bot]
    have hz := LinearMap.range_eq_bot.mp hr
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hz x

theorem mem_jointScalarSupport_iff_ambientJointProjection :
    c ∈ jointScalarSupport (fun i => (T i).toLinearMap) ↔
      ambientJointProjection K T c ≠ 0 :=
  not_congr (ambientJointProjection_eq_zero_iff K T c).symm

end ProjectionSupport

section FullCornerSupport

open MeasureTheory

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable (τ : Representation ℂ G H) (S : Subrepresentation τ)
variable (hS : IsClosed (S : Set H))
variable (hτ : ∀ (g : G) (x : H), ‖τ g x‖ = ‖x‖)

/-- Point support detects nonvanishing of the unchanged entire-domain corner
projection, without any assertion that the support is nonempty. -/
theorem mem_cornerScalarSupport_iff_fullJointProjection
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) (c : ι → ℂ) :
    c ∈ cornerScalarSupport τ S μ K hK f ↔
      cornerFullJointProjection μ K hK τ S hS hτ f c ≠ 0 := by
  let : CompleteSpace S.toSubmodule := hS.completeSpace_coe
  let : CompleteSpace (fixedVectors S.toRepresentation K.toSubgroup) :=
    fullFixed_completeSpace τ hτ S hS K.toSubgroup
  dsimp only [cornerScalarSupport, cornerFullJointProjection]
  exact mem_jointScalarSupport_iff_ambientJointProjection
    (fixedVectors S.toRepresentation K.toSubgroup)
    (fun i => cornerContinuousAction μ K hK τ S hτ (f i)) c

end FullCornerSupport
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance spectralSupportRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSupportContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSupportSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSupportFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance spectralSupportFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance spectralSupportLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- Actual scalar systems occurring in the entire spherical fixed subspace
of the original completed tensor slice. Zero tails are allowed. -/
def hilbertSphericalScalarSupport (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) : Set (Fin (r + 2) → ℂ) :=
  TensorHilbertHeckeAux.jointScalarSupport (P.sliceHilbertStandardHeckeOperator b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
