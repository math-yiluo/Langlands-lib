import Langlands.Automorphic.FiniteTensorHilbertSpherical
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Noetherian.Basic

/-! # Direct sums of original joint eigenspaces and their spectral span -/

noncomputable section
open scoped Classical TensorProduct DirectSum
universe uF uV uI
set_option autoImplicit false
set_option maxHeartbeats 40000

namespace Langlands.TensorHilbertHeckeAux

universe uA uB

variable {ι : Type uI}
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]

/-- Distinct scalar systems give an independent family of ordinary joint
eigenspaces. The original operators need not commute. -/
theorem jointEigenspaces_iSupIndep (T : ι → Module.End ℂ A) :
    iSupIndep (jointEigenspace T) := by
  suffices ∀ c (s : Finset (ι → ℂ)), c ∉ s →
      Disjoint (jointEigenspace T c) (s.sup (jointEigenspace T)) by
    simpa only [iSupIndep_iff_supIndep, Finset.supIndep_iff_disjoint_erase] using!
      fun (s : Finset (ι → ℂ)) (c : ι → ℂ) _ =>
        this c (s.erase c) (s.notMem_erase c)
  intro c s
  induction s using Finset.induction_on with
  | empty => simp
  | insert d s _ ih =>
    intro hc
    obtain ⟨hcd : c ≠ d, hcs : c ∉ s⟩ := by
      rwa [Finset.mem_insert, not_or] at hc
    specialize ih hcs
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hcd
    let g : Module.End ℂ A := T i - d i • LinearMap.id
    have hg (a : ι → ℂ) (x : A) (hx : x ∈ jointEigenspace T a) :
        g x ∈ jointEigenspace T a := by
      change T i x - d i • x ∈ jointEigenspace T a
      rw [(mem_jointEigenspace_iff T a x).mp hx i]
      exact (jointEigenspace T a).sub_mem
        ((jointEigenspace T a).smul_mem _ hx)
        ((jointEigenspace T a).smul_mem _ hx)
    have hgs : (s.sup (jointEigenspace T)).map g ≤ s.sup (jointEigenspace T) := by
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup]
      refine iSup₂_mono fun a _ => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hg a x hx
    rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
    have hgy : g y = 0 := by
      change T i y - d i • y = 0
      rw [(mem_jointEigenspace_iff T d y).mp hy i, sub_self]
    have hmem : g (y + z) ∈
        jointEigenspace T c ⊓ s.sup (jointEigenspace T) := by
      refine ⟨hg c (y + z) hx, ?_⟩
      rw [map_add, hgy, zero_add]
      exact hgs (Submodule.mem_map_of_mem hz)
    have hzero : g (y + z) = 0 := by
      simpa only [ih.eq_bot, Submodule.mem_bot] using hmem
    have hscalar : g (y + z) = (c i - d i) • (y + z) := by
      change T i (y + z) - d i • (y + z) = (c i - d i) • (y + z)
      rw [(mem_jointEigenspace_iff T c (y + z)).mp hx i, sub_smul]
    exact (smul_eq_zero.mp (hscalar.symm.trans hzero)).resolve_left
      (sub_ne_zero.mpr hi)

/-- The actual algebraic span of all ordinary joint eigenspaces. It need not
equal the ambient space. -/
def jointSpectralSpan (T : ι → Module.End ℂ A) : Submodule ℂ A :=
  ⨆ c, jointEigenspace T c

/-- The canonical finite-sum inclusion of original joint eigenvectors. -/
def jointSpectralSum (T : ι → Module.End ℂ A) :
    (⨁ c : ι → ℂ, jointEigenspace T c) →ₗ[ℂ] A :=
  DirectSum.coeLinearMap (jointEigenspace T)

theorem jointSpectralSum_lof (T : ι → Module.End ℂ A)
    (c : ι → ℂ) (x : jointEigenspace T c) :
    jointSpectralSum T (DirectSum.lof ℂ (ι → ℂ) (fun a => ↥(jointEigenspace T a)) c x) = x :=
  DirectSum.coeLinearMap_lof (jointEigenspace T) c x

theorem jointSpectralSum_injective (T : ι → Module.End ℂ A) :
    Function.Injective (jointSpectralSum T) :=
  (jointEigenspaces_iSupIndep T).dfinsupp_lsum_injective

theorem jointSpectralSum_range (T : ι → Module.End ℂ A) :
    (jointSpectralSum T).range = jointSpectralSpan T :=
  DirectSum.range_coeLinearMap

/-- The direct sum is identified with precisely its actual spectral span. -/
def jointSpectralSpanEquiv (T : ι → Module.End ℂ A) :
    (⨁ c : ι → ℂ, jointEigenspace T c) ≃ₗ[ℂ] jointSpectralSpan T :=
  (LinearEquiv.ofInjective (jointSpectralSum T) (jointSpectralSum_injective T)).trans
    (LinearEquiv.ofEq _ _ (jointSpectralSum_range T))

theorem jointSpectralSpanEquiv_apply_val (T : ι → Module.End ℂ A)
    (x : ⨁ c : ι → ℂ, jointEigenspace T c) :
    (jointSpectralSpanEquiv T x).val = jointSpectralSum T x := rfl

/-- Surjectivity of the canonical sum is exactly the additional whole-space
spanning obligation. -/
theorem jointSpectralSum_surjective_iff (T : ι → Module.End ℂ A) :
    Function.Surjective (jointSpectralSum T) ↔ jointSpectralSpan T = ⊤ := by
  rw [← LinearMap.range_eq_top, jointSpectralSum_range]

/-- Every original operator preserves the actual span, even without a
commutation hypothesis on the ambient space. -/
theorem jointSpectralSpan_map_le (T : ι → Module.End ℂ A) (j : ι) :
    (jointSpectralSpan T).map (T j) ≤ jointSpectralSpan T := by
  change (⨆ c, jointEigenspace T c).map (T j) ≤ _
  rw [Submodule.map_iSup]
  refine iSup_le fun c => ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [(mem_jointEigenspace_iff T c x).mp hx j]
  exact (jointSpectralSpan T).smul_mem _ ((le_iSup (jointEigenspace T) c) hx)

/-- A genuine intertwining equivalence maps exactly the original spectral
span onto the new one. -/
theorem jointSpectralSpan_map_equiv (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    (jointSpectralSpan T).map e.toLinearMap = jointSpectralSpan U := by
  simp only [jointSpectralSpan, Submodule.map_iSup]
  apply iSup_congr
  intro c
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_jointEigenspace_equiv_iff e T U c h x).mpr hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (mem_jointEigenspace_equiv_iff e T U c h (e.symm y)).mp
      (by simpa only [e.apply_symm_apply] using hy)

/-- Restrict the same equivalence, without choosing replacement vectors. -/
def jointSpectralSpanTransport (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B)
    (h : ∀ i x, e (T i x) = U i (e x)) :
    jointSpectralSpan T ≃ₗ[ℂ] jointSpectralSpan U :=
  e.ofSubmodules _ _ (jointSpectralSpan_map_equiv e T U h)

theorem jointSpectralSpanTransport_apply_val (e : A ≃ₗ[ℂ] B)
    (T : ι → Module.End ℂ A) (U : ι → Module.End ℂ B)
    (h : ∀ i x, e (T i x) = U i (e x)) (x : jointSpectralSpan T) :
    (jointSpectralSpanTransport e T U h x).val = e x := rfl

/-- Independence gives finite point support in finite dimension even for
an infinite operator-index type. -/
theorem finite_nonzero_jointEigenspaces [FiniteDimensional ℂ A]
    (T : ι → Module.End ℂ A) :
    {c | jointEigenspace T c ≠ ⊥}.Finite :=
  Submodule.finite_ne_bot_of_iSupIndep (jointEigenspaces_iSupIndep T)

section Corner

open MeasureTheory
universe uG uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (τ : Representation ℂ G W) (S : Subrepresentation τ)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The ordinary joint-eigenvector span inside the entire fixed space. -/
def cornerSpectralSpan (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) :
    Submodule ℂ (fixedVectors S.toRepresentation K.toSubgroup) :=
  jointSpectralSpan (fun i => cornerAction τ S μ K hK (f i))

/-- A supplied genuine smooth model identifies the original corner spans. -/
def factorCornerSpectralSpanEquiv {σ : Representation ℂ G A} (hσ : IsSmooth σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) :
    jointSpectralSpan (fun i => Hecke.cornerAction μ σ hσ K hK (f i)) ≃ₗ[ℂ]
      cornerSpectralSpan τ S μ K hK f :=
  jointSpectralSpanTransport (TensorHilbertFixedAux.factorFixedEquiv τ S e K)
    _ _ (fun i x => cornerAction_factor τ S μ K hK hσ e (f i) x)

/-- Admissibility of a genuine model makes the set of nonzero ordinary joint
spaces finite, with no finiteness premise on the family of corner elements. -/
theorem finite_nonzero_cornerJointEigenspaces {σ : Representation ℂ G A}
    (hσ : IsAdmissible σ)
    (e : σ.Equiv (S ⊓ Langlands.smoothSubrepresentation τ).toRepresentation)
    (f : ι → Hecke.HeckeAlgebra.Corner μ K hK) :
    {c | cornerJointEigenspace τ S μ K hK f c ≠ ⊥}.Finite := by
  let : FiniteDimensional ℂ (fixedVectors S.toRepresentation K.toSubgroup) :=
    TensorHilbertFixedAux.factorFixed_finite τ S e K (hσ.2 K)
  exact finite_nonzero_jointEigenspaces _

end Corner
end Langlands.TensorHilbertHeckeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {r : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance spectralSpanRationalGroup :
    AddCommGroup (RationalInvariantFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSpanContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSpanSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F (r + 1)) := Submodule.addCommGroup _
local instance spectralSpanFormsGroup :
    AddCommGroup (AutomorphicForms F (r + 1)) := Submodule.addCommGroup _
local instance spectralSpanFiniteSpaceGroup (S : FiniteRealization F (r + 1)) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance spectralSpanLocalSpaceGroup (v : FinitePlace F)
    (L : LocalRealization F (r + 1) v) : AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v}
variable {S : FiniteRealization F (r + 1)}
variable (P : FiniteTensorPresentation F (r + 1) ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual ordinary spherical eigenvector span inside every fixed vector
of the closed completed tensor slice. Zero tails are allowed. -/
def hilbertSphericalSpectralSpan (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Submodule ℂ (P.SliceHilbertSphericalVectors b v y) :=
  TensorHilbertHeckeAux.jointSpectralSpan (P.sliceHilbertStandardHeckeOperator b v y)

/-- The actual finite-sum inclusion of the original spherical joint spaces. -/
def hilbertSphericalSpectralSum (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (⨁ c : Fin (r + 2) → ℂ,
      TensorHilbertHeckeAux.jointEigenspace
        (P.sliceHilbertStandardHeckeOperator b v y) c) →ₗ[ℂ]
      P.SliceHilbertSphericalVectors b v y :=
  TensorHilbertHeckeAux.jointSpectralSum (P.sliceHilbertStandardHeckeOperator b v y)

/-- The direct sum identifies with its actual algebraic span of the original
fixed vectors. -/
def hilbertSphericalSpectralSpanEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (⨁ c : Fin (r + 2) → ℂ,
      TensorHilbertHeckeAux.jointEigenspace
        (P.sliceHilbertStandardHeckeOperator b v y) c) ≃ₗ[ℂ]
      P.hilbertSphericalSpectralSpan b v y :=
  TensorHilbertHeckeAux.jointSpectralSpanEquiv (P.sliceHilbertStandardHeckeOperator b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
