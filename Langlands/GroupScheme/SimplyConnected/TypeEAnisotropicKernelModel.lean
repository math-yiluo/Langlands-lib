import Langlands.GroupScheme.SimplyConnected.AnisotropicInnerTypeADivisionModel
import Langlands.GroupScheme.Reductive.TitsKernelIndexChoice
import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedProof
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Actual anisotropic-kernel models for the branch-marked E6 and E7 indices

The full type-A zero diagram transports through the actual kernel comparison.
Simply connectedness then gives a central division norm-one model with exact degree.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]

/-- Positive rank, every ordered Cartan entry of the actual zero subdiagram,
and triviality of the full star action on all its vertices. -/
def HasInnerTypeAZeroDiagram (d : TitsIndexData G) (n : ℕ) : Prop :=
  0 < n ∧
    (∃ q : d.zeroVertices ≃ Fin n,
      ∀ a b, d.cartan a.val b.val = CartanMatrix.A n (q a) (q b)) ∧
    ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.zeroVertices),
      d.star σ a.val = a.val

/-- The full actual kernel comparison transports an inner type-A zero diagram
to actual inner type A of the kernel. -/
theorem KernelComparison.hasInnerTypeA_of_zeroDiagram
    {d : TitsIndexData G} {e : TitsIndexData H} {ι : H ⟶ G}
    (h : d.KernelComparison ι e) {n : ℕ} (hA : d.HasInnerTypeAZeroDiagram n) :
    e.HasInnerTypeA n := by
  obtain ⟨hn, ⟨q, hq⟩, hstar⟩ := hA
  refine ⟨hn, ⟨h.vertexEquiv.trans q, ?_⟩, h.star_trivial_iff.mpr hstar⟩
  intro a b
  exact (h.vertexEquiv_cartan a b).symm.trans (hq (h.vertexEquiv a) (h.vertexEquiv b))

/-- The chosen actual anisotropic kernel is simply connected when the
ambient group is simply connected. -/
theorem AnisotropicKernelIndex.isSimplyConnected
    {d : TitsIndexData G} (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G) :
    IsSimplyConnected p.kernel :=
  splitTorusCentralizerDerivedSimplyConnected k G hsc d.splitTorus d.splitInclusion
    d.maximalSplit.1 p.centralizer p.inclusion p.represents p.kernel p.derived p.isDerived

/-- An inner type-A zero diagram gives an actual central division norm-one
model of the anisotropic kernel, with exact reduced degree. -/
theorem anisotropicKernel_divisionModel_of_innerTypeAZeroDiagram
    (d : TitsIndexData G) {n : ℕ} (hsc : IsSimplyConnected G)
    (hA : d.HasInnerTypeAZeroDiagram n) :
    HasCentralDivisionNormOnePresentation d.anisotropicKernelIndex.kernel (n + 1) := by
  let p := d.anisotropicKernelIndex
  exact centralDivisionNormOnePresentation_of_anisotropic_innerTypeA p.index n
    (p.isSimplyConnected hsc) p.anisotropic (p.comparison.hasInnerTypeA_of_zeroDiagram hA)

/-- Deleting the unique distinguished vertex transports its complementary
Cartan matrix to a full type-A zero diagram. -/
theorem hasInnerTypeAZeroDiagram_of_single_mark
    (d : TitsIndexData G) {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (e : d.Vertex ≃ Fin (n + 1)) (p : Fin (n + 1))
    (h : d.IsNumberingOf M (fun i => i = p) e) (hstar : d.StarIsTrivial)
    (hM : ∀ i j : Fin n, M (p.succAbove i) (p.succAbove j) = CartanMatrix.A n i j) :
    d.HasInnerTypeAZeroDiagram n := by
  classical
  have hz (a : d.Vertex) : a ∈ d.zeroVertices ↔ e a ≠ p := by
    have hm : a ∉ d.zeroVertices ↔ e a = p := h.2 a
    simpa only [not_not] using not_congr hm
  let q0 : d.zeroVertices ≃ {i : Fin (n + 1) // i ≠ p} := Equiv.subtypeEquiv e hz
  let q : d.zeroVertices ≃ Fin n := q0.trans (finSuccAboveEquiv p).symm
  have hq (a : d.zeroVertices) : e a.val = p.succAbove (q a) := by
    exact (congrArg Subtype.val ((finSuccAboveEquiv p).apply_symm_apply (q0 a))).symm
  refine ⟨hn, ⟨q, ?_⟩, fun σ a => hstar σ a.val⟩
  intro a b
  rw [h.1, hq a, hq b]
  exact hM _ _

/-- With only branch vertex 1 distinguished and trivial full star, E6 has
an actual A5 zero subdiagram. -/
theorem hasInnerTypeAZeroDiagram_of_E6_branch_mark
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) : d.HasInnerTypeAZeroDiagram 5 := by
  apply hasInnerTypeAZeroDiagram_of_single_mark d (by decide) (CartanMatrix.E 6) e 1
    ?_ hstar (by
      simp only [CartanMatrix.E, CartanMatrix.A, Matrix.of_apply]
      decide)
  simpa [IsNumberingOf, Fin.ext_iff] using h

/-- With only branch vertex 1 distinguished and trivial full star, E7 has
an actual A6 zero subdiagram. -/
theorem hasInnerTypeAZeroDiagram_of_E7_branch_mark
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7)
    (h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) : d.HasInnerTypeAZeroDiagram 6 := by
  apply hasInnerTypeAZeroDiagram_of_single_mark d (by decide) (CartanMatrix.E 7) e 1
    ?_ hstar (by
      simp only [CartanMatrix.E, CartanMatrix.A, Matrix.of_apply]
      decide)
  simpa [IsNumberingOf, Fin.ext_iff] using h

/-- The actual E6 branch-marked kernel has a central division norm-one model
of reduced degree six. -/
theorem anisotropicKernel_divisionModel_of_E6_branch_mark
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6) (hsc : IsSimplyConnected G)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) :
    HasCentralDivisionNormOnePresentation d.anisotropicKernelIndex.kernel 6 :=
  d.anisotropicKernel_divisionModel_of_innerTypeAZeroDiagram hsc
    (d.hasInnerTypeAZeroDiagram_of_E6_branch_mark e h hstar)

/-- The actual E7 branch-marked kernel has a central division norm-one model
of reduced degree seven. -/
theorem anisotropicKernel_divisionModel_of_E7_branch_mark
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7) (hsc : IsSimplyConnected G)
    (h : d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)
    (hstar : d.StarIsTrivial) :
    HasCentralDivisionNormOnePresentation d.anisotropicKernelIndex.kernel 7 :=
  d.anisotropicKernel_divisionModel_of_innerTypeAZeroDiagram hsc
    (d.hasInnerTypeAZeroDiagram_of_E7_branch_mark e h hstar)

end Langlands.GroupScheme.TitsIndexData
