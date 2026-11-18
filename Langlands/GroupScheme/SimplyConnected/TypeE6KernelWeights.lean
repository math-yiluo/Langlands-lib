import Langlands.GroupScheme.Reductive.TitsKernelWeightRestriction
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel
import Langlands.GroupScheme.SimplyConnected.TypeDVectorQuotient
import Langlands.LinearAlgebra.TypeANegationWeyl

/-! # The first actual E6 weight and its branch-kernel restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {d : TitsIndexData G} {a : TitsIndexData H} {ι : H ⟶ G}

/-- In a branch-marked E6 numbering, the zero vertices are precisely those
whose number differs from one. -/
theorem e6Branch_zero_iff (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (v : d.Vertex) :
    v ∈ d.zeroVertices ↔ e v ≠ (1 : Fin 6) := by
  have hm : v ∉ d.zeroVertices ↔ e v = (1 : Fin 6) := by
    simpa only [distinguishedVertices, Set.mem_compl_iff, Fin.ext_iff, Fin.val_one]
      using h.2 v
  simpa only [not_not] using not_congr hm

/-- Number the actual zero vertices by deleting vertex one, keeping the
remaining order `0,2,3,4,5`. -/
def e6BranchZeroNumbering (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) :
    d.zeroVertices ≃ Fin 5 :=
  (Equiv.subtypeEquiv e (e6Branch_zero_iff e h)).trans
    (finSuccAboveEquiv (1 : Fin 6)).symm

/-- Recover the original E6 number from the zero-diagram number. -/
theorem e6BranchZeroNumbering_ambient (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (v : d.zeroVertices) :
    e v.val = (1 : Fin 6).succAbove (e6BranchZeroNumbering e h v) :=
  (congrArg Subtype.val ((finSuccAboveEquiv (1 : Fin 6)).apply_symm_apply
    ((Equiv.subtypeEquiv e (e6Branch_zero_iff e h)) v))).symm

/-- Transport the ordered E6 branch complement to the actual kernel vertices. -/
def KernelComparison.e6BranchNumbering (c : d.KernelComparison ι a)
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) :
    a.Vertex ≃ Fin 5 :=
  c.vertexEquiv.trans (e6BranchZeroNumbering e h)

/-- The full actual-kernel numbering remembers the original ambient number. -/
theorem KernelComparison.e6BranchNumbering_ambient (c : d.KernelComparison ι a)
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (v : a.Vertex) :
    e (c.vertexEquiv v).val =
      (1 : Fin 6).succAbove (c.e6BranchNumbering e h v) :=
  e6BranchZeroNumbering_ambient e h (c.vertexEquiv v)

/-- Every ordered actual kernel Cartan entry is the corresponding A5 entry. -/
theorem KernelComparison.e6BranchNumbering_cartan (c : d.KernelComparison ι a)
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (v w : a.Vertex) :
    a.cartan v w =
      CartanMatrix.A 5 (c.e6BranchNumbering e h v) (c.e6BranchNumbering e h w) := by
  rw [← c.vertexEquiv_cartan, h.1,
    c.e6BranchNumbering_ambient e h, c.e6BranchNumbering_ambient e h]
  have hM : ∀ i j : Fin 5,
      CartanMatrix.E 6 ((1 : Fin 6).succAbove i) ((1 : Fin 6).succAbove j) =
        CartanMatrix.A 5 i j := by
    simp only [CartanMatrix.E, CartanMatrix.A, Matrix.of_apply]
    decide
  exact hM _ _

/-- Restriction of the first integral E6 weight is the first integral weight
of the actual kernel, in the explicit A5 numbering. -/
theorem KernelComparison.weightRestriction_e6_firstWeight
    (c : d.KernelComparison ι a)
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hd : d.pinning.rootDatum.corootSpan ℤ = ⊤)
    (ha : a.pinning.rootDatum.corootSpan ℤ = ⊤) :
    c.weightRestriction
        (Langlands.TypeANegationWeyl.firstWeight
          d.pinning.rootDatum d.pinning.base e hd (by decide)) =
      Langlands.TypeANegationWeyl.firstWeight
        a.pinning.rootDatum a.pinning.base (c.e6BranchNumbering e h) ha (by decide) := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq a.pinning.rootDatum a.pinning.base ha
  intro v
  rw [c.pairing_weightRestriction_simple,
    Langlands.TypeANegationWeyl.pairing_firstWeight,
    Langlands.TypeANegationWeyl.pairing_firstWeight,
    c.e6BranchNumbering_ambient e h]
  have hzero : ∀ i : Fin 5, ((1 : Fin 6).succAbove i).val = 0 ↔ i.val = 0 := by decide
  simp only [Fin.ext_iff, hzero]

/-- The restriction formula applies to the particular actual anisotropic
kernel chosen by the supplied index, with no coroot-span premise. -/
theorem anisotropicKernel_weightRestriction_e6_firstWeight
    (e : d.Vertex ≃ Fin 6)
    (h : d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e)
    (hsc : IsSimplyConnected G) :
    d.anisotropicKernelIndex.comparison.weightRestriction
        (Langlands.TypeANegationWeyl.firstWeight
          d.pinning.rootDatum d.pinning.base e (d.pinning_corootSpan_eq_top hsc)
          (by decide)) =
      Langlands.TypeANegationWeyl.firstWeight
        d.anisotropicKernelIndex.index.pinning.rootDatum
        d.anisotropicKernelIndex.index.pinning.base
        (d.anisotropicKernelIndex.comparison.e6BranchNumbering e h)
        (d.anisotropicKernelIndex.index.pinning_corootSpan_eq_top
          (d.anisotropicKernelIndex.isSimplyConnected hsc)) (by decide) :=
  d.anisotropicKernelIndex.comparison.weightRestriction_e6_firstWeight e h _ _

end Langlands.GroupScheme.TitsIndexData
