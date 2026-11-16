import Langlands.GroupScheme.Reductive.TitsKernelVertexComparison
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Torus.CentralizerSmooth

/-! # Choosing the actual anisotropic kernel and its index comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- An actual centralizer, its actual derived group and the index comparison
with the ambient zero subdiagram. -/
structure AnisotropicKernelIndex where
  centralizer : GroupScheme (Spec (CommRingCat.of k))
  inclusion : centralizer ⟶ G
  represents : (torusCentralizer d.splitInclusion).IsRepresentedBy inclusion
  kernel : GroupScheme (Spec (CommRingCat.of k))
  derived : kernel ⟶ centralizer
  isDerived : IsDerivedSubgroup derived
  [affine : IsAffineHom kernel.X.hom]
  [finiteType : LocallyOfFiniteType kernel.X.hom]
  index : TitsIndexData kernel
  anisotropic : IsAnisotropic kernel
  comparison : d.KernelComparison (derived ≫ inclusion) index

attribute [instance] AnisotropicKernelIndex.affine AnisotropicKernelIndex.finiteType

/-- Published representability and anisotropic-kernel theorems provide an
actual kernel with an actual Cartan and full-star comparison. -/
theorem nonempty_anisotropicKernelIndex : Nonempty d.AnisotropicKernelIndex := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨M, j, -, -, hj⟩ := torusCentralizer_hasSmoothClosedRepresentative
    d.splitInclusion d.maximalSplit.1 d.isSemisimple.isConnectedReductive.smooth
  have hM := d.centralizer_isConnectedReductive hj
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : Smooth M.X.hom := hM.smooth
  obtain ⟨D, i, hDa, hDf, hi⟩ := derivedSubgroupRepresentability k M
  let : IsAffineHom D.X.hom := hDa
  let : LocallyOfFiniteType D.X.hom := hDf
  obtain ⟨_, _, e, he⟩ := titsAnisotropicKernelIndex k G d M j hj D i hi
  exact ⟨{
    centralizer := M
    inclusion := j
    represents := hj
    kernel := D
    derived := i
    isDerived := hi
    index := e
    anisotropic := (titsAnisotropicKernel k G d M j hj D i hi).2
    comparison := he }⟩

/-- Choose an actual anisotropic kernel and the published comparison of its
index with the ambient zero subdiagram. -/
def anisotropicKernelIndex : d.AnisotropicKernelIndex :=
  Classical.choice d.nonempty_anisotropicKernelIndex

end Langlands.GroupScheme.TitsIndexData
