import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerRootModel
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Torus.WeylImageFinite
import Langlands.LinearAlgebra.LeviCorootSpan

/-! # A simple-coroot face for an actual split-torus centralizer -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A base and a subset of its simple indices spanning a supplied smaller
coroot lattice on the same ambient lattice. -/
structure SplitTorusCentralizerCorootFace
    {J K X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (R : RootDatum K X Y) where
  base : P.Base
  support : Set J
  support_subset : support ⊆ (base.support : Set J)
  span_eq : R.corootSpan ℤ = Submodule.span ℤ (P.coroot '' support)

namespace SplitTorusCentralizerRootModel

variable {k : Type u} [Field k]
  {G M : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  [IsAffineHom M.X.hom] [LocallyOfFiniteType M.X.hom]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {a : A.toGrp ⟶ G} {j : M ⟶ G}
  (C : SplitTorusCentralizerRootModel a j)
  {J : Type v} {K : Type w}
  {P : RootDatum J (characterLattice C.torus) (cocharacterLattice C.torus)}
  {R : RootDatum K (characterLattice C.torus) (cocharacterLattice C.torus)}

/-- For supplied actual root data, the centralizer root range consists of the
ambient roots pairing to zero with the model's generic cocharacter. -/
theorem root_range_eq_zero (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hP : IsRootDatumOf C.ambient P) (hR : IsRootDatumOf C.centralizer R) :
    Set.range R.root = P.root ''
      {p | latticePairing C.torus (P.root p) (C.cocharacter hA) = 0} := by
  rw [hR.2.1]
  change relativeRoots C.centralizer = _
  rw [C.relativeRoots_eq_pairing hA hj]
  ext α
  constructor
  · rintro ⟨hα, hzero⟩
    have hmem : α ∈ Set.range P.root := by
      rw [hP.2.1]
      exact hα
    obtain ⟨p, rfl⟩ := hmem
    exact ⟨p, hzero, rfl⟩
  · rintro ⟨p, hzero, rfl⟩
    refine ⟨?_, hzero⟩
    change P.root p ∈ roots C.ambient
    rw [← hP.2.1]
    exact Set.mem_range_self p

/-- The actual ambient Weyl-image finiteness theorem supplies the root/coroot
embedding for the centralizer's supplied root datum. -/
def rootDatumEmbedding (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hP : IsRootDatumOf C.ambient P) (hR : IsRootDatumOf C.centralizer R) :
    SameTorusRootDatumEmbedding P R := by
  haveI : IsClosedImmersion C.ambient.hom.hom.left := C.ambient_maximal.2.1
  haveI : Finite (weylImage C.ambient) :=
    splitTorusWeylImageFinite k G C.torus C.isSplit C.ambient C.ambient_maximal.2.1
  apply hP.sameTorusSubgroupEmbedding C.ambient C.centralizer j
    C.centralizer_comp hR
  intro α hα
  change α ∈ relativeRoots C.centralizer at hα
  rw [C.relativeRoots_eq_pairing hA hj] at hα
  exact hα.1

/-- Construct a simple-coroot face spanning the integral coroot lattice of
the actual centralizer, from its supplied root datum and the ambient datum. -/
def corootFace [Finite J] [P.IsReduced] (hA : IsSplitTorus A.toGrp)
    (hj : (torusCentralizer a).IsRepresentedBy j)
    (hP : IsRootDatumOf C.ambient P) (hR : IsRootDatumOf C.centralizer R) :
    SplitTorusCentralizerCorootFace P R := by
  let F := Langlands.LinearAlgebra.rootZeroCorootFace P
    ((latticePairing C.torus).flip (C.cocharacter hA))
  refine
    { base := F.base
      support := F.support
      support_subset := F.support_subset
      span_eq := ?_ }
  exact ((C.rootDatumEmbedding hA hj hP hR).corootSpan_eq _
    (C.root_range_eq_zero hA hj hP hR)).trans F.span_eq

end SplitTorusCentralizerRootModel

end Langlands.GroupScheme
