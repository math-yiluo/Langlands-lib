import Langlands.GroupScheme.OrthogonalMatrix.CoverTorusTransport
import Langlands.GroupScheme.OrthogonalMatrix.TypeD
import Langlands.GroupScheme.CentralIsogeny.RootDatumHomConstruction
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Reductive.Pinning
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! # Root and coroot coordinates for a supplied orthogonal-cover torus -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Langlands.GroupScheme.OrthogonalMatrix

variable {k : Type u} [Field k] {n : ℕ}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G)
  {pi : G ⟶ identityComponent (groupScheme (Fin n) (CommRingCat.of k))}

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- Standard coordinates of every actual source root, with the actual
coroot-pairing and root-pullback compatibilities. -/
structure CoverRootCoordinates (q : p.torus ⟶ 𝔻) where
  root : p.rootIndex → Fin n → ℤ
  pullback_root : ∀ a, q ≫ (GeneralLinear.characterCoordEquiv (Fin n) k).symm (root a) =
    p.rootDatum.root a
  pairing : ∀ (chi : characterLattice 𝔻) (a : p.rootIndex),
    latticePairing p.torus (q ≫ chi) (p.rootDatum.coroot a) =
      dotProduct (GeneralLinear.characterCoordEquiv (Fin n) k chi) (root a)
  roots_pullback : ∀ chi ∈ roots (identityTorus (Fin n) k),
    ∃ a : p.rootIndex, q ≫ chi = p.rootDatum.root a

/-- Central-isogeny root transport and the standard type-D coroot computation
supply the integral coordinate comparison. -/
theorem nonempty_coverRootCoordinates (hn : 4 ≤ n) (hpi : IsCentralIsogeny pi)
    (tr : StandardTorusTransport p.inclusion pi) :
    Nonempty (CoverRootCoordinates p tr.torusMap) := by
  let : Nontrivial (Fin n) := Fintype.one_lt_card_iff_nontrivial.mp (by simp; omega)
  let H := identityComponent (groupScheme (Fin n) (CommRingCat.of k))
  have hH := isConnectedReductive_identityComponent (Fin n) k
  have := hH.isAffineHom
  have := hH.smooth
  have := p.isConnectedReductive.smooth
  have hphi := hpi.comp_iso (H.innerIso tr.point)
  have htiso := hphi.isIsogeny_torusRestriction p.isConnectedReductive hH
    p.isSplitTorus (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k)
    p.isMaximalTorus (isMaximalTorus_identityTorus (Fin n) k) tr.torusMap tr.square
  obtain ⟨J, _, Q, hQ, -⟩ := rootDatumExistence k H hH 𝔻
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k)
    (identityTorus (Fin n) k) (isMaximalTorus_identityTorus (Fin n) k)
  let f := hphi.rootDatumHomOfCentralIsogeny p.rootDatum Q p.isSplitTorus
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k)
    (isMaximalTorus_identityTorus (Fin n) k).2.1 tr.torusMap tr.square htiso
    p.isRootDatum hQ
  let r : p.rootIndex → characterLattice 𝔻 := fun a => Q.root (f.indexEquiv.symm a)
  have hf := hphi.rootDatumHomOfCentralIsogeny_spec p.rootDatum Q p.isSplitTorus
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k)
    (isMaximalTorus_identityTorus (Fin n) k).2.1 tr.torusMap tr.square htiso
    p.isRootDatum hQ
  have hr (a : p.rootIndex) : tr.torusMap ≫ r a = p.rootDatum.root a := by
    rw [← hf.1 (r a)]
    simpa only [r, Equiv.apply_symm_apply] using
      f.root_weightMap_apply Q p.rootDatum (f.indexEquiv.symm a)
  have hc (a : p.rootIndex) : p.rootDatum.coroot a ≫ tr.torusMap =
      Q.coroot (f.indexEquiv.symm a) :=
    f.coroot_coweightMap_apply Q p.rootDatum a
  have hcoord (a : p.rootIndex) :
      GeneralLinear.cocharacterCoordEquiv (Fin n) k (Q.coroot (f.indexEquiv.symm a)) =
        GeneralLinear.characterCoordEquiv (Fin n) k (r a) := by
    have hmem : r a ∈ roots (diagonalTorus (Fin n) (CommRingCat.of k)) := by
      rw [← roots_identityTorus (Fin n) k, ← hQ.2.1]
      exact Set.mem_range_self _
    obtain ⟨x, y, hxy, hxy', hroot⟩ := exists_eq_weightChar_add_of_mem_roots hmem
    have hcoroot := coroot_eq_weightCochar_add hQ (by simp; omega) hxy hxy' hroot
    rw [hcoroot, hroot, map_add, map_add, cocharacterCoordEquiv_weightCochar,
      cocharacterCoordEquiv_weightCochar, characterCoordEquiv_weightChar,
      characterCoordEquiv_weightChar]
  refine ⟨⟨fun a => GeneralLinear.characterCoordEquiv (Fin n) k (r a), ?_, ?_, ?_⟩⟩
  · intro a
    simpa only [LinearEquiv.symm_apply_apply] using hr a
  · intro chi a
    calc
      latticePairing p.torus (tr.torusMap ≫ chi) (p.rootDatum.coroot a) =
          latticePairing 𝔻 chi (p.rootDatum.coroot a ≫ tr.torusMap) := by
        simp only [latticePairing_apply, Category.assoc]
      _ = _ := by rw [hc, GeneralLinear.latticePairing_coord, hcoord]; rfl
  · intro chi hchi
    obtain ⟨a, rfl⟩ : chi ∈ Set.range Q.root := by rwa [hQ.2.1]
    exact ⟨f.indexEquiv a, f.root_weightMap_apply Q p.rootDatum a⟩

/-- Choose the actual integral root-coordinate comparison. -/
def coverRootCoordinates (hn : 4 ≤ n) (hpi : IsCentralIsogeny pi)
    (tr : StandardTorusTransport p.inclusion pi) :
    CoverRootCoordinates p tr.torusMap :=
  Classical.choice (nonempty_coverRootCoordinates p hn hpi tr)

end Langlands.GroupScheme.OrthogonalMatrix
