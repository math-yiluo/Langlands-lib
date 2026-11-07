import Langlands.GroupScheme.Reductive.PinningScalarCoherence

/-! # Pinned scalar-tower isomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

section Constructor
variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (p : SplitPinning G) (q : SplitPinning H)

/-- Package compatible actual group and torus isomorphisms using the canonical
linear differential equation on the chosen simple-root vectors. -/
def Iso.ofLinear (torusIso : p.torus ≅ q.torus) (groupIso : G ≅ H)
    (square : p.inclusion ≫ groupIso.hom =
      CommGroupScheme.groupHom torusIso.hom ≫ q.inclusion)
    (indexEquiv : p.rootIndex ≃ q.rootIndex)
    (root_eq : ∀ a, characterLattice.congr torusIso (p.rootDatum.root a) =
      q.rootDatum.root (indexEquiv a))
    (coroot_eq : ∀ a, cocharacterLattice.congr torusIso (p.rootDatum.coroot a) =
      q.rootDatum.coroot (indexEquiv a))
    (simple_iff : ∀ a, a ∈ p.base.support ↔ indexEquiv a ∈ q.base.support)
    (rootVector_eq : ∀ a : p.base.support,
      Lie.targetMapLinear groupIso.hom (CommRingCat.of k) (p.pinning.rootVector a) =
        q.pinning.rootVector ⟨indexEquiv a, (simple_iff a).mp a.property⟩) :
    Iso p q :=
  ⟨torusIso, groupIso, square, indexEquiv, root_eq, coroot_eq, simple_iff, rootVector_eq⟩

end Constructor

section Tower
variable {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [Algebra.IsAlgebraic k K] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

attribute [local instance] towerAffine

private def towerAssemblyTorus :=
  Iso.ofLinear ((p.baseChange (F := K)).baseChange (F := L)) (p.baseChange (F := L))
    (p.baseChangeTowerTorusIso (K := K) (L := L))

private def towerAssemblyGroup :=
  p.towerAssemblyTorus (K := K) (L := L)
    (baseChangeTowerGroupIso (k := k) (K := K) (L := L) (G := G))

private def towerAssemblySquare :=
  p.towerAssemblyGroup (K := K) (L := L)
    (p.baseChangeTowerIso_square (K := K) (L := L))

private def towerAssemblyIndex :=
  p.towerAssemblySquare (K := K) (L := L)
    (p.baseChangeTowerIndexEquiv (K := K) (L := L))

private def towerAssemblyRoot :=
  p.towerAssemblyIndex (K := K) (L := L)
    (p.baseChangeTowerIso_root (K := K) (L := L))

private def towerAssemblyCoroot :=
  p.towerAssemblyRoot (K := K) (L := L)
    (p.baseChangeTowerIso_coroot (K := K) (L := L))

private def towerAssemblySimple :=
  p.towerAssemblyCoroot (K := K) (L := L)
    (p.baseChangeTowerIso_simple_iff (K := K) (L := L))

/-- The canonical comparison of iterated and direct algebraic scalar extension
preserves the complete supplied pinning. -/
def baseChangeTowerIso :
    Iso ((p.baseChange (F := K)).baseChange (F := L)) (p.baseChange (F := L)) :=
  p.towerAssemblySimple (K := K) (L := L)
    (p.baseChangeTowerIso_rootVector (K := K) (L := L))

end Tower
end Langlands.GroupScheme.SplitPinning
