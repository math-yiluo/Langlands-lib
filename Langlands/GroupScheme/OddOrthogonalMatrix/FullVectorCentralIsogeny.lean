import Langlands.GroupScheme.OddOrthogonalMatrix.VectorCentralIsogeny
import Langlands.GroupScheme.OddOrthogonalMatrix.Connected
import Langlands.GroupScheme.CentralIsogeny.Transport

/-! # The split vector central isogeny to the full odd norm-one group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering

variable {K : Type u} [Field K] {n : ℕ}
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    {I : Type u}
    (P : RootDatum I (characterLattice T) (cocharacterLattice T)) (i : T.toGrp ⟶ G)

/-- The actual split vector map with the full odd norm-one group as target. -/
def VectorCentralIsogeny.fullMap (s : VectorCentralIsogeny (n := n) P i) (hn : 2 ≤ n) :
    G ⟶ groupScheme (Fin n) K := s.map ≫ (identityComponentIso hn).hom

/-- The full target map retains the actual finite flat surjective central isogeny property. -/
theorem VectorCentralIsogeny.central_fullMap (s : VectorCentralIsogeny (n := n) P i)
    (hn : 2 ≤ n) : IsCentralIsogeny (s.fullMap P i hn) :=
  s.central.comp_iso (identityComponentIso hn)

/-- Its compatible torus map lands in the original actual diagonal torus. -/
theorem VectorCentralIsogeny.commutes_fullMap (s : VectorCentralIsogeny (n := n) P i)
    (hn : 2 ≤ n) :
    i ≫ s.fullMap P i hn = CommGroupScheme.groupHom s.torusMap ≫ diagonalTorus (Fin n) K := by
  rw [VectorCentralIsogeny.fullMap, ← Category.assoc, s.commutes, Category.assoc,
    identityComponentIso_hom, identityTorus_comp]

/-- The full target has exactly the original scheme-theoretic kernel on every test. -/
theorem VectorCentralIsogeny.comp_fullMap_eq_one_iff (s : VectorCentralIsogeny (n := n) P i)
    (hn : 2 ≤ n) (U : Over (Spec (CommRingCat.of K))) (x : U ⟶ G.X) :
    x ≫ (s.fullMap P i hn).hom.hom = 1 ↔ x ≫ s.map.hom.hom = 1 := by
  have : Mono (identityComponentIso (K := K) hn).hom.hom.hom := inferInstance
  rw [VectorCentralIsogeny.fullMap, Grp.comp_hom_hom, ← Category.assoc]
  constructor
  · intro hx
    apply (cancel_mono (identityComponentIso (K := K) hn).hom.hom.hom).mp
    simpa only [MonObj.one_comp] using hx
  · intro hx
    rw [hx, MonObj.one_comp]

end Langlands.GroupScheme.OddOrthogonalMatrix.TypeBNumbering
