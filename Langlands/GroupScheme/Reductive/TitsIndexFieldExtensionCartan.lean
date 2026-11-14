import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Reductive.RootDatumFieldComparison
import Langlands.GroupScheme.GaloisPointTowerBaseChange
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix

/-! # Comparing an actual Tits-index Cartan matrix after splitting -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private instance titsIndexCartanBaseChangeAffine
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

namespace TitsIndexData

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Algebra L (SeparableClosure k)] [IsScalarTower k L (SeparableClosure k)]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  (hS : IsSplitTorus S.toGrp)
  {i : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}
  (hi : IsMaximalTorus i)
  {J : Type u} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
  (hP : IsRootDatumOf i P)

include hS hi hP

/-- A supplied actual root datum of a split maximal torus after field
extension is equivalent to the absolute datum in the original Tits index. -/
theorem nonempty_rootDatumEquiv_of_split_maximalTorus :
    Nonempty (RootPairing.Equiv P d.pinning.rootDatum) := by
  let Gext := (GroupScheme.baseChange (algebraBaseMap k L)).obj G
  have hGL := connectedReductiveFieldExtensionStatement k L G
    d.isSemisimple.isConnectedReductive
  let := hGL.smooth
  let b := algebraBaseMap L (SeparableClosure k)
  have hGLE := connectedReductiveFieldExtensionStatement L (SeparableClosure k) Gext hGL
  have hiE := (maximalTorusBaseChange L (SeparableClosure k) Gext S i hi.1 hi.2.1).mp hi
  have hPE := hP.baseChange (K := SeparableClosure k) Gext S hS i
  obtain ⟨e⟩ := nonempty_rootDatumEquiv_of_iso hGLE d.pinning.isConnectedReductive
    (hS.baseChange b) d.pinning.isSplitTorus hiE d.pinning.isMaximalTorus
    (GaloisPointComparison.towerBaseChangeIso k L (SeparableClosure k) G)
    hPE d.pinning.isRootDatum
  exact ⟨e.comp (SplitRootDatum.baseChangeEquiv b S hS P)⟩

/-- A chosen full equivalence from the supplied split datum to the absolute
datum in the original Tits index. -/
def splitMaximalTorusRootDatumEquiv :
    RootPairing.Equiv P d.pinning.rootDatum :=
  Classical.choice (d.nonempty_rootDatumEquiv_of_split_maximalTorus hS hi hP)

/-- Transport the particular absolute base in the Tits index to the supplied
split maximal torus after field extension. -/
def splitMaximalTorusBase : P.Base :=
  d.pinning.base.map (d.splitMaximalTorusRootDatumEquiv hS hi hP).symm

/-- The actual Tits-index vertices correspond to the support of the transported
base. -/
def splitMaximalTorusBaseEquiv :
    d.Vertex ≃ (d.splitMaximalTorusBase hS hi hP).support := by
  classical
  exact d.pinning.base.supportMapEquiv (d.splitMaximalTorusRootDatumEquiv hS hi hP).symm

/-- The transported base preserves every integer Cartan entry of the original
absolute Tits index. -/
theorem cartanMatrix_splitMaximalTorusBaseEquiv (a c : d.Vertex) :
    (d.splitMaximalTorusBase hS hi hP).cartanMatrix
      (d.splitMaximalTorusBaseEquiv hS hi hP a)
      (d.splitMaximalTorusBaseEquiv hS hi hP c) = d.cartan a c := by
  classical
  let E := d.splitMaximalTorusRootDatumEquiv hS hi hP
  let b := d.pinning.base.map E.symm
  let e : d.Vertex ≃ b.support := d.pinning.base.supportMapEquiv E.symm
  change b.cartanMatrix (e a) (e c) = d.cartan a c
  have h := d.pinning.base.map_equiv_cartanMatrix E.symm
  have he := congrFun (congrFun h (e a)) (e c)
  change b.cartanMatrix (e a) (e c) =
    d.pinning.base.cartanMatrix (e.symm (e a)) (e.symm (e c)) at he
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at he
  calc
    b.cartanMatrix (e a) (e c) = d.pinning.base.cartanMatrix a c := he
    _ = d.cartan a c := by
      exact d.pinning.rootDatum.algebraMap_pairingIn ℤ a.val c.val

/-- A base of the supplied split datum has the exact integer Cartan matrix
of the actual absolute Tits index, up to the indicated vertex equivalence. -/
theorem exists_base_cartanEquiv_of_split_maximalTorus :
    ∃ (b : P.Base) (e : d.Vertex ≃ b.support),
      ∀ a c, b.cartanMatrix (e a) (e c) = d.cartan a c :=
  ⟨d.splitMaximalTorusBase hS hi hP, d.splitMaximalTorusBaseEquiv hS hi hP,
    d.cartanMatrix_splitMaximalTorusBaseEquiv hS hi hP⟩

end TitsIndexData

end Langlands.GroupScheme
