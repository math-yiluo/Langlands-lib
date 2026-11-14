import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentation
import Langlands.GroupScheme.OrthogonalMatrix.Smooth
import Langlands.GroupScheme.IdentityComponent.Transport
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.GroupScheme.Reductive.AlignedPinningBaseChange
import Langlands.GroupScheme.Reductive.PinningScalarCoherence
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof

/-! # Actual split covers under direct and iterated scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

variable {K L D : Type u} [Field K] [Field L] [Algebra K L]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {m n degree : ℕ} {sigma : FirstKindInvolution K D}
  {q : sigma.QuadraticForms (Fin m)}
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {pi : G ⟶ sigma.isometryGroup q}
  (e : OrthogonalMoritaComparison sigma q L degree n)
  (hpi : sigma.IsSpinCover q pi)

local instance splitCoverOrthogonalSmooth :
    Smooth (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of L)

local instance splitCoverOrthogonalAffine :
    IsAffineHom (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of L)

/-- The supplied spin cover in the actual full orthogonal Morita coordinates. -/
def splitCover :
    (GroupScheme.baseChange (algebraBaseMap K L)).obj G ⟶
      identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)) := by
  letI := hpi.smooth
  exact (GroupScheme.baseChange (algebraBaseMap K L)).map
      (Classical.choose hpi.exists_centralIsogeny) ≫
    (IdentityComponent.baseChangeIso (sigma.isometryGroup q) (algebraMap K L) ≪≫
      IdentityComponent.mapIso e.groupIso).hom

theorem isCentralIsogeny_splitCover : IsCentralIsogeny (splitCover e hpi) := by
  letI := hpi.smooth
  exact ((Classical.choose_spec hpi.exists_centralIsogeny).1.baseChange
    (algebraBaseMap K L)).comp_iso
      (IdentityComponent.baseChangeIso (sigma.isometryGroup q) (algebraMap K L) ≪≫
        IdentityComponent.mapIso e.groupIso)

include hpi in
theorem isSimplyConnected_splitCover :
    IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap K L)).obj G) :=
  isSimplyConnectedFieldExtension K L G hpi.isSimplyConnected

@[reassoc]
theorem splitCover_factor :
    splitCover e hpi ≫
        identityComponentι (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)) =
      (GroupScheme.baseChange (algebraBaseMap K L)).map pi ≫ e.groupIso.hom := by
  letI := hpi.smooth
  simp only [splitCover, Iso.trans_hom, Category.assoc,
    IdentityComponent.mapIso_hom_identityComponentι,
    IdentityComponent.baseChangeIso_hom_identityComponentι_assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    (Classical.choose_spec hpi.exists_centralIsogeny).2]

variable (F : Type u) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- The same central cover on the iterated pullback used by a scalar-extended
pinning. Its source is identified with the direct pullback by the actual
pullback-composition isomorphism. -/
def splitCoverTower :
    (GroupScheme.baseChange (algebraBaseMap F L)).obj
        ((GroupScheme.baseChange (algebraBaseMap K F)).obj G) ⟶
      identityComponent (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)) :=
  (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
    (algebraBaseMap K L) (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) G).hom ≫
      splitCover e hpi

theorem isCentralIsogeny_splitCoverTower :
    IsCentralIsogeny (splitCoverTower e hpi F) :=
  (isCentralIsogeny_splitCover e hpi).iso_comp
    (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
      (algebraBaseMap K L) (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) G)

omit [Algebra K L] [IsScalarTower K F L] in
include hpi in
theorem isSimplyConnected_splitCoverTower :
    IsSimplyConnected ((GroupScheme.baseChange (algebraBaseMap F L)).obj
      ((GroupScheme.baseChange (algebraBaseMap K F)).obj G)) :=
  isSimplyConnectedFieldExtension F L _
    (isSimplyConnectedFieldExtension K F G hpi.isSimplyConnected)

@[reassoc]
theorem splitCoverTower_factor :
    splitCoverTower e hpi F ≫
        identityComponentι (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)) =
      (GroupScheme.baseChange (algebraBaseMap F L)).map
          ((GroupScheme.baseChange (algebraBaseMap K F)).map pi) ≫
        (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
          (algebraBaseMap K L)
          (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L))
          (sigma.isometryGroup q)).hom ≫ e.groupIso.hom := by
  rw [splitCoverTower, Category.assoc, splitCover_factor, ← Category.assoc,
    ← Descent.pullbackComparison_naturality, Category.assoc]

variable [Algebra.IsAlgebraic F L]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap K F)).obj G).X.hom]

/-- Full scheme-kernel alignment survives the actual iterated/direct cover
comparison. The original vertex is retained by the pinning's simple equivalence. -/
theorem splitCoverTower_alignment
    (p : SplitPinning ((GroupScheme.baseChange (algebraBaseMap K F)).obj G))
    (v : p.base.support)
    (h : p.FundamentalWeightTrivialOnKernel v
      ((GroupScheme.baseChange (algebraBaseMap K F)).map pi)) :
    (p.baseChange (F := L)).FundamentalWeightTrivialOnKernel
      (p.baseChangeSimpleEquiv (F := L) v) (splitCoverTower e hpi F) := by
  intro chi hv hw
  have hbc := SplitPinning.FundamentalWeightTrivialOnKernel.baseChange
    (F := L) p v _ h chi hv hw
  let j :=
    (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
      (algebraBaseMap K L)
      (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L))
      (sigma.isometryGroup q)).hom ≫ e.groupIso.hom
  haveI : IsIso j := inferInstance
  haveI : IsIso j.hom.hom := (Grp.forget (Over _)).map_isIso j
  apply characterLattice.TrivialOnKernel.of_postcomp chi
    ((p.baseChange (F := L)).inclusion ≫ splitCoverTower e hpi F)
    (identityComponentι (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)))
  have hc := characterLattice.TrivialOnKernel.comp_mono chi
    ((p.baseChange (F := L)).inclusion ≫
      (GroupScheme.baseChange (algebraBaseMap F L)).map
        ((GroupScheme.baseChange (algebraBaseMap K F)).map pi)) j hbc
  simpa only [Category.assoc, splitCoverTower_factor, j] using hc

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita
