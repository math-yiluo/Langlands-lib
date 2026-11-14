import Langlands.GroupScheme.Quaternionic.SpinCoverScalarComparison

/-! # Cocharacter comparison for the actual iterated split spin cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

local instance vectorReductionScalarAffine {S T : Scheme.{u}} (b : T ⟶ S)
    (G : GroupScheme S) [IsAffineHom G.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  exact MorphismProperty.pullback_snd _ _ inferInstance

namespace Quaternionic.OrthogonalMorita

variable {K F L D : Type u} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
  [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {m n degree : ℕ} {sigma : FirstKindInvolution K D}
  {q : sigma.QuadraticForms (Fin m)}
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {pi : G ⟶ sigma.isometryGroup q}
  (e : OrthogonalMoritaComparison sigma q L degree n)
  (hpi : sigma.IsSpinCover q pi)

local instance vectorReductionOrthogonalSmooth :
    Smooth (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.smooth_groupScheme (Fin n) (CommRingCat.of L)

local instance vectorReductionOrthogonalAffine :
    IsAffineHom (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L)).X.hom :=
  OrthogonalMatrix.isAffineHom_groupScheme (Fin n) (CommRingCat.of L)

/-- The action of the actual iterated torus pullback in the split orthogonal
coordinates chosen by the supplied Morita comparison. -/
def splitCoverTowerTorusMap
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G) :
    ((CommGroupScheme.baseChange (algebraBaseMap F L)).obj
      ((CommGroupScheme.baseChange (algebraBaseMap K F)).obj T)).toGrp ⟶
        OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L) :=
  (GroupScheme.baseChange (algebraBaseMap F L)).map
      ((GroupScheme.baseChange (algebraBaseMap K F)).map i) ≫
    splitCoverTower e hpi F ≫
    identityComponentι (OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))

/-- The actual cocharacter square for the iterated split cover. -/
theorem splitCoverTower_cocharacter
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
    (nu : cocharacterLattice T) :
    Dynamic.baseChangeCocharacter (algebraBaseMap K L)
        (CommGroupScheme.groupHom nu ≫ i ≫ pi) ≫ e.groupIso.hom =
      CommGroupScheme.groupHom
          (cocharacterLattice.baseChange (algebraBaseMap F L)
            ((CommGroupScheme.baseChange (algebraBaseMap K F)).obj T)
            (cocharacterLattice.baseChange (algebraBaseMap K F) T nu)) ≫
        splitCoverTowerTorusMap e hpi T i := by
  unfold splitCoverTowerTorusMap
  have hnu := congrArg CommGroupScheme.groupHom
    (Descent.cocharacterBaseChange_tower (algebraBaseMap K F) (algebraBaseMap F L)
      (algebraBaseMap K L) (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) T nu)
  change CommGroupScheme.groupHom
      (cocharacterLattice.baseChange (algebraBaseMap F L)
        ((CommGroupScheme.baseChange (algebraBaseMap K F)).obj T)
        (cocharacterLattice.baseChange (algebraBaseMap K F) T nu)) ≫
      (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
        (algebraBaseMap K L)
        (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) T.toGrp).hom =
    CommGroupScheme.groupHom (cocharacterLattice.baseChange (algebraBaseMap K L) T nu)
      at hnu
  have hi := Descent.pullbackComparison_naturality (algebraBaseMap K F)
    (algebraBaseMap F L) (algebraBaseMap K L)
    (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) (i ≫ pi)
  calc
    _ = (CommGroupScheme.groupHom
          (cocharacterLattice.baseChange (algebraBaseMap F L)
            ((CommGroupScheme.baseChange (algebraBaseMap K F)).obj T)
            (cocharacterLattice.baseChange (algebraBaseMap K F) T nu)) ≫
        (Descent.pullbackComparison (algebraBaseMap K F) (algebraBaseMap F L)
          (algebraBaseMap K L)
          (Lie.algebraBaseMap_tower (k := K) (K := F) (L := L)) T.toGrp).hom) ≫
          (GroupScheme.baseChange (algebraBaseMap K L)).map (i ≫ pi) ≫
            e.groupIso.hom := by
      rw [hnu]
      simp only [cocharacterLattice.groupHom_baseChange_dynamic,
        Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
    _ = _ := by
      simpa only [splitCoverTower_factor, Functor.map_comp, Category.assoc] using
        congrArg (fun a => CommGroupScheme.groupHom
          (cocharacterLattice.baseChange (algebraBaseMap F L)
            ((CommGroupScheme.baseChange (algebraBaseMap K F)).obj T)
            (cocharacterLattice.baseChange (algebraBaseMap K F) T nu)) ≫
              a ≫ e.groupIso.hom) hi.symm

end Quaternionic.OrthogonalMorita

end Langlands.GroupScheme
