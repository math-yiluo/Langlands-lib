import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Rational.VectorFieldBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.TangentImageBaseChange

/-! # Actual field extension of supplied normalized root maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace VectorGroup

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

/-- The inverse standard comparison preserves each scalar parameter on every test. -/
theorem baseChangePointsEquiv_scalarPoint_inv
    (T : Over (Spec (CommRingCat.of F))) (c : Γ(T.left, ⊤)) :
    baseChangePointsEquiv (algebraBaseMap k F)
        (groupScheme (CommRingCat.of k) 1) T
        (scalarPoint (CommRingCat.of F) T c ≫ (fieldBaseChangeIso k F 1).inv.hom.hom) =
      scalarPoint (CommRingCat.of k) ((Over.map (algebraBaseMap k F)).obj T) c := by
  apply (coordinates (CommRingCat.of k) 1 _).injective
  have h := coordinates_fieldBaseChangeIso_hom k F 1 T
    (scalarPoint (CommRingCat.of F) T c ≫ (fieldBaseChangeIso k F 1).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  exact h.symm.trans (by
    apply Multiplicative.toAdd.injective
    funext j
    exact (coordinates_scalarPoint (CommRingCat.of F) T c j).trans
      (coordinates_scalarPoint (CommRingCat.of k) ((Over.map (algebraBaseMap k F)).obj T)
        c j).symm)

end VectorGroup

namespace SplitPinning

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

local instance standardAffine (K : Type u) [Field K] (d : ℕ) :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of K) d).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of K) d

local instance standardBaseChangeAffine (d : ℕ) :
    IsAffineHom ((GroupScheme.baseChange bc).obj
      (VectorGroup.groupScheme (CommRingCat.of k) d)).X.hom := by
  change IsAffineHom (pullback.snd _ bc)
  infer_instance

local instance standardFiniteType (d : ℕ) :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of k) d).X.hom := by
  have := RelativeRoot.IsVectorGroupOfDimension.smooth
    ⟨VectorGroup.coordinates (CommRingCat.of k) d, VectorGroup.isNaturalVectorCoordinates⟩
  infer_instance

namespace NormalizedRootParametrization

variable {a : p.base.support} (x : p.NormalizedRootParametrization a)

/-- Extend the original root homomorphism, identifying its source with the new standard line. -/
def fieldBaseChangeHom : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ GF :=
  (VectorGroup.fieldBaseChangeIso k F 1).inv ≫ (GroupScheme.baseChange bc).map x.hom

/-- Evaluation of the extended homomorphism projects to the original supplied root point. -/
theorem fieldBaseChangeHom_point (T : Over (Spec (CommRingCat.of F)))
    (c : Γ(T.left, ⊤)) :
    baseChangePointsEquiv bc G T
        (VectorGroup.scalarPoint (CommRingCat.of F) T c ≫
          (x.fieldBaseChangeHom (F := F)).hom.hom) =
      x.point ((Over.map bc).obj T) c := by
  rw [fieldBaseChangeHom, Grp.comp_hom_hom, ← Category.assoc,
    baseChangePointsEquiv_comp, VectorGroup.baseChangePointsEquiv_scalarPoint_inv]
  rfl

variable [Algebra.IsAlgebraic k F]

/-- The actual extended root homomorphism represents the entire transported intrinsic subgroup. -/
theorem fieldBaseChangeHom_represents :
    SubgroupFunctor.IsRepresentedBy
      (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
        ((p.baseChange (F := F)).rootDatum.root
          (p.baseChangeSimpleEquiv (F := F) a).val))
      (x.fieldBaseChangeHom (F := F)) := by
  have h := x.represents.baseChange bc
  change SubgroupFunctor.IsRepresentedBy
    (RelativeRoot.subgroup ((GroupScheme.baseChange bc).map p.inclusion)
      (characterLattice.baseChange bc p.torus (p.rootDatum.root a))) _
  rw [RelativeRoot.subgroup_baseChange]
  refine ⟨?_, ?_⟩
  · have : Mono ((GroupScheme.baseChange bc).map x.hom).hom.hom := h.1
    change Mono ((VectorGroup.fieldBaseChangeIso k F 1).inv.hom.hom ≫
      ((GroupScheme.baseChange bc).map x.hom).hom.hom)
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp (VectorGroup.fieldBaseChangeIso k F 1).symm
      ((GroupScheme.baseChange bc).map x.hom)).trans h.2

omit [Algebra.IsAlgebraic k F] in
/-- Closedness is retained by actual pullback and the source isomorphism. -/
theorem fieldBaseChangeHom_isClosedSubgroup :
    IsClosedSubgroup (x.fieldBaseChangeHom (F := F)) := by
  have hc := x.isClosedSubgroup.baseChange bc
  change IsClosedImmersion
    ((VectorGroup.fieldBaseChangeIso k F 1).inv.hom.hom.left ≫
      ((GroupScheme.baseChange bc).map x.hom).hom.hom.left)
  have : IsClosedImmersion ((GroupScheme.baseChange bc).map x.hom).hom.hom.left := hc
  infer_instance

omit [Algebra.IsAlgebraic k F] in
/-- Torus equivariance of the supplied root map persists on all scheme tests. -/
theorem fieldBaseChangeHom_torus_equivariant
    (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ ((CommGroupScheme.baseChange bc).obj p.torus).X) (c : Γ(T.left, ⊤)) :
    (t ≫ ((GroupScheme.baseChange bc).map p.inclusion).hom.hom) *
        (VectorGroup.scalarPoint (CommRingCat.of F) T c ≫
          (x.fieldBaseChangeHom (F := F)).hom.hom) *
        (t ≫ ((GroupScheme.baseChange bc).map p.inclusion).hom.hom)⁻¹ =
      VectorGroup.scalarPoint (CommRingCat.of F) T
          (VectorGroup.charValue
            (characterLattice.baseChange bc p.torus (p.rootDatum.root a))
            T t * c) ≫ (x.fieldBaseChangeHom (F := F)).hom.hom := by
  apply (baseChangePointsEquiv bc G T).injective
  rw [map_mul, map_mul, map_inv, fieldBaseChangeHom_point, fieldBaseChangeHom_point]
  rw [baseChangePointsEquiv_comp]
  rw [show VectorGroup.charValue
      (characterLattice.baseChange bc p.torus (p.rootDatum.root a)) T t =
      VectorGroup.charValue (p.rootDatum.root a) ((Over.map bc).obj T)
        (baseChangePointsEquiv bc p.torus.toGrp T t) by
    exact congrArg Units.val (RelativeRoot.characterValue_baseChange bc
      (p.rootDatum.root a) T t)]
  exact x.torus_equivariant ((Over.map bc).obj T)
    (baseChangePointsEquiv bc p.torus.toGrp T t) c

omit [Algebra.IsAlgebraic k F] in
/-- The differential of the actual extended root map retains the scalar-extended root vector. -/
theorem fieldBaseChangeHom_derivative :
    haveI := p.isConnectedReductive.smooth
    Lie.targetMapLinear (x.fieldBaseChangeHom (F := F)) F (VectorGroup.standardEpsilon F) =
      Lie.schemeScalarExtension (K := F) G (1 ⊗ₜ[k] p.pinning.rootVector a) := by
  have := p.isConnectedReductive.smooth
  rw [← VectorGroup.targetMapLinear_fieldBaseChangeIso_standardEpsilon k F,
    ← LinearMap.comp_apply, ← Lie.targetMapLinear_comp]
  have hcomp : (VectorGroup.fieldBaseChangeIso k F 1).hom ≫
      x.fieldBaseChangeHom (F := F) = (GroupScheme.baseChange bc).map x.hom := by
    rw [fieldBaseChangeHom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [hcomp, Lie.targetMapLinear_schemeScalarExtension_one_tmul, x.derivative]

/-- Actual scalar extension of the supplied normalized simple-root parametrization. -/
def fieldBaseChange :
    (p.baseChange (F := F)).NormalizedRootParametrization
      (p.baseChangeSimpleEquiv (F := F) a) where
  hom := x.fieldBaseChangeHom (F := F)
  represents := x.fieldBaseChangeHom_represents
  isClosedSubgroup := x.fieldBaseChangeHom_isClosedSubgroup
  torus_equivariant := x.fieldBaseChangeHom_torus_equivariant
  derivative := by
    rw [p.baseChange_rootVector]
    exact x.fieldBaseChangeHom_derivative

end NormalizedRootParametrization

end SplitPinning

end Langlands.GroupScheme
