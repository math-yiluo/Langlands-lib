import Langlands.GroupScheme.Rational.EvenChainClassGenerators
import Langlands.GroupScheme.Rational.ClassFunctionsBaseChange
import Langlands.GroupScheme.Rational.SteinbergFieldBaseChange
import Langlands.GroupScheme.Rational.EvenChainPatternProducts
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Field base change for even-path pattern products -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

section Descent

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance evenChainFieldBaseChangeIsAffineHom : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

/-- Equal images in the canonical quotient give equal values of all class functions. -/
theorem SplitPinning.classEvaluation_eq_of_rho_eq {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] {g g' : rationalPoints H}
    (h : g ≫ ClassFunctions.rho H = g' ≫ ClassFunctions.rho H) (f : ClassFunctions.algebra H) :
    SplitPinning.classEvaluation g f = SplitPinning.classEvaluation g' f := by
  have he : ∀ x : rationalPoints H,
      (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv F H.X x :
          Lie.AffinePoints H F) ≫ ClassFunctions.rho H =
        (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).hom ≫ x ≫
          ClassFunctions.rho H := by
    intro x
    change ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso F).hom ≫ x ≫ 𝟙 _) ≫
      ClassFunctions.rho H = _
    rw [Category.comp_id, Category.assoc]
  apply ClassFunctions.evaluation_eq_of_rho_eq H
  rw [he, he, h]

/-- The scalar extension of a class function, as a class function of the base change. -/
def ClassFunctions.fieldExtension (f : ClassFunctions.algebra G) : ClassFunctions.algebra GF :=
  ClassFunctions.BaseChange.invariants k F G (1 ⊗ₜ f)

theorem ClassFunctions.fieldExtension_val (f : ClassFunctions.algebra G) :
    (ClassFunctions.fieldExtension (F := F) f).val =
      ClassFunctions.BaseChange.restriction k F G f.val := by
  have h := congrArg (fun φ => φ (1 ⊗ₜ f))
    (ClassFunctions.BaseChange.invariants_inclusion k F G)
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h
  exact h.symm

omit [IsAffineHom G.X.hom] in
/-- The base-valued point of an extended rational point is the original point with
coefficients extended. -/
theorem affineBaseChangeEquiv_baseChangeBasePoint (g : rationalPoints G) :
    Lie.affineBaseChangeEquiv k F G F
        (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv F (GF).X
          (baseChangeBasePoint bc G g)) =
      Lie.affineMap G (Algebra.ofId k F)
        (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv k G.X g) := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left,
    Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv_left,
    baseChangeBasePoint_fst, Lie.affineMap_apply, Over.comp_left,
    Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv_left]
  rfl

/-- Class functions extended to the base change evaluate at extended rational points to the
images of their original values. -/
theorem classEvaluation_baseChangeBasePoint (g : rationalPoints G)
    (f : ClassFunctions.algebra G) :
    SplitPinning.classEvaluation (baseChangeBasePoint bc G g)
        (ClassFunctions.fieldExtension (F := F) f) =
      algebraMap k F (SplitPinning.classEvaluation g f) := by
  have h := congrArg (fun φ => φ f.val)
    (ClassFunctions.BaseChange.point_restriction k F G F
      (Langlands.AlgebraicGeometry.PointTopology.rationalPointEquiv F (GF).X
        (baseChangeBasePoint bc G g)))
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h
  rw [affineBaseChangeEquiv_baseChangeBasePoint, Lie.pointCoordinates_naturality] at h
  change Lie.pointCoordinates (GF) _ (ClassFunctions.fieldExtension (F := F) f).val = _
  rw [ClassFunctions.fieldExtension_val, ← h]
  rfl

/-- **Descent of quotient equalities.** Two rational points whose extensions to a field
extension have the same image in the canonical quotient of the base change have the same image
in the canonical quotient. -/
theorem rho_eq_of_baseChangeBasePoint_rho_eq {g g' : rationalPoints G}
    (h : baseChangeBasePoint bc G g ≫ ClassFunctions.rho (GF) =
      baseChangeBasePoint bc G g' ≫ ClassFunctions.rho (GF)) :
    g ≫ ClassFunctions.rho G = g' ≫ ClassFunctions.rho G := by
  apply SplitPinning.rho_eq_of_classEvaluation_eq
  intro f
  apply (algebraMap k F).injective
  rw [← classEvaluation_baseChangeBasePoint, ← classEvaluation_baseChangeBasePoint]
  exact SplitPinning.classEvaluation_eq_of_rho_eq h _

end Descent

section Points

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

/-- The extended point of a rational point is the constant family of the original point. -/
theorem baseChangePointsEquiv_baseChangeBasePoint (g : rationalPoints G) :
    baseChangePointsEquiv bc G (Over.mk (𝟙 _)) (baseChangeBasePoint bc G g) =
      G.constantPoint g ((Over.map bc).obj (Over.mk (𝟙 _))) := by
  have h := baseChangePointsEquiv_constantPoint bc G g (Over.mk (𝟙 _))
  rwa [constantPoint_self] at h

/-- Extension of rational points along the field extension, as a group homomorphism. -/
def fieldBaseChangePoint : rationalPoints G →* rationalPoints (GF) where
  toFun g := baseChangeBasePoint bc G g
  map_one' := by
    apply (baseChangePointsEquiv bc G (Over.mk (𝟙 _))).injective
    rw [baseChangePointsEquiv_baseChangeBasePoint, map_one]
    exact G.constantPoint_one _
  map_mul' g h := by
    apply (baseChangePointsEquiv bc G (Over.mk (𝟙 _))).injective
    rw [baseChangePointsEquiv_baseChangeBasePoint, map_mul,
      baseChangePointsEquiv_baseChangeBasePoint, baseChangePointsEquiv_baseChangeBasePoint]
    exact G.constantPoint_mul g h _

@[simp] theorem fieldBaseChangePoint_apply (g : rationalPoints G) :
    fieldBaseChangePoint (F := F) g = baseChangeBasePoint bc G g := rfl

/-- A rational point of the base change is the extension of `g` as soon as its projection is
the constant family of `g`. -/
theorem eq_baseChangeBasePoint_of {y : rationalPoints (GF)} {g : rationalPoints G}
    (h : baseChangePointsEquiv bc G (Over.mk (𝟙 _)) y =
      G.constantPoint g ((Over.map bc).obj (Over.mk (𝟙 _)))) :
    y = baseChangeBasePoint bc G g := by
  apply (baseChangePointsEquiv bc G (Over.mk (𝟙 _))).injective
  rw [h, baseChangePointsEquiv_baseChangeBasePoint]

/-- Extension of rational points maps a subgroup functor into its base change. -/
theorem baseChangeBasePoint_mem_baseChange {Φ : SubgroupFunctor G} {g : rationalPoints G}
    (hg : g ∈ Φ.carrier (Over.mk (𝟙 _))) :
    baseChangeBasePoint bc G g ∈ (Φ.baseChange bc).carrier (Over.mk (𝟙 _)) := by
  rw [SubgroupFunctor.mem_baseChange, baseChangePointsEquiv_baseChangeBasePoint]
  exact Φ.comp_mem _ hg

end Points

namespace SplitPinning

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance evenChainBaseChangeIsAffineHom' : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

local instance evenChainStandardAffine (K : Type u) [Field K] (d : ℕ) :
    IsAffineHom (VectorGroup.groupScheme (CommRingCat.of K) d).X.hom :=
  VectorGroup.isAffineHom_groupScheme (CommRingCat.of K) d

local instance evenChainStandardBaseChangeAffine (d : ℕ) :
    IsAffineHom ((GroupScheme.baseChange bc).obj
      (VectorGroup.groupScheme (CommRingCat.of k) d)).X.hom := by
  change IsAffineHom (pullback.snd _ bc)
  infer_instance

local instance evenChainStandardFiniteType (d : ℕ) :
    LocallyOfFiniteType (VectorGroup.groupScheme (CommRingCat.of k) d).X.hom := by
  have := RelativeRoot.IsVectorGroupOfDimension.smooth
    ⟨VectorGroup.coordinates (CommRingCat.of k) d, VectorGroup.isNaturalVectorCoordinates⟩
  infer_instance

namespace RootParametrization

variable {α : p.rootIndex} (x : p.RootParametrization α)

/-- Extend a root homomorphism, identifying its source with the new standard line. -/
def fieldBaseChangeHom : VectorGroup.groupScheme (CommRingCat.of F) 1 ⟶ GF :=
  (VectorGroup.fieldBaseChangeIso k F 1).inv ≫ (GroupScheme.baseChange bc).map x.hom

/-- Evaluation of the extended homomorphism projects to the original root point. -/
theorem fieldBaseChangeHom_point (T : Over (Spec (CommRingCat.of F)))
    (c : Γ(T.left, ⊤)) :
    baseChangePointsEquiv bc G T
        (VectorGroup.scalarPoint (CommRingCat.of F) T c ≫
          (x.fieldBaseChangeHom (F := F)).hom.hom) =
      x.point ((Over.map bc).obj T) c := by
  rw [fieldBaseChangeHom, Grp.comp_hom_hom, ← Category.assoc,
    baseChangePointsEquiv_comp, VectorGroup.baseChangePointsEquiv_scalarPoint_inv]
  rfl

/-- The extended root homomorphism represents the transported root subgroup. -/
theorem fieldBaseChangeHom_represents [Algebra.IsAlgebraic k F] :
    SubgroupFunctor.IsRepresentedBy
      (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
        ((p.baseChange (F := F)).rootDatum.root α))
      (x.fieldBaseChangeHom (F := F)) := by
  have h := x.represents.baseChange bc
  change SubgroupFunctor.IsRepresentedBy
    (RelativeRoot.subgroup ((GroupScheme.baseChange bc).map p.inclusion)
      (characterLattice.baseChange bc p.torus (p.rootDatum.root α))) _
  rw [RelativeRoot.subgroup_baseChange]
  refine ⟨?_, ?_⟩
  · have : Mono ((GroupScheme.baseChange bc).map x.hom).hom.hom := h.1
    change Mono ((VectorGroup.fieldBaseChangeIso k F 1).inv.hom.hom ≫
      ((GroupScheme.baseChange bc).map x.hom).hom.hom)
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp (VectorGroup.fieldBaseChangeIso k F 1).symm
      ((GroupScheme.baseChange bc).map x.hom)).trans h.2

/-- Closedness is retained by pullback and the source isomorphism. -/
theorem fieldBaseChangeHom_isClosedSubgroup :
    IsClosedSubgroup (x.fieldBaseChangeHom (F := F)) := by
  have hc := x.isClosedSubgroup.baseChange bc
  change IsClosedImmersion
    ((VectorGroup.fieldBaseChangeIso k F 1).inv.hom.hom.left ≫
      ((GroupScheme.baseChange bc).map x.hom).hom.hom.left)
  have : IsClosedImmersion ((GroupScheme.baseChange bc).map x.hom).hom.hom.left := hc
  infer_instance

/-- Torus equivariance of the root map persists on all scheme tests. -/
theorem fieldBaseChangeHom_torus_equivariant
    (T : Over (Spec (CommRingCat.of F)))
    (t : T ⟶ ((CommGroupScheme.baseChange bc).obj p.torus).X) (c : Γ(T.left, ⊤)) :
    (t ≫ ((GroupScheme.baseChange bc).map p.inclusion).hom.hom) *
        (VectorGroup.scalarPoint (CommRingCat.of F) T c ≫
          (x.fieldBaseChangeHom (F := F)).hom.hom) *
        (t ≫ ((GroupScheme.baseChange bc).map p.inclusion).hom.hom)⁻¹ =
      VectorGroup.scalarPoint (CommRingCat.of F) T
          (VectorGroup.charValue
            (characterLattice.baseChange bc p.torus (p.rootDatum.root α))
            T t * c) ≫ (x.fieldBaseChangeHom (F := F)).hom.hom := by
  apply (baseChangePointsEquiv bc G T).injective
  rw [map_mul, map_mul, map_inv, fieldBaseChangeHom_point, fieldBaseChangeHom_point]
  rw [baseChangePointsEquiv_comp]
  rw [show VectorGroup.charValue
      (characterLattice.baseChange bc p.torus (p.rootDatum.root α)) T t =
      VectorGroup.charValue (p.rootDatum.root α) ((Over.map bc).obj T)
        (baseChangePointsEquiv bc p.torus.toGrp T t) by
    exact congrArg Units.val (RelativeRoot.characterValue_baseChange bc
      (p.rootDatum.root α) T t)]
  exact x.torus_equivariant ((Over.map bc).obj T)
    (baseChangePointsEquiv bc p.torus.toGrp T t) c

/-- Scalar extension of a root parametrization. -/
def fieldBaseChange [Algebra.IsAlgebraic k F] :
    (p.baseChange (F := F)).RootParametrization α where
  hom := x.fieldBaseChangeHom (F := F)
  represents := x.fieldBaseChangeHom_represents
  isClosedSubgroup := x.fieldBaseChangeHom_isClosedSubgroup
  torus_equivariant := x.fieldBaseChangeHom_torus_equivariant

end RootParametrization

namespace ReflectionRepresentative

variable [Algebra.IsAlgebraic k F] {α : p.rootIndex} (n : p.ReflectionRepresentative α)

/-- Transport a reflection representative and its torus automorphism. -/
def fieldBaseChange : (p.baseChange (F := F)).ReflectionRepresentative α where
  point := baseChangeBasePoint bc G n.point
  torusAut := (CommGroupScheme.baseChange bc).mapIso n.torusAut
  normalizes := n.normalizes.baseChangeBasePoint bc
  characterAut_eq := by
    apply LinearEquiv.ext
    intro χF
    obtain ⟨χ, rfl⟩ := (characterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).surjective χF
    change characterAut ((CommGroupScheme.baseChange bc).mapIso n.torusAut)
      (characterLattice.baseChange bc p.torus χ) =
        (SplitRootDatum.baseChange bc p.torus p.isSplitTorus p.rootDatum).reflection α
          (characterLattice.baseChange bc p.torus χ)
    rw [characterAut_baseChange, SplitRootDatum.baseChange_reflection, n.characterAut_eq]

end ReflectionRepresentative

section Data

variable [Algebra.IsAlgebraic k F]

/-- Pairings of the transported root datum are the original pairings. -/
theorem baseChange_pairing_eq (i j : p.rootIndex) :
    (p.baseChange (F := F)).rootDatum.pairing i j = p.rootDatum.pairing i j := by
  rw [← RootPairing.root_coroot_eq_pairing, ← RootPairing.root_coroot_eq_pairing]
  exact SplitRootDatum.baseChange_pairing bc p.torus p.isSplitTorus p.rootDatum _ _

/-- A path component stays a path component of the transported base. -/
theorem isPathComponent_baseChange {L : ℕ} {β : Fin L → p.base.support}
    (hβ : Langlands.LinearAlgebra.RootDatumPathWeights.IsPathComponent β) :
    Langlands.LinearAlgebra.RootDatumPathWeights.IsPathComponent
      (P := (p.baseChange (F := F)).rootDatum) (b := (p.baseChange (F := F)).base)
      (fun i => p.baseChangeSimpleEquiv (F := F) (β i)) where
  pos := hβ.pos
  pairing_eq i j := by
    change (p.baseChange (F := F)).rootDatum.pairing (β i : p.rootIndex) (β j : p.rootIndex) = _
    rw [baseChange_pairing_eq]
    exact hβ.pairing_eq i j
  isOrthogonal z hz i := by
    obtain ⟨zv, hzv⟩ := z
    have hzv' : zv ∈ p.base.support := by
      have h : zv ∈ (p.baseChangeBase (F := F)).support := hzv
      rwa [baseChangeBase_support] at h
    have hz' : (⟨zv, hzv'⟩ : p.base.support) ∉ Set.range β := by
      rintro ⟨j, hj⟩
      apply hz ⟨j, ?_⟩
      apply Subtype.ext
      change ((β j : p.base.support) : p.rootIndex) = zv
      rw [hj]
    have h := hβ.isOrthogonal _ hz' i
    change (p.baseChange (F := F)).rootDatum.pairing zv (β i : p.rootIndex) = 0 ∧
      (p.baseChange (F := F)).rootDatum.pairing (β i : p.rootIndex) zv = 0
    rw [baseChange_pairing_eq, baseChange_pairing_eq]
    exact h

/-- Extension of rational points maps the subgroup generated by the root subgroups of `± α`
into the corresponding subgroup of the base change. -/
theorem baseChangeBasePoint_mem_rootSup {r : p.rootIndex} {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _))) :
    baseChangeBasePoint bc G g ∈
      (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
          ((p.baseChange (F := F)).rootDatum.root r)).carrier (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
          (-(p.baseChange (F := F)).rootDatum.root r)).carrier (Over.mk (𝟙 _)) := by
  have hmem : ∀ χ : characterLattice p.torus, ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion χ).carrier (Over.mk (𝟙 _)) →
        fieldBaseChangePoint (F := F) g ∈
          (RelativeRoot.subgroup ((GroupScheme.baseChange bc).map p.inclusion)
            (characterLattice.baseChange bc p.torus χ)).carrier (Over.mk (𝟙 _)) := by
    intro χ g hg
    rw [RelativeRoot.subgroup_baseChange]
    exact baseChangeBasePoint_mem_baseChange hg
  have hle : (RelativeRoot.subgroup p.inclusion (p.rootDatum.root r)).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root r)).carrier (Over.mk (𝟙 _)) ≤
      ((RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
          ((p.baseChange (F := F)).rootDatum.root r)).carrier (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
          (-(p.baseChange (F := F)).rootDatum.root r)).carrier (Over.mk (𝟙 _))).comap
        (fieldBaseChangePoint (F := F)) := by
    refine sup_le (fun g hg => Subgroup.mem_sup_left (hmem _ g hg)) (fun g hg => ?_)
    apply Subgroup.mem_sup_right
    have h := hmem _ g hg
    rwa [map_neg] at h
  exact hle hg

namespace SteinbergModifiedData

variable (D : p.SteinbergModifiedData)

/-- Transport of merged-root data along the field extension. -/
def fieldBaseChange : (p.baseChange (F := F)).SteinbergModifiedData where
  a := p.baseChangeSimpleEquiv (F := F) D.a
  b := p.baseChangeSimpleEquiv (F := F) D.b
  a_ne_b h := D.a_ne_b ((p.baseChangeSimpleEquiv (F := F)).injective h)
  alpha := D.alpha
  root_eq := by
    change characterLattice.baseChange bc p.torus (p.rootDatum.root D.alpha) =
      characterLattice.baseChange bc p.torus (p.rootDatum.root D.a) +
        characterLattice.baseChange bc p.torus (p.rootDatum.root D.b)
    rw [D.root_eq, map_add]
  xAlpha := D.xAlpha.fieldBaseChange
  nAlpha := D.nAlpha.fieldBaseChange
  ca := algebraMap k F D.ca
  cb := algebraMap k F D.cb
  ca_ne_zero := (map_ne_zero (algebraMap k F)).mpr D.ca_ne_zero
  cb_ne_zero := (map_ne_zero (algebraMap k F)).mpr D.cb_ne_zero

end SteinbergModifiedData

namespace EvenChainData

variable {J : Type u} (C : p.EvenChainData J)

/-- Transport of even-path data along the field extension. -/
def fieldBaseChange : (p.baseChange (F := F)).EvenChainData J where
  half := C.half
  path c i := p.baseChangeSimpleEquiv (F := F) (C.path c i)
  isPathComponent c := isPathComponent_baseChange (C.isPathComponent c)
  disjoint c c' i i' h := C.disjoint c c' i i' ((p.baseChangeSimpleEquiv (F := F)).injective h)
  modified c := (C.modified c).fieldBaseChange
  modified_a c := congrArg (p.baseChangeSimpleEquiv (F := F)) (C.modified_a c)
  modified_b c := congrArg (p.baseChangeSimpleEquiv (F := F)) (C.modified_b c)
  nAlpha_mem c := baseChangeBasePoint_mem_rootSup (C.nAlpha_mem c)

/-- The unmerged simple roots correspond under the field extension. -/
def restFieldBaseChange : C.Rest ≃ (C.fieldBaseChange (F := F)).Rest :=
  (p.baseChangeSimpleEquiv (F := F)).subtypeEquiv fun j => by
    change (∀ c, j ≠ (C.modified c).a ∧ j ≠ (C.modified c).b) ↔
      ∀ c, p.baseChangeSimpleEquiv (F := F) j ≠ p.baseChangeSimpleEquiv (F := F) (C.modified c).a ∧
        p.baseChangeSimpleEquiv (F := F) j ≠ p.baseChangeSimpleEquiv (F := F) (C.modified c).b
    simp only [ne_eq, (p.baseChangeSimpleEquiv (F := F)).injective.eq_iff]

@[simp] theorem restFieldBaseChange_apply_val (j : C.Rest) :
    ((C.restFieldBaseChange (F := F) j : (C.fieldBaseChange (F := F)).Rest) :
      (p.baseChange (F := F)).base.support) = p.baseChangeSimpleEquiv (F := F) j.val := rfl

/-- The transported ordering of the unmerged simple roots is again middle-out. -/
theorem isMiddleOut_fieldBaseChange {q : ℕ} {e : Fin q ≃ C.Rest} (he : C.IsMiddleOut e) :
    (C.fieldBaseChange (F := F)).IsMiddleOut (e.trans (C.restFieldBaseChange (F := F))) := by
  intro c i i' j j' hj hj' hlt
  refine he c i i' j j' ?_ ?_ hlt
  · exact (p.baseChangeSimpleEquiv (F := F)).injective hj
  · exact (p.baseChangeSimpleEquiv (F := F)).injective hj'

end EvenChainData

end Data

section PointCompatibility

omit [IsAffineHom G.X.hom] in
/-- Extension of a rational point of a map from the additive line: the coordinate is extended
along `k → F`. -/
theorem baseChangeBasePoint_scalarPoint_comp
    (y : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G) (c : k) :
    baseChangeBasePoint bc G (VectorGroup.scalarPoint (CommRingCat.of k) (Over.mk (𝟙 _))
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) ≫ y.hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of F) (Over.mk (𝟙 _))
          ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F c)) ≫
        ((VectorGroup.fieldBaseChangeIso k F 1).inv ≫
          (GroupScheme.baseChange bc).map y).hom.hom := by
  symm
  apply eq_baseChangeBasePoint_of
  rw [Grp.comp_hom_hom, ← Category.assoc, baseChangePointsEquiv_comp,
    VectorGroup.baseChangePointsEquiv_scalarPoint_inv]
  unfold GroupScheme.constantPoint
  rw [← Category.assoc, VectorGroup.scalarPoint_comp]
  congr 2
  change _ = (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k F))).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
  rw [Category.id_comp, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

variable [Algebra.IsAlgebraic k F]

theorem RootParametrization.baseChangeBasePoint_rationalPoint {α : p.rootIndex}
    (x : p.RootParametrization α) (c : k) :
    baseChangeBasePoint bc G (x.rationalPoint c) =
      (x.fieldBaseChange (F := F)).rationalPoint (algebraMap k F c) :=
  baseChangeBasePoint_scalarPoint_comp x.hom c

theorem NormalizedRootParametrization.baseChangeBasePoint_rationalPoint {a : p.base.support}
    (x : p.NormalizedRootParametrization a) (c : k) :
    baseChangeBasePoint bc G (x.toRootParametrization.rationalPoint c) =
      (x.fieldBaseChange (F := F)).toRootParametrization.rationalPoint (algebraMap k F c) :=
  baseChangeBasePoint_scalarPoint_comp x.hom c

theorem NormalizedRootParametrization.baseChangeBasePoint_unitPoint {a : p.base.support}
    (x : p.NormalizedRootParametrization a) :
    baseChangeBasePoint bc G x.unitPoint = (x.fieldBaseChange (F := F)).unitPoint := by
  change baseChangeBasePoint bc G (x.toRootParametrization.rationalPoint 1) =
    (x.fieldBaseChange (F := F)).toRootParametrization.rationalPoint 1
  rw [NormalizedRootParametrization.baseChangeBasePoint_rationalPoint, map_one]

omit [Algebra.IsAlgebraic k F] in
/-- Extension of rational points maps root subgroups into the transported root subgroups. -/
theorem baseChangeBasePoint_mem_subgroup (χ : characterLattice p.torus) {g : rationalPoints G}
    (hg : g ∈ (RelativeRoot.subgroup p.inclusion χ).carrier (Over.mk (𝟙 _))) :
    baseChangeBasePoint bc G g ∈
      (RelativeRoot.subgroup ((GroupScheme.baseChange bc).map p.inclusion)
        (characterLattice.baseChange bc p.torus χ)).carrier (Over.mk (𝟙 _)) := by
  rw [RelativeRoot.subgroup_baseChange]
  exact baseChangeBasePoint_mem_baseChange hg

/-- Canonical reflection representatives commute with the field extension. -/
theorem NormalizedRootParametrization.baseChangeBasePoint_reflectionRepresentative
    {a : p.base.support} (x : p.NormalizedRootParametrization a) :
    baseChangeBasePoint bc G x.reflectionRepresentative.point =
      (x.fieldBaseChange (F := F)).reflectionRepresentative.point := by
  have hspec := x.oppositeFactorPair_spec
  set q := x.oppositeFactorPair
  have hneg : ∀ g : rationalPoints G,
      g ∈ (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root a)).carrier (Over.mk (𝟙 _)) →
        baseChangeBasePoint bc G g ∈ (RelativeRoot.subgroup (p.baseChange (F := F)).inclusion
          (-(p.baseChange (F := F)).rootDatum.root
            (p.baseChangeSimpleEquiv (F := F) a).val)).carrier (Over.mk (𝟙 _)) := by
    intro g hg
    have h := baseChangeBasePoint_mem_subgroup (F := F) (-p.rootDatum.root a) hg
    rwa [map_neg] at h
  have hF : RelativeRoot.IsOppositeFactorPair (p.baseChange (F := F)).inclusion
      ((p.baseChange (F := F)).rootDatum.root (p.baseChangeSimpleEquiv (F := F) a).val)
      (x.fieldBaseChange (F := F)).unitPoint
      (baseChangeBasePoint bc G q.1, baseChangeBasePoint bc G q.2) := by
    refine ⟨hneg _ hspec.1, hneg _ hspec.2.1, ?_⟩
    rw [← x.baseChangeBasePoint_unitPoint]
    have hmul : baseChangeBasePoint bc G q.1 * baseChangeBasePoint bc G x.unitPoint *
        baseChangeBasePoint bc G q.2 =
          baseChangeBasePoint bc G (q.1 * x.unitPoint * q.2) := by
      simp only [← fieldBaseChangePoint_apply, map_mul]
    rw [hmul]
    obtain ⟨σ, hσ⟩ := hspec.2.2
    exact ⟨_, hσ.baseChangeBasePoint bc⟩
  have heq := (x.fieldBaseChange (F := F)).eq_oppositeFactorPair hF
  rw [NormalizedRootParametrization.reflectionRepresentative_point,
    NormalizedRootParametrization.reflectionRepresentative_point, ← heq]
  simp only [← fieldBaseChangePoint_apply, map_mul]
  rw [fieldBaseChangePoint_apply (F := F) x.unitPoint, x.baseChangeBasePoint_unitPoint]

/-- The canonical representatives of the transported root maps are the extended canonical
representatives. -/
theorem canonicalSimpleReflectionRepresentatives_fieldBaseChange
    (x : p.NormalizedSimpleRootParametrizations) (a : p.base.support) :
    (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x)
        (p.baseChangeSimpleEquiv (F := F) a)).point =
      baseChangeBasePoint bc G (canonicalSimpleReflectionRepresentatives x a).point := by
  change ((fieldBaseChangeRootMaps (F := F) x)
    (p.baseChangeSimpleEquiv (F := F) a)).reflectionRepresentative.point = _
  rw [fieldBaseChangeRootMaps_apply]
  exact ((x a).baseChangeBasePoint_reflectionRepresentative).symm

/-- The coroot points commute with the field extension. -/
theorem corootRationalPoint_fieldBaseChange (α : p.rootIndex) (t : kˣ) :
    corootRationalPoint (p.baseChange (F := F)) α (Units.map (algebraMap k F).toMonoidHom t) =
      baseChangeBasePoint bc G (corootRationalPoint p α t) := by
  apply eq_baseChangeBasePoint_of
  have hcor : ((p.baseChange (F := F)).corootHom α).hom.hom =
      (Dynamic.baseChangeCocharacter bc (CommGroupScheme.groupHom (p.rootDatum.coroot α) ≫
        p.inclusion)).hom.hom := by
    change (CommGroupScheme.groupHom (cocharacterLattice.baseChange bc p.torus
        (p.rootDatum.coroot α)) ≫ (GroupScheme.baseChange bc).map p.inclusion).hom.hom = _
    rw [cocharacterLattice.groupHom_baseChange_dynamic]
    simp only [Dynamic.baseChangeCocharacter, Functor.map_comp, Category.assoc]
  rw [corootRationalPoint, hcor, Dynamic.baseChangePointsEquiv_baseChangeCocharacter]
  unfold GroupScheme.constantPoint corootRationalPoint
  rw [corootHom_hom_hom, ← Category.assoc]
  congr 1
  apply (Gm.pointsEquiv _ _).injective
  rw [← Gm.baseChangeUnitsEquiv_apply, Gm.baseChangeUnitsEquiv_baseChangeIso_inv,
    Gm.pointsEquiv_naturality]
  apply Units.ext
  have hF : ((Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of F)))))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
        (Units.map (algebraMap k F).toMonoidHom t))).val =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F t) := by
    have h := Gm.affinePointsEquiv_val (𝟙 (Spec (CommRingCat.of F)))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of F)))).symm
        (Units.map (algebraMap k F).toMonoidHom t))
    rw [MulEquiv.apply_symm_apply] at h
    rw [show (algebraMap k F t : F) = ((Units.map (algebraMap k F).toMonoidHom t : Fˣ) : F)
      from rfl, h]
    exact ((Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _).symm
  have hk : ((Gm.pointsEquiv _ (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t)).val =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv t := by
    have h := Gm.affinePointsEquiv_val (𝟙 (Spec (CommRingCat.of k)))
      ((Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))).symm t)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    exact ((Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id_apply _).symm
  rw [hF, Units.coe_map, hk]
  change _ = (𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k F))).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv t)
  rw [Category.id_comp, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end PointCompatibility

section ProductCompatibility

variable [Algebra.IsAlgebraic k F] (x : p.NormalizedSimpleRootParametrizations)

theorem SteinbergModifiedData.baseChangeBasePoint_ua (D : p.SteinbergModifiedData) :
    baseChangeBasePoint bc G (D.ua x) =
      (D.fieldBaseChange (F := F)).ua (fieldBaseChangeRootMaps (F := F) x) := by
  change _ = ((fieldBaseChangeRootMaps (F := F) x)
    (p.baseChangeSimpleEquiv (F := F) D.a)).toRootParametrization.rationalPoint
      (algebraMap k F D.ca)
  rw [fieldBaseChangeRootMaps_apply]
  exact NormalizedRootParametrization.baseChangeBasePoint_rationalPoint _ _

theorem SteinbergModifiedData.baseChangeBasePoint_ub (D : p.SteinbergModifiedData) :
    baseChangeBasePoint bc G (D.ub x) =
      (D.fieldBaseChange (F := F)).ub (fieldBaseChangeRootMaps (F := F) x) := by
  change _ = ((fieldBaseChangeRootMaps (F := F) x)
    (p.baseChangeSimpleEquiv (F := F) D.b)).toRootParametrization.rationalPoint
      (algebraMap k F D.cb)
  rw [fieldBaseChangeRootMaps_apply]
  exact NormalizedRootParametrization.baseChangeBasePoint_rationalPoint _ _

variable {J : Type u} (C : p.EvenChainData J)

/-- The blocks of the transported data are the extended blocks. -/
theorem EvenChainData.baseChangeBasePoint_block (c : J) (b : Bool) (s : k) (t : kˣ) :
    baseChangeBasePoint bc G (C.block x c b s t) =
      (C.fieldBaseChange (F := F)).block (fieldBaseChangeRootMaps (F := F) x) c b
        (algebraMap k F s) (Units.map (algebraMap k F).toMonoidHom t) := by
  have hx : baseChangeBasePoint bc G ((C.modified c).xAlpha.rationalPoint s) =
      ((C.fieldBaseChange (F := F)).modified c).xAlpha.rationalPoint (algebraMap k F s) :=
    RootParametrization.baseChangeBasePoint_rationalPoint _ _
  have hn : baseChangeBasePoint bc G (C.modified c).nAlpha.point =
      ((C.fieldBaseChange (F := F)).modified c).nAlpha.point := rfl
  have hco : baseChangeBasePoint bc G (corootRationalPoint p (C.modified c).alpha t) =
      corootRationalPoint (p.baseChange (F := F)) ((C.fieldBaseChange (F := F)).modified c).alpha
        (Units.map (algebraMap k F).toMonoidHom t) :=
    (corootRationalPoint_fieldBaseChange _ _).symm
  have hua := (C.modified c).baseChangeBasePoint_ua (F := F) x
  have hub := (C.modified c).baseChangeBasePoint_ub (F := F) x
  rw [← fieldBaseChangePoint_apply]
  unfold EvenChainData.block
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, map_mul, fieldBaseChangePoint_apply]
    rw [hx, hn]
  · simp only [↓reduceIte, map_mul, fieldBaseChangePoint_apply]
    rw [hub, hua, hx, hn, hco]
    rfl

/-- The pattern products of the transported data are the extended pattern products. -/
theorem EvenChainData.baseChangeBasePoint_patternProduct {r q : ℕ} (o : Fin r ≃ J)
    (e : Fin q ≃ C.Rest) (ε : J → Bool) (s : J → k) (t : J → kˣ) (d : Fin q → k) :
    baseChangeBasePoint bc G
        (C.patternProduct x (canonicalSimpleReflectionRepresentatives x) o e ε s t d) =
      (C.fieldBaseChange (F := F)).patternProduct (fieldBaseChangeRootMaps (F := F) x)
        (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x)) o
        (e.trans (C.restFieldBaseChange (F := F))) ε (fun c => algebraMap k F (s c))
        (fun c => Units.map (algebraMap k F).toMonoidHom (t c))
        (fun j => algebraMap k F (d j)) := by
  rw [← fieldBaseChangePoint_apply]
  unfold EvenChainData.patternProduct
  rw [map_mul, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
  congr 2
  · apply congrArg List.ofFn
    funext j
    exact C.baseChangeBasePoint_block x _ _ _ _
  · apply congrArg List.ofFn
    funext j
    simp only [Function.comp_apply, map_mul, fieldBaseChangePoint_apply]
    change _ = ((fieldBaseChangeRootMaps (F := F) x)
        (p.baseChangeSimpleEquiv (F := F) (e j).1)).toRootParametrization.rationalPoint
          (algebraMap k F (d j)) *
      (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x)
        (p.baseChangeSimpleEquiv (F := F) (e j).1)).point
    rw [fieldBaseChangeRootMaps_apply, canonicalSimpleReflectionRepresentatives_fieldBaseChange,
      NormalizedRootParametrization.baseChangeBasePoint_rationalPoint]

/-- The ordinary ordered product with canonical representatives, at rational coordinates,
commutes with the field extension. -/
theorem baseChangeBasePoint_steinbergProductPoint {r : ℕ} (e : Fin r ≃ p.base.support)
    (c : Fin r → k) :
    baseChangeBasePoint bc G (steinbergProductPoint e x (canonicalSimpleReflectionRepresentatives x)
        (Over.mk (𝟙 _)) (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).inv (c j))) =
      steinbergProductPoint (fieldBaseChangeOrder (F := F) e) (fieldBaseChangeRootMaps (F := F) x)
        (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x))
        (Over.mk (𝟙 _))
        (fun j => (Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F (c j))) := by
  rw [← fieldBaseChangePoint_apply]
  unfold steinbergProductPoint
  rw [map_list_prod, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, map_mul, fieldBaseChangePoint_apply]
  have hT : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ y = y := fun y => by
    rw [show toUnit (Over.mk (𝟙 _)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp]
  have hTF : ∀ y : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (GF).X,
      toUnit (Over.mk (𝟙 (Spec (CommRingCat.of F)))) ≫ y = y := fun y => by
    rw [show toUnit (Over.mk (𝟙 _)) = 𝟙 _ from toUnit_unique _ _, Category.id_comp]
  rw [hT, hTF]
  change _ = ((fieldBaseChangeRootMaps (F := F) x)
      (p.baseChangeSimpleEquiv (F := F) (e j))).point (Over.mk (𝟙 _))
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv (algebraMap k F (c j))) *
    (canonicalSimpleReflectionRepresentatives (fieldBaseChangeRootMaps (F := F) x)
      (p.baseChangeSimpleEquiv (F := F) (e j))).point
  rw [fieldBaseChangeRootMaps_apply, canonicalSimpleReflectionRepresentatives_fieldBaseChange]
  congr 1
  exact NormalizedRootParametrization.baseChangeBasePoint_rationalPoint (x (e j)) (c j)

end ProductCompatibility

end SplitPinning

end Langlands.GroupScheme
