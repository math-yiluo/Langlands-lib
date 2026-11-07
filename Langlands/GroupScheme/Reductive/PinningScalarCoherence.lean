import Langlands.GroupScheme.Reductive.PinnedScalarTransport
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.Lie.FieldExtension

/-! # Coherence of actual scalar extensions of complete pinnings -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Descent

section Schemes

variable {S T U : Scheme.{u}} (f : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ f = r)

def pullbackTestComparison (V : Over U) :
    (Over.map r).obj V ≅ (Over.map f).obj ((Over.map q).obj V) :=
  Over.isoMk (Iso.refl _) (by simp [← h])

theorem pullbackComparison_points (G : GroupScheme S) (V : Over U)
    (x : V ⟶ ((GroupScheme.baseChange q).obj
      ((GroupScheme.baseChange f).obj G)).X) :
    baseChangePointsEquiv r G V (x ≫ (pullbackComparison f q r h G).hom.hom.hom) =
      (pullbackTestComparison f q r h V).hom ≫
        baseChangePointsEquiv f G ((Over.map q).obj V)
          (baseChangePointsEquiv q ((GroupScheme.baseChange f).obj G) V x) := by
  apply Over.OverMorphism.ext
  change (x.left ≫ (pullbackComparison f q r h G).hom.hom.hom.left) ≫
      pullback.fst G.X.hom r =
    𝟙 _ ≫ ((x.left ≫ pullback.fst ((GroupScheme.baseChange f).obj G).X.hom q) ≫
      pullback.fst G.X.hom f)
  rw [Category.id_comp, Category.assoc, pullbackComparison_hom_fst, Category.assoc]

theorem gmBaseChange_tower :
    (GroupScheme.baseChange q).map (Gm.baseChangeIso f).hom ≫
        (Gm.baseChangeIso q).hom =
      (pullbackComparison f q r h (Gm S).toGrp).hom ≫ (Gm.baseChangeIso r).hom := by
  apply hom_ext_points
  intro V x
  apply (Gm.pointsEquiv U V).injective
  change Gm.pointsEquiv U V
      ((x ≫ ((GroupScheme.baseChange q).map (Gm.baseChangeIso f).hom).hom.hom) ≫
        (Gm.baseChangeIso q).hom.hom.hom) =
    Gm.pointsEquiv U V
      ((x ≫ (pullbackComparison f q r h (Gm S).toGrp).hom.hom.hom) ≫
        (Gm.baseChangeIso r).hom.hom.hom)
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply,
    baseChangePointsEquiv_comp, Gm.pointsEquiv_baseChangeIso_hom,
    Gm.pointsEquiv_baseChangeIso_hom]
  simp only [Gm.baseChangeUnitsEquiv_apply]
  rw [pullbackComparison_points, Gm.pointsEquiv_naturality]
  change _ = Units.map (𝟙 V.left : V.left ⟶ V.left).appTop.hom.toMonoidHom _
  simp

def commPullbackComparison (C : CommGroupScheme S) :
    (CommGroupScheme.baseChange q).obj ((CommGroupScheme.baseChange f).obj C) ≅
      (CommGroupScheme.baseChange r).obj C :=
  CommGroupScheme.isoOfGroupIso (pullbackComparison f q r h C.toGrp)

theorem commPullbackComparison_naturality {C D : CommGroupScheme S} (a : C ⟶ D) :
    (CommGroupScheme.baseChange q).map ((CommGroupScheme.baseChange f).map a) ≫
        (commPullbackComparison f q r h D).hom =
      (commPullbackComparison f q r h C).hom ≫ (CommGroupScheme.baseChange r).map a :=
  congrArg Additive.ofMul (pullbackComparison_naturality f q r h
    (CommGroupScheme.groupHom a))

theorem gmCommBaseChange_tower :
    (CommGroupScheme.baseChange q).map (Gm.commBaseChangeIso f).hom ≫
        (Gm.commBaseChangeIso q).hom =
      (commPullbackComparison f q r h (Gm S)).hom ≫ (Gm.commBaseChangeIso r).hom :=
  congrArg Additive.ofMul (gmBaseChange_tower f q r h)

theorem gmCommBaseChange_tower_inv :
    (Gm.commBaseChangeIso q).inv ≫
        (CommGroupScheme.baseChange q).map (Gm.commBaseChangeIso f).inv ≫
        (commPullbackComparison f q r h (Gm S)).hom =
      (Gm.commBaseChangeIso r).inv := by
  have he :
      (CommGroupScheme.baseChange q).mapIso (Gm.commBaseChangeIso f) ≪≫
          Gm.commBaseChangeIso q =
        commPullbackComparison f q r h (Gm S) ≪≫ Gm.commBaseChangeIso r :=
    Iso.ext (gmCommBaseChange_tower f q r h)
  have hi := congrArg Iso.inv he
  change (Gm.commBaseChangeIso q).inv ≫
      (CommGroupScheme.baseChange q).map (Gm.commBaseChangeIso f).inv =
    (Gm.commBaseChangeIso r).inv ≫ (commPullbackComparison f q r h (Gm S)).inv at hi
  rw [← Category.assoc, hi, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem characterBaseChange_tower (C : CommGroupScheme S) (χ : characterLattice C) :
    characterLattice.baseChange q ((CommGroupScheme.baseChange f).obj C)
        (characterLattice.baseChange f C χ) =
      (commPullbackComparison f q r h C).hom ≫ characterLattice.baseChange r C χ := by
  change (CommGroupScheme.baseChange q).map
      ((CommGroupScheme.baseChange f).map χ ≫ (Gm.commBaseChangeIso f).hom) ≫
        (Gm.commBaseChangeIso q).hom =
    (commPullbackComparison f q r h C).hom ≫
      (CommGroupScheme.baseChange r).map χ ≫ (Gm.commBaseChangeIso r).hom
  rw [Functor.map_comp, Category.assoc]
  rw [gmCommBaseChange_tower, ← Category.assoc, commPullbackComparison_naturality,
    Category.assoc]

theorem characterBaseChange_tower_inv (C : CommGroupScheme S) (χ : characterLattice C) :
    (commPullbackComparison f q r h C).inv ≫
      characterLattice.baseChange q ((CommGroupScheme.baseChange f).obj C)
        (characterLattice.baseChange f C χ) = characterLattice.baseChange r C χ := by
  rw [characterBaseChange_tower f q r h, Iso.inv_hom_id_assoc]

theorem cocharacterBaseChange_tower (C : CommGroupScheme S) (ν : cocharacterLattice C) :
    cocharacterLattice.baseChange q ((CommGroupScheme.baseChange f).obj C)
        (cocharacterLattice.baseChange f C ν) ≫ (commPullbackComparison f q r h C).hom =
      cocharacterLattice.baseChange r C ν := by
  change ((Gm.commBaseChangeIso q).inv ≫
      (CommGroupScheme.baseChange q).map
        ((Gm.commBaseChangeIso f).inv ≫ (CommGroupScheme.baseChange f).map ν)) ≫
        (commPullbackComparison f q r h C).hom =
    (Gm.commBaseChangeIso r).inv ≫ (CommGroupScheme.baseChange r).map ν
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [commPullbackComparison_naturality]
  simpa only [Category.assoc] using congrArg
    (fun a => a ≫ (CommGroupScheme.baseChange r).map ν)
    (gmCommBaseChange_tower_inv f q r h)

end Schemes

end Descent

namespace Lie

section CoefficientNotation

variable {L : Type u} [CommRing L]
    {G H : GroupScheme (Spec (CommRingCat.of L))} (f : G ⟶ H)

set_option maxHeartbeats 100000 in
theorem targetMap_self_cat (x : lieKernel G (CommRingCat.of L)) :
    targetMap f (CommRingCat.of L) x = targetMap f L x := rfl

theorem targetMap_self_cat_eq (x : lieKernel G (CommRingCat.of L))
    (y : lieKernel H (CommRingCat.of L)) (h : targetMap f L x = y) :
    targetMap f (CommRingCat.of L) x = y := h

end CoefficientNotation

section AdditiveMaps

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

theorem targetMapLinear_ofMul (x : lieKernel G A) :
    targetMapLinear f A (Additive.ofMul x) =
      Additive.ofMul (targetMap f A x) := rfl

theorem targetMapLinear_apply (x : Additive (lieKernel G A)) :
    targetMapLinear f A x = Additive.ofMul (targetMap f A x.toMul) := rfl

theorem targetMapLinear_eq_of_toMul_eq (x : Additive (lieKernel G A))
    (y : Additive (lieKernel H A)) (h : targetMap f A x.toMul = y.toMul) :
    targetMapLinear f A x = y :=
  (targetMapLinear_apply f A x).trans (congrArg Additive.ofMul h)

end AdditiveMaps

section Rings

variable {k K : Type u} [CommRing k] [CommRing K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))

theorem kernelFieldExtension_val_fst (x : lieKernel G k) :
    (kernelFieldExtension (K := K) G x).val.left ≫
        pullback.fst G.X.hom (algebraBaseMap k K) =
      (lieKernelMap G (Algebra.ofId k K) x).val.left := by
  have h := congrArg (fun z => z.val.left)
    ((kernelBaseChangeEquiv k K G K).apply_symm_apply
      (lieKernelMap G (Algebra.ofId k K) x))
  simpa only [kernelBaseChangeEquiv_val, affineBaseChangeEquiv_left,
    kernelFieldExtension, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h

theorem kernelFieldExtension_val_fst_eq (x : lieKernel G k) :
    (kernelFieldExtension (K := K) G x).val.left ≫
        pullback.fst G.X.hom (algebraBaseMap k K) =
      Spec.map (CommRingCat.ofHom
        (GeneralLinear.DualNumber.coefficientMap (algebraMap k K))) ≫ x.val.left := by
  rw [kernelFieldExtension_val_fst, lieKernelMap_val, affineMap_apply, Over.comp_left]
  rfl

variable {L : Type u} [CommRing L] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]

theorem algebraBaseMap_tower :
    algebraBaseMap K L ≫ algebraBaseMap k K = algebraBaseMap k L := by
  unfold algebraBaseMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq k K L]

theorem dualNumberSpecMap_tower :
    Spec.map (CommRingCat.ofHom
        (GeneralLinear.DualNumber.coefficientMap (algebraMap K L))) ≫
      Spec.map (CommRingCat.ofHom
        (GeneralLinear.DualNumber.coefficientMap (algebraMap k K))) =
    Spec.map (CommRingCat.ofHom
      (GeneralLinear.DualNumber.coefficientMap (algebraMap k L))) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z <;>
    change algebraMap K L (algebraMap k K _) = algebraMap k L _
  all_goals exact congrFun (congrArg DFunLike.coe
    (IsScalarTower.algebraMap_eq k K L).symm) _

theorem kernelFieldExtension_tower_projection (x : lieKernel G k) :
    (targetMap
        (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
          (algebraBaseMap k L) (algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
        (kernelFieldExtension (K := L)
          ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
          (kernelFieldExtension (K := K) G x))).val.left ≫
        pullback.fst G.X.hom (algebraBaseMap k L) =
      (kernelFieldExtension (K := L) G x).val.left ≫
        pullback.fst G.X.hom (algebraBaseMap k L) := by
  simp only [lieKernelTarget_val, Over.comp_left, Category.assoc,
    Descent.pullbackComparison_hom_fst]
  rw [← Category.assoc, kernelFieldExtension_val_fst_eq, Category.assoc,
    kernelFieldExtension_val_fst_eq, kernelFieldExtension_val_fst_eq,
    ← Category.assoc, dualNumberSpecMap_tower]

theorem kernelFieldExtension_tower (x : lieKernel G k) :
    targetMap
        (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
          (algebraBaseMap k L) (algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
        (kernelFieldExtension (K := L)
          ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
          (kernelFieldExtension (K := K) G x)) =
      kernelFieldExtension (K := L) G x := by
  apply (kernelBaseChangeEquiv k L G L).injective
  apply Subtype.ext
  apply Over.OverMorphism.ext
  simpa only [kernelBaseChangeEquiv_val, affineBaseChangeEquiv_left] using
    kernelFieldExtension_tower_projection (K := K) G x

end Rings

section Fields

variable {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance scalarAffine {S T : Scheme.{u}} (f : T ⟶ S)
    (C : GroupScheme S) [IsAffineHom C.X.hom] :
    IsAffineHom ((GroupScheme.baseChange f).obj C).X.hom := by
  change IsAffineHom (pullback.snd C.X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

local instance scalarFiniteType {S T : Scheme.{u}} (f : T ⟶ S)
    (C : GroupScheme S) [LocallyOfFiniteType C.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange f).obj C).X.hom := by
  change LocallyOfFiniteType (pullback.snd C.X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

omit [LocallyOfFiniteType G.X.hom] in
theorem kernelFieldExtension_tower_additive (x : Additive (lieKernel G k)) :
    targetMapLinear
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
      (Additive.ofMul (kernelFieldExtension (K := L)
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        (kernelFieldExtension (K := K) G x.toMul))) =
      Additive.ofMul (kernelFieldExtension (K := L) G x.toMul) :=
  (targetMapLinear_ofMul _ L _).trans
    (congrArg Additive.ofMul (kernelFieldExtension_tower (K := K) G x.toMul))

omit [Algebra k L] [IsScalarTower k K L] in
theorem schemeScalarExtension_iterated_one_tmul (x : Additive (lieKernel G k)) :
    schemeScalarExtension (K := L) ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      (1 ⊗ₜ[K] schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x)) =
    Additive.ofMul (kernelFieldExtension (K := L)
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
      (kernelFieldExtension (K := K) G x.toMul)) := by
  exact (schemeScalarExtension_one_tmul (K := L)
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x))).trans
      (congrArg (fun z : Additive (lieKernel
          ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K) =>
        Additive.ofMul (kernelFieldExtension (K := L)
          ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) z.toMul))
        (schemeScalarExtension_one_tmul (K := K) G x))

/-- The actual pullback comparison preserves the two successive extensions of
an actual Lie vector. -/
theorem schemeScalarExtension_tower_one_tmul (x : Additive (lieKernel G k)) :
    targetMapLinear
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
      (schemeScalarExtension (K := L) ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        (1 ⊗ₜ[K] schemeScalarExtension (K := K) G (1 ⊗ₜ[k] x))) =
      schemeScalarExtension (K := L) G (1 ⊗ₜ[k] x) := by
  exact (congrArg (targetMapLinear
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L)
    (schemeScalarExtension_iterated_one_tmul (K := K) (L := L) G x)).trans
      ((kernelFieldExtension_tower_additive (K := K) G x).trans
        (schemeScalarExtension_one_tmul (K := L) G x).symm)

end Fields

end Lie

namespace SplitPinning

section KernelIso

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (p : SplitPinning G) (q : SplitPinning H)

/-- Construct a pinned isomorphism by checking the chosen vectors on their
actual multiplicative dual-number identity kernels. -/
def Iso.ofKernel (torusIso : p.torus ≅ q.torus) (groupIso : G ≅ H)
    (square : p.inclusion ≫ groupIso.hom =
      CommGroupScheme.groupHom torusIso.hom ≫ q.inclusion)
    (indexEquiv : p.rootIndex ≃ q.rootIndex)
    (root_eq : ∀ a, characterLattice.congr torusIso (p.rootDatum.root a) =
      q.rootDatum.root (indexEquiv a))
    (coroot_eq : ∀ a, cocharacterLattice.congr torusIso (p.rootDatum.coroot a) =
      q.rootDatum.coroot (indexEquiv a))
    (simple_iff : ∀ a, a ∈ p.base.support ↔ indexEquiv a ∈ q.base.support)
    (rootVector_eq : ∀ a : p.base.support,
      Lie.targetMap groupIso.hom k (p.pinning.rootVector a).toMul =
        (q.pinning.rootVector ⟨indexEquiv a, (simple_iff a).mp a.property⟩).toMul) :
    Iso p q where
  torusIso := torusIso
  groupIso := groupIso
  square := square
  indexEquiv := indexEquiv
  root_eq := root_eq
  coroot_eq := coroot_eq
  simple_iff := simple_iff
  rootVector_eq := by
    intro a
    apply Additive.toMul.injective
    exact rootVector_eq a

/-- Equality of the actual kernel points implies the required equality of
chosen root vectors under the differential. -/
theorem rootVector_map_of_kernel (f : G ⟶ H) (a : p.base.support) (b : q.base.support)
    (h : Lie.targetMap f k (p.pinning.rootVector a).toMul =
      (q.pinning.rootVector b).toMul) :
    Lie.targetMapLinear f (CommRingCat.of k) (p.pinning.rootVector a) =
      q.pinning.rootVector b := by
  apply Additive.toMul.injective
  exact h

/-- Change the ambient map and target simple index along proved equalities. -/
theorem rootVector_map_congr (f g : G ⟶ H) (a : p.base.support)
    (b c : q.base.support) (hf : f = g) (hb : b = c)
    (h : Lie.targetMapLinear f (CommRingCat.of k) (p.pinning.rootVector a) =
      q.pinning.rootVector b) :
    Lie.targetMapLinear g (CommRingCat.of k) (p.pinning.rootVector a) =
      q.pinning.rootVector c := by
  cases hf
  cases hb
  exact h

end KernelIso

section ScalarKernel

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

theorem baseChange_rootVector_kernel (a : p.base.support) :
    ((p.baseChange (F := K)).pinning.rootVector
      (p.baseChangeSimpleEquiv (F := K) a)).toMul =
      Lie.kernelFieldExtension (K := K) G (p.pinning.rootVector a).toMul := by
  have := p.isConnectedReductive.smooth
  exact congrArg Additive.toMul ((p.baseChange_rootVector (F := K) a).trans
    (Lie.schemeScalarExtension_one_tmul (K := K) G (p.pinning.rootVector a)))

end ScalarKernel

section Tower

variable {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [Algebra.IsAlgebraic k K] [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic k L]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance towerAffine {S T : Scheme.{u}} (f : T ⟶ S)
    (C : GroupScheme S) [IsAffineHom C.X.hom] :
    IsAffineHom ((GroupScheme.baseChange f).obj C).X.hom := by
  change IsAffineHom (pullback.snd C.X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

local instance towerFiniteType {S T : Scheme.{u}} (f : T ⟶ S)
    (C : GroupScheme S) [LocallyOfFiniteType C.X.hom] :
    LocallyOfFiniteType ((GroupScheme.baseChange f).obj C).X.hom := by
  change LocallyOfFiniteType (pullback.snd C.X.hom f)
  exact MorphismProperty.pullback_snd _ _ inferInstance

omit [Algebra k L] [IsScalarTower k K L] [Algebra.IsAlgebraic k L] in
theorem baseChangeTower_rootVector_kernel_extension (a : p.base.support) :
    (((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector
      ((p.baseChange (F := K)).baseChangeSimpleEquiv (F := L)
        (p.baseChangeSimpleEquiv (F := K) a))).toMul =
      Lie.kernelFieldExtension (K := L)
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)
        (Lie.kernelFieldExtension (K := K) G (p.pinning.rootVector a).toMul) :=
  ((p.baseChange (F := K)).baseChange_rootVector_kernel (K := L)
    (p.baseChangeSimpleEquiv (F := K) a)).trans
      (congrArg (Lie.kernelFieldExtension (K := L)
        ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
        (p.baseChange_rootVector_kernel (K := K) a))

set_option maxHeartbeats 100000 in
theorem baseChangeTower_rootVector_kernel (a : p.base.support) :
    Lie.targetMap
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
      ((((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector
        ((p.baseChange (F := K)).baseChangeSimpleEquiv (F := L)
          (p.baseChangeSimpleEquiv (F := K) a))).toMul) =
      ((p.baseChange (F := L)).pinning.rootVector
        (p.baseChangeSimpleEquiv (F := L) a)).toMul :=
  (congrArg (Lie.targetMap
    (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
      (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L)
    (p.baseChangeTower_rootVector_kernel_extension (K := K) (L := L) a)).trans
      ((Lie.kernelFieldExtension_tower (K := K) G (p.pinning.rootVector a).toMul).trans
        (p.baseChange_rootVector_kernel (K := L) a).symm)

omit [IsScalarTower k K L] in
theorem baseChangeTower_simple_iff (a : p.rootIndex) :
    a ∈ ((p.baseChange (F := K)).baseChange (F := L)).base.support ↔
      a ∈ (p.baseChange (F := L)).base.support := by
  change a ∈ (p.baseChange (F := K)).baseChangeBase.support ↔
    a ∈ p.baseChangeBase.support
  rw [baseChangeBase_support]
  change a ∈ p.baseChangeBase.support ↔ a ∈ p.baseChangeBase.support
  rfl

set_option maxHeartbeats 100000 in
theorem baseChangeTower_rootVector_kernel_all
    (a : ((p.baseChange (F := K)).baseChange (F := L)).base.support) :
    Lie.targetMap
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
      ((((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector a).toMul) =
      ((p.baseChange (F := L)).pinning.rootVector
        ⟨a.val, (p.baseChangeTower_simple_iff (K := K) (L := L) a.val).mp a.property⟩).toMul := by
  let aK : (p.baseChange (F := K)).base.support :=
    ((p.baseChange (F := K)).baseChangeSimpleEquiv (F := L)).symm a
  let a₀ : p.base.support := (p.baseChangeSimpleEquiv (F := K)).symm aK
  have hs : (p.baseChange (F := K)).baseChangeSimpleEquiv (F := L)
      (p.baseChangeSimpleEquiv (F := K) a₀) = a := by
    simp only [a₀, aK, Equiv.apply_symm_apply]
  have ht : p.baseChangeSimpleEquiv (F := L) a₀ =
      ⟨a.val, (p.baseChangeTower_simple_iff (K := K) (L := L) a.val).mp a.property⟩ := by
    apply Subtype.ext
    rfl
  exact (congrArg (fun b => Lie.targetMap
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom L
      ((((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector b).toMul)) hs.symm).trans
    ((p.baseChangeTower_rootVector_kernel (K := K) (L := L) a₀).trans
      (congrArg (fun b => ((p.baseChange (F := L)).pinning.rootVector b).toMul) ht))

set_option maxHeartbeats 100000 in
theorem baseChangeTower_square :
    ((p.baseChange (F := K)).baseChange (F := L)).inclusion ≫
        (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
          (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom =
      CommGroupScheme.groupHom
        (Descent.commPullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
          (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L))
            p.torus).hom ≫ (p.baseChange (F := L)).inclusion :=
  Descent.pullbackComparison_naturality _ _ _ _ p.inclusion

set_option maxHeartbeats 100000 in
theorem baseChangeTower_root (a : p.rootIndex) :
    characterLattice.congr
      (Descent.commPullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) p.torus)
      (((p.baseChange (F := K)).baseChange (F := L)).rootDatum.root a) =
        (p.baseChange (F := L)).rootDatum.root a :=
  Descent.characterBaseChange_tower_inv (algebraBaseMap k K)
    (algebraBaseMap K L) (algebraBaseMap k L)
    (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) p.torus (p.rootDatum.root a)

set_option maxHeartbeats 100000 in
theorem baseChangeTower_coroot (a : p.rootIndex) :
    cocharacterLattice.congr
      (Descent.commPullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) p.torus)
      (((p.baseChange (F := K)).baseChange (F := L)).rootDatum.coroot a) =
        (p.baseChange (F := L)).rootDatum.coroot a :=
  Descent.cocharacterBaseChange_tower (algebraBaseMap k K)
    (algebraBaseMap K L) (algebraBaseMap k L)
    (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) p.torus (p.rootDatum.coroot a)

set_option maxHeartbeats 100000 in
theorem baseChangeTower_rootVector_all
    (a : ((p.baseChange (F := K)).baseChange (F := L)).base.support) :
    Lie.targetMapLinear
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom
      (CommRingCat.of L)
      (((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector a) =
      (p.baseChange (F := L)).pinning.rootVector
        ⟨a.val, (p.baseChangeTower_simple_iff (K := K) (L := L) a.val).mp a.property⟩ :=
  rootVector_map_of_kernel ((p.baseChange (F := K)).baseChange (F := L))
    (p.baseChange (F := L)) _ _ _
    (p.baseChangeTower_rootVector_kernel_all (K := K) (L := L) a)

set_option maxHeartbeats 100000 in
/-- The canonical comparison on the actual tori of the two extended pinnings. -/
def baseChangeTowerTorusIso :
    ((p.baseChange (F := K)).baseChange (F := L)).torus ≅
      (p.baseChange (F := L)).torus :=
  Descent.commPullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
    (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) p.torus

/-- The actual ambient group comparison for a scalar tower. -/
def baseChangeTowerGroupIso :
    (GroupScheme.baseChange (algebraBaseMap K L)).obj
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) ≅
    (GroupScheme.baseChange (algebraBaseMap k L)).obj G :=
  Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
    (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G

/-- The canonical tower comparison leaves the supplied root indices unchanged. -/
def baseChangeTowerIndexEquiv :
    ((p.baseChange (F := K)).baseChange (F := L)).rootIndex ≃
      (p.baseChange (F := L)).rootIndex := Equiv.refl _

set_option maxHeartbeats 100000 in
theorem baseChangeTowerIso_square :
    ((p.baseChange (F := K)).baseChange (F := L)).inclusion ≫
        (baseChangeTowerGroupIso (k := k) (K := K) (L := L) (G := G)).hom =
      CommGroupScheme.groupHom (p.baseChangeTowerTorusIso (K := K) (L := L)).hom ≫
        (p.baseChange (F := L)).inclusion :=
  p.baseChangeTower_square (K := K) (L := L)

set_option maxHeartbeats 100000 in
theorem baseChangeTowerIso_root
    (a : ((p.baseChange (F := K)).baseChange (F := L)).rootIndex) :
    characterLattice.congr (p.baseChangeTowerTorusIso (K := K) (L := L))
        (((p.baseChange (F := K)).baseChange (F := L)).rootDatum.root a) =
      (p.baseChange (F := L)).rootDatum.root
        (p.baseChangeTowerIndexEquiv (K := K) (L := L) a) :=
  p.baseChangeTower_root (K := K) (L := L) a

set_option maxHeartbeats 100000 in
theorem baseChangeTowerIso_coroot
    (a : ((p.baseChange (F := K)).baseChange (F := L)).rootIndex) :
    cocharacterLattice.congr (p.baseChangeTowerTorusIso (K := K) (L := L))
        (((p.baseChange (F := K)).baseChange (F := L)).rootDatum.coroot a) =
      (p.baseChange (F := L)).rootDatum.coroot
        (p.baseChangeTowerIndexEquiv (K := K) (L := L) a) :=
  p.baseChangeTower_coroot (K := K) (L := L) a

omit [IsScalarTower k K L] in
set_option maxHeartbeats 100000 in
theorem baseChangeTowerIso_simple_iff
    (a : ((p.baseChange (F := K)).baseChange (F := L)).rootIndex) :
    a ∈ ((p.baseChange (F := K)).baseChange (F := L)).base.support ↔
      p.baseChangeTowerIndexEquiv (K := K) (L := L) a ∈
        (p.baseChange (F := L)).base.support :=
  p.baseChangeTower_simple_iff (K := K) (L := L) a

omit [Algebra.IsAlgebraic k K] [Algebra.IsAlgebraic K L]
    [Algebra.IsAlgebraic k L] [IsAffineHom G.X.hom] in
theorem baseChangeTowerGroupIso_hom :
    (baseChangeTowerGroupIso (k := k) (K := K) (L := L) (G := G)).hom =
      (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
        (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom :=
  rfl

set_option maxHeartbeats 100000 in
theorem baseChangeTowerIso_rootVector
    (a : ((p.baseChange (F := K)).baseChange (F := L)).base.support) :
    Lie.targetMapLinear
      (baseChangeTowerGroupIso (k := k) (K := K) (L := L) (G := G)).hom
      (CommRingCat.of L)
      (((p.baseChange (F := K)).baseChange (F := L)).pinning.rootVector a) =
      (p.baseChange (F := L)).pinning.rootVector
        ⟨p.baseChangeTowerIndexEquiv (K := K) (L := L) a,
          (p.baseChangeTowerIso_simple_iff (K := K) (L := L) a.val).mp a.property⟩ :=
  rootVector_map_congr (k := L)
    ((p.baseChange (F := K)).baseChange (F := L)) (p.baseChange (F := L))
    (Descent.pullbackComparison (algebraBaseMap k K) (algebraBaseMap K L)
      (algebraBaseMap k L) (Lie.algebraBaseMap_tower (k := k) (K := K) (L := L)) G).hom
    (baseChangeTowerGroupIso (k := k) (K := K) (L := L) (G := G)).hom a
    ⟨a.val, (p.baseChangeTower_simple_iff (K := K) (L := L) a.val).mp a.property⟩
    ⟨p.baseChangeTowerIndexEquiv (K := K) (L := L) a,
      (p.baseChangeTowerIso_simple_iff (K := K) (L := L) a.val).mp a.property⟩
    (baseChangeTowerGroupIso_hom (k := k) (K := K) (L := L) (G := G)).symm
    (by apply Subtype.ext; rfl)
    (p.baseChangeTower_rootVector_all (K := K) (L := L) a)

end Tower

end SplitPinning

end Langlands.GroupScheme
