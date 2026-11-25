import Langlands.Geometry.FormalGroup.DeligneIntegralImageSheaf
import Langlands.Geometry.FormalGroup.DeligneIntegerShift
import Langlands.Geometry.FormalGroup.DeligneEtaQuotientBaseChange
import Langlands.Geometry.ModuleSheafSubobject

/-! # Actual determinant subsheaves in Deligne's normalization -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Langlands.ModuleSheaf

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F]
  {X : TopCat.{u}}

/-- The actual scalar-restriction stalk comparison is natural in rational sheaves. -/
theorem restrictionStalkIso_naturality
    {N N' : X.Sheaf (ModuleCat.{u} F)} (g : N ⟶ N') (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
        ((rationalRestriction F X).map g).hom ≫
        (restrictionStalkIso F X N' x).hom =
      (restrictionStalkIso F X N x).hom ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map g.hom) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, restrictionStalkIso_germ, ← Category.assoc,
    restrictionStalkIso_germ, ← Functor.map_comp,
    TopCat.Presheaf.stalkFunctor_map_germ]
  rfl

/-- Postcomposition of the actual integral-image stalk map by a rational sheaf map. -/
theorem imageStalkMap_postcomp
    (M : X.Sheaf (ModuleCat.{u} O)) {N N' : X.Sheaf (ModuleCat.{u} F)}
    (f : M ⟶ (rationalRestriction F X).obj N) (g : N ⟶ N') (x : X) :
    imageStalkMap M N' (f ≫ (rationalRestriction F X).map g) x =
      imageStalkMap M N f x ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map g.hom) := by
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  change T.map (f.hom ≫ ((rationalRestriction F X).map g).hom) ≫ _ = _
  rw [T.map_comp, Category.assoc, restrictionStalkIso_naturality]
  rfl

/-- Actual multiplication by a nonzero field coefficient is a sheaf isomorphism. -/
def coefficientMultiplicationIso (N : X.Sheaf (ModuleCat.{u} F)) (a : F) (ha : a ≠ 0) :
    N ≅ N where
  hom := coefficientMultiplication N a
  inv := coefficientMultiplication N a⁻¹
  hom_inv_id := by
    apply Sheaf.hom_ext
    ext U s
    change a⁻¹ • (a • s) = s
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  inv_hom_id := by
    apply Sheaf.hom_ext
    ext U s
    change a • (a⁻¹ • s) = s
    rw [smul_smul, mul_inv_cancel₀ ha, one_smul]

/-- The actual stalk of coefficient multiplication is multiplication by that coefficient. -/
theorem coefficientMultiplication_stalk (N : X.Sheaf (ModuleCat.{u} F))
    (a : F) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} F) x).map
        (coefficientMultiplication N a).hom =
      ModuleCat.ofHom (LinearMap.lsmul F
        (TopCat.Presheaf.stalk (C := ModuleCat.{u} F) N.obj x) a) := by
  apply TopCat.Presheaf.stalk_hom_ext
  intro U hx
  rw [TopCat.Presheaf.stalkFunctor_map_germ]
  ext s
  exact (TopCat.Presheaf.germ N.obj U x hx).hom.map_smul a s

/-- Exterior ambient stalk coordinates intertwine multiplication after taking the wedge. -/
theorem exteriorAmbientStalkIso_coefficient
    (N : X.Sheaf (ModuleCat.{u} F)) (k : ℕ) (a : F) (x : X) :
    (TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
        ((rationalRestriction F X).map
          (coefficientMultiplication (exteriorSheaf N.obj k) a)).hom ≫
        (exteriorAmbientStalkIso (O := O) N k x).hom =
      (exteriorAmbientStalkIso (O := O) N k x).hom ≫
        (ModuleCat.restrictScalars (algebraMap O F)).map
          (ModuleCat.ofHom (LinearMap.lsmul F
            ((TopCat.Presheaf.stalk (C := ModuleCat.{u} F) N.obj x).exteriorPower k) a)) := by
  change _ ≫ ((restrictionStalkIso F X (exteriorSheaf N.obj k) x).hom ≫
      (ModuleCat.restrictScalars (algebraMap O F)).map
        (exteriorSheafStalkIso N.obj x k).hom) = _
  rw [← Category.assoc, restrictionStalkIso_naturality, Category.assoc,
    coefficientMultiplication_stalk]
  dsimp only [exteriorAmbientStalkIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc]
  apply congrArg (fun g =>
    (restrictionStalkIso F X (exteriorSheaf N.obj k) x).hom ≫ g)
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg ((ModuleCat.restrictScalars (algebraMap O F)).map)
  ext s
  exact (exteriorSheafStalkIso N.obj x k).hom.hom.map_smul a s

/-- Actual inverse image transports the stalk image by the canonical stalk isomorphism. -/
theorem stalkImage_inverseImage {Y : TopCat.{u}} (f : X ⟶ Y)
    {M N : Y.Sheaf (ModuleCat.{u} O)} (g : M ⟶ N) (x : X) :
    (stalkImage g (f x)).map (inverseImageStalkIso f N x).hom.hom =
      stalkImage ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g) x := by
  have h := congrArg (fun k => k.hom) (inverseImageStalkIso_naturality f g x)
  simp only [ModuleCat.hom_comp] at h
  unfold stalkImage
  rw [← LinearMap.range_comp, h]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (inverseImageStalkIso f M x).toLinearEquiv.surjective)

/-- Equality of two inverse-image subobjects is detected at the image points. -/
theorem subobject_inverseImage_eq_iff {Y : TopCat.{u}} (f : X ⟶ Y)
    {A B N : Y.Sheaf (ModuleCat.{u} O)} (g : A ⟶ N) (h : B ⟶ N)
    [Mono g] [Mono h] :
    Subobject.mk ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map g) =
        Subobject.mk ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map h) ↔
      ∀ x : X, stalkImage g (f x) = stalkImage h (f x) := by
  rw [subobject_mk_eq_iff_stalkImage_eq]
  apply forall_congr'
  intro x
  rw [← stalkImage_inverseImage f g x, ← stalkImage_inverseImage f h x]
  exact (Submodule.map_injective_of_injective
    (inverseImageStalkIso f N x).toLinearEquiv.injective).eq_iff

namespace LatticePiSheaf

variable {d : ℕ} {π : O} (M : LatticePiSheaf d π X)

/-- The actual determinant subsheaf generated by the degree-i integral component. -/
def componentDeterminantSubsheaf (i : ZMod d) : X.Sheaf (ModuleCat.{u} O) :=
  exteriorSubsheaf (M.component i) (rationalLattice F X d π M.sheaf)
    (M.componentToRational F i) d

/-- Its monomorphic inclusion in the top exterior rational sheaf. -/
def componentDeterminantInclusion (i : ZMod d) :
    M.componentDeterminantSubsheaf (F := F) i ⟶
      exteriorAmbient (O := O) (rationalLattice F X d π M.sheaf) d :=
  exteriorSubsheafInclusion (M.component i) (rationalLattice F X d π M.sheaf)
    (M.componentToRational F i) d

instance (i : ZMod d) : Mono (M.componentDeterminantInclusion (F := F) i) := by
  unfold componentDeterminantInclusion
  infer_instance

/-- The independently constructed component determinant inclusion has the expected stalk image. -/
theorem componentDeterminantInclusion_stalk_range (i : ZMod d) (x : X) :
    (stalkImage (M.componentDeterminantInclusion (F := F) i) x).map
        (exteriorAmbientStalkIso (O := O) (rationalLattice F X d π M.sheaf) d x).hom.hom =
      exteriorStalkLattice F d _ (M.componentStalkLattice F i x) := by
  unfold stalkImage
  rw [← LinearMap.range_comp]
  change LinearMap.range (exteriorSubsheafStalkMap (M.component i)
    (rationalLattice F X d π M.sheaf) (M.componentToRational F i) d x).hom = _
  rw [exteriorSubsheafStalkMap_range, M.imageStalkMap_componentToRational F i x]
  rfl

end LatticePiSheaf

namespace FramedLatticePiSheaf

variable {d : ℕ} [NeZero d] {π : O} (M : FramedLatticePiSheaf d π X F)

/-- The actual integral-frame sheaf map translated by every integer Pi power. -/
def translatedIntegralFrameSheafMap (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
      (ModuleCat.of O (Fin d → O)) ⟶
        (rationalRestriction F X).obj (rationalLattice F X d π M.lattice.sheaf) :=
  M.integralFrameSheafMap F ≫ (rationalRestriction F X).map
    (rationalPiAut F X d π M.lattice.sheaf hπ ^ n).asIso.hom

/-- The translated sheaf map has the previously constructed Pi-translated frame stalk image. -/
theorem translatedIntegralFrameSheafMap_stalk_range
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    LinearMap.range (imageStalkMap
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
        (ModuleCat.of O (Fin d → O)))
      (rationalLattice F X d π M.lattice.sheaf)
      (M.translatedIntegralFrameSheafMap hπ n) x).hom =
        M.translatedFrameStalkLattice F hπ n x := by
  rw [translatedIntegralFrameSheafMap, imageStalkMap_postcomp,
    ModuleCat.hom_comp, LinearMap.range_comp, M.imageStalkMap_integralFrameSheafMap_range,
    ← rationalPiStalkAut_zpow_hom]
  rfl

/-- The actual exterior subsheaf generated by the Pi-translated integral frame. -/
def translatedFrameDeterminantSubsheaf (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    X.Sheaf (ModuleCat.{u} O) :=
  exteriorSubsheaf
    ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
      (ModuleCat.of O (Fin d → O)))
    (rationalLattice F X d π M.lattice.sheaf)
    (M.translatedIntegralFrameSheafMap hπ n) d

/-- The source's pi^(-n) multiplication is applied on the rational exterior sheaf. -/
def determinantScalingIso (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    exteriorAmbient (O := O) (rationalLattice F X d π M.lattice.sheaf) d ≅
      exteriorAmbient (O := O) (rationalLattice F X d π M.lattice.sheaf) d :=
  (rationalRestriction F X).mapIso
    (coefficientMultiplicationIso
      (exteriorSheaf (rationalLattice F X d π M.lattice.sheaf).obj d)
      (algebraMap O F π ^ (-n)) (zpow_ne_zero _ hπ))

/-- The normalized determinant lattice is a genuine monomorphic sheaf inclusion. -/
def normalizedFrameDeterminantInclusion (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    M.translatedFrameDeterminantSubsheaf hπ n ⟶
      exteriorAmbient (O := O) (rationalLattice F X d π M.lattice.sheaf) d :=
  exteriorSubsheafInclusion
    ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
      (ModuleCat.of O (Fin d → O)))
    (rationalLattice F X d π M.lattice.sheaf)
    (M.translatedIntegralFrameSheafMap hπ n) d ≫
      (M.determinantScalingIso hπ n).hom

instance (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    Mono (M.normalizedFrameDeterminantInclusion hπ n) := by
  unfold normalizedFrameDeterminantInclusion
  infer_instance

/-- The actual normalized determinant inclusion has exactly the literal stalk lattice. -/
theorem normalizedFrameDeterminantInclusion_stalk_range
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) (x : X) :
    (stalkImage (M.normalizedFrameDeterminantInclusion hπ n) x).map
        (exteriorAmbientStalkIso (O := O)
          (rationalLattice F X d π M.lattice.sheaf) d x).hom.hom =
      M.normalizedFrameDeterminant F hπ n x := by
  let T := TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x
  unfold stalkImage
  rw [← LinearMap.range_comp]
  change LinearMap.range
    (T.map ((exteriorSubsheafInclusion
      ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
        (ModuleCat.of O (Fin d → O)))
      (rationalLattice F X d π M.lattice.sheaf)
      (M.translatedIntegralFrameSheafMap hπ n) d).hom ≫
        ((rationalRestriction F X).map
          (coefficientMultiplication
            (exteriorSheaf (rationalLattice F X d π M.lattice.sheaf).obj d)
            (algebraMap O F π ^ (-n)))).hom) ≫
      (exteriorAmbientStalkIso (O := O)
        (rationalLattice F X d π M.lattice.sheaf) d x).hom).hom = _
  rw [T.map_comp, Category.assoc, exteriorAmbientStalkIso_coefficient,
    ← Category.assoc, ModuleCat.hom_comp, LinearMap.range_comp]
  change scaleStalkLattice F (algebraMap O F π ^ (-n)) _
      (LinearMap.range (exteriorSubsheafStalkMap
        ((constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).obj
          (ModuleCat.of O (Fin d → O)))
        (rationalLattice F X d π M.lattice.sheaf)
        (M.translatedIntegralFrameSheafMap hπ n) d x).hom) = _
  rw [exteriorSubsheafStalkMap_range, M.translatedIntegralFrameSheafMap_stalk_range]
  rfl

end FramedLatticePiSheaf

open _root_.AlgebraicGeometry

namespace SheafPreDatum

variable {d : ℕ} [NeZero d] {π : O} {S : Scheme.{u}} {φ : O →+* Γ(S, ⊤)}
  (D : SheafPreDatum d π F φ)

/-- The actual component determinant subobject restricted to its Pi-zero locus. -/
def componentDeterminantOnPiZeroLocus (i : ZMod d) :
    Subobject ((TopCat.Sheaf.pullback (ModuleCat.{u} O) (D.piZeroInclusion i)).obj
      (exteriorAmbient (O := O)
        (rationalLattice F (S : TopCat) d π D.eta.lattice.sheaf) d)) :=
  Subobject.mk ((TopCat.Sheaf.pullback (ModuleCat.{u} O) (D.piZeroInclusion i)).map
    (D.eta.lattice.componentDeterminantInclusion (F := F) i))

/-- The independently normalized frame determinant subobject on the same locus. -/
def normalizedFrameDeterminantOnPiZeroLocus (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    Subobject ((TopCat.Sheaf.pullback (ModuleCat.{u} O)
      (D.piZeroInclusion (n : ZMod d))).obj
        (exteriorAmbient (O := O)
          (rationalLattice F (S : TopCat) d π D.eta.lattice.sheaf) d)) :=
  Subobject.mk ((TopCat.Sheaf.pullback (ModuleCat.{u} O)
    (D.piZeroInclusion (n : ZMod d))).map
      (D.eta.normalizedFrameDeterminantInclusion hπ n))

/-- Deligne's condition (c) expressed as equality of actual sheaf subobjects. -/
def DeterminantSubsheavesNormalized (hπ : algebraMap O F π ≠ 0) : Prop :=
  ∀ n : ℤ, D.componentDeterminantOnPiZeroLocus (n : ZMod d) =
    D.normalizedFrameDeterminantOnPiZeroLocus hπ n

set_option maxHeartbeats 800000 in
/-- Equality on one Pi-zero locus is precisely the corresponding stalk-lattice condition. -/
theorem determinantOnPiZeroLocus_eq_iff
    (hπ : algebraMap O F π ≠ 0) (n : ℤ) :
    D.componentDeterminantOnPiZeroLocus (n : ZMod d) =
        D.normalizedFrameDeterminantOnPiZeroLocus hπ n ↔
      ∀ x : D.piZeroSpace (n : ZMod d),
        D.componentDeterminant (n : ZMod d) x.val =
          D.eta.normalizedFrameDeterminant F hπ n x.val := by
  rw [componentDeterminantOnPiZeroLocus, normalizedFrameDeterminantOnPiZeroLocus,
    subobject_inverseImage_eq_iff]
  apply forall_congr'
  intro x
  let e := exteriorAmbientStalkIso (O := O)
    (rationalLattice F (S : TopCat) d π D.eta.lattice.sheaf) d
      (D.piZeroInclusion (n : ZMod d) x)
  rw [← (Submodule.map_injective_of_injective e.toLinearEquiv.injective).eq_iff]
  change
    (stalkImage (D.eta.lattice.componentDeterminantInclusion (F := F) (n : ZMod d))
      (D.piZeroInclusion (n : ZMod d) x)).map e.hom.hom =
    (stalkImage (D.eta.normalizedFrameDeterminantInclusion hπ n)
      (D.piZeroInclusion (n : ZMod d) x)).map e.hom.hom ↔ _
  rw [D.eta.lattice.componentDeterminantInclusion_stalk_range,
    D.eta.normalizedFrameDeterminantInclusion_stalk_range]
  rfl

/-- The independently constructed sheaf condition and literal stalk condition are equivalent. -/
theorem determinantSubsheavesNormalized_iff (hπ : algebraMap O F π ≠ 0) :
    D.DeterminantSubsheavesNormalized hπ ↔ D.DeterminantNormalized hπ := by
  constructor
  · intro h n x hx
    exact (D.determinantOnPiZeroLocus_eq_iff hπ n).mp (h n) ⟨x, hx⟩
  · intro h n
    apply (D.determinantOnPiZeroLocus_eq_iff hπ n).mpr
    intro x
    exact h n x.val x.property

end SheafPreDatum

end Langlands.DeligneFormalSpace
