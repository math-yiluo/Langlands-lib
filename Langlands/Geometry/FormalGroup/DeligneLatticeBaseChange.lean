import Langlands.Geometry.FormalGroup.DeligneSheafBaseChange
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.DirectSum.Decomposition

/-! # Actual inverse image of Deligne's flat graded and framed lattices -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits TopologicalSpace DirectSum

variable {O : Type u} [CommRing O] {X Y : TopCat.{u}}

/-- The actual inverse-image stalk is the original stalk at the image point. -/
def inverseImageStalkIso (f : X ⟶ Y) (M : Y.Sheaf (ModuleCat.{u} O)) (x : X) :
    TopCat.Presheaf.stalk M.obj (f x) ≅
      TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M).obj x := by
  let N := (TopCat.Presheaf.pullback (ModuleCat.{u} O) f).obj M.obj
  letI := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (ModuleCat.{u} O) N
  exact (TopCat.Presheaf.stalkPullbackIso (ModuleCat.{u} O) f M.obj x) ≪≫
    asIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
      (toSheafify (Opens.grothendieckTopology X) N)) ≪≫
    (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)) ⋙
      TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).mapIso
        ((TopCat.Sheaf.pullbackIso (ModuleCat.{u} O) f).app M)).symm

instance inverseImage_preservesFiniteLimits (f : X ⟶ Y) :
    PreservesFiniteLimits (TopCat.Sheaf.pullback (ModuleCat.{u} O) f) := by
  let : ReflectsLimits (CategoryTheory.forget (ModuleCat.{u} O)) :=
    reflectsLimits_of_reflectsIsomorphisms
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f)
    (ModuleCat.{u} O) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)

instance inverseImage_additive (f : X ⟶ Y) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Multiplication by a coefficient on the actual module sheaf. -/
def coefficientMultiplication (M : X.Sheaf (ModuleCat.{u} O)) (a : O) : M ⟶ M where
  hom := {
    app U := ModuleCat.ofHom (LinearMap.lsmul O (M.obj.obj U) a)
    naturality {U V} g := by
      ext x
      exact ((M.obj.map g).hom.map_smul a x).symm }

/-- Inverse image commutes with coefficient multiplication on an actual sheaf. -/
theorem inverseImage_smul (f : X ⟶ Y) (M : Y.Sheaf (ModuleCat.{u} O)) (a : O) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (coefficientMultiplication M a) =
      coefficientMultiplication ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj M) a := by
  let adj := TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{u} O) f
  apply (adj.homEquiv _ _).injective
  rw [← Category.comp_id ((TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map
    (coefficientMultiplication M a)), Adjunction.homEquiv_naturality_left,
    adj.homEquiv_id, Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  ext U x
  exact ((adj.unit.app M).hom.app U).hom.map_smul a x

variable {d : ℕ} {π : O}

/-- The restriction comparison for the actual Pi-algebra sheaf. -/
def inverseImageLatticeScalarIso (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj (latticeScalarSheaf d π Y M) ≅
      latticeScalarSheaf d π X
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) :=
  (inverseImageRestrictionIso (algebraMap O (PiAlgebra d π)) f).app M

/-- Actual inverse image of Pi multiplication is Pi multiplication. -/
theorem inverseImage_latticePiIntegral (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).map
        (latticePiIntegral d π Y M) =
      latticePiIntegral d π X
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) :=
  inverseImage_smul f M (PiAlgebra.pi d π)

/-- The actual coefficient comparison intertwines the distinguished operators. -/
theorem inverseImageLatticeScalarIso_pi (f : X ⟶ Y)
    (M : Y.Sheaf (ModuleCat.{u} (PiAlgebra d π))) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (latticePi d π Y M) ≫
        (inverseImageLatticeScalarIso f M).hom =
      (inverseImageLatticeScalarIso f M).hom ≫
        latticePi d π X
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M) := by
  have h := (inverseImageRestrictionIso (algebraMap O (PiAlgebra d π)) f).hom.naturality
    (latticePiIntegral d π Y M)
  dsimp only [Functor.comp_map] at h
  rw [inverseImage_latticePiIntegral] at h
  exact h

/-- A finite family of inclusions with orthogonal left inverses and total sum
identity gives an internal sum of its actual ranges. -/
theorem isInternal_of_finite_splitting {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : ModuleCat.{u} O} {C : ι → ModuleCat.{u} O}
    (a : ∀ i, C i →ₗ[O] V) (p : ∀ i, V →ₗ[O] C i)
    (hdiag : ∀ i x, p i (a i x) = x)
    (hoff : ∀ i j, j ≠ i → ∀ x, p i (a j x) = 0)
    (hsum : ∀ x, ∑ i, a i (p i x) = x) :
    DirectSum.IsInternal (fun i => LinearMap.range (a i)) := by
  classical
  let W := fun i => LinearMap.range (a i)
  have hp (z : ⨁ i, W i) (i : ι) :
      a i (p i (DirectSum.coeAddMonoidHom W z)) = (z i).val := by
    induction z using DirectSum.induction_on with
    | zero => simp
    | of j w =>
        obtain ⟨x, hx⟩ := w.property
        by_cases hji : j = i
        · subst j
          simp only [DirectSum.coeAddMonoidHom_of, ← hx,
            hdiag, DirectSum.of_eq_same]
        · rw [DirectSum.coeAddMonoidHom_of, ← hx, hoff i j hji,
            map_zero, DirectSum.of_eq_of_ne (β := fun i => ↥(W i)) j i w (Ne.symm hji)]
          rfl
    | add z w hz hw =>
        simp only [map_add, hz, hw, DirectSum.add_apply, Submodule.coe_add]
  constructor
  · intro z w h
    apply DirectSum.ext
    intro i
    apply Subtype.ext
    exact (hp z i).symm.trans ((congrArg (fun x => a i (p i x)) h).trans (hp w i))
  · intro x
    refine ⟨∑ i, DirectSum.of (fun i => W i) i ⟨a i (p i x), ⟨p i x, rfl⟩⟩, ?_⟩
    change DirectSum.coeAddMonoidHom W
      (∑ i, DirectSum.of (fun i => W i) i ⟨a i (p i x), ⟨p i x, rfl⟩⟩) = x
    simpa only [map_sum, DirectSum.coeAddMonoidHom_of] using hsum x

namespace LatticePiSheaf

variable (M : LatticePiSheaf d π Y)

/-- The canonical linear projection on sections, using the existing internal sum. -/
def sectionProjection (U : (Opens Y)ᵒᵖ) (i : ZMod d) :
    (latticeScalarSheaf d π Y M.sheaf).obj.obj U →ₗ[O] (M.component i).obj.obj U := by
  classical
  exact (LinearEquiv.ofInjective ((M.inclusion i).hom.app U).hom
      (M.injective i U)).symm.toLinearMap.comp
    ((DirectSum.component O (ZMod d)
      (fun j => LinearMap.range ((M.inclusion j).hom.app U).hom) i).comp
      (LinearEquiv.ofBijective (DirectSum.coeLinearMap
        (fun j => LinearMap.range ((M.inclusion j).hom.app U).hom))
          (M.isInternal U)).symm.toLinearMap)

@[simp]
theorem sectionProjection_inclusion (U : (Opens Y)ᵒᵖ) (i : ZMod d)
    (x : (M.component i).obj.obj U) :
    M.sectionProjection U i (((M.inclusion i).hom.app U) x) = x := by
  classical
  change (LinearEquiv.ofInjective ((M.inclusion i).hom.app U).hom
    (M.injective i U)).symm
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap
      (fun j => LinearMap.range ((M.inclusion j).hom.app U).hom))
        (M.isInternal U)).symm (((M.inclusion i).hom.app U) x) i) = x
  rw [(M.isInternal U).ofBijective_coeLinearMap_of_mem
    (show ((M.inclusion i).hom.app U) x ∈
      LinearMap.range ((M.inclusion i).hom.app U).hom from ⟨x, rfl⟩)]
  exact (LinearEquiv.ofInjective ((M.inclusion i).hom.app U).hom
    (M.injective i U)).symm_apply_apply x

@[simp]
theorem sectionProjection_inclusion_ne (U : (Opens Y)ᵒᵖ) {i j : ZMod d}
    (hji : j ≠ i) (x : (M.component j).obj.obj U) :
    M.sectionProjection U i (((M.inclusion j).hom.app U) x) = 0 := by
  classical
  change (LinearEquiv.ofInjective ((M.inclusion i).hom.app U).hom
    (M.injective i U)).symm
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap
      (fun j => LinearMap.range ((M.inclusion j).hom.app U).hom))
        (M.isInternal U)).symm (((M.inclusion j).hom.app U) x) i) = 0
  rw [(M.isInternal U).ofBijective_coeLinearMap_of_mem_ne hji
    (show ((M.inclusion j).hom.app U) x ∈
      LinearMap.range ((M.inclusion j).hom.app U).hom from ⟨x, rfl⟩), map_zero]

/-- Equality of linear maps can be tested on all homogeneous inclusions. -/
theorem section_hom_ext (U : (Opens Y)ᵒᵖ) {N : ModuleCat.{u} O}
    {a b : (latticeScalarSheaf d π Y M.sheaf).obj.obj U →ₗ[O] N}
    (h : ∀ i x, a (((M.inclusion i).hom.app U) x) =
      b (((M.inclusion i).hom.app U) x)) : a = b := by
  classical
  ext x
  obtain ⟨z, rfl⟩ := (M.isInternal U).surjective x
  induction z using DirectSum.induction_on with
  | zero => simp
  | of i w =>
      obtain ⟨x, hx⟩ := w.property
      simpa only [DirectSum.coeAddMonoidHom_of, hx] using h i x
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The section projections respect restriction maps and so are sheaf maps. -/
def projection (i : ZMod d) : latticeScalarSheaf d π Y M.sheaf ⟶ M.component i where
  hom := {
    app U := ConcreteCategory.ofHom (C := ModuleCat.{u} O)
      (X := (latticeScalarSheaf d π Y M.sheaf).obj.obj U)
      (Y := (M.component i).obj.obj U) (M.sectionProjection U i)
    naturality {U V} g := by
      apply ModuleCat.hom_ext
      apply M.section_hom_ext U
      intro j x
      have hj := NatTrans.naturality (M.inclusion j).hom g
      have hjx := congrArg (fun k => k x) hj
      change M.sectionProjection V i
        (((latticeScalarSheaf d π Y M.sheaf).obj.map g) (((M.inclusion j).hom.app U) x)) =
        ((M.component i).obj.map g)
          (M.sectionProjection U i (((M.inclusion j).hom.app U) x))
      by_cases hji : j = i
      · subst j
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
          sectionProjection_inclusion] using
          congrArg (M.sectionProjection V i) hjx.symm
      · simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
          sectionProjection_inclusion_ne M U hji,
          sectionProjection_inclusion_ne M V hji, map_zero] using
          congrArg (M.sectionProjection V i) hjx.symm }

@[simp]
theorem inclusion_projection (i : ZMod d) :
    M.inclusion i ≫ M.projection i = 𝟙 _ := by
  apply Sheaf.hom_ext
  ext U x
  exact M.sectionProjection_inclusion U i x

@[simp]
theorem inclusion_projection_ne {i j : ZMod d} (hji : j ≠ i) :
    M.inclusion j ≫ M.projection i = 0 := by
  apply Sheaf.hom_ext
  ext U x
  exact M.sectionProjection_inclusion_ne U hji x

variable [NeZero d]

/-- The finite homogeneous projections sum to the identity. -/
theorem sum_projection_inclusion :
    ∑ i : ZMod d, M.projection i ≫ M.inclusion i = 𝟙 _ := by
  classical
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply M.section_hom_ext U
  intro j x
  change (((sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} O)).map
    (∑ i : ZMod d, M.projection i ≫ M.inclusion i)).app U).hom
      (((M.inclusion j).hom.app U) x) = ((M.inclusion j).hom.app U) x
  rw [(sheafToPresheaf (Opens.grothendieckTopology Y) (ModuleCat.{u} O)).map_sum]
  simp only [NatTrans.app_sum,
    ModuleCat.hom_sum, LinearMap.sum_apply]
  change (∑ i : ZMod d, ((M.inclusion i).hom.app U)
    (M.sectionProjection U i (((M.inclusion j).hom.app U) x))) =
      ((M.inclusion j).hom.app U) x
  rw [Finset.sum_eq_single j]
  · rw [M.sectionProjection_inclusion]
  · intro i _ hij
    rw [M.sectionProjection_inclusion_ne U (Ne.symm hij), map_zero]
  · simp

/-- The pulled homogeneous inclusion uses the actual coefficient comparison. -/
def inverseImageInclusion (f : X ⟶ Y) (i : ZMod d) :
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj (M.component i) ⟶
      latticeScalarSheaf d π X
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M.sheaf) :=
  (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (M.inclusion i) ≫
    (inverseImageLatticeScalarIso f M.sheaf).hom

/-- The corresponding actual inverse-image projection. -/
def inverseImageProjection (f : X ⟶ Y) (i : ZMod d) :
    latticeScalarSheaf d π X
        ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M.sheaf) ⟶
      (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj (M.component i) :=
  (inverseImageLatticeScalarIso f M.sheaf).inv ≫
    (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (M.projection i)

omit [NeZero d] in
@[simp]
theorem inverseImageInclusion_projection (f : X ⟶ Y) (i : ZMod d) :
    M.inverseImageInclusion f i ≫ M.inverseImageProjection f i = 𝟙 _ := by
  simp only [inverseImageInclusion, inverseImageProjection, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, inclusion_projection]
  exact (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map_id _

omit [NeZero d] in
@[simp]
theorem inverseImageInclusion_projection_ne (f : X ⟶ Y) {i j : ZMod d} (hji : j ≠ i) :
    M.inverseImageInclusion f j ≫ M.inverseImageProjection f i = 0 := by
  simp only [inverseImageInclusion, inverseImageProjection, Category.assoc,
    Iso.hom_inv_id_assoc, ← Functor.map_comp, inclusion_projection_ne M hji,
    Functor.map_zero]

/-- Inverse image preserves the finite total-sum equation. -/
theorem inverseImage_sum_projection_inclusion (f : X ⟶ Y) :
    ∑ i : ZMod d, M.inverseImageProjection f i ≫ M.inverseImageInclusion f i = 𝟙 _ := by
  classical
  let P := TopCat.Sheaf.pullback (ModuleCat.{u} O) f
  let e := inverseImageLatticeScalarIso f M.sheaf
  calc
    _ = e.inv ≫ (∑ i : ZMod d, P.map (M.projection i ≫ M.inclusion i)) ≫ e.hom := by
      simp only [inverseImageInclusion, inverseImageProjection, P, e, Functor.map_comp,
        Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
    _ = 𝟙 _ := by
      rw [← P.map_sum, M.sum_projection_inclusion, P.map_id, Category.id_comp, e.inv_hom_id]

/-- The actual pulled components retain their sectionwise internal direct sum. -/
theorem inverseImage_isInternal (f : X ⟶ Y) (U : (Opens X)ᵒᵖ) :
    DirectSum.IsInternal
      (fun i => LinearMap.range ((M.inverseImageInclusion f i).hom.app U).hom) := by
  classical
  apply isInternal_of_finite_splitting
    (fun i => ((M.inverseImageInclusion f i).hom.app U).hom)
    (fun i => ((M.inverseImageProjection f i).hom.app U).hom)
  · intro i x
    exact congrArg (fun g => ((g.hom.app U).hom x))
      (M.inverseImageInclusion_projection f i)
  · intro i j hji x
    exact congrArg (fun g => ((g.hom.app U).hom x))
      (M.inverseImageInclusion_projection_ne f hji)
  · intro x
    have h := congrArg
      (fun g : latticeScalarSheaf d π X
          ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M.sheaf) ⟶
          latticeScalarSheaf d π X
            ((TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M.sheaf) =>
        (((sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).map
          g).app U).hom x) (M.inverseImage_sum_projection_inclusion f)
    rw [(sheafToPresheaf (Opens.grothendieckTopology X) (ModuleCat.{u} O)).map_id] at h
    simp only [Functor.map_sum, NatTrans.app_sum, ModuleCat.hom_sum,
      LinearMap.sum_apply, Functor.map_comp, NatTrans.comp_app,
      ModuleCat.hom_comp, LinearMap.comp_apply,
      NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply] at h
    simpa only [ObjectProperty.ι_map, ObjectProperty.ι_obj] using h

/-- Actual inverse image of the flat graded Pi-algebra lattice. -/
def inverseImage (f : X ⟶ Y) : LatticePiSheaf d π X where
  sheaf := (TopCat.Sheaf.pullback (ModuleCat.{u} (PiAlgebra d π)) f).obj M.sheaf
  flat x := (Module.Flat.equiv_iff (inverseImageStalkIso f M.sheaf x).toLinearEquiv).mp
    (M.flat (f x))
  component i := (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).obj (M.component i)
  inclusion := M.inverseImageInclusion f
  injective i U := by
    apply Function.LeftInverse.injective (g := ((M.inverseImageProjection f i).hom.app U))
    intro x
    exact congrArg (fun g => ((g.hom.app U).hom x))
      (M.inverseImageInclusion_projection f i)
  isInternal := M.inverseImage_isInternal f
  pi i := (TopCat.Sheaf.pullback (ModuleCat.{u} O) f).map (M.pi i)
  pi_inclusion i := by
    simp only [inverseImageInclusion]
    rw [ ← Category.assoc, ← Functor.map_comp, M.pi_inclusion,
      Functor.map_comp, Category.assoc, inverseImageLatticeScalarIso_pi,
      ← Category.assoc]

end LatticePiSheaf

namespace FramedLatticePiSheaf

variable {F : Type u} [Field F] [Algebra O F] [NeZero d]

/-- Inverse image of the actual rational frame, through the canonical constant
and rationalization comparisons. -/
def inverseImage (M : FramedLatticePiSheaf d π Y F) (f : X ⟶ Y) :
    FramedLatticePiSheaf d π X F where
  lattice := M.lattice.inverseImage f
  frame := ((inverseImageConstantIso (O := F) f).app
      (ModuleCat.of F (Fin d → F))).symm ≪≫
    (TopCat.Sheaf.pullback (ModuleCat.{u} F) f).mapIso M.frame ≪≫
    (inverseImageRationalIso (F := F) f).app (M.lattice.component 0)

end FramedLatticePiSheaf

end Langlands.DeligneFormalSpace
