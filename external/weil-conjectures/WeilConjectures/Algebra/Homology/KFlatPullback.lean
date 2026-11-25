/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatModuleBaseChange
import WeilConjectures.Algebra.Homology.KFlatStalkCriterion
import WeilConjectures.Algebra.Homology.TensorPullbackStalkComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-!
# Pullback preserves K-flat complexes

Source: Stacks Project, Cohomology, Lemma 20.26.8, Tag 06YC
(blueprint: lem-pc-kflat-pullback-preservation).

The pulled-back complex has terms given by the topological module inverse image
followed by sheafified sectionwise change of rings along the adjoint structure map.
Its differentials are inverse images of the original differentials followed by
`changeOfRingsHom`. No comparison with an abstract module pullback is used.
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace CochainComplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)

/-- The ring map `f⁻¹ OY → OX` adjoint to the structure-sheaf map.
Source: Stacks, Tag 0095 (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackRingMap : TopCat.Sheaf.inverseImageRing f OY ⟶ OX :=
  ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) CommRingCat.{w} _ _).homEquiv OY OX).symm φ

private theorem inverseImageModuleMap_zero
    (M N : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) :
    TopCat.Sheaf.inverseImageModuleMap f OY M (0 : M ⟶ N) = 0 := by
  let F := TopCat.Sheaf.inverseImageConstruction f AddCommGrpCat.{w}
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) AddCommGrpCat.{w}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have : F.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : F.PreservesZeroMorphisms := inferInstance
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk, F]
  rfl

private theorem changeOfRingsHom_zero
    (M N : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (TopCat.Sheaf.inverseImageRing f OY))) :
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      M (0 : M ⟶ N) = 0 := by
  let p :
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap f OX OY φ) M ⟶
      SheafOfModules.changeOfRingsPresheaf.{w, w, w} (tensorPullbackRingMap f OX OY φ) N :=
    { app := fun U ↦ (ModuleCat.extendScalars _).map ((0 : M ⟶ N).val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality _ M 0 }
  have hp : p = 0 := by
    apply PresheafOfModules.hom_ext
    intro U
    have hz : (0 : M ⟶ N).val.app U = 0 := rfl
    change (ModuleCat.extendScalars
      ((tensorPullbackRingMap f OX OY φ).hom.app U).hom).map _ = 0
    rw [hz]
    exact Functor.map_zero _ _ _
  change (PresheafOfModules.sheafification
    (𝟙 ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OX).obj)).map p = 0
  rw [hp, Functor.map_zero]

private theorem inverseImageModuleMap_comp
    {M N P : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)} (a : M ⟶ N) (b : N ⟶ P) :
    TopCat.Sheaf.inverseImageModuleMap f OY M (a ≫ b) =
      TopCat.Sheaf.inverseImageModuleMap f OY M a ≫
        TopCat.Sheaf.inverseImageModuleMap f OY N b := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  simp [TopCat.Sheaf.inverseImageModuleMap, PresheafOfModules.homMk]
  rfl

private theorem changeOfRingsHom_comp
    {M N P : SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj
          (TopCat.Sheaf.inverseImageRing f OY))} (a : M ⟶ N) (b : N ⟶ P) :
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      M (a ≫ b) =
    SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ) M a ≫
      SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ) N b := by
  unfold SheafOfModules.changeOfRingsHom
  rw [← Functor.map_comp]
  congr 1
  apply PresheafOfModules.hom_ext
  intro U
  change (ModuleCat.extendScalars
    ((tensorPullbackRingMap f OX OY φ).hom.app U).hom).map (a.val.app U ≫ b.val.app U) = _
  exact Functor.map_comp _ _ _

variable (K : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)

/-- The differential obtained by inverse image and the sectionwise tensor map.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackDifferential (i j : ℤ) :
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X i)) ⟶
    SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
      (TopCat.Sheaf.inverseImageModule f OY (K.X j)) :=
  SheafOfModules.changeOfRingsHom.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
    (TopCat.Sheaf.inverseImageModuleMap f OY (K.X i) (K.d i j))

/-- The tensor pullback differential has cochain shape.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation).
Proof: outside the cochain shape the original differential is zero. The inverse-image
abelian-sheaf functor preserves zero maps, as do sectionwise extension of scalars and
module sheafification. Hence the displayed differential is zero. -/
theorem tensorPullbackDifferential_shape (i j : ℤ)
    (h : ¬ (ComplexShape.up ℤ).Rel i j) :
    tensorPullbackDifferential f OX OY φ K i j = 0 := by
  unfold tensorPullbackDifferential
  rw [K.shape i j h, inverseImageModuleMap_zero, changeOfRingsHom_zero]

/-- Consecutive tensor pullback differentials compose to zero.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation).
Proof: the inverse-image abelian-sheaf functor preserves composition and zero maps;
the module maps have exactly those underlying abelian maps. Sectionwise extension of
scalars and sheafification preserve composition and zero maps as well. Apply these
facts to `K.d_comp_d i j k`. -/
theorem tensorPullbackDifferential_comp (i j k : ℤ) :
    tensorPullbackDifferential f OX OY φ K i j ≫
      tensorPullbackDifferential f OX OY φ K j k = 0 := by
  unfold tensorPullbackDifferential
  rw [← changeOfRingsHom_comp, ← inverseImageModuleMap_comp, K.d_comp_d,
    inverseImageModuleMap_zero, changeOfRingsHom_zero]

/-- The termwise formula `f⁻¹ K ⊗_{f⁻¹ OY} OX`, including its differentials.
Source: Stacks, Tags 0095 and 06YC (blueprint: lem-pc-kflat-pullback-preservation). -/
def tensorPullbackComplex : CochainComplex (SheafOfModules.{w}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{w} RingCat.{w})).obj OX)) ℤ where
  X i := SheafOfModules.changeOfRings.{w, w, w} (tensorPullbackRingMap f OX OY φ)
    (TopCat.Sheaf.inverseImageModule f OY (K.X i))
  d := tensorPullbackDifferential f OX OY φ K
  shape := tensorPullbackDifferential_shape f OX OY φ K
  d_comp_d' i j k _ _ := tensorPullbackDifferential_comp f OX OY φ K i j k

set_option backward.isDefEq.respectTransparency true in
/-- Pullback along a morphism of ringed spaces preserves K-flatness. Source: Stacks,
Tag 06YC (blueprint: lem-pc-kflat-pullback-preservation).

Proof:
1. At `x : X`, set `y = f x`, `A = OY_y`, and `B = OX_x`. The inverse-image stalk
   isomorphism (lem-weil-pbc-topological-inverse-image-stalk) and the change-of-rings
   tensor-stalk isomorphism (lem-weil-pbc-stalk-change-of-rings-tensor), natural in the
   differentials, identify the pullback stalk complex with `K_y ⊗_A B`.
2. The forward direction of lem-pc-kflat-stalk-criterion makes `K_y` K-flat over `A`.
3. For any acyclic `B`-complex `L`, restriction to `A` is acyclic, and associativity of
   tensor products and total-complex direct sums identifies
   `Tot(L ⊗_B (K_y ⊗_A B))` with `Tot(L ⊗_A K_y)`. The latter is acyclic by
   def-pc-kflat-complex and def-pc-tensor-complex-sheaves. Thus the pullback stalk is
   K-flat; this is Stacks Tag 06Y1 and requires no flatness of the ring map.
4. The reverse direction of lem-pc-kflat-stalk-criterion on `X` proves the conclusion.
-/
theorem isKFlat_pullback
    {X Y : TopCat.{w}} (f : X ⟶ Y)
    (OX : Sheaf (Opens.grothendieckTopology X) CommRingCat.{w})
    (OY : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{w})
    (φ : OY ⟶ ((Opens.map f).sheafPushforwardContinuous CommRingCat.{w}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj OX)
    (K : CochainComplex (SheafOfModules.{w}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat.{w} RingCat.{w})).obj OY)) ℤ)
    (hK : K.IsKFlatTensor) :
    IsKFlatTensor (R := OX) (tensorPullbackComplex f OX OY φ K) := by
  let RX : AlgebraicGeometry.RingedSpace.{w} :=
    { carrier := X, presheaf := OX.obj, IsSheaf := OX.property }
  let RY : AlgebraicGeometry.RingedSpace.{w} :=
    { carrier := Y, presheaf := OY.obj, IsSheaf := OY.property }
  have hstalk :=
    (AlgebraicGeometry.RingedSpace.isKFlat_iff_stalk_isKFlat RY K).mp hK
  apply (AlgebraicGeometry.RingedSpace.isKFlat_iff_stalk_isKFlat RX
    (tensorPullbackComplex f OX OY φ K)).mpr
  intro x L hL
  let ρ := AlgebraicGeometry.RingedSpace.tensorPullbackStalkRingHom RX RY f
    (tensorPullbackRingMap f OX OY φ) x
  let e := tensorPullbackStalkComplexIso RX RY f
    (tensorPullbackRingMap f OX OY φ) K (tensorPullbackComplex f OX OY φ K)
    (fun i ↦ Iso.refl _)
    (by
      intro i j
      exact (Category.comp_id _).trans (Category.id_comp _).symm) x
  have : (AlgebraicGeometry.RingedSpace.moduleStalkFunctor RY (f x)).PreservesZeroMorphisms :=
    AlgebraicGeometry.RingedSpace.moduleStalkFunctor_preservesZeroMorphisms RY (f x)
  have ht := acyclic_mapBifunctor_extendScalars_of_kFlat ρ
    (((AlgebraicGeometry.RingedSpace.moduleStalkFunctor RY (f x)).mapHomologicalComplex
      (.up ℤ)).obj K)
    (by intro F hF; exact hstalk (f x) F hF) L hL
  let T := ((MonoidalCategory.curriedTensor
    (ModuleCat.{w} (RX.presheaf.stalk x))).map₂CochainComplex).obj L
  intro i
  exact (ht i).of_iso (T.mapIso e)

end
end CochainComplex
