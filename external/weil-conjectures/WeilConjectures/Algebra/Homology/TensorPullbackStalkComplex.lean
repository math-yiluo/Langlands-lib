/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkChangeOfRings
public import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransport

/-!
# The stalk complex of termwise tensor pullback

Let `f : X ⟶ Y` be a continuous map of ringed spaces with structure map
`α : f⁻¹𝒪_Y ⟶ 𝒪_X`, and let `x : X`. We define the canonical stalk ring map
`ρ : 𝒪_{Y,f x} → 𝒪_{X,x}` (`AlgebraicGeometry.RingedSpace.tensorPullbackStalkRingHom`), the
natural isomorphism `(M_{f x}) ⊗_ρ 𝒪_{X,x} ≅ (𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹M)_x`
(`AlgebraicGeometry.RingedSpace.tensorPullbackStalkIso`), and its termwise extension to complexes
(`CochainComplex.tensorPullbackStalkComplexIso`).

Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC.
(blueprint: lem-pc-tensor-pullback-stalk-complex)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry.RingedSpace

variable (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
  (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf) (x : X)

/-- The canonical stalk ring map `𝒪_{Y,f x} → 𝒪_{X,x}`: the inverse-image stalk comparison
`𝒪_{Y,f x} ≅ (f⁻¹𝒪_Y)_x` followed by the stalk of `α`. -/
def tensorPullbackStalkRingHom : Y.presheaf.stalk (f x) →+* X.presheaf.stalk x :=
  ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom.comp
    (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))).hom

/-- The stalk at `x` of the tensor pullback `𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹M` is the extension of scalars
of `M_{f x}` along `tensorPullbackStalkRingHom`. It is the composite of the inverse-image
scalar transport and the change-of-rings stalk isomorphism.
Source: Stacks Project, Sheaves, Tag 0098. -/
def tensorPullbackStalkIso (M : RingedSpace.Modules Y) :
    (ModuleCat.extendScalars (tensorPullbackStalkRingHom X Y f α x)).obj
        ((RingedSpace.moduleStalkFunctor Y (f x)).obj M) ≅
      (RingedSpace.moduleStalkFunctor X x).obj
        (SheafOfModules.changeOfRings.{u, u, u} α
          (TopCat.Sheaf.inverseImageModule f Y.sheaf M)) :=
  Classical.choose (Classical.choose_spec
      (exists_ringed_inverseImage_stalk_scalar_transport X Y f α x)) M ≪≫
    Classical.choose (SheafOfModules.stalkChangeOfRingsIso X.carrier
      (TopCat.Sheaf.inverseImageRing f Y.sheaf) X.sheaf α x)
      (TopCat.Sheaf.inverseImageModule f Y.sheaf M)

/-- `tensorPullbackStalkIso` is natural in the module. -/
theorem tensorPullbackStalkIso_hom_naturality (M N : RingedSpace.Modules Y) (a : M ⟶ N) :
    (ModuleCat.extendScalars (tensorPullbackStalkRingHom X Y f α x)).map
        ((RingedSpace.moduleStalkFunctor Y (f x)).map a) ≫
        (tensorPullbackStalkIso X Y f α x N).hom =
      (tensorPullbackStalkIso X Y f α x M).hom ≫ (RingedSpace.moduleStalkFunctor X x).map
        (SheafOfModules.changeOfRingsHom.{u, u, u} α
          (TopCat.Sheaf.inverseImageModule f Y.sheaf M)
          (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a)) := by
  have h := exists_ringed_inverseImage_stalk_scalar_transport X Y f α x
  have h' := SheafOfModules.stalkChangeOfRingsIso X.carrier
    (TopCat.Sheaf.inverseImageRing f Y.sheaf) X.sheaf α x
  let ρ := tensorPullbackStalkRingHom X Y f α x
  let c := Classical.choose h
  let β := Classical.choose (Classical.choose_spec h)
  let τ := Classical.choose h'
  have hβ := (Classical.choose_spec (Classical.choose_spec h)).1
  have hc := (Classical.choose_spec (Classical.choose_spec h)).2
  have hτ := (Classical.choose_spec h').2
  change (ModuleCat.extendScalars ρ).map
      ((RingedSpace.moduleStalkFunctor Y (f x)).map a) ≫ (β N ≪≫ τ _).hom =
    (β M ≪≫ τ _).hom ≫ _
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (τ _).hom ((β N).hom
    ((ModuleCat.extendScalars ρ).map
      ((RingedSpace.moduleStalkFunctor Y (f x)).map a)
      (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
        (1 : X.presheaf.stalk x) m))) = _
  rw [ModuleCat.ExtendScalars.map_tmul, hβ, hc]
  change (τ _).hom _ = (RingedSpace.moduleStalkFunctor X x).map _
    ((τ _).hom ((β M).hom (@TensorProduct.tmul _ _ _ _ _ _ (Module.compHom _ ρ) _
        (1 : X.presheaf.stalk x) m)))
  rw [hβ]
  exact (hτ _ _ (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a) 1 (c M m)).symm

end AlgebraicGeometry.RingedSpace

namespace CochainComplex

variable (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
  (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf)
  (K : CochainComplex (RingedSpace.Modules Y) ℤ)
  (P : CochainComplex (RingedSpace.Modules X) ℤ)
  (e : ∀ i : ℤ, P.X i ≅
    SheafOfModules.changeOfRings.{u, u, u} α
      (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i)))
  (he : ∀ i j : ℤ, P.d i j ≫ (e j).hom =
    (e i).hom ≫ SheafOfModules.changeOfRingsHom.{u, u, u} α
      (TopCat.Sheaf.inverseImageModule f Y.sheaf (K.X i))
      (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf (K.X i) (K.d i j)))
  (x : X)

/-- A complex `P` with the termwise tensor pullback formula `e` has the expected stalk complex:
the stalk of `P` at `x` is the extension of scalars of the stalk of `K` at `f x` along the
canonical ring map `RingedSpace.tensorPullbackStalkRingHom`.
Source: Stacks Project, Sheaves, Tag 0098; Cohomology, Tag 06YC, stalk comparison.
(blueprint: lem-pc-tensor-pullback-stalk-complex)

Proof: at `x`, the natural inverse-image stalk isomorphisms identify the source
ring and module stalks with those at `f x`. Their formulas on adjunction-unit germs,
and semilinearity of that unit, show that the module comparison respects the ring
comparison. Compose the inverse ring-stalk isomorphism with the stalk of `α` to get
`ρ`. Change of rings commutes with stalks: apply `stalkChangeOfRingsIso` termwise,
then the preceding inverse-image module comparison. These linear isomorphisms give
extension of scalars of the original stalk terms. Naturality on module morphisms
identifies the differentials with extension of the stalk differentials. Finally
compose with the stalks of `e`; the assumed differential square gives a chain
isomorphism to the stalk of `P`. This argument imposes no boundedness or flatness
assumption; if `X` is empty there is no `x`, and zero stalk rings cause no exception. -/
def tensorPullbackStalkComplexIso :
    ((ModuleCat.extendScalars
        (RingedSpace.tensorPullbackStalkRingHom X Y f α x)).mapHomologicalComplex (.up ℤ)).obj
      (((RingedSpace.moduleStalkFunctor Y (f x)).mapHomologicalComplex (.up ℤ)).obj K) ≅
    ((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)).obj P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ RingedSpace.tensorPullbackStalkIso X Y f α x (K.X i) ≪≫
      ((RingedSpace.moduleStalkFunctor X x).mapIso (e i)).symm) (by
    intro i j _
    change ((RingedSpace.tensorPullbackStalkIso X Y f α x (K.X i)).hom ≫
        (RingedSpace.moduleStalkFunctor X x).map (e i).inv) ≫
        (RingedSpace.moduleStalkFunctor X x).map (P.d i j) =
      (ModuleCat.extendScalars (RingedSpace.tensorPullbackStalkRingHom X Y f α x)).map
        ((RingedSpace.moduleStalkFunctor Y (f x)).map (K.d i j)) ≫
        ((RingedSpace.tensorPullbackStalkIso X Y f α x (K.X j)).hom ≫
          (RingedSpace.moduleStalkFunctor X x).map (e j).inv)
    apply (cancel_mono ((RingedSpace.moduleStalkFunctor X x).map (e j).hom)).1
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
    rw [he i j]
    simp only [← Category.assoc]
    simp only [Iso.inv_hom_id, Category.id_comp]
    rw [(RingedSpace.moduleStalkFunctor X x).map_id, Category.comp_id]
    exact (RingedSpace.tensorPullbackStalkIso_hom_naturality X Y f α x
      (K.X i) (K.X j) (K.d i j)).symm)

/-- In degree `i`, `tensorPullbackStalkComplexIso` is the stalk tensor-pullback isomorphism of
`K.X i` followed by the stalk of `(e i).inv`. -/
@[simp]
theorem tensorPullbackStalkComplexIso_hom_f (i : ℤ) :
    (tensorPullbackStalkComplexIso X Y f α K P e he x).hom.f i =
      (RingedSpace.tensorPullbackStalkIso X Y f α x (K.X i)).hom ≫
        (RingedSpace.moduleStalkFunctor X x).map (e i).inv :=
  rfl

end CochainComplex

end
