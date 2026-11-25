/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.Topology.Algebra.Module.FiniteDimension
import WeilConjectures.CategoryTheory.Sites.MonObj
public import Mathlib.Combinatorics.Quiver.ReflQuiver

/-!
# Coordinates of a finite subfield basis on condensed modules

Source: blueprint main-20261015, chap-The-pro-etale-site,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, first two sentences
(blueprint: lem-sfb-condensed-subfield-basis).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Profinite

private noncomputable def continuousAddHom
    {A B : Type} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+ B) (hf : Continuous f) :
    continuousMapRingObj.{u} A ⟶ continuousMapRingObj B :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
      { toFun s := ULift.up (⟨fun x ↦ f (s.down x), hf.comp s.down.continuous⟩ : C(S.unop, B))
        map_zero' := by apply ULift.ext; ext x; exact f.map_zero
        map_add' s t := by apply ULift.ext; ext x; exact f.map_add _ _ }
     naturality := fun _ _ _ ↦ rfl }⟩

private noncomputable abbrev abelianize :
    Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1} ⥤
      Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  sheafCompose _ (forget₂ RingCat Ab)

open MonoidalCategory MonObj Functor.LaxMonoidal in
private lemma sectionwise_linear
    (R S T : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    (φ : R ⟶ S) (ψ : R ⟶ T) (f : abelianize.obj S ⟶ abelianize.obj T)
    (hf : (Functor.whiskerRight φ.hom (forget₂ RingCat Ab) ▷
        (S.obj ⋙ forget₂ RingCat Ab)) ≫ μ[S.obj ⋙ forget₂ RingCat Ab] ≫ f.hom =
      (R.obj ⋙ forget₂ RingCat Ab) ◁ f.hom ≫
        (Functor.whiskerRight ψ.hom (forget₂ RingCat Ab) ▷
          (T.obj ⋙ forget₂ RingCat Ab)) ≫ μ[T.obj ⋙ forget₂ RingCat Ab]) :
    (abelianize.map φ ▷ abelianize.obj S) ≫ μ[abelianize.obj S] ≫ f =
      abelianize.obj R ◁ f ≫
        (abelianize.map ψ ▷ abelianize.obj T) ≫ μ[abelianize.obj T] := by
  let : MonObj (abelianize.obj S).obj := S.obj.monObjCompForget₂
  let : MonObj (abelianize.obj T).obj := T.obj.monObjCompForget₂
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← μ_natural_left_assoc,
    reassoc_of% (Sheaf.μ_comp_map_mul (abelianize.obj S)),
    ← μ_natural_right_assoc, ← μ_natural_left_assoc, Sheaf.μ_comp_map_mul]
  exact hf

private noncomputable abbrev coefficientMap
    {A B : Type} [Ring A] [Ring B] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing A] [IsTopologicalRing B] (φ : A →+* B) (hφ : Continuous φ) :=
  abelianize.{u}.map (continuousMapRingSheafMap φ hφ)

private lemma coefficientMap_self
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (h : Continuous (algebraMap A A)) :
    coefficientMap.{u} (algebraMap A A) h = 𝟙 _ := rfl

open MonoidalCategory MonObj Functor.LaxMonoidal in
private lemma continuousLinearAction
    (K A B : Type) [CommRing K] [Ring A] [Ring B]
    [TopologicalSpace K] [TopologicalSpace A] [TopologicalSpace B]
    [IsTopologicalRing K] [IsTopologicalRing A] [IsTopologicalRing B]
    [Algebra K A] [Algebra K B]
    (hA : Continuous (algebraMap K A)) (hB : Continuous (algebraMap K B))
    (f : A →ₗ[K] B) (hf : Continuous f) :
    (coefficientMap (algebraMap K A) hA ▷ continuousMapRingObj.{u} A) ≫ μ ≫
        continuousAddHom f.toAddMonoidHom hf =
      continuousMapRingObj K ◁ continuousAddHom f.toAddMonoidHom hf ≫
        (coefficientMap (algebraMap K B) hB ▷ continuousMapRingObj B) ≫ μ := by
  apply sectionwise_linear (continuousMapRingSheaf K) (continuousMapRingSheaf A)
    (continuousMapRingSheaf B)
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a x
  apply ULift.ext
  ext s
  change f (algebraMap K A (a.down s) * x.down s) =
    algebraMap K B (a.down s) * f (x.down s)
  simpa only [Algebra.smul_def] using f.map_smul (a.down s) (x.down s)

private lemma module_sum_app
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) R}
    {I : Type*} (s : Finset I) (f : I → (M ⟶ N))
    (S : Profinite.{u}ᵒᵖ) (a : M.X.obj.obj S) :
    (∑ i ∈ s, f i).hom.hom.app S a = ∑ i ∈ s, (f i).hom.hom.app S a :=
  map_sum
    ({ toFun := fun f ↦ f.hom.hom.app S a
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : (M ⟶ N) →+ N.X.obj.obj S) f s

private lemma sum_down_apply
    {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    {S : Profinite.{u}} {I : Type*} (s : Finset I)
    (f : I → ULift.{u + 1} C(S, A)) (x : S) :
    (∑ i ∈ s, f i).down x = ∑ i ∈ s, (f i).down x :=
  map_sum
    ({ toFun := fun f ↦ f.down x
       map_zero' := rfl
       map_add' := fun _ _ ↦ rfl } : ULift.{u + 1} C(S, A) →+ A) f s

end Profinite
