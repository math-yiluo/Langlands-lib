/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over

/-! # Sliced ringed morphism with a specified underlying comparison

This is the geometric-data part of ordinary ringed pullback localization.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory

namespace CategoryTheory

private theorem binary_conjugate
    {E E' : Type*} [Category E] [Category E'] [CartesianMonoidalCategory E']
    {F G : E ⥤ E'} (α : F ≅ G)
    {X₁ X₂ X₃ X₁₂ : E} (p₁ : X₁₂ ⟶ X₁) (p₂ : X₁₂ ⟶ X₂)
    (a : X₁₂ ⟶ X₃) {Y₁ Y₂ Y₃ : E'}
    (r₁ : F.obj X₁ ⟶ Y₁) (r₂ : F.obj X₂ ⟶ Y₂) (r₃ : F.obj X₃ ⟶ Y₃)
    (b : Y₁ ⊗ Y₂ ⟶ Y₃)
    (h : F.map a ≫ r₃ = CartesianMonoidalCategory.lift
      (F.map p₁ ≫ r₁) (F.map p₂ ≫ r₂) ≫ b) :
    G.map a ≫ α.inv.app X₃ ≫ r₃ = CartesianMonoidalCategory.lift
      (G.map p₁ ≫ α.inv.app X₁ ≫ r₁)
      (G.map p₂ ≫ α.inv.app X₂ ≫ r₂) ≫ b := by
  rw [α.inv.naturality_assoc, h, CartesianMonoidalCategory.comp_lift_assoc]
  rw [← α.inv.naturality_assoc, ← α.inv.naturality_assoc]

private abbrev ringSets {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) := (sheafCompose J (forget RingCat)).obj R

private abbrev ringSections {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ) :
    Ring ((ringSets R).obj.obj U) := inferInstanceAs (Ring (R.obj.obj U))
attribute [local instance] ringSections

private def ringBinary {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (op : ∀ U : Cᵒᵖ, R.obj.obj U → R.obj.obj U → R.obj.obj U)
    (hn : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) x y,
      R.obj.map f (op U x y) = op V (R.obj.map f x) (R.obj.map f y)) :
    ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ⟨{ app := fun U ↦ TypeCat.ofHom (fun x ↦ op U x.1 x.2)
     naturality := by intro U V f; ext x; exact (hn f x.1 x.2).symm }⟩

private def ringAdd {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x + y) (fun f x y ↦ (R.obj.map f).hom.map_add x y)

private def ringMul {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : ringSets R ⊗ ringSets R ⟶ ringSets R :=
  ringBinary R (fun _ x y ↦ x * y) (fun f x y ↦ (R.obj.map f).hom.map_mul x y)

private theorem ringAdd_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Add.add (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringAdd R := by
  ext U t
  exact h U t

private theorem ringMul_eq {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {T : Sheaf J (Type u)}
    (x y z : T ⟶ ringSets R) (h : ∀ U t,
      z.hom.app U t = @Mul.mul (R.obj.obj U) inferInstance (x.hom.app U t) (y.hom.app U t)) :
    z = CartesianMonoidalCategory.lift x y ≫ ringMul R := by
  ext U t
  exact h U t
private def ringZero {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.zero _

private def ringOne {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : 𝟙_ (Sheaf J (Type u)) ⟶ ringSets R :=
  RingedToposMorphism.RingData.one _

private theorem ringData_add {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringAdd S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringAdd R := by
  ext U t
  exact e.ring_add _ _ _ _ (fun _ _ ↦ rfl) U t

private theorem ringData_mul {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (e : RingedToposMorphism.RingData R S) :
    e.inverse.map (ringMul S) ≫ e.ringMap = CartesianMonoidalCategory.lift
      (e.inverse.map (CartesianMonoidalCategory.fst _ _) ≫ e.ringMap)
      (e.inverse.map (CartesianMonoidalCategory.snd _ _) ≫ e.ringMap) ≫ ringMul R := by
  ext U t
  exact e.ring_mul _ _ _ _ (fun _ _ ↦ rfl) U t

set_option backward.isDefEq.respectTransparency false in
private noncomputable def pullbackSliceRingData {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J CommRingCat.{u}} {S : Sheaf K CommRingCat.{u}}
    (e : RingedToposMorphism (localCoefficientRings R) (localCoefficientRings S))
    (A : Sheaf K (Type u))
    (F : Sheaf (elementTopology A) (Type u) ⥤
      Sheaf (elementTopology (e.inverse.obj A)) (Type u))
    (G : Sheaf (elementTopology (e.inverse.obj A)) (Type u) ⥤
      Sheaf (elementTopology A) (Type u))
    (adj : F ⊣ G)
    (hF : PreservesFiniteLimits F)
    (q : e.inverse ⋙ elementSheafPullback (e.inverse.obj A) ≅
      elementSheafPullback A ⋙ F) :
    RingedToposMorphism.RingData
      (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))
      (localCoefficientRings (presentationElementRing S A)) where
  inverse := F
  direct := G
  adj := adj
  leftExact := hF
  ringMap := q.inv.app (ringSets (localCoefficientRings S)) ≫
    (elementSheafPullback (e.inverse.obj A)).map e.ringMap
  ring_zero := by
    intro T z hz U t
    have he : e.inverse.map (ringZero (localCoefficientRings S)) ≫ e.ringMap =
        RingedToposMorphism.RingData.zero _ := by
      ext V x
      exact e.ring_zero _ _ (fun _ _ ↦ rfl) V x
    have hz' : z = CartesianMonoidalCategory.toUnit T ≫
        (elementSheafPullback A).map (ringZero (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringZero (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (elementSheafPullback (e.inverse.obj A)).map e.ringMap) hn
    change F.map ((elementSheafPullback A).map
        (ringZero (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (elementSheafPullback (e.inverse.obj A)).map (e.inverse.map _ ) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ F.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_one := by
    intro T z hz U t
    have he : e.inverse.map (ringOne (localCoefficientRings S)) ≫ e.ringMap =
        RingedToposMorphism.RingData.one _ := by
      ext V x
      exact e.ring_one _ _ (fun _ _ ↦ rfl) V x
    have hz' : z = CartesianMonoidalCategory.toUnit T ≫
        (elementSheafPullback A).map (ringOne (localCoefficientRings S)) := by
      ext V x
      exact hz V x
    have hn := q.inv.naturality (ringOne (localCoefficientRings S))
    have hn' := congrArg (fun f ↦ f ≫
      (elementSheafPullback (e.inverse.obj A)).map e.ringMap) hn
    change F.map ((elementSheafPullback A).map
        (ringOne (localCoefficientRings S))) ≫ q.inv.app _ ≫ _ = _ at hn'
    change _ = q.inv.app _ ≫
      (elementSheafPullback (e.inverse.obj A)).map (e.inverse.map _ ) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap at hn'
    rw [← Functor.map_comp, he] at hn'
    have hz'' := congrArg (fun f ↦ F.map f ≫
      (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap)) hz'
    simp only [Functor.map_comp, Category.assoc] at hz''
    rw [hn'] at hz''
    exact (congrArg (fun f ↦ f.hom.app U t) hz'').trans (by rfl)
  ring_add := by
    intro T x y z hz U t
    change T ⟶ (elementSheafPullback A).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (elementSheafPullback (e.inverse.obj A)).map (ringData_add e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringAdd (localCoefficientRings S))
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      (ringAdd (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))) h
    have hz' := ringAdd_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : F.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (F.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap)
          (F.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ≫
          ringAdd (localCoefficientRings (presentationElementRing R (e.inverse.obj A))) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change F.map (CartesianMonoidalCategory.lift x y) ≫
        ((elementSheafPullback A ⋙ F).map (ringAdd (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← F.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''
  ring_mul := by
    intro T x y z hz U t
    change T ⟶ (elementSheafPullback A).obj (ringSets (localCoefficientRings S)) at x y z
    have h := congrArg (elementSheafPullback (e.inverse.obj A)).map (ringData_mul e.ringData)
    simp only [Functor.map_comp] at h
    have h' := binary_conjugate q
      (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _)
      (ringMul (localCoefficientRings S))
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      ((elementSheafPullback (e.inverse.obj A)).map e.ringMap)
      (ringMul (localCoefficientRings (presentationElementRing R (e.inverse.obj A)))) h
    have hz' := ringMul_eq
      (localCoefficientRings (presentationElementRing S A)) x y z hz
    have h'' : F.map z ≫ (q.inv.app (ringSets (localCoefficientRings S)) ≫
        (elementSheafPullback (e.inverse.obj A)).map e.ringMap) =
        CartesianMonoidalCategory.lift
          (F.map x ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap)
          (F.map y ≫ q.inv.app (ringSets (localCoefficientRings S)) ≫
            (elementSheafPullback (e.inverse.obj A)).map e.ringMap) ≫
          ringMul (localCoefficientRings (presentationElementRing R (e.inverse.obj A))) := by
      rw [hz', Functor.map_comp, Category.assoc]
      change F.map (CartesianMonoidalCategory.lift x y) ≫
        ((elementSheafPullback A ⋙ F).map (ringMul (localCoefficientRings S)) ≫
          q.inv.app (ringSets (localCoefficientRings S)) ≫ _) = _
      rw [h', CartesianMonoidalCategory.comp_lift_assoc]
      have hf : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.fst (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = x := by ext V v; rfl
      have hs : CartesianMonoidalCategory.lift x y ≫ (elementSheafPullback A).map
          (CartesianMonoidalCategory.snd (ringSets (localCoefficientRings S))
            (ringSets (localCoefficientRings S))) = y := by ext V v; rfl
      simp only [Functor.comp_map, ← Category.assoc, ← F.map_comp, hf, hs]
    exact congrArg (fun f ↦ f.hom.app U t) h''

/-- Construct the sliced ringed morphism with its prescribed comparison.

Source: Stacks Project, Sites, Tag 04H1; Modules on Sites, Tag 04IF
(blueprint: lem-weil-pbc-geometric-ringed-pullback-slice-data).

Proof: Apply `Over.postAdjunctionLeft` to `f.adj` at A, then compose its adjunction
with the two fibre equivalences to obtain an adjunction whose left adjoint is
`L = y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙ x.fibreEquivalence.inverse`.
Equivalences preserve finite limits, and `Over.post f.inverse` preserves them
because `f.inverse` does. Define the structural map to be `q.hom.app RY` followed
by the restriction of `f.ringMap`. Naturality of q at the zero, one, addition and
multiplication maps proves preservation of the corresponding ring operations.
For binary operations, use the universal product of the operand sheaves as the
test object. The projections identify the two components of the product comparison;
for constants, uniqueness of the map to the terminal object identifies its comparison.
Thus these equations hold for arbitrary generalized sections, including all section
objects of the element site, and give `RingedToposMorphism.RingData`.
Lift this geometric ring data to modules by transporting addition, zero and scalar
multiplication through inverse image and its finite-product comparisons. The resulting
module direct image is right adjoint by the ringed geometric module construction.
This supplies every module field of `RingedToposMorphism`, without making a choice of
an unconstrained underlying sheaf. Its inverse is L, so take `slice = Iso.refl L`
and `a = q`; the first conclusion is the unit law for whiskering and composition,
and the structural-map equation follows directly from its definition. -/
theorem geometric_ringed_pullback_slice_data
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u))
    (y : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A)
    (x : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A))
    (q : elementSheafPullback A ⋙
        (y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙ x.fibreEquivalence.inverse) ≅
      f.inverse ⋙ elementSheafPullback (f.inverse.obj A)) :
    ∃ (fA : RingedToposMorphism
        (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
        (localCoefficientRings (presentationElementRing RY A)))
      (slice : fA.inverse ≅ y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙
        x.fibreEquivalence.inverse)
      (a : elementSheafPullback A ⋙ fA.inverse ≅
        f.inverse ⋙ elementSheafPullback (f.inverse.obj A)),
      a = Functor.isoWhiskerLeft (elementSheafPullback A) slice ≪≫ q ∧
      fA.ringMap = a.hom.app
          ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj
            (localCoefficientRings RY)) ≫
        (elementSheafPullback (f.inverse.obj A)).map f.ringMap := by
  let F := y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙
    x.fibreEquivalence.inverse
  let G := x.fibreEquivalence.symm.inverse ⋙ Over.post f.direct ⋙
    Over.pullback (f.adj.unit.app A) ⋙ y.fibreEquivalence.inverse
  let adjPost := Over.postAdjunctionLeft (X := A) f.adj
  let adj := y.fibreEquivalence.toAdjunction.comp
    (adjPost.comp x.fibreEquivalence.symm.toAdjunction)
  letI : PreservesFiniteLimits f.inverse := f.leftExact
  letI : PreservesFiniteLimits (Over.post (X := A) f.inverse) := inferInstance
  letI : PreservesFiniteLimits y.fibreEquivalence.functor := inferInstance
  letI : PreservesFiniteLimits x.fibreEquivalence.inverse := inferInstance
  have hF : PreservesFiniteLimits F := by
    dsimp only [F]
    infer_instance
  let d := pullbackSliceRingData f A F G adj hF q.symm
  let fA := d.withModules (Classical.choice
    (SheafOfModules.ringData_inducedModules _ _ d))
  let slice : fA.inverse ≅ F := Iso.refl _
  let a := Functor.isoWhiskerLeft (elementSheafPullback A) slice ≪≫ q
  refine ⟨fA, slice, a, rfl, ?_⟩
  change d.ringMap = a.hom.app _ ≫
    (elementSheafPullback (f.inverse.obj A)).map f.ringMap
  simp only [a, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Iso.refl_hom,
    Functor.map_id, Category.id_comp]
  rfl

end CategoryTheory
