/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Sites.Point.Monoidal
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Tensor products and scalar extension at geometric étale stalks

Source: Stacks Project, Tags 007K, 008B, 03EL and 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar).

Scalar extension is expressed by its universal property: a left adjoint to restriction
of scalars. Its adjunction unit sends `m` to `1 ⊗ m`; consequently `a • unit m`
is `a ⊗ m`. This formulation includes noncommutative coefficient rings.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
attribute [local instance] CategoryTheory.Sheaf.braidedCategory

section Tensor

variable {R : Type (u + 1)} [CommRing R]

private theorem stalk_tensorator
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    letI := (sheafificationAdjunction Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ p.sheafFiber F G =
      Functor.LaxMonoidal.μ p.presheafFiber F.obj G.obj ≫
        p.presheafFiber.map (Functor.LaxMonoidal.μ
          (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F G)) := by
  dsimp only
  let p := (pointSmallEtale y).ulift.{u + 1}
  let J := Y.smallEtaleTopology
  let A := ModuleCat.{u + 1} R
  let L := presheafToSheaf J A
  let T := p.sheafFiber (A := A)
  let e := p.presheafToSheafCompSheafFiberIso A
  let adj := sheafificationAdjunction J A
  let := adj.rightAdjointLaxMonoidal
  -- Compare through sheafification, then cancel its monoidal structure maps.
  have ht := NatTrans.IsMonoidal.tensor (τ := e.inv) F.obj G.obj
  dsimp only [Functor.comp_obj] at ht
  have he (H : Sheaf J A) :
      e.inv.app H.obj ≫ T.map (adj.counit.app H) = 𝟙 (T.obj H) := by
    change p.presheafFiber.map (adj.unit.app H.obj) ≫
      p.presheafFiber.map ((sheafToPresheaf J A).map (adj.counit.app H)) = 𝟙 _
    rw [← Functor.map_comp]
    have h := congrArg (fun k ↦ p.presheafFiber.map k) (adj.right_triangle_components H)
    simpa only [sheafToPresheaf, ObjectProperty.ι_obj, CategoryTheory.Functor.map_id,
      Functor.id_obj] using h
  have hm : p.presheafFiber.map (Functor.LaxMonoidal.μ
      (sheafToPresheaf J A) F G) =
      e.inv.app (F.obj ⊗ G.obj) ≫
        T.map (Functor.OplaxMonoidal.δ L F.obj G.obj) ≫
          T.map (adj.counit.app F ⊗ₘ adj.counit.app G) := by
    rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_apply]
    simp only [Functor.map_comp]
    rfl
  rw [hm, ← Category.assoc, ht]
  simp only [Functor.LaxMonoidal.comp_μ, Category.assoc]
  rw [← Functor.map_comp_assoc, Functor.Monoidal.μ_δ,
    CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.LaxMonoidal.μ_natural]
  rw [tensorHom_comp_tensorHom_assoc]
  change Functor.LaxMonoidal.μ T F G =
    ((e.inv.app F.obj ≫ T.map (adj.counit.app F)) ⊗ₘ
      (e.inv.app G.obj ≫ T.map (adj.counit.app G))) ≫ Functor.LaxMonoidal.μ T F G
  rw [he, he]
  exact ((congrArg (fun k ↦ k ≫ Functor.LaxMonoidal.μ T F G)
    (id_tensorHom_id (T.obj F) (T.obj G))).trans (Category.id_comp _)).symm

/-- Source: Stacks 007K, 008B, 03EL, 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 1.
Step 1 uses `definition-torsion-sheaves--3` to identify the tensor
presheaf stalk with the tensor sheaf stalk. Step 2 uses
`definition-torsion-sheaves--3`: represent two germs on a common
refinement and tensor their sections; further refinements prove independence of choices.
The inverse sends a pure tensor section to the tensor of its germs, and the two composites
are identities on generators. Step 3 checks uniqueness on those generators. -/
theorem etale_stalk_tensor_unique
    (F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (let p := (pointSmallEtale y).ulift.{u + 1}
    let T := p.sheafFiber (A := ModuleCat.{u + 1} R)
    letI : T.Monoidal := inferInstanceAs
      ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).Monoidal
    letI := (sheafificationAdjunction Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
    let P := fun f : T.obj F ⊗ T.obj G ⟶ T.obj (F ⊗ G) ↦
      ∀ (U : Y.Etale) (x : p.fiber.obj U),
        (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x G.obj) ≫ f =
          (Functor.LaxMonoidal.μ
            (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F G).app (op U) ≫
            p.toPresheafFiber U x (F ⊗ G).obj
    (∃! f, P f) ∧ P (Functor.LaxMonoidal.μ T F G) ∧
      IsIso (Functor.LaxMonoidal.μ T F G)) := by
  dsimp only
  let p := (pointSmallEtale y).ulift.{u + 1}
  let := (sheafificationAdjunction Y.smallEtaleTopology
    (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
  have hμ (U : Y.Etale) (x : p.fiber.obj U) :
      (p.toPresheafFiber U x F.obj ⊗ₘ p.toPresheafFiber U x G.obj) ≫
        Functor.LaxMonoidal.μ p.sheafFiber F G =
      (Functor.LaxMonoidal.μ
        (sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) F G).app (op U) ≫
          p.toPresheafFiber U x (F ⊗ G).obj := by
    rw [stalk_tensorator y]
    rw [← Category.assoc, p.tensorHom_comp_toPresheafFiber_μ]
    exact p.toPresheafFiber_naturality _ U x
  refine ⟨⟨Functor.LaxMonoidal.μ p.sheafFiber F G, hμ, ?_⟩, hμ, inferInstance⟩
  intro a ha
  apply ((p.isColimitPresheafFiberCocone F.obj).tensor
    (p.isColimitPresheafFiberCocone G.obj)).hom_ext
  intro j
  let U := j.unop.1
  let x := j.unop.2
  exact (ha U x).trans (hμ U x).symm

end Tensor

section Scalar

variable {R S : Type (u + 1)} [Ring R] [Ring S] (f : R →+* S)

/-- Source: Stacks 007K, 008B and 04FM
(blueprint: lem-pod-etale-stalk-tensor-scalar), clause 2, individual-map uniqueness.
Step 4: form balanced maps on sections and pass to the filtered neighborhood colimit
using `definition-torsion-sheaves--3`. A tensor of a germ maps
to the class of its tensor section, independently of the representative. The inverse
maps that section class to its tensor of germs. The composites fix generators.
`definition-torsion-sheaves--3` then identifies the target with the
sheafified stalk. Uniqueness follows on generators, including every `a ⊗ s` by
left `S`-linearity. The two existing comparison isomorphisms define that same map. -/
theorem etale_stalk_scalar_component_unique
    (E : ModuleCat.{u + 1} R ⥤ ModuleCat.{u + 1} S)
    (adj : E ⊣ ModuleCat.restrictScalars f)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    (letI := adj.isLeftAdjoint
    let p := (pointSmallEtale y).ulift.{u + 1}
    let J := Y.smallEtaleTopology
    let B := ModuleCat.{u + 1} S
    let Q := (presheafToSheaf J B).obj (F.obj ⋙ E)
    let c₀ := (p.presheafFiberCompIso E).inv.app F.obj ≫
      (p.presheafToSheafCompSheafFiberIso B).inv.app (F.obj ⋙ E)
    let P := fun c : E.obj (p.sheafFiber.obj F) ⟶ p.sheafFiber.obj Q ↦
      ∀ (U : Y.Etale) (x : p.fiber.obj U),
        p.toPresheafFiber U x F.obj ≫ adj.unit.app (p.sheafFiber.obj F) ≫
          (ModuleCat.restrictScalars f).map c =
        adj.unit.app (F.obj.obj (op U)) ≫
          (ModuleCat.restrictScalars f).map
            ((toSheafify J (F.obj ⋙ E)).app (op U) ≫
              p.toPresheafFiber U x Q.obj)
    (∃! c, P c) ∧ P c₀ ∧ IsIso c₀) := by
  let := adj.isLeftAdjoint
  dsimp only
  let p := (pointSmallEtale y).ulift.{u + 1}
  let J := Y.smallEtaleTopology
  let B := ModuleCat.{u + 1} S
  let Q := (presheafToSheaf J B).obj (F.obj ⋙ E)
  let c₀ := (p.presheafFiberCompIso E).inv.app F.obj ≫
    (p.presheafToSheafCompSheafFiberIso B).inv.app (F.obj ⋙ E)
  have hc (U : Y.Etale) (x : p.fiber.obj U) :
      E.map (p.toPresheafFiber U x F.obj) ≫ c₀ =
        (toSheafify J (F.obj ⋙ E)).app (op U) ≫ p.toPresheafFiber U x Q.obj := by
    dsimp [c₀]
    rw [← p.toPresheafFiber_presheafFiberCompIso_hom_app E U x F.obj]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact p.toPresheafFiber_naturality (toSheafify J (F.obj ⋙ E)) U x
  have hp (U : Y.Etale) (x : p.fiber.obj U) :
      p.toPresheafFiber U x F.obj ≫ adj.unit.app (p.sheafFiber.obj F) ≫
        (ModuleCat.restrictScalars f).map c₀ =
      adj.unit.app (F.obj.obj (op U)) ≫ (ModuleCat.restrictScalars f).map
        ((toSheafify J (F.obj ⋙ E)).app (op U) ≫ p.toPresheafFiber U x Q.obj) := by
    erw [← Category.assoc, ← adj.unit_naturality]
    rw [Category.assoc]
    simpa only [Functor.comp_map, Category.assoc, ← Functor.map_comp] using
      congrArg (fun k ↦ adj.unit.app (F.obj.obj (op U)) ≫
        (ModuleCat.restrictScalars f).map k) (hc U x)
  refine ⟨⟨c₀, hp, ?_⟩, hp, ?_⟩
  · intro c h
    apply (adj.homEquiv _ _).injective
    apply p.presheafFiber_hom_ext
    intro U x
    simpa only [Adjunction.homEquiv_apply, Category.assoc, sheafToPresheaf,
      ObjectProperty.ι_obj] using (h U x).trans (hp U x).symm
  · dsimp [c₀]
    infer_instance

end Scalar

end AlgebraicGeometry.Scheme
