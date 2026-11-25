/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.RingedTensorEdge.RingedTensorEdgeInducedAdjunction
import WeilConjectures.AlgebraicGeometry.RingedTopoiInverseImagePairing
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Tensor compatibility on ordinary module sheaves

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory
namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

open CategoryTheory.Limits MonoidalCategory
open RingedTensor

attribute [local irreducible] monoidalCategory

private theorem insertion_natural
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    {M N : A.mateModules} (v : M ⟶ N) :
    e.inverse.map ((underlying A.ring).map v) ≫ e.insertion N =
      e.insertion M ≫ (underlying B.ring).map (e.pullback.map v) := by
  obtain ⟨m, am, t, hm, _, _⟩ := e.inducedModuleAdjunction
  apply (e.adjunction.homEquiv _ _).injective
  have hN := hm N (e.pullback.obj N) (𝟙 _)
  change (underlying A.ring).map (am.homEquiv N _ (𝟙 _)) ≫ _ =
    e.adjunction.homEquiv _ _
      (e.insertion N ≫ (underlying B.ring).map (𝟙 _)) at hN
  erw [(underlying B.ring).map_id, Category.comp_id] at hN
  erw [e.adjunction.homEquiv_naturality_left, ← hN, ← hm]
  erw [← Category.assoc, ← Functor.map_comp, ← am.homEquiv_naturality_left]
  simp only [Category.comp_id]

private theorem insertion_pure
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (M N : A.mateModules) (Z : Sheaf A.topology (Type u))
    (x : Z ⟶ (underlying A.ring).obj M) (y : Z ⟶ (underlying A.ring).obj N)
    (z : Z ⟶ (underlying A.ring).obj ((monoidalCategory A.ring).tensorObj M N))
    (hz : ∀ W t, z.hom.app W t = pure A.ring M N W
      (x.hom.app W t) (y.hom.app W t)) :
    e.inverse.map z ≫ e.insertion ((monoidalCategory A.ring).tensorObj M N) ≫
      (underlying B.ring).map (e.ordinaryTensor.mu M N).hom =
    CartesianMonoidalCategory.lift (e.inverse.map x ≫ e.insertion M)
      (e.inverse.map y ≫ e.insertion N) ≫
      pureSheaf B.ring (e.pullback.obj M) (e.pullback.obj N) := by
  ext W t
  exact e.ordinaryTensor.pure M N Z x y z hz W t

private theorem compositeTensor_ext
    (M N : Y.mateModules) (H : X'.mateModules)
    {a b : k.pullback.obj (g.pullback.obj ((monoidalCategory Y.ring).tensorObj M N)) ⟶ H}
    (hab : k.inverse.map (g.inverse.map (pureSheaf Y.ring M N)) ≫
        k.inverse.map (g.insertion ((monoidalCategory Y.ring).tensorObj M N)) ≫
        k.insertion (g.pullback.obj ((monoidalCategory Y.ring).tensorObj M N)) ≫
        (underlying X'.ring).map a =
      k.inverse.map (g.inverse.map (pureSheaf Y.ring M N)) ≫
        k.inverse.map (g.insertion ((monoidalCategory Y.ring).tensorObj M N)) ≫
        k.insertion (g.pullback.obj ((monoidalCategory Y.ring).tensorObj M N)) ≫
        (underlying X'.ring).map b) : a = b := by
  obtain ⟨mg, ag, tg, hg, _, _⟩ := g.inducedModuleAdjunction
  obtain ⟨mk, ak, tk, hk, _, _⟩ := k.inducedModuleAdjunction
  let E := (ak.homEquiv (g.pullback.obj ((monoidalCategory Y.ring).tensorObj M N)) H).trans
    (ag.homEquiv ((monoidalCategory Y.ring).tensorObj M N) (mk.modules.obj H))
  have hE (v : k.pullback.obj (g.pullback.obj
      ((monoidalCategory Y.ring).tensorObj M N)) ⟶ H) :
      (underlying Y.ring).map (E v) ≫
        mg.underlying.hom.app (mk.modules.obj H) ≫
        g.direct.map (mk.underlying.hom.app H) =
      (g.adjunction.comp k.adjunction).homEquiv _ _
        (k.inverse.map (g.insertion ((monoidalCategory Y.ring).tensorObj M N)) ≫
          k.insertion (g.pullback.obj ((monoidalCategory Y.ring).tensorObj M N)) ≫
          (underlying X'.ring).map v) := by
    dsimp only [E, Equiv.trans_apply]
    rw [← Category.assoc, hg, ← g.adjunction.homEquiv_naturality_right]
    rw [Category.assoc, hk, ← k.adjunction.homEquiv_naturality_left]
    rw [Adjunction.comp_homEquiv]
    rfl
  apply E.injective
  apply pure_hom_ext Y.ring M N (mg.modules.obj (mk.modules.obj H))
  have hh := congrArg ((g.adjunction.comp k.adjunction).homEquiv _ _) hab
  change (g.adjunction.comp k.adjunction).homEquiv _ _
      ((g.inverse ⋙ k.inverse).map (pureSheaf Y.ring M N) ≫ _) =
    (g.adjunction.comp k.adjunction).homEquiv _ _
      ((g.inverse ⋙ k.inverse).map (pureSheaf Y.ring M N) ≫ _) at hh
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    ← hE a, ← hE b] at hh
  have he : pureSheaf Y.ring M N ≫ (underlying Y.ring).map (E a) =
      pureSheaf Y.ring M N ≫ (underlying Y.ring).map (E b) := by
    apply (cancel_mono (mg.underlying.hom.app (mk.modules.obj H) ≫
      g.direct.map (mk.underlying.hom.app H))).mp
    simpa only [Category.assoc] using hh
  intro W m n
  exact congrArg (fun t ↦ t.hom.app W (m, n)) he

private theorem composite_pure
    {A B C : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (d : RingedTensorEdge B C)
    (M N : A.mateModules) (Z : Sheaf A.topology (Type u))
    (x : Z ⟶ (underlying A.ring).obj M) (y : Z ⟶ (underlying A.ring).obj N)
    (z : Z ⟶ (underlying A.ring).obj ((monoidalCategory A.ring).tensorObj M N))
    (hz : ∀ W t, z.hom.app W t = pure A.ring M N W
      (x.hom.app W t) (y.hom.app W t)) :
    d.inverse.map (e.inverse.map z) ≫
      d.inverse.map (e.insertion ((monoidalCategory A.ring).tensorObj M N)) ≫
      d.insertion (e.pullback.obj ((monoidalCategory A.ring).tensorObj M N)) ≫
      (underlying C.ring).map (d.pullback.map (e.ordinaryTensor.mu M N).hom) ≫
      (underlying C.ring).map
        (d.ordinaryTensor.mu (e.pullback.obj M) (e.pullback.obj N)).hom =
    CartesianMonoidalCategory.lift
      (d.inverse.map (e.inverse.map x) ≫ d.inverse.map (e.insertion M) ≫
        d.insertion (e.pullback.obj M))
      (d.inverse.map (e.inverse.map y) ≫ d.inverse.map (e.insertion N) ≫
        d.insertion (e.pullback.obj N)) ≫
      pureSheaf C.ring (d.pullback.obj (e.pullback.obj M))
        (d.pullback.obj (e.pullback.obj N)) := by
  have he := insertion_pure e M N Z x y z hz
  have hp := insertion_pure d (e.pullback.obj M) (e.pullback.obj N)
    (e.inverse.obj Z) (e.inverse.map x ≫ e.insertion M)
    (e.inverse.map y ≫ e.insertion N)
    (e.inverse.map z ≫ e.insertion ((monoidalCategory A.ring).tensorObj M N) ≫
      (underlying B.ring).map (e.ordinaryTensor.mu M N).hom)
    (fun W t ↦ congrArg (fun v ↦ v.hom.app W t) he)
  simp only [Functor.map_comp, Category.assoc] at hp
  have hn := insertion_natural d (e.ordinaryTensor.mu M N).hom
  erw [reassoc_of% hn] at hp
  exact hp

private theorem pairing_square {C : Type*} [Category C] [CartesianMonoidalCategory C]
    {P Q A B A₁ A₂ B₁ B₂ D E : C}
    (z : Q ⟶ A) (v : P ⟶ B) (r : Q ⟶ P) (a : A ⟶ B)
    (t : A ⟶ D) (u : B ⟶ E) (d : D ⟶ E)
    (x : Q ⟶ A₁) (y : Q ⟶ A₂) (x' : P ⟶ B₁) (y' : P ⟶ B₂)
    (a₁ : A₁ ⟶ B₁) (a₂ : A₂ ⟶ B₂)
    (p : A₁ ⊗ A₂ ⟶ D) (p' : B₁ ⊗ B₂ ⟶ E)
    (ha : z ≫ a = r ≫ v)
    (ht : z ≫ t = CartesianMonoidalCategory.lift x y ≫ p)
    (hu : v ≫ u = CartesianMonoidalCategory.lift x' y' ≫ p')
    (hx : x ≫ a₁ = r ≫ x') (hy : y ≫ a₂ = r ≫ y')
    (hp : p ≫ d = (a₁ ⊗ₘ a₂) ≫ p') :
    z ≫ a ≫ u = z ≫ t ≫ d := by
  rw [← Category.assoc z a u, ha, Category.assoc, hu,
    ← Category.assoc z t d, ht, Category.assoc, hp,
    ← Category.assoc (CartesianMonoidalCategory.lift x y) (a₁ ⊗ₘ a₂) p',
    CartesianMonoidalCategory.lift_map, hx, hy,
    ← CartesianMonoidalCategory.comp_lift]
  simp only [Category.assoc]

-- The generator calculation compares four scalar-extension presentations.
/-- Tensor compatibility of the linear square on two ordinary module sheaves.

Proof: precompose with the iterated scalar-extension insertion on the inverse
image of a generalized pure tensor m tensor n. The four canonical pure-tensor
formulas identify each path with the tensor of the two iterated insertions.
The insertion equation of s identifies these insertions on m and n. Naturality
of s.sets with respect to the generalized pair of sections identifies the
underlying inverse-image elements, since finite-limit preserving inverse image
preserves their product. Consequently the two composites agree on these inserted
pure tensors. The scalar-extension universal property extends this equality to
scalar multiples, linearity extends it to sums, and the tensor and sheafification
universal properties give equality of module-sheaf morphisms. Structural ring
maps need not be flat; the same calculation works for zero rings and zero modules.
Source: Stacks, Cohomology on Sites, Tag 07A4 (lemma-pullback-tensor-product),
and the tensor part of Tag 0E48 (remark-compatible-with-diagram).
(blueprint: lem-weil-pbc-ringed-square-module-tensor-compatibility). -/
theorem ringedSquareModuleTensorCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (M N : SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) :
    s.modules.hom.app ((monoidalCategory Y.ring).tensorObj M N) ≫
      h.pullback.map (f.ordinaryTensor.mu M N).hom ≫
      (h.ordinaryTensor.mu (f.pullback.obj M) (f.pullback.obj N)).hom =
    k.pullback.map (g.ordinaryTensor.mu M N).hom ≫
      (k.ordinaryTensor.mu (g.pullback.obj M) (g.pullback.obj N)).hom ≫
      (monoidalCategory X'.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N) := by
  let T := (monoidalCategory Y.ring).tensorObj M N
  let P := (underlying Y.ring).obj M ⊗ (underlying Y.ring).obj N
  let x : P ⟶ (underlying Y.ring).obj M := CartesianMonoidalCategory.fst _ _
  let y : P ⟶ (underlying Y.ring).obj N := CartesianMonoidalCategory.snd _ _
  have hf := composite_pure f h M N P x y (pureSheaf Y.ring M N) (by intros; rfl)
  have hg := composite_pure g k M N P x y (pureSheaf Y.ring M N) (by intros; rfl)
  have factor {L : Y.mateModules} (v : P ⟶ (underlying Y.ring).obj L) :
      k.inverse.map (g.inverse.map v) ≫ k.inverse.map (g.insertion L) ≫
        k.insertion (g.pullback.obj L) ≫ (underlying X'.ring).map (s.modules.hom.app L) =
      s.sets.hom.app P ≫ h.inverse.map (f.inverse.map v) ≫
        h.inverse.map (f.insertion L) ≫ h.insertion (f.pullback.obj L) := by
    have hv := s.sets.hom.naturality v
    dsimp only [Functor.comp_map] at hv
    erw [s.insertion L, reassoc_of% hv]
  apply compositeTensor_ext M N
  let U := underlying X'.ring
  have result := pairing_square
    (k.inverse.map (g.inverse.map (pureSheaf Y.ring M N)) ≫
      k.inverse.map (g.insertion T) ≫ k.insertion (g.pullback.obj T))
    (h.inverse.map (f.inverse.map (pureSheaf Y.ring M N)) ≫
      h.inverse.map (f.insertion T) ≫ h.insertion (f.pullback.obj T))
    (s.sets.hom.app P) (U.map (s.modules.hom.app T))
    (U.map (k.pullback.map (g.ordinaryTensor.mu M N).hom) ≫
      U.map (k.ordinaryTensor.mu (g.pullback.obj M) (g.pullback.obj N)).hom)
    (U.map (h.pullback.map (f.ordinaryTensor.mu M N).hom) ≫
      U.map (h.ordinaryTensor.mu (f.pullback.obj M) (f.pullback.obj N)).hom)
    (U.map ((monoidalCategory X'.ring).tensorHom
      (s.modules.hom.app M) (s.modules.hom.app N)))
    (k.inverse.map (g.inverse.map x) ≫ k.inverse.map (g.insertion M) ≫
      k.insertion (g.pullback.obj M))
    (k.inverse.map (g.inverse.map y) ≫ k.inverse.map (g.insertion N) ≫
      k.insertion (g.pullback.obj N))
    (h.inverse.map (f.inverse.map x) ≫ h.inverse.map (f.insertion M) ≫
      h.insertion (f.pullback.obj M))
    (h.inverse.map (f.inverse.map y) ≫ h.inverse.map (f.insertion N) ≫
      h.insertion (f.pullback.obj N))
    (U.map (s.modules.hom.app M)) (U.map (s.modules.hom.app N))
    (pureSheaf X'.ring (k.pullback.obj (g.pullback.obj M))
      (k.pullback.obj (g.pullback.obj N)))
    (pureSheaf X'.ring (h.pullback.obj (f.pullback.obj M))
      (h.pullback.obj (f.pullback.obj N)))
    (by simpa only [Category.assoc] using factor (pureSheaf Y.ring M N))
    (by simpa only [Category.assoc] using hg)
    (by simpa only [Category.assoc] using hf)
    (by simpa only [Category.assoc] using factor x)
    (by simpa only [Category.assoc] using factor y)
    (pureSheaf_natural X'.ring (s.modules.hom.app M) (s.modules.hom.app N)).symm
  simpa only [U, Functor.map_comp, Category.assoc] using result

end SheafOfModules
