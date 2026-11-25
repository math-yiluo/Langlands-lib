/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareModuleTensorCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorTotalComponent

/-! # The hom-oriented ordinary total tensor square

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory MonoidalCategory

namespace SheafOfModules

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

private theorem inverse_square {A : Type*} [Category A] {V W X Z : A}
    (a : V ≅ W) (b : X ≅ Z) (p : V ⟶ X) (q : W ⟶ Z)
    (hp : p ≫ b.hom = a.hom ≫ q) : a.inv ≫ p = q ≫ b.inv := by
  calc
    a.inv ≫ p = a.inv ≫ (p ≫ b.hom) ≫ b.inv := by simp
    _ = a.inv ≫ (a.hom ≫ q) ≫ b.inv := by rw [hp]
    _ = q ≫ b.inv := by simp

private theorem inverse_module_square
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (M N : SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) :
    (k.ordinaryTensor.mu (g.pullback.obj M) (g.pullback.obj N)).inv ≫
      k.pullback.map (g.ordinaryTensor.mu M N).inv ≫
      s.modules.hom.app ((monoidalCategory Y.ring).tensorObj M N) =
    (monoidalCategory X'.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N) ≫
      (h.ordinaryTensor.mu (f.pullback.obj M) (f.pullback.obj N)).inv ≫
      h.pullback.map (f.ordinaryTensor.mu M N).inv := by
  let a := k.pullback.mapIso (g.ordinaryTensor.mu M N) ≪≫
    k.ordinaryTensor.mu (g.pullback.obj M) (g.pullback.obj N)
  let b := h.pullback.mapIso (f.ordinaryTensor.mu M N) ≪≫
    h.ordinaryTensor.mu (f.pullback.obj M) (f.pullback.obj N)
  have hh := inverse_square a b
    (s.modules.hom.app ((monoidalCategory Y.ring).tensorObj M N))
    ((monoidalCategory X'.ring).tensorHom (s.modules.hom.app M) (s.modules.hom.app N))
    (by simpa only [a, b, Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
      ringedSquareModuleTensorCompatibility s M N)
  simpa only [a, b, Iso.trans_inv, Functor.mapIso_inv, Category.assoc] using hh

private theorem total_map_eq {A : Type*} [Category A] [CategoryTheory.Abelian A]
    [MonoidalCategory A] [MonoidalPreadditive A] [CategoryTheory.Limits.HasCoproducts.{0} A]
    {P P' Q Q' : CochainComplex A ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (Functor.uncurry.obj ((MonoidalCategory.curriedTensor A).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))).map (CategoryTheory.Prod.mkHom a b) =
      HomologicalComplex.mapBifunctorMap a b (MonoidalCategory.curriedTensor A) (.up ℤ) := by
  simp [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.mapBifunctorMap, ← HomologicalComplex₂.total.map_comp]

-- Keep the four comparison endpoints explicit through the degreewise calculation.
/-- The hom-oriented total tensor square commutes.

Proof: test degreewise on every total-complex coproduct summand. The component
formula reduces both paths to the inverse ordinary module tensor square followed
by the pullback of the same inclusion. Naturality of the specified module square
moves it past the inclusion. The inverse module square follows by conjugating the
ordinary module tensor identity by the two canonical tensor isomorphisms.
Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0E48.
(blueprint: lem-weil-pbc-ringed-square-ordinary-tensor-hom-compatibility). -/
theorem ringedSquareOrdinaryTensorHomCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ) :
  let F := f.pullback.mapHomologicalComplex (.up ℤ)
  let G := g.pullback.mapHomologicalComplex (.up ℤ)
  let H := h.pullback.mapHomologicalComplex (.up ℤ)
  let K := k.pullback.mapHomologicalComplex (.up ℤ)
  let γ := (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom
  let ef := f.ordinaryTensor.totalIso Y.ring X.ring f.inverseRing
    f.inverse f.algebraic f.ringMap f.pullback f.object_eq
    f.pushforward f.moduleAdjunction P Q
  let eg := g.ordinaryTensor.totalIso Y.ring Y'.ring g.inverseRing
    g.inverse g.algebraic g.ringMap g.pullback g.object_eq
    g.pushforward g.moduleAdjunction P Q
  let eh := h.ordinaryTensor.totalIso X.ring X'.ring h.inverseRing
    h.inverse h.algebraic h.ringMap h.pullback h.object_eq
    h.pushforward h.moduleAdjunction (F.obj P) (F.obj Q)
  let ek := k.ordinaryTensor.totalIso Y'.ring X'.ring k.inverseRing
    k.inverse k.algebraic k.ringMap k.pullback k.object_eq
    k.pushforward k.moduleAdjunction (G.obj P) (G.obj Q)
  let TY := Functor.uncurry.obj
    ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) _
      (monoidalCategory Y.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let TZ := Functor.uncurry.obj
    ((@MonoidalCategory.curriedTensor (SheafOfModules.{u}
      ((sheafCompose X'.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj X'.ring)) _
      (monoidalCategory X'.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
  let a : TZ.obj (K.obj (G.obj P), K.obj (G.obj Q)) ≅ K.obj (G.obj (TY.obj (P, Q))) :=
    ek ≪≫ K.mapIso eg
  let b : TZ.obj (H.obj (F.obj P), H.obj (F.obj Q)) ≅ H.obj (F.obj (TY.obj (P, Q))) :=
    eh ≪≫ H.mapIso ef
  TZ.map (CategoryTheory.Prod.mkHom (γ.app P) (γ.app Q)) ≫ b.hom =
      a.hom ≫ γ.app (TY.obj (P, Q)) := by
  intro F G H K γ ef eg eh ek TY TZ a b
  let := monoidalCategory Y.ring
  let := monoidalCategory X.ring
  let := monoidalCategory Y'.ring
  let := monoidalCategory X'.ring
  let := ringedTensorPreadditive Y.ring
  let := ringedTensorPreadditive X.ring
  let := ringedTensorPreadditive Y'.ring
  let := ringedTensorPreadditive X'.ring
  dsimp only [a, b, Iso.trans_hom, Functor.mapIso_hom]
  conv_lhs => arg 1; rw [total_map_eq]
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  simp only [HomologicalComplex.comp_f, Category.assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc]
  change ((γ.app P).f i ▷ _) ≫ (_ ◁ (γ.app Q).f j) ≫
      CochainComplex.ιMapBifunctor (H.obj (F.obj P)) (H.obj (F.obj Q))
        (MonoidalCategory.curriedTensor _) i j n hij ≫ eh.hom.f n ≫ h.pullback.map (ef.hom.f n) =
    CochainComplex.ιMapBifunctor (K.obj (G.obj P)) (K.obj (G.obj Q))
        (MonoidalCategory.curriedTensor _) i j n hij ≫
      ek.hom.f n ≫ k.pullback.map (eg.hom.f n) ≫ (γ.app (TY.obj (P, Q))).f n
  conv_lhs => rw [← MonoidalCategory.tensorHom_def_assoc]
  conv_lhs =>
    arg 2
    rw [reassoc_of% (ringedTensorTotalComponent h (F.obj P) (F.obj Q) i j n hij)]
  conv_rhs =>
    rw [reassoc_of% (ringedTensorTotalComponent k (G.obj P) (G.obj Q) i j n hij)]
  have hf := congrArg (fun a ↦ h.pullback.map a) (ringedTensorTotalComponent f P Q i j n hij)
  have hg := congrArg (fun a ↦ k.pullback.map a) (ringedTensorTotalComponent g P Q i j n hij)
  simp only [Functor.map_comp] at hf hg
  conv_lhs => arg 2; arg 2; rw [hf]
  conv_rhs => arg 2; rw [reassoc_of% hg]
  have hn := s.modules.hom.naturality
    (CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) i j n hij)
  dsimp only [Functor.comp_map] at hn
  change (k.pullback.map (g.pullback.map _) ≫ s.modules.hom.app _) =
    s.modules.hom.app _ ≫ h.pullback.map (f.pullback.map _) at hn
  change _ = (k.ordinaryTensor.mu (g.pullback.obj (P.X i))
    (g.pullback.obj (Q.X j))).inv ≫ k.pullback.map
      (g.ordinaryTensor.mu (P.X i) (Q.X j)).inv ≫
    k.pullback.map (g.pullback.map _) ≫ s.modules.hom.app _
  conv_rhs => arg 2; arg 2; rw [hn]
  have hm := congrArg (fun a ↦ a ≫ h.pullback.map (f.pullback.map
    (CochainComplex.ιMapBifunctor P Q (MonoidalCategory.curriedTensor _) i j n hij)))
    (inverse_module_square s (P.X i) (Q.X j))
  simpa only [Category.assoc, γ, F, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex, Functor.mapHomologicalComplex,
    MonoidalCategory.curriedTensor_obj_obj, Functor.comp_obj] using hm.symm

end SheafOfModules
