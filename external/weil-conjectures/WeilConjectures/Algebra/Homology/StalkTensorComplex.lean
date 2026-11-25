/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import WeilConjectures.Algebra.Homology.StalkTensorComplexDegrees
import WeilConjectures.Algebra.Homology.StalkTensorComplexDifferential
import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalks commute with total tensor complexes

Source: Stacks Project, Cohomology, Lemma 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex).
-/

@[expose] public section

universe u₁

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

-- Assemble the degreewise comparison in abstract categories to keep instance terms small.
private theorem tensorComparison_iso_of_degrees
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [MonoidalCategory C] [MonoidalCategory D]
    [(curriedTensor C).PreservesZeroMorphisms]
    [∀ A, ((curriedTensor C).obj A).PreservesZeroMorphisms]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ A, ((curriedTensor D).obj A).PreservesZeroMorphisms]
    [∀ F K : CochainComplex C ℤ,
      HomologicalComplex.HasMapBifunctor F K (curriedTensor C) (.up ℤ)]
    [∀ F K : CochainComplex D ℤ,
      HomologicalComplex.HasMapBifunctor F K (curriedTensor D) (.up ℤ)]
    (T : C ⥤ D) [T.Additive]
    (φ : ∀ A B : C, T.obj (A ⊗ B) ≅ T.obj A ⊗ T.obj B)
    (hφ : ∀ (A B A' B' : C) (f : A ⟶ A') (g : B ⟶ B'),
      T.map (f ⊗ₘ g) ≫ (φ A' B').hom =
        (φ A B).hom ≫ (T.map f ⊗ₘ T.map g))
    (e : ∀ (F K : CochainComplex C ℤ) (n : ℤ),
      ((T.mapHomologicalComplex (.up ℤ)).obj (mapBifunctor F K (curriedTensor _))).X n ≅
        (mapBifunctor ((T.mapHomologicalComplex (.up ℤ)).obj F)
          ((T.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor _)).X n)
    (he : ∀ (F K : CochainComplex C ℤ)
        (p q n : ℤ) (h : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
      T.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ) p q n h) ≫
        (e F K n).hom = (φ (F.X p) (K.X q)).hom ≫ HomologicalComplex.ιMapBifunctor
          ((T.mapHomologicalComplex (.up ℤ)).obj F)
          ((T.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor _) (.up ℤ) p q n h)
    (hd : ∀ (F K : CochainComplex C ℤ) (n m : ℤ),
      (e F K n).hom ≫ (mapBifunctor ((T.mapHomologicalComplex (.up ℤ)).obj F)
          ((T.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor _)).d n m =
        ((T.mapHomologicalComplex (.up ℤ)).obj
          (mapBifunctor F K (curriedTensor _))).d n m ≫ (e F K m).hom) :
    ∃ e : ∀ (F K : CochainComplex C ℤ),
      (T.mapHomologicalComplex (.up ℤ)).obj (mapBifunctor F K (curriedTensor _)) ≅
        mapBifunctor ((T.mapHomologicalComplex (.up ℤ)).obj F)
          ((T.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor _),
      ∀ (F K F' K' : CochainComplex C ℤ)
        (f : F ⟶ F') (g : K ⟶ K'),
        (T.mapHomologicalComplex (.up ℤ)).map
            (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)) ≫
            (e F' K').hom =
          (e F K).hom ≫ HomologicalComplex.mapBifunctorMap
            ((T.mapHomologicalComplex (.up ℤ)).map f)
            ((T.mapHomologicalComplex (.up ℤ)).map g) (curriedTensor _) (.up ℤ) := by
  have h_ext (F K : CochainComplex C ℤ) (n : ℤ)
      (M : D)
      (a b : ((T.mapHomologicalComplex (.up ℤ)).obj (mapBifunctor F K (curriedTensor _))).X n ⟶ M)
      (h : ∀ p q (hpq : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = n),
        T.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor _) (.up ℤ)
          p q n hpq) ≫ a = T.map (HomologicalComplex.ιMapBifunctor F K
            (curriedTensor _) (.up ℤ) p q n hpq) ≫ b) : a = b := by
    apply (cancel_epi (e F K n).inv).1
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply (cancel_epi (φ (F.X p) (K.X q)).hom).1
    simp only [← Category.assoc]
    rw [← he F K p q n hpq]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h p q hpq
  let E (F K : CochainComplex C ℤ) :=
    HomologicalComplex.Hom.isoOfComponents (e F K) (fun n m _ ↦ hd F K n m)
  refine ⟨E, ?_⟩
  intro F K F' K' f g
  apply HomologicalComplex.Hom.ext
  funext n
  change T.map ((HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)).f n) ≫
      (e F' K' n).hom = (e F K n).hom ≫
        (HomologicalComplex.mapBifunctorMap ((T.mapHomologicalComplex (.up ℤ)).map f)
          ((T.mapHomologicalComplex (.up ℤ)).map g)
          (curriedTensor _) (.up ℤ)).f n
  apply h_ext F K n
  intro p q hpq
  have hi := he F K p q n hpq
  have hi' := he F' K' p q n hpq
  calc
    _ = T.map ((f.f p ⊗ₘ g.f q) ≫ HomologicalComplex.ιMapBifunctor F' K'
        (curriedTensor _) (.up ℤ) p q n hpq) ≫ (e F' K' n).hom := by
      rw [← Functor.map_comp_assoc, HomologicalComplex.ι_mapBifunctorMap]
      simp only [tensorHom_def, Category.assoc]
      rfl
    _ = T.map (f.f p ⊗ₘ g.f q) ≫ (φ (F'.X p) (K'.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((T.mapHomologicalComplex (.up ℤ)).obj F')
          ((T.mapHomologicalComplex (.up ℤ)).obj K')
          (curriedTensor _) (.up ℤ) p q n hpq := by
      rw [Functor.map_comp, Category.assoc, hi']
    _ = (φ (F.X p) (K.X q)).hom ≫ (T.map (f.f p) ⊗ₘ T.map (g.f q)) ≫
        HomologicalComplex.ιMapBifunctor ((T.mapHomologicalComplex (.up ℤ)).obj F')
          ((T.mapHomologicalComplex (.up ℤ)).obj K')
          (curriedTensor _) (.up ℤ) p q n hpq := by
      rw [← Category.assoc, hφ, Category.assoc]
    _ = _ := by
      rw [← Category.assoc _ (e F K n).hom, hi, Category.assoc,
        HomologicalComplex.ι_mapBifunctorMap]
      simp only [tensorHom_def, Category.assoc]
      rfl

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance : MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

private instance stalk_additive : (RingedSpace.moduleStalkFunctor X x).Additive where
  map_add := by
    intro M N f g
    ext m
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f + g).val) m = _
    change (TopCat.Presheaf.stalkFunctor Ab x).map
      ((PresheafOfModules.toPresheaf _).map (f.val + g.val)) m = _
    rw [Functor.map_add, Functor.map_add]
    rfl

/-- (blueprint: lem-pc-stalk-tensor-complex) Stacks Project, Cohomology, Lemma 06YB:
there is an isomorphism from the stalk of the total tensor complex to the total tensor
complex of the stalks, natural in both complexes. Both total complexes use direct sums
in degree `n` over `p + q = n` and differential `d_F ⊗ 1 + (-1)^p 1 ⊗ d_K`.

Proof:
1. By `def-pc-tensor-complex-sheaves`, the degree `n` term is the direct sum of `F^p ⊗ K^q`.
   Apply `lem-pc-stalk-direct-sums` to move the stalk through this direct sum.
2. Apply `lem-pc-ringed-space-module-stalk-tensor` to each summand. Its natural comparison
   identifies the summands with `F_x^p ⊗ K_x^q`, giving the degreewise isomorphisms.
3. Naturality of the module comparison carries the differentials on the two factors to
   their stalk maps. Additivity preserves the sign `(-1)^p`. Thus the maps commute with
   the total differential and form isomorphisms of complexes. The same naturality on each
   summand gives the asserted square for every pair of morphisms of complexes. -/
theorem exists_stalk_tensor_complex_iso :
    ∃ e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ),
      (S).obj (mapBifunctor F K (curriedTensor _)) ≅
        mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _),
      ∀ (F K F' K' : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (f : F ⟶ F') (g : K ⟶ K'),
        (S).map (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)) ≫
            (e F' K').hom =
          (e F K).hom ≫ HomologicalComplex.mapBifunctorMap
            ((S).map f) ((S).map g) (curriedTensor _) (.up ℤ) := by
  refine (SheafOfModules.stalkTensorIso X x).elim fun φ hφ ↦ ?_
  refine (exists_stalk_tensor_degree_iso X x φ).elim fun e he ↦ ?_
  let := stalk_additive X x
  let : ∀ F K : CochainComplex (SheafOfModules.{u₁} O) ℤ,
      HomologicalComplex.HasMapBifunctor F K (curriedTensor _) (.up ℤ) :=
    fun F K ↦ inferInstance
  let : ∀ F K : CochainComplex (ModuleCat.{u₁} (X.presheaf.stalk x)) ℤ,
      HomologicalComplex.HasMapBifunctor F K (curriedTensor _) (.up ℤ) :=
    fun F K ↦ inferInstance
  exact tensorComparison_iso_of_degrees (RingedSpace.moduleStalkFunctor X x) φ hφ.2 e he
    (stalk_tensor_degree_differential X x φ hφ.2 e he)

end CochainComplex
