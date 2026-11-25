/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.Sites.SiteCechFreeComplexExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian

/-!
# The cocycle lifting step for injective module presheaves

Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after Tag 03FB,
using Tags 03AS, 03F5 and 03AT. No topology or covering condition enters this step.
-/

@[expose] public section

universe u v w r s

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {T : Type v} {U : C}
  {f : T → C} {hom : ∀ t, f t ⟶ U}

private noncomputable def cochainToTuple (S : SiteCechComplex f hom)
    (R : Cᵒᵖ ⥤ RingCat.{v}) (M : PresheafOfModules.{v} R) (n : ℕ)
    (b : S.cochains M.presheaf n) :
    S.tuplePresheaf n ⟶ M.presheaf ⋙ forget AddCommGrpCat where
  app X := ↾fun x ↦ M.presheaf.map x.2.op (b x.1)
  naturality X Y g := by
    apply ConcreteCategory.hom_ext
    intro x
    change M.presheaf.map (g.unop ≫ x.2).op (b x.1) =
      M.presheaf.map g (M.presheaf.map x.2.op (b x.1))
    rw [op_comp, M.presheaf.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeCochainEquiv (S : SiteCechComplex f hom)
    (R : Cᵒᵖ ⥤ RingCat.{v}) (M : PresheafOfModules.{v} R) (n : ℕ) :
    ((S.freeComplex R).X n ⟶ M) ≃+ S.cochains M.presheaf n where
  toFun a t := a.app (op (S.W n t)) (ModuleCat.freeMk (⟨t, 𝟙 _⟩))
  invFun b := PresheafOfModules.freeHomEquiv.symm (cochainToTuple S R M n b)
  left_inv a := by
    apply PresheafOfModules.freeHomEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply NatTrans.ext
    funext X
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨t, g⟩ := x
    change M.presheaf.map g.op
      (a.app (op (S.W n t)) (ModuleCat.freeMk ⟨t, 𝟙 _⟩)) =
      a.app X (ModuleCat.freeMk ⟨t, g⟩)
    have h := PresheafOfModules.naturality_apply a g.op
      (ModuleCat.freeMk ⟨t, 𝟙 _⟩)
    dsimp [SiteCechComplex.freeComplex, SiteCechComplex.tupleSimplicial,
      PresheafOfModules.free, PresheafOfModules.freeObj] at h
    simpa [ModuleCat.freeDesc_apply, SiteCechComplex.tuplePresheaf,
      PresheafOfModules.presheaf] using! h.symm
  right_inv b := by
    funext t
    simp only [PresheafOfModules.freeHomEquiv, Equiv.coe_fn_symm_mk,
      PresheafOfModules.freeObjDesc_app]
    erw [ModuleCat.freeDesc_apply]
    change M.presheaf.map (𝟙 (S.W n t)).op (b t) = b t
    simp
  map_add' a b := by
    funext t
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem freeCochainEquiv_boundary (S : SiteCechComplex f hom)
    (R : Cᵒᵖ ⥤ RingCat.{v}) (M : PresheafOfModules.{v} R) (n : ℕ)
    (a : (S.freeComplex R).X n ⟶ M) :
    freeCochainEquiv S R M (n + 1) ((S.freeComplex R).d (n + 1) n ≫ a) =
      S.differentialValue M.presheaf n (freeCochainEquiv S R M n a) := by
  funext t
  simp only [SiteCechComplex.freeComplex,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  change (freeCochainEquiv S R M (n + 1)
    (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
      ((PresheafOfModules.free R).map (S.tupleMap j.succAbove) ≫ a))) t = _
  rw [map_sum]
  simp only [map_zsmul]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    (freeCochainEquiv S R M (n + 1)
      ((PresheafOfModules.free R).map (S.tupleMap j.succAbove) ≫ a)) :
    ∀ t : Fin (n + 2) → T, M.presheaf.obj (op (S.W (n + 1) t))) t = _
  rw [Finset.sum_apply]
  change (∑ j : Fin (n + 2), (-1 : ℤ) ^ j.val •
    a.app (op (S.W (n + 1) t))
      ((ModuleCat.free (R.obj (op (S.W (n + 1) t)))).map
        ((S.tupleMap j.succAbove).app _) (ModuleCat.freeMk ⟨t, 𝟙 _⟩))) = _
  simp only [ModuleCat.free_map_apply]
  dsimp [SiteCechComplex.tupleMap, SiteCechComplex.differentialValue,
    freeCochainEquiv]
  simp only [Category.id_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have h := PresheafOfModules.naturality_apply a (S.indexMap t j.succAbove).op
    (ModuleCat.freeMk ⟨t ∘ j.succAbove, 𝟙 _⟩)
  dsimp [SiteCechComplex.freeComplex, SiteCechComplex.tupleSimplicial,
    PresheafOfModules.free, PresheafOfModules.freeObj] at h
  simpa [ModuleCat.freeDesc_apply, SiteCechComplex.tuplePresheaf,
    PresheafOfModules.presheaf] using! h

/-- Every positive-degree cocycle with values in an injective module presheaf is a
coboundary. Unlike the ringed-site theorem, this concerns presheaf injectivity and
an arbitrary family admitting the specified fibre products, without sheafification.
Homs, rings, module values and family indices share a universe, so the free
representables lie in the category in which injectivity is assumed.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after the application
of Tag 03FB; Tags 03AS, 03F5 and 03AT.
(blueprint: lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift)

Proof: form the chain complex K of coproducts of free representable R-module
presheaves on the chosen products. Its boundary deletes factors with alternating
signs. At each object W, group its basis by the composite W -> U. The universal
property identifies each group with tuples in the set of lifts of that composite.
The empty lift set gives zero; inserting a chosen lift contracts every nonempty
summand in positive degrees. Hence K is exact there (03F5 and 03AT).
Free Yoneda and the coproduct universal property identify maps K_n -> M with
cochains of M.presheaf (03AS). Precomposition by the boundary is exactly
`differentialValue`: Yoneda sends each deletion projection to its restriction map.
A cocycle in degree q+1 is thus a map K_(q+1) -> M killing the incoming boundary.
Exactness factors it through the image of K_(q+1) -> K_q. Injectivity extends
that map along the image inclusion into K_q. The resulting map K_q -> M
corresponds to the desired cochain b, and its precomposition is the original
cocycle. This argument includes q=0, since exactness is used at q+1, not at q. -/
theorem injective_presheaf_module_cech_cocycle_lift
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{v})
    (M : PresheafOfModules.{v} R) [Injective M]
    {T : Type v} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c := by
  let K := S.freeComplex R
  let e := freeCochainEquiv S R M
  have hK : (ShortComplex.mk (K.d (q + 2) (q + 1)) (K.d (q + 1) q)
      (K.d_comp_d _ _ _)).Exact :=
    (HomologicalComplex.exactAt_iff' K (q + 2) (q + 1) q
      (by simp) (by simp)).1 (S.freeComplex_exactAt R q)
  let a : K.X (q + 1) ⟶ M := (e (q + 1)).symm c
  have ha : K.d (q + 2) (q + 1) ≫ a = 0 := by
    apply (e (q + 2)).injective
    rw [map_zero]
    change freeCochainEquiv S R M ((q + 1) + 1)
      ((S.freeComplex R).d ((q + 1) + 1) (q + 1) ≫ a) = 0
    rw [freeCochainEquiv_boundary]
    simpa [a, e] using hc
  refine ⟨e q (hK.descToInjective a ha), ?_⟩
  rw [← freeCochainEquiv_boundary, hK.comp_descToInjective a ha]
  exact (e (q + 1)).apply_symm_apply c

end CategoryTheory
