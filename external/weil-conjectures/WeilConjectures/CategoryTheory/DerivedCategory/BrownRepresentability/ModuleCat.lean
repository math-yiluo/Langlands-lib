/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingleCoyoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Brown representability for the derived category of a ring

Let `R` be a (not necessarily commutative) ring. We show that the shifts of `R[0]` form a family
of compact generators of the unbounded derived category `D(R)` of `R`-modules
(`DerivedCategory.compactGenerators_moduleCat`):

* `D(R)` has coproducts (`DerivedCategory.hasColimitsOfShape_discrete`): they are computed by
  coproducts of cochain complexes (`DerivedCategory.isColimitCofanMkQObj`);
* `R[0]` is compact (`DerivedCategory.isCompactObj_singleFunctor_obj_self`): a morphism
  `R[0] ⟶ X` is an element of `H⁰(X)`, and `H⁰` commutes with coproducts;
* if `Hom(R[0]⟦n⟧, X) = 0` for all `n`, then all the cohomology modules of `X` vanish, so that
  `X = 0`.

Hence Brown representability holds for `D(R)` (Stacks Lemma 13.38.1): every triangulated functor
out of `D(R)` which preserves coproducts is a left adjoint
(`DerivedCategory.isLeftAdjoint_of_preservesCoproducts_moduleCat`). This is the input of the
proof of Stacks Tag 0F5Y, used in the blueprint node
`theorem-existence-exceptional-inverse-image--1`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Opposite Pretriangulated BrownRepresentability

namespace ModuleCat

variable {R : Type*} [Ring R] {C : Type*} [Category* C] {β : Type*} {Y : β → C}

/-- Let `G` be a functor to `R`-modules preserving a coproduct `c` of a family `Y`. Every element
of `G(c.pt)` is a finite sum of images of elements of the `G(Y j)`. -/
lemma exists_finset_eq_sum_map_apply (G : C ⥤ ModuleCat R) {c : Cofan Y} (hc : IsColimit c)
    [PreservesColimit (Discrete.functor Y) G] (x : G.obj c.pt) :
    ∃ (S : Finset β) (m : ∀ j, G.obj (Y j)), x = ∑ j ∈ S, G.map (c.inj j) (m j) := by
  classical
  let N : Submodule R (G.obj c.pt) := ⨆ j, LinearMap.range (G.map (c.inj j)).hom
  have h : ofHom N.mkQ = 0 := (isColimitOfPreserves G hc).hom_ext fun ⟨j⟩ ↦ by
    ext y
    simpa [Cofan.inj] using (Submodule.Quotient.mk_eq_zero N).2
      (Submodule.mem_iSup_of_mem j (LinearMap.mem_range_self _ y))
  have hx : x ∈ N := (Submodule.Quotient.mk_eq_zero N).1 (by simpa using congr(($h).hom x))
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 hx
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 hS
  refine ⟨S, fun j ↦ (μ j).2.choose, ?_⟩
  rw [← hμ]
  exact Finset.sum_congr rfl fun j _ ↦ (μ j).2.choose_spec.symm

end ModuleCat

namespace DerivedCategory

variable {R : Type v} [Ring R] [HasDerivedCategory.{v} (ModuleCat.{v} R)]

/-- The object `R[0]` of the derived category of `R`-modules is compact. -/
lemma isCompactObj_singleFunctor_obj_self :
    IsCompactObj ((singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R R)) := by
  intro J X c hc f
  let E := singleFunctorZeroHomEquiv (ModuleCat.of R R)
  obtain ⟨S, m, hm⟩ := ModuleCat.exists_finset_eq_sum_map_apply
    (homologyFunctor (ModuleCat.{v} R) 0) hc ((E c.pt f).hom (1 : R))
  refine ⟨S, fun j ↦ (E (X j)).symm (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (m j))), ?_⟩
  apply (E c.pt).injective
  have key : ∀ (g : ∀ j, (singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R R) ⟶ X j),
      E c.pt (∑ j ∈ S, g j ≫ c.inj j) =
        ∑ j ∈ S, E (X j) (g j) ≫ (homologyFunctor (ModuleCat.{v} R) 0).map (c.inj j) := by
    intro g
    simp [E, Functor.map_sum, Preadditive.comp_sum]
  rw [key]
  simp only [Equiv.apply_symm_apply]
  ext1
  refine LinearMap.ext_ring ?_
  rw [hm]
  simp [ModuleCat.hom_sum]

/-- The shifts `R[0]⟦n⟧` of `R[0]`, indexed by `ULift ℤ`. -/
noncomputable def shiftedUnit (R : Type v) [Ring R] [HasDerivedCategory.{v} (ModuleCat.{v} R)]
    (n : ULift.{v} ℤ) : DerivedCategory (ModuleCat.{v} R) :=
  ((singleFunctor (ModuleCat.{v} R) 0).obj (ModuleCat.of R R))⟦n.down⟧

/-- An object `X` of `D(R)` with `Hom(R[0]⟦n⟧, X) = 0` for all `n` is zero. -/
lemma isZero_of_forall_shiftedUnit (X : DerivedCategory (ModuleCat.{v} R))
    (hX : ∀ n (f : shiftedUnit R n ⟶ X), f = 0) : IsZero X := by
  refine isZero_of_forall_isZero_homology X fun m ↦ ?_
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun x y ↦ ?_⟩
  have h₀ : ∀ z : (homologyFunctor (ModuleCat.{v} R) m).obj X, z = 0 := by
    intro z
    let e := ((shiftFunctorCompPreadditiveCoyonedaObjSingleFunctorZeroIso
      (ModuleCat.of R R) m).app X)
    let adj : shiftFunctor (DerivedCategory (ModuleCat.{v} R)) (-m) ⊣ shiftFunctor _ m :=
      (shiftEquiv' _ (-m) m (by simp)).toAdjunction
    have h₁ : e.inv (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z)) = 0 := by
      rw [← (adj.homEquiv _ _).apply_symm_apply (e.inv _),
        hX ⟨-m⟩ ((adj.homEquiv _ _).symm _), Adjunction.homEquiv_unit]
      simp
    have h₂ := congr(($(e.inv_hom_id_apply (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ z))))
      |>.hom (1 : R))
    rw [h₁, map_zero] at h₂
    simpa using h₂.symm
  rw [h₀ x, h₀ y]

/-- The shifts of `R[0]` form a family of compact generators of `D(R)`. -/
lemma compactGenerators_moduleCat : CompactGenerators (shiftedUnit R) where
  exists_iso_shift i n :=
    ⟨⟨i.down + n⟩, ⟨(shiftFunctorAdd' _ i.down n _ rfl).app _⟩⟩
  isCompactObj _ := isCompactObj_singleFunctor_obj_self.shift _
  isZero_of_forall_eq_zero := isZero_of_forall_shiftedUnit

/-- **Brown representability for `D(R)`** (Stacks Lemma 13.38.1, input of Stacks Tag 0F5Y):
every triangulated functor out of the derived category of `R`-modules which preserves coproducts
is a left adjoint. -/
theorem isLeftAdjoint_of_preservesCoproducts_moduleCat {T : Type u'} [Category.{v} T]
    [Preadditive T] [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
    [Pretriangulated T] (F : DerivedCategory (ModuleCat.{v} R) ⥤ T) [F.CommShift ℤ]
    [F.IsTriangulated] [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] :
    F.IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_compactGenerators compactGenerators_moduleCat F

end DerivedCategory
