/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Sheafification of locally exact complexes

Let `S : X₁ ⟶ X₂ ⟶ X₃` be a short complex of presheaves of `R`-modules on a site `(C, J)`. If `S`
is *locally exact*, i.e. every section `x` of `X₂` with `g x = 0` is locally in the image of `f`,
then its sheafification is exact (`CategoryTheory.Presheaf.exact_map_presheafToSheaf`). The proof
shows that the unit `H ⟶ a(H)` of the homology presheaf `H` of `S` vanishes, using that a morphism
from a presheaf to a sheaf vanishing on the image of a locally surjective morphism is zero.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [Ring R]

/-- A section of a sheaf of modules which vanishes locally is zero. -/
lemma eq_zero_of_locally_eq_zero (F : Sheaf J (ModuleCat.{w} R)) {W : C}
    (s : F.obj.obj (op W)) (S : Sieve W) (hS : S ∈ J W)
    (h : ∀ ⦃W' : C⦄ (g : W' ⟶ W), S g → (F.obj.map g.op).hom s = 0) : s = 0 := by
  have := F.property.hom_ext ⟨S, hS⟩ (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ s)) 0
    (fun I ↦ by
      ext
      simp [h I.f I.hf])
  simpa using congr(($this).hom 1)

/-- A morphism from a presheaf of modules to a sheaf of modules which vanishes on the image of a
locally surjective morphism is zero. -/
lemma eq_zero_of_comp_eq_zero {X Z : Cᵒᵖ ⥤ ModuleCat.{w} R} {F : Sheaf J (ModuleCat.{w} R)}
    (t : X ⟶ Z) (ψ : Z ⟶ F.obj) (h : t ≫ ψ = 0)
    (ht : ∀ (W : C) (z : Z.obj (op W)), imageSieve t z ∈ J W) : ψ = 0 := by
  ext W z
  simp only [NatTrans.app_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
  refine eq_zero_of_locally_eq_zero F _ _ (ht W.unop z) ?_
  rintro W' g ⟨y, hy⟩
  have h' := congr(($h).app (op W') y)
  calc (F.obj.map g.op).hom ((ψ.app W).hom z)
      _ = (ψ.app (op W')).hom ((Z.map g.op).hom z) := (congr(($(ψ.naturality g.op)).hom z)).symm
      _ = (ψ.app (op W')).hom ((t.app (op W')).hom y) := by rw [← hy]
      _ = 0 := by simpa using h'

variable [HasSheafify J (ModuleCat.{w} R)]

/-- **Sheafification of a locally exact short complex is exact.** If every section `x` of `X₂`
with `g x = 0` lies locally in the image of `f`, the sheafification of `S` is exact. -/
theorem exact_map_presheafToSheaf (S : ShortComplex (Cᵒᵖ ⥤ ModuleCat.{w} R))
    (hS : ∀ (W : C) (x : S.X₂.obj (op W)), (S.g.app (op W)).hom x = 0 → imageSieve S.f x ∈ J W) :
    (S.map (presheafToSheaf J _)).Exact := by
  let hd := S.leftHomologyData
  rw [hd.exact_map_iff, IsZero.iff_id_eq_zero]
  apply ((sheafificationAdjunction J _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_id, Adjunction.homEquiv_apply, Functor.map_zero, comp_zero]
  rw [← cancel_epi hd.π, comp_zero]
  refine eq_zero_of_comp_eq_zero hd.f' _ (by rw [hd.f'_π_assoc, zero_comp]) fun W z ↦ ?_
  have hi : ∀ W', Function.Injective (hd.i.app W').hom := fun W' ↦
    (ModuleCat.mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 inferInstance W')
  refine J.superset_covering ?_ (hS W ((hd.i.app _).hom z) ?_)
  · rintro W' g ⟨y, hy⟩
    refine ⟨y, hi _ ?_⟩
    calc (hd.i.app _).hom ((hd.f'.app _).hom y)
        _ = (S.f.app _).hom y := congr(($(hd.f'_i)).app _ |>.hom y)
        _ = (S.X₂.map g.op).hom ((hd.i.app _).hom z) := hy
        _ = (hd.i.app _).hom ((hd.K.map g.op).hom z) :=
          by simp
  · exact congr(($(hd.wi)).app _ |>.hom z)

/-- The sheafification of a locally surjective morphism of presheaves of modules is an
epimorphism. -/
theorem epi_map_presheafToSheaf {X Y : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : X ⟶ Y)
    (hf : ∀ (W : C) (y : Y.obj (op W)), imageSieve f y ∈ J W) :
    Epi ((presheafToSheaf J _).map f) :=
  (exact_map_presheafToSheaf (ShortComplex.mk f (0 : Y ⟶ Y) comp_zero)
    fun W y _ ↦ hf W y).epi_f (Functor.map_zero _ _ _)

end CategoryTheory.Presheaf
