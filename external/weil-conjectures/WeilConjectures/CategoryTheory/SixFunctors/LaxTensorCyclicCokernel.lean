/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Lax tensor comparison on matching cyclic cokernels

Source: Stacks 03EK (balanced tensor products) and 099N(5) (finite reductions).
(blueprint: lem-sfb-lax-tensor-cyclic-cokernel).
-/

@[expose] public section
set_option autoImplicit false
universe a b c d
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory

/-- A lax additive functor's tensor comparison is invertible on a cyclic quotient
when both coefficient units present that quotient by the same scalar on every image.

Source: Stacks 03EK and 099N(5); finite-reduction argument of
`det-lem-int-tensor-pullback.proof.md`.
(blueprint: lem-sfb-lax-tensor-cyclic-cokernel).

Proof: tensor the source cokernel presentation by M. Since tensor preserves finite
colimits, after identifying M tensor the unit with M this is the cokernel of its
scalar dC. Apply F, which preserves finite colimits, and identify F(M tensor the
unit) with F(M) using the image of the source unitor. On the other hand, tensor
the target cokernel presentation by F(M), and use its unitor. This gives the
cokernel of dD acting on F(M). The displayed scalar identity identifies these
two endomorphisms. Lax monoidal naturality for r, followed by the right unit axiom,
says that mu F M N intertwines their cokernel projections. The unique map between
two cokernels of the same endomorphism with this projection equation is an
isomorphism; its inverse is the comparison in the other direction. This argument
only uses cokernel universal properties and the specified functor and tensor
comparisons, and includes the zero quotient and zero source object. -/
theorem laxTensorCyclicCokernel
    {C : Type a} [Category.{b} C] [Abelian C] [MonoidalCategory C]
    [MonoidalPreadditive C]
    [∀ M : C, PreservesFiniteColimits (tensorLeft M)]
    {D : Type c} [Category.{d} D] [Abelian D] [MonoidalCategory D]
    [MonoidalPreadditive D]
    [∀ M : D, PreservesFiniteColimits (tensorLeft M)]
    (F : C ⥤ D) [F.Additive] [F.LaxMonoidal] [PreservesFiniteColimits F]
    (N : C) (r : 𝟙_ C ⟶ N) (dC : End (𝟙_ C)) (dD : End (𝟙_ D))
    (zC : dC.asHom ≫ r = 0) (hC : IsColimit (CokernelCofork.ofπ r zC))
    (zD : dD.asHom ≫ (Functor.LaxMonoidal.ε F ≫ F.map r) = 0)
    (hD : IsColimit (CokernelCofork.ofπ (Functor.LaxMonoidal.ε F ≫ F.map r) zD))
    (hs : ∀ M : C,
      F.map ((ρ_ M).inv ≫ (M ◁ (dC).asHom) ≫ (ρ_ M).hom) =
        (ρ_ (F.obj M)).inv ≫ (F.obj M ◁ (dD).asHom) ≫ (ρ_ (F.obj M)).hom)
    (M : C) : IsIso (Functor.LaxMonoidal.μ F M N) := by
  let H : C ⥤ D := tensorLeft M ⋙ F
  let c := (CokernelCofork.ofπ r zC).map H
  let d := (CokernelCofork.ofπ (Functor.LaxMonoidal.ε F ≫ F.map r) zD).map
    (tensorLeft (F.obj M))
  let hc : IsColimit c := CokernelCofork.mapIsColimit _ hC H
  let hd : IsColimit d := CokernelCofork.mapIsColimit _ hD (tensorLeft (F.obj M))
  let e : F.obj (M ⊗ 𝟙_ C) ≅ F.obj M ⊗ 𝟙_ D :=
    F.mapIso (ρ_ M) ≪≫ (ρ_ (F.obj M)).symm
  have he : e.hom ≫ (F.obj M ◁ dD.asHom) = F.map (M ◁ dC.asHom) ≫ e.hom := by
    apply (cancel_epi (F.map (ρ_ M).inv)).1
    apply (cancel_mono (ρ_ (F.obj M)).hom).1
    simpa only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc,
      Iso.inv_hom_id, F.map_id, Category.id_comp, Category.comp_id] using (hs M).symm
  let j : d.pt ≅ c.pt := CokernelCofork.mapIsoOfIsColimit hd hc
    (Arrow.isoMk (f := Arrow.mk (F.obj M ◁ dD.asHom))
      (g := Arrow.mk (F.map (M ◁ dC.asHom))) e.symm e.symm (by
        change e.inv ≫ F.map (M ◁ dC.asHom) = (F.obj M ◁ dD.asHom) ≫ e.inv
        rw [Iso.inv_comp_eq, ← Category.assoc, he, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]))
  have hμ : d.π ≫ Functor.LaxMonoidal.μ F M N = e.inv ≫ c.π := by
    change (F.obj M ◁ (Functor.LaxMonoidal.ε F ≫ F.map r)) ≫
      Functor.LaxMonoidal.μ F M N =
        ((ρ_ (F.obj M)).hom ≫ F.map (ρ_ M).inv) ≫ F.map (M ◁ r)
    rw [whiskerLeft_comp, Category.assoc, Functor.LaxMonoidal.μ_natural_right]
    rw [← Category.assoc, ← cancel_epi (ρ_ (F.obj M)).inv]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
    exact Functor.LaxMonoidal.right_unitality_inv_assoc F M _
  have hj : d.π ≫ j.hom = e.inv ≫ c.π := by
    exact CokernelCofork.π_mapOfIsColimit hd c _
  have : Epi d.π := Cofork.IsColimit.epi hd
  have hm : Functor.LaxMonoidal.μ F M N = j.hom :=
    (cancel_epi d.π).1 (hμ.trans hj.symm)
  rw [hm]
  infer_instance

end CategoryTheory
