/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedHomologyInjective

/-! Transfer of large coproducts from a derived category to its abelian category. -/

@[expose] public section

universe w uA vA vH

open CategoryTheory.Limits

namespace CategoryTheory

/-- Large derived coproducts give large coproducts in the underlying category.

Source: the first step of node new-stage3-gabriel-popescu-large-hom-right-adjoint,
the explicit derived-to-abelian extension of Stacks Project Tag 0F5S.
The extension uses injective copresentations and degree-zero cohomology.

(auxiliary; not a blueprint node)

Proof in words: for a family X_i at the displayed size, take the coproduct K
of the degree-zero objects X_i[0] in D(A), and set P = H^0(K). Apply H^0 to
the injections to obtain maps X_i -> P. If I is injective, I[0] is
K-injective; exactness of Hom(-,I) identifies Hom_D(K,I[0]) naturally with
Hom_A(H^0(K),I). The derived coproduct property therefore identifies the
map Hom_A(P,I) -> product_i Hom_A(X_i,I) with a bijection.
For arbitrary Y, embed Y into an injective I^0, and embed its cokernel into
an injective I^1. This gives an exact sequence 0 -> Y -> I^0 -> I^1.
The two functors Hom_A(P,-) and product_i Hom_A(X_i,-) are left exact.
The comparison maps for I^0 and I^1 are bijections and commute with the
map I^0 -> I^1. Taking kernels gives the comparison bijection for Y.
This is precisely the universal property of the displayed cofan with vertex
P. Thus every family of the displayed size has a coproduct. The argument
also covers the empty family, for which P is a zero object.
-/
theorem derived_large_coproducts_transfer
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    [HasCoproducts.{max w vA vH} (DerivedCategory A)] :
    HasCoproducts.{max w vA vH} A := by
  classical
  intro J
  refine ⟨fun F ↦ ?_⟩
  let X : J → A := fun j ↦ F.obj ⟨j⟩
  let S := DerivedCategory.singleFunctor A 0
  let H := DerivedCategory.homologyFunctor A 0
  let e := DerivedCategory.singleFunctorCompHomologyFunctorIso A 0
  let D : J → DerivedCategory A := fun j ↦ S.obj (X j)
  let P := H.obj (∐ D)
  let ι : ∀ j, X j ⟶ P := fun j ↦ (e.app (X j)).inv ≫ H.map (Sigma.ι D j)
  have hH (K : DerivedCategory A) (I : A) [Injective I] :
      Function.Bijective (fun a : K ⟶ S.obj I ↦ H.map a ≫ (e.app I).hom) := by
    have h := derived_homology_injective_bijective K I
    refine ⟨fun a b hab ↦ h.injective ((cancel_mono (e.app I).hom).1 hab), ?_⟩
    intro g
    obtain ⟨a, ha⟩ := h.surjective (g ≫ (e.app I).inv)
    refine ⟨a, ?_⟩
    change H.map a = _ at ha
    change H.map a ≫ (e.app I).hom = g
    rw [ha, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hI (I : A) [Injective I] :
      Function.Bijective (fun a : P ⟶ I ↦ fun j ↦ ι j ≫ a) := by
    constructor
    · intro a b hab
      obtain ⟨a', rfl⟩ := (hH (∐ D) I).surjective a
      obtain ⟨b', rfl⟩ := (hH (∐ D) I).surjective b
      congr 1
      apply Sigma.hom_ext
      intro j
      apply (hH (D j) I).injective
      have hj := congr_fun hab j
      change ((e.app (X j)).inv ≫ H.map (Sigma.ι D j)) ≫
        (H.map a' ≫ (e.app I).hom) = ((e.app (X j)).inv ≫ H.map (Sigma.ι D j)) ≫
          (H.map b' ≫ (e.app I).hom) at hj
      change H.map (Sigma.ι D j ≫ a') ≫ (e.app I).hom =
        H.map (Sigma.ι D j ≫ b') ≫ (e.app I).hom
      rw [Functor.map_comp, Functor.map_comp]
      exact (cancel_epi (e.app (X j)).inv).1 (by simpa only [Category.assoc] using hj)
    · intro g
      refine ⟨H.map (Sigma.desc (fun j ↦ S.map (g j))) ≫ (e.app I).hom, ?_⟩
      funext j
      dsimp [ι]
      rw [Category.assoc, ← H.map_comp_assoc, Sigma.ι_comp_desc]
      have hn := e.hom.naturality (g j)
      dsimp at hn
      rw [hn]
      exact (e.app (X j)).inv_hom_id_assoc (g j)
  have hbij (Y : A) : Function.Bijective (fun a : P ⟶ Y ↦ fun j ↦ ι j ≫ a) := by
    constructor
    · intro a b hab
      apply (cancel_mono (Injective.ι Y)).1
      apply (hI (Injective.under Y)).injective
      funext j
      simp only [← Category.assoc, congr_fun hab j]
    · intro g
      obtain ⟨a, ha⟩ := (hI (Injective.under Y)).surjective
        (fun j ↦ g j ≫ Injective.ι Y)
      have hz : a ≫ cokernel.π (Injective.ι Y) = 0 := by
        apply (cancel_mono (Injective.ι (cokernel (Injective.ι Y)))).1
        apply (hI (Injective.under (cokernel (Injective.ι Y)))).injective
        funext j
        change ι j ≫ ((a ≫ cokernel.π (Injective.ι Y)) ≫
          Injective.ι (cokernel (Injective.ι Y))) = ι j ≫
            (0 ≫ Injective.ι (cokernel (Injective.ι Y)))
        have haj : ι j ≫ a = g j ≫ Injective.ι Y := congr_fun ha j
        rw [← Category.assoc, ← Category.assoc, haj]
        simp only [Category.assoc, cokernel.condition_assoc, zero_comp, comp_zero]
      refine ⟨Abelian.monoLift (Injective.ι Y) a hz, ?_⟩
      funext j
      apply (cancel_mono (Injective.ι Y)).1
      simpa only [Category.assoc, Abelian.monoLift_comp] using congr_fun ha j
  let c : Cofan X := Cofan.mk P ι
  let hc : IsColimit c := Cofan.IsColimit.mk c
    (fun t ↦ (hbij t.pt).surjective t.inj |>.choose)
    (fun t j ↦ congr_fun ((hbij t.pt).surjective t.inj |>.choose_spec) j)
    (fun t m hm ↦ (hbij t.pt).injective
      (by
        funext j
        exact (hm j).trans
          (congr_fun (((hbij t.pt).surjective t.inj).choose_spec) j).symm))
  have : HasColimit (Discrete.functor (F.obj ∘ Discrete.mk)) := HasColimit.mk ⟨c, hc⟩
  exact hasColimit_of_iso (Discrete.natIsoFunctor (F := F))

end CategoryTheory
