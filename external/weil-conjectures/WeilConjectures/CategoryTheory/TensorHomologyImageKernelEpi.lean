/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.Images
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor homology maps onto the kernel of the image inclusion

Source: Stacks Project, Tag 0653, the Tor argument in `lemma-last-one-flat`.
(blueprint: lem-pc-module-tensor-homology-image-kernel-epi).
-/

@[expose] public section

universe u

namespace CategoryTheory

open MonoidalCategory Limits

private theorem tensorSingleIso_inv_naturality
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {N N' : ModuleCat.{u} A} (f : N ⟶ N') :
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat A)) N P).inv ≫
        (((curriedTensor (ModuleCat A)).map₂CochainComplex).obj P).map
          ((CochainComplex.singleFunctor (ModuleCat A) 0).map f) =
      (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat A)).map f) (.up ℤ)).app P ≫
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat A)) N' P).inv := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp [CochainComplex.mapBifunctorSingle₂Iso_inv, CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    whiskerLeft_comp]

-- Comparing total tensor complexes with termwise tensoring requires extra type reductions.
set_option backward.isDefEq.respectTransparency false in
/-- Tensor homology surjects naturally onto the kernel of the tensor image inclusion.
Source: Stacks Project, Tag 0653, the Tor argument in `lemma-last-one-flat`.
(blueprint: lem-pc-module-tensor-homology-image-kernel-epi)

Proof: Factor d = P.d (a-1) a as the epimorphism pi onto K = im(d), followed by
its monic inclusion iota. Tensor pi with N; right exactness preserves its
surjectivity. The total tensor complex with N in degree zero is naturally
isomorphic to the complex obtained by tensoring every term and differential
of P with N. Its cycles in degree a-1 map under pi tensor N into the kernel
of iota tensor N, since d = pi followed by iota. The preceding differential
is killed by pi: cancel the monic iota in d_previous followed by pi followed
by iota = 0. Thus the map on cycles kills boundaries and descends to homology.
To prove surjectivity, lift any element y of the tensor kernel along pi tensor N
to x. Its outgoing differential equals (iota tensor N)(y) = 0, so x is a cycle
and its homology class maps to y. Tensor bifunctoriality makes this construction
commute with each map N -> N'; cancel the epimorphism from cycles to homology
and the monic kernel inclusion to verify naturality. Evaluation preserves
kernels, so these components define a map into the functor-category kernel.
This argument needs no flatness of P. -/
theorem exists_epi_tensor_homology_to_image_kernel
    (A : Type u) [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) :
    ∃ σ : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0 ⋙
        ((curriedTensor (ModuleCat.{u} A)).map₂CochainComplex).obj P ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) (a - 1)) ⟶
      Limits.kernel ((curriedTensor (ModuleCat.{u} A)).map
        (Abelian.image.ι (P.d (a - 1) a))),
      ∀ N : ModuleCat.{u} A, Epi (σ.app N) := by
  classical
  let d := P.d (a - 1) a
  let K := Abelian.image d
  let i : K ⟶ P.X a := Abelian.image.ι d
  let π : P.X (a - 1) ⟶ K := Abelian.factorThruImage d
  have hπ : π ≫ i = d := Abelian.image.fac d
  have hprev (j : ℤ) : P.d j (a - 1) ≫ π = 0 := by
    rw [← cancel_mono i, Category.assoc, hπ, zero_comp]
    exact P.d_comp_d j (a - 1) a
  let C := CochainComplex.singleFunctor (ModuleCat A) 0 ⋙
    ((curriedTensor (ModuleCat A)).map₂CochainComplex).obj P
  let E (N : ModuleCat.{u} A) := ((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P
  let S (N : ModuleCat.{u} A) := (E N).sc (a - 1)
  let e (N : ModuleCat.{u} A) : C.obj N ≅ E N :=
    CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (ModuleCat A)) N P
  let H := HomologicalComplex.homologyFunctor (ModuleCat A) (.up ℤ) (a - 1)
  have hw (N : ModuleCat.{u} A) :
      (S N).toCycles ≫ ((S N).iCycles ≫ π ▷ N) = 0 := by
    rw [← Category.assoc, ShortComplex.toCycles_i]
    change ((P.d _ (a - 1)) ▷ N) ≫ π ▷ N = 0
    rw [← comp_whiskerRight, hprev, MonoidalPreadditive.zero_whiskerRight]
  let ψ (N : ModuleCat.{u} A) : (E N).homology (a - 1) ⟶ K ⊗ N :=
    (S N).descHomology ((S N).iCycles ≫ π ▷ N) (hw N)
  have hψ (N : ModuleCat.{u} A) :
      (E N).homologyπ (a - 1) ≫ ψ N = (S N).iCycles ≫ π ▷ N :=
    (S N).π_descHomology _ _
  let α : tensorLeft K ⟶ tensorLeft (P.X a) := (curriedTensor (ModuleCat A)).map i
  let β : C ⋙ H ⟶ tensorLeft K := {
    app := fun N ↦ H.map (e N).hom ≫ ψ N
    naturality := fun N N' f ↦ by
      let Γ := (NatTrans.mapHomologicalComplex
        ((tensoringRight (ModuleCat A)).map f) (.up ℤ)).app P
      have he : C.map f ≫ (e N').hom = (e N).hom ≫ Γ := by
        apply (cancel_epi (e N).inv).mp
        have hi : (e N).inv ≫ C.map f = Γ ≫ (e N').inv :=
          tensorSingleIso_inv_naturality P f
        rw [← Category.assoc, hi]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc]
      have hn : H.map Γ ≫ ψ N' = ψ N ≫ K ◁ f := by
        apply (cancel_epi ((E N).homologyπ (a - 1))).mp
        change (E N).homologyπ (a - 1) ≫
          HomologicalComplex.homologyMap Γ (a - 1) ≫ ψ N' = _
        rw [HomologicalComplex.homologyπ_naturality_assoc]
        rw [hψ N', ← Category.assoc ((E N).homologyπ (a - 1)), hψ N]
        change HomologicalComplex.cyclesMap Γ (a - 1) ≫
          (E N').iCycles (a - 1) ≫ π ▷ N' =
          (E N).iCycles (a - 1) ≫ π ▷ N ≫ K ◁ f
        rw [HomologicalComplex.cyclesMap_i_assoc]
        change (E N).iCycles (a - 1) ≫ P.X (a - 1) ◁ f ≫ π ▷ N' = _
        rw [whisker_exchange]
      change H.map (C.map f) ≫ H.map (e N').hom ≫ ψ N' =
        (H.map (e N).hom ≫ ψ N) ≫ K ◁ f
      rw [← Functor.map_comp_assoc, he, Functor.map_comp, Category.assoc, hn]
      exact (Category.assoc _ _ _).symm }
  have w : β ≫ α = 0 := by
    apply NatTrans.ext
    funext N
    change H.map (e N).hom ≫ ψ N ≫ i ▷ N = 0
    apply (cancel_epi (H.map (e N).inv)).mp
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id,
      Category.id_comp, comp_zero]
    apply (cancel_epi ((E N).homologyπ (a - 1))).mp
    rw [← Category.assoc, hψ, Category.assoc, ← comp_whiskerRight, hπ, comp_zero]
    change (E N).iCycles (a - 1) ≫ (E N).d (a - 1) a = 0
    exact (E N).iCycles_d _ _
  let γ : C ⋙ H ⟶ Limits.kernel α := Limits.kernel.lift α β w
  refine ⟨γ, fun N ↦ ?_⟩
  have fac : γ.app N ≫ (Limits.kernel.ι α).app N = β.app N :=
    congrArg (fun t ↦ t.app N) (Limits.kernel.lift_ι α β w)
  have hsurj : Function.Surjective (π ▷ N).hom := by
    change Function.Surjective (π.hom.rTensor N)
    exact π.hom.rTensor_surjective N ((ModuleCat.epi_iff_surjective π).mp inferInstance)
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  let z := ((Limits.kernel.ι α).app N).hom y
  have hz : (i ▷ N).hom z = 0 :=
    congrArg (fun t ↦ (t.app N).hom y) (Limits.kernel.condition α)
  obtain ⟨x, hx⟩ := hsurj z
  have hcycle : (S N).g.hom x = 0 := by
    have hdx : (d ▷ N).hom x = 0 := by
      rw [← hπ, comp_whiskerRight, ModuleCat.comp_apply, hx]
      exact hz
    change (P.d (a - 1) ((ComplexShape.up ℤ).next (a - 1)) ▷ N).hom x = 0
    have hn : (ComplexShape.up ℤ).next (a - 1) = a :=
      (ComplexShape.up ℤ).next_eq' (by simp)
    rw [hn]
    exact hdx
  let xc : (S N).cycles := (S N).moduleCatCyclesIso.inv.hom ⟨x, hcycle⟩
  have hc : (S N).iCycles.hom xc = x := by
    have h := congrArg (fun t ↦ t.hom ⟨x, hcycle⟩)
      ((S N).moduleCatCyclesIso_inv_iCycles)
    exact h
  refine ⟨(H.map (e N).inv).hom (((E N).homologyπ (a - 1)).hom xc), ?_⟩
  apply (ModuleCat.mono_iff_injective ((Limits.kernel.ι α).app N)).mp inferInstance
  have hb : (E N).homologyπ (a - 1) ≫ H.map (e N).inv ≫ β.app N =
      (S N).iCycles ≫ π ▷ N := by
    change (E N).homologyπ (a - 1) ≫ H.map (e N).inv ≫
      H.map (e N).hom ≫ ψ N = _
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
    exact hψ N
  have hb' := congrArg (fun t ↦ t.hom xc) hb
  have hf := congrArg (fun t ↦ t.hom
    ((H.map (e N).inv).hom (((E N).homologyπ (a - 1)).hom xc))) fac
  refine hf.trans (hb'.trans ?_)
  change (π ▷ N).hom ((S N).iCycles.hom xc) = z
  rw [hc, hx]

end CategoryTheory
