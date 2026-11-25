/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedAlgebraData
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedDegreeData
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Local ideal coefficients of the graded quotient kernel

Source: Stacks Project, Tag 09MS, the direct-sum ideal sequence.
(blueprint: lem-sc-tensor-graded-kernel-local-ideal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal

private theorem epi_local_lift {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q)
    [Epi f] (U : X.Opens) (s : Γ(Q, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
      ∃ t : Γ(P, V), f.app V t = Q.presheaf.map (homOfLE h).op s := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have : Epi (F.map f) := inferInstance
  have hs : TopCat.Presheaf.IsLocallySurjective (F.map f).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance
  obtain ⟨V, h, ⟨t, ht⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hs U s x hx
  exact ⟨V, h, hxV, t, ht⟩

private theorem tensor_local_lift {X : Scheme.{u}} (P Q : X.Modules)
    (U : X.Opens) (s : Γ(P ⊗ Q, U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (h : V ≤ U), x ∈ V ∧
      ∃ t : Γ(P, V) ⊗[Γ(X, V)] Γ(Q, V),
        tensorSectionsMap P Q V t = (P ⊗ Q).presheaf.map (homOfLE h).op s := by
  have hs := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map
      (Functor.LaxMonoidal.μ (forgetToPresheafOfModules X) P Q)) s
  obtain ⟨V, i, ⟨t, ht⟩, hxV⟩ := hs x hx
  exact ⟨V, leOfHom i, hxV, t, ht⟩

private theorem tensor_image_mem {X : Scheme.{u}} (J : X.IdealSheafData)
    (B : Under X.sheaf) (V : X.affineOpens) :
    let M : X.Modules := commAlgebraSheafModule X.sheaf B
    let μ : J.toModules ⊗ M ⟶ M := J.toModulesι ▷ M ≫ (λ_ M).hom
    ∀ t : Γ(J.toModules, V.1) ⊗[Γ(X, V.1)] Γ(M, V.1),
      (show B.right.obj.obj (op V.1) from μ.app V.1
        (tensorSectionsMap J.toModules M V.1 t)) ∈
        Ideal.map (B.hom.hom.app (op V.1)).hom (J.ideal V) := by
  dsimp only
  intro t
  let M : X.Modules := commAlgebraSheafModule X.sheaf B
  let μ : J.toModules ⊗ M ⟶ M := J.toModulesι ▷ M ≫ (λ_ M).hom
  change (show B.right.obj.obj (op V.1) from μ.app V.1
    (tensorSectionsMap J.toModules M V.1 t)) ∈ _
  induction t using TensorProduct.inductionOn with
  | tmul r s =>
    rw [tensorSectionsMap_tmul]
    change (show B.right.obj.obj (op V.1) from (λ_ M).hom.app V.1
      ((J.toModulesι ▷ M).app V.1 (tmulSection r s))) ∈ _
    rw [whiskerRight_app_tmulSection, leftUnitor_hom_app_tmulSection']
    change (B.hom.hom.app (op V.1)).hom (J.toModulesι.app V.1 r) *
      (show B.right.obj.obj (op V.1) from s) ∈ _
    exact Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ ((J.range_toModulesι_app V).subset ⟨r, rfl⟩))
  | add t₁ t₂ h₁ h₂ =>
    simpa only [map_add] using (Ideal.add_mem _ h₁ h₂)

private theorem image_locally_ideal {X : Scheme.{u}} (J : X.IdealSheafData)
    (B : Under X.sheaf) :
    let M : X.Modules := commAlgebraSheafModule X.sheaf B
    let μ : J.toModules ⊗ M ⟶ M := J.toModulesι ▷ M ≫ (λ_ M).hom
    ∀ (U : X.Opens) (s : Γ(image μ, U)) (x : X), x ∈ U →
      ∃ (W : X.Opens) (hWU : W ≤ U), x ∈ W ∧
        ∀ (V : X.affineOpens) (hVW : V.1 ≤ W),
          (show B.right.obj.obj (op V.1) from (image.ι μ).app V.1
            ((image μ).presheaf.map (homOfLE (hVW.trans hWU)).op s)) ∈
            Ideal.map (B.hom.hom.app (op V.1)).hom (J.ideal V) := by
  dsimp only
  let M : X.Modules := commAlgebraSheafModule X.sheaf B
  let μ : J.toModules ⊗ M ⟶ M := J.toModulesι ▷ M ≫ (λ_ M).hom
  intro U s x hx
  obtain ⟨W₀, h₀, hx₀, t, ht⟩ := epi_local_lift (factorThruImage μ) U s x hx
  obtain ⟨W, h₁, hx₁, r, hr⟩ := tensor_local_lift J.toModules M W₀ t x hx₀
  refine ⟨W, h₁.trans h₀, hx₁, ?_⟩
  intro V hV
  let T := Functor.LaxMonoidal.μ (forgetToPresheafOfModules X) J.toModules M
  let rV := (J.toModules.val ⊗ M.val).map (homOfLE hV).op r
  have hTV : tensorSectionsMap J.toModules M V.1 rV =
      (J.toModules ⊗ M).presheaf.map (homOfLE hV).op
        (tensorSectionsMap J.toModules M W r) :=
    PresheafOfModules.naturality_apply T (homOfLE hV).op r
  have hm (W' W'' : X.Opens) (h : W' ≤ W'') (z : Γ(J.toModules ⊗ M, W'')) :
      μ.app W' ((J.toModules ⊗ M).presheaf.map (homOfLE h).op z) =
        M.presheaf.map (homOfLE h).op (μ.app W'' z) :=
    PresheafOfModules.naturality_apply μ.val (homOfLE h).op z
  have hi (W' W'' : X.Opens) (h : W' ≤ W'') (z : Γ(image μ, W'')) :
      (image.ι μ).app W' ((image μ).presheaf.map (homOfLE h).op z) =
        M.presheaf.map (homOfLE h).op ((image.ι μ).app W'' z) :=
    PresheafOfModules.naturality_apply (image.ι μ).val (homOfLE h).op z
  have hfac : μ.app W₀ t = (image.ι μ).app W₀
      ((image μ).presheaf.map (homOfLE h₀).op s) := by
    rw [← ht]
    change μ.app W₀ t = (factorThruImage μ ≫ image.ι μ).app W₀ t
    rw [image.fac]
  have he : μ.app V.1 (tensorSectionsMap J.toModules M V.1 rV) =
      (image.ι μ).app V.1
        ((image μ).presheaf.map (homOfLE (hV.trans (h₁.trans h₀))).op s) := by
    rw [hTV, hm, hr, hm, hfac, presheaf_map_map_apply, homOfLE_comp]
    rw [← hi V.1 W₀ (hV.trans h₁), presheaf_map_map_apply]
    rfl
  rw [← he]
  exact tensor_image_mem J B V rV

section KernelFactor
attribute [local irreducible] tensorGradedAlgebraMap tensorGradedUnit
  commAlgebraSheafModule tensorPullback

private theorem gradedKernelFactor {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (A : TensorGradedAlgebraData j L) :
    let M : X.Modules := commAlgebraSheafModule X.sheaf A.B
    let μ : j.ker.toModules ⊗ M ⟶ M := j.ker.toModulesι ▷ M ≫ (λ_ M).hom
    ∃ f : kernel (tensorGradedAlgebraMap A.p) ⟶ image μ,
      f ≫ image.ι μ = kernel.ι (tensorGradedAlgebraMap A.p) := by
  classical
  dsimp only
  let M : X.Modules := commAlgebraSheafModule X.sheaf A.B
  let μ : ∀ F : X.Modules, j.ker.toModules ⊗ F ⟶ F := fun F ↦
    j.ker.toModulesι ▷ F ≫ (λ_ F).hom
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  -- Direct choice avoids dependent elimination through the surrounding local definitions.
  let D := Classical.choice (tensorGradedDegreeData_exists j L A)
  have factors (d : ℕ) : ∃ f : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
      image (μ M), f ≫ image.ι (μ M) =
        kernel.ι (tensorGradedUnit j (L.tensorPow d)) ≫ A.b d := by
    let F := L.tensorPow d
    obtain ⟨_, w, ⟨hk⟩⟩ := closedImmersion_unit_kernel j F
    have hz : kernel.ι (tensorGradedUnit j F) ≫ adj.unit.app F = 0 := by
      apply (cancel_mono ((pushforward j).map ((adj.leftAdjointUniq adj').hom.app F))).1
      rw [Category.assoc, adj.unit_leftAdjointUniq_hom_app adj' F]
      have hunit : adj'.unit.app F = tensorGradedUnit j F := by
        unfold tensorGradedUnit
        rfl
      rw [hunit, zero_comp]
      exact kernel.condition _
    let g := hk.lift (KernelFork.ofι (kernel.ι (tensorGradedUnit j F)) hz)
    have hg : g ≫ image.ι (μ F) = kernel.ι (tensorGradedUnit j F) :=
      hk.fac _ WalkingParallelPair.zero
    have hμ : (j.ker.toModules ◁ A.b d) ≫ μ M = μ F ≫ A.b d := by
      dsimp only [μ]
      calc
        _ = (j.ker.toModulesι ▷ F ≫ (𝟙_ X.Modules) ◁ A.b d) ≫ (λ_ M).hom := by
          exact (Category.assoc _ _ _).symm.trans
            (congrArg (fun f ↦ f ≫ (λ_ M).hom)
              (whisker_exchange (C := X.Modules) j.ker.toModulesι (A.b d)))
        _ = j.ker.toModulesι ▷ F ≫ ((𝟙_ X.Modules) ◁ A.b d ≫ (λ_ M).hom) :=
          Category.assoc _ _ _
        _ = j.ker.toModulesι ▷ F ≫ ((λ_ F).hom ≫ A.b d) :=
          congrArg (fun f ↦ j.ker.toModulesι ▷ F ≫ f)
            (leftUnitor_naturality (C := X.Modules) (A.b d))
        _ = _ := (Category.assoc _ _ _).symm
    let sq : Arrow.mk (μ F) ⟶ Arrow.mk (μ M) :=
      Arrow.homMk (j.ker.toModules ◁ A.b d) (A.b d) hμ
    refine ⟨g ≫ image.map sq, ?_⟩
    have hmap : image.map sq ≫ image.ι (μ M) = image.ι (μ F) ≫ A.b d :=
      image.map_ι sq
    rw [Category.assoc, hmap, ← Category.assoc, hg]
  choose f hf using factors
  refine ⟨D.k_colimit.desc (Cofan.mk (image (μ M)) f), ?_⟩
  apply D.k_colimit.hom_ext
  intro d
  change D.k d.as ≫ (_ ≫ image.ι (μ M)) = D.k d.as ≫ _
  have hd : D.k d.as ≫ D.k_colimit.desc (Cofan.mk (image (μ M)) f) = f d.as :=
    D.k_colimit.fac _ d
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g ↦ g ≫ image.ι (μ M)) hd).trans
      ((hf d.as).trans (D.k_inclusion d.as).symm))

end KernelFactor

/-- Two sections of the graded quotient kernel locally lie in the extended base ideal.
No square-zero assumption, multiplication law, or invertibility assumption is used.
Source: Stacks Project, Tag 09MS, direct-sum ideal sequence, and Tag 04CJ (1).
Proof: use the kernel coproduct from TensorGradedDegreeData. In each degree,
the closed-immersion unit kernel formula factors its kernel inclusion through
the image of J ⊗ L^d → L^d. Uniqueness of adjunctions transfers that formula
to the chosen tensorGradedUnit. Naturality of ideal multiplication then maps
each degreewise image into the image of J ⊗ B → B; coproduct descent factors
the whole kernel inclusion through that image. Sections of a kernel lift on
every open. A section of the multiplication image lifts locally to J ⊗ B,
and local surjectivity of the tensor sheafification represents it by a tensor
of sections on a smaller open. On every affine subopen, induction on that
tensor reduces ideal membership to pure tensors. Their images are products
of algebra sections with structure-map images of elements of J.ideal, by
range_toModulesι_app and the left-unitor formula. Addition preserves membership.
Apply this to both sections and choose an affine neighborhood inside the
intersection of the two resulting neighborhoods. The proof uses neither
invertibility, homogeneous multiplication, nor square-zero. The empty-scheme
case is vacuous because a point x is part of the hypotheses.
(blueprint: lem-sc-tensor-graded-kernel-local-ideal). -/
theorem tensorGradedKernel_locally_ideal {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) (A : TensorGradedAlgebraData j L)
    (U : X.Opens) (a b : A.B.right.obj.obj (op U))
    (ha : A.p.right.hom.app (op U) a = 0)
    (hb : A.p.right.hom.app (op U) b = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : X.affineOpens) (hVU : V.1 ≤ U), x ∈ V.1 ∧
      A.B.right.obj.map (homOfLE hVU).op a ∈
        Ideal.map (A.B.hom.hom.app (op V.1)).hom (j.ker.ideal V) ∧
      A.B.right.obj.map (homOfLE hVU).op b ∈
        Ideal.map (A.B.hom.hom.app (op V.1)).hom (j.ker.ideal V) := by
  let M : X.Modules := commAlgebraSheafModule X.sheaf A.B
  let N : X.Modules := commAlgebraSheafModule X.sheaf A.C
  let p : M ⟶ N := tensorGradedAlgebraMap A.p
  let μ : j.ker.toModules ⊗ M ⟶ M := j.ker.toModulesι ▷ M ≫ (λ_ M).hom
  let aM : Γ(M, U) := a
  let bM : Γ(M, U) := b
  have haM : p.app U aM = 0 := by
    unfold p tensorGradedAlgebraMap
    exact ha
  have hbM : p.app U bM = 0 := by
    unfold p tensorGradedAlgebraMap
    exact hb
  obtain ⟨ka, hka⟩ := (range_map_kernelι U p).ge haM
  obtain ⟨kb, hkb⟩ := (range_map_kernelι U p).ge hbM
  have hfactor : ∃ f : (kernel p : X.Modules) ⟶ (image μ : X.Modules),
      f ≫ image.ι μ = kernel.ι p := gradedKernelFactor j L A
  obtain ⟨f, hf⟩ := hfactor
  have hfa : (image.ι μ).app U (f.app U ka) = aM := by
    change (f ≫ image.ι μ).app U ka = aM
    rw [hf]
    exact hka
  have hfb : (image.ι μ).app U (f.app U kb) = bM := by
    change (f ≫ image.ι μ).app U kb = bM
    rw [hf]
    exact hkb
  obtain ⟨Wa, hWa, hxa, hma⟩ := image_locally_ideal j.ker A.B U (f.app U ka) x hx
  obtain ⟨Wb, hWb, hxb, hmb⟩ := image_locally_ideal j.ker A.B U (f.app U kb) x hx
  obtain ⟨V, hVaff, hxV, hV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ Wa ⊓ Wb from ⟨hxa, hxb⟩)
  let Va : X.affineOpens := ⟨V, hVaff⟩
  have hVa : V ≤ Wa := le_trans hV inf_le_left
  have hVb : V ≤ Wb := le_trans hV inf_le_right
  have hVU : V ≤ U := hVa.trans hWa
  refine ⟨Va, hVU, hxV, ?_, ?_⟩
  · have he := PresheafOfModules.naturality_apply (image.ι μ).val
      (homOfLE hVU).op (f.app U ka)
    change (image.ι μ).app V
      ((image μ).presheaf.map (homOfLE hVU).op (f.app U ka)) =
        M.presheaf.map (homOfLE hVU).op ((image.ι μ).app U (f.app U ka)) at he
    rw [hfa] at he
    exact he ▸ hma Va hVa
  · have he := PresheafOfModules.naturality_apply (image.ι μ).val
      (homOfLE hVU).op (f.app U kb)
    change (image.ι μ).app V
      ((image μ).presheaf.map (homOfLE hVU).op (f.app U kb)) =
        M.presheaf.map (homOfLE hVU).op ((image.ι μ).app U (f.app U kb)) at he
    rw [hfb] at he
    exact he ▸ hmb Va hVb

end
end AlgebraicGeometry.Scheme.Modules
