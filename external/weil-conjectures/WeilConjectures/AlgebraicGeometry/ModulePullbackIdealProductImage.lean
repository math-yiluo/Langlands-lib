/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Subobject.Limits
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import all WeilConjectures.AlgebraicGeometry.AffinePushforwardIdealProduct

/-! # Image of the pullback of an ideal-module product

Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0887,
using Modules Lemma 01BG and Algebra Lemma 00DF
(blueprint: lem-weil-pbc-module-pullback-ideal-product-image).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option autoImplicit false

private theorem hom_zero_of_paired_affine {X Y : Scheme.{v}} (f : X ⟶ Y)
    {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ (V : Y.affineOpens) (U : X.affineOpens), U.1 ≤ f ⁻¹ᵁ V.1 →
      ∀ s : Γ(M, U.1), φ.app U.1 s = 0) : φ = 0 := by
  open Opposite TopologicalSpace in
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change φ.app W s = 0
  let A := {a : Y.affineOpens × X.affineOpens //
    a.2.1 ≤ f ⁻¹ᵁ a.1.1 ∧ a.2.1 ≤ W}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun a : A ↦ a.1.2.1) W (fun a ↦ homOfLE a.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ W ⊓ f ⁻¹ᵁ V from ⟨hx, hxV⟩) (W ⊓ f ⁻¹ᵁ V).2
    exact Opens.mem_iSup.mpr
      ⟨⟨(⟨V, hV⟩, ⟨U, hU⟩), hUW.trans inf_le_right, hUW.trans inf_le_left⟩, hxU⟩
  · intro a
    have hn := congrArg (fun q ↦ q s)
      (φ.mapPresheaf.naturality (homOfLE a.2.2).op)
    change φ.app a.1.2.1 (M.presheaf.map (homOfLE a.2.2).op s) =
      N.presheaf.map (homOfLE a.2.2).op (φ.app W s) at hn
    rw [map_zero, ← hn]
    exact h a.1.1 a.1.2 a.2.1 _

private theorem subobject_le_of_paired_affine_range {X Y : Scheme.{v}} (f : X ⟶ Y)
    {M N P : X.Modules} (i : M ⟶ P) (j : N ⟶ P) [Mono i] [Mono j]
    (h : ∀ (V : Y.affineOpens) (U : X.affineOpens), U.1 ≤ f ⁻¹ᵁ V.1 →
      Set.range (i.app U.1) ⊆ Set.range (j.app U.1)) :
    Subobject.mk i ≤ Subobject.mk j := by
  have hz : i ≫ cokernel.π j = 0 := by
    apply hom_zero_of_paired_affine f
    intro V U hUV s
    obtain ⟨t, ht⟩ := h V U hUV ⟨s, rfl⟩
    change (cokernel.π j).app U.1 (i.app U.1 s) = 0
    rw [← ht]
    exact congrArg (fun q ↦ q.app U.1 t) (cokernel.condition j)
  let k : M ⟶ Abelian.image j := kernel.lift (cokernel.π j) i hz
  let l : M ⟶ N := k ≫ inv (Abelian.factorThruImage j)
  apply Subobject.mk_le_mk_of_comm l
  change k ≫ inv (Abelian.factorThruImage j) ≫ j = i
  calc
    k ≫ inv (Abelian.factorThruImage j) ≫ j =
        k ≫ inv (Abelian.factorThruImage j) ≫
          Abelian.factorThruImage j ≫ Abelian.image.ι j :=
      congrArg (fun q ↦ k ≫ inv (Abelian.factorThruImage j) ≫ q)
        (Abelian.image.fac j).symm
    _ = k ≫ Abelian.image.ι j := by rw [IsIso.inv_hom_id_assoc]
    _ = i := kernel.lift_ι _ _ hz

open Opposite in
open scoped TensorProduct in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem modulePullbackIdealProductImage_affine_range {X Y : Scheme.{v}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) :
    ∀ (V : Y.affineOpens) (U : X.affineOpens), U.1 ≤ f ⁻¹ᵁ V.1 →
      Set.range (((Scheme.Modules.tensorPullback f).map
        (Scheme.idealModuleProductι J.toModulesι G)).app U.1) =
      Set.range ((Scheme.idealModuleProductι (J.comap f).toModulesι
        ((Scheme.Modules.tensorPullback f).obj G)).app U.1) := by
  classical
  intro V U hUV
  have : G.IsQuasicoherent := hG
  let K := Scheme.idealModuleProduct J.toModulesι G
  have hK : K.IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J G).1
  let e : Scheme.Modules.tensorPullback f ≅ Scheme.Modules.pullback f :=
    Adjunction.leftAdjointUniq (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some
      (Scheme.Modules.pullbackPushforwardAdjunction f)
  have hTG : ((Scheme.Modules.tensorPullback f).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (e.app G).symm
      (Scheme.Modules.isQuasicoherent_pullback f G)
  let : Algebra Γ(Y, V.1) Γ(X, U.1) := (f.appLE V.1 U.1 hUV).hom.toAlgebra
  let : ∀ M : Y.Modules, Module Γ(Y, V.1)
      Γ((Scheme.Modules.tensorPullback f).obj M, U.1) :=
    fun M ↦ Module.compHom _ (f.appLE V.1 U.1 hUV).hom
  obtain ⟨c, hc, -, -, hn⟩ :=
    Scheme.Modules.exists_tensorPullback_affine_sections f V U hUV
  let i := Scheme.idealModuleProductι J.toModulesι G
  let φ := (Scheme.Modules.tensorPullback f).map i
  let Q : Submodule Γ(X, U.1) Γ((Scheme.Modules.tensorPullback f).obj G, U.1) :=
    (φ.val.app (op U.1)).hom.range
  let I := (J.comap f).ideal U
  have hi : Set.range (i.app V.1) =
      {s | s ∈ J.ideal V • (⊤ : Submodule Γ(Y, V.1) Γ(G, V.1))} :=
    ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J G).2.2.2.1 V).1
  have hnat (t : Γ(K, V.1) ⊗[Γ(Y, V.1)] Γ(X, U.1)) :
      φ.app U.1 (c K hK t) =
        c G hG (TensorProduct.map (i.val.app (op V.1)).hom LinearMap.id t) :=
    hn K G hK hG i t
  have hI : I = Ideal.map (f.appLE V.1 U.1 hUV).hom (J.ideal V) :=
    Scheme.IdealSheafData.ideal_comap_appLE J f V U hUV
  rw [((Scheme.Modules.ideal_times_quasiCoherent_affine_sections
    (J.comap f) ((Scheme.Modules.tensorPullback f).obj G)).2.2.2.1 U).1]
  change (Q : Set Γ((Scheme.Modules.tensorPullback f).obj G, U.1)) = _
  suffices Q = I • (⊤ : Submodule Γ(X, U.1)
      Γ((Scheme.Modules.tensorPullback f).obj G, U.1)) from
    congrArg (fun P : Submodule Γ(X, U.1)
      Γ((Scheme.Modules.tensorPullback f).obj G, U.1) ↦
        (P : Set Γ((Scheme.Modules.tensorPullback f).obj G, U.1))) this
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    obtain ⟨z, rfl⟩ := (hc K hK).2 s
    change φ.app U.1 (c K hK z) ∈ I • ⊤
    induction z using TensorProduct.inductionOn with
    | tmul r b =>
      rw [hnat, TensorProduct.map_tmul, LinearMap.id_apply]
      have hr : i.app V.1 r ∈ J.ideal V •
          (⊤ : Submodule Γ(Y, V.1) Γ(G, V.1)) :=
        (Set.ext_iff.mp hi _).mp ⟨r, rfl⟩
      change c G hG (i.app V.1 r ⊗ₜ[Γ(Y, V.1)] b) ∈ I • ⊤
      refine Submodule.smul_induction_on
        (p := fun s ↦ c G hG (s ⊗ₜ[Γ(Y, V.1)] b) ∈ I • ⊤) hr ?_ ?_
      · intro a ha m hm
        rw [← TensorProduct.smul_tmul', LinearMap.map_smul]
        change (f.appLE V.1 U.1 hUV).hom a •
          c G hG (m ⊗ₜ[Γ(Y, V.1)] b) ∈ I •
            (⊤ : Submodule Γ(X, U.1) Γ((Scheme.Modules.tensorPullback f).obj G, U.1))
        apply Submodule.smul_mem_smul
        · rw [hI]; exact Ideal.mem_map_of_mem _ ha
        · exact Submodule.mem_top
      · intro m m' hm hm'
        rw [TensorProduct.add_tmul, map_add]
        exact Submodule.add_mem _ hm hm'
    | add z z' hz hz' =>
      simp only [map_add]
      exact Submodule.add_mem _ hz hz'
  · have hgen (a : Γ(Y, V.1)) (ha : a ∈ J.ideal V)
        (n : Γ((Scheme.Modules.tensorPullback f).obj G, U.1)) :
        (f.appLE V.1 U.1 hUV).hom a • n ∈ Q := by
      obtain ⟨t, rfl⟩ := (hc G hG).2 n
      induction t using TensorProduct.inductionOn with
      | tmul m b =>
        have ham : a • m ∈ J.ideal V •
            (⊤ : Submodule Γ(Y, V.1) Γ(G, V.1)) :=
          Submodule.smul_mem_smul ha Submodule.mem_top
        obtain ⟨r, hr⟩ := (Set.ext_iff.mp hi _).mpr ham
        refine ⟨c K hK (r ⊗ₜ[Γ(Y, V.1)] b), ?_⟩
        change φ.app U.1 (c K hK (r ⊗ₜ[Γ(Y, V.1)] b)) = _
        rw [hnat, TensorProduct.map_tmul, LinearMap.id_apply]
        change c G hG (i.app V.1 r ⊗ₜ[Γ(Y, V.1)] b) = _
        rw [hr, ← TensorProduct.smul_tmul', LinearMap.map_smul]
        rfl
      | add t t' ht ht' =>
        rw [map_add, smul_add]
        exact Q.add_mem ht ht'
    have hle : I • (⊤ : Submodule Γ(X, U.1)
        Γ((Scheme.Modules.tensorPullback f).obj G, U.1)) ≤ Q := by
      apply Submodule.smul_le.mpr
      intro b hb n _
      rw [hI] at hb
      change b ∈ Submodule.span Γ(X, U.1)
        ((f.appLE V.1 U.1 hUV).hom '' (J.ideal V : Set Γ(Y, V.1))) at hb
      induction hb using Submodule.span_induction generalizing n with
      | mem b hb =>
        obtain ⟨a, ha, rfl⟩ := hb
        exact hgen a ha n
      | zero => simp only [zero_smul]; exact Q.zero_mem
      | add b b' hb hb' ih ih' =>
        rw [add_smul]; exact Q.add_mem (ih n Submodule.mem_top) (ih' n Submodule.mem_top)
      | smul d b hb ih =>
        rw [smul_eq_mul, mul_smul]
        exact Q.smul_mem d (ih n Submodule.mem_top)
    exact hle

/-- Pulling back the inclusion of an ideal-module product has image the product by the
extended ideal. Source: Stacks Project, Cohomology of Schemes, proof of Lemma 0887.
(blueprint: lem-weil-pbc-module-pullback-ideal-product-image).

Proof: choose affine opens V in Y and U in X with U contained in the inverse image of V.
Write A = O_Y(V), B = O_X(U), a = J(V), and M = G(V). Quasi-coherent affine sections
identify G with M and JG with aM, and the pullback section comparison identifies the
pulled-back inclusion with aM tensor_A B -> M tensor_A B. Its image is generated by
am tensor b = m tensor rho(a)b; hence it is rho(a)B times M tensor_A B. The affine ideal
extension formula identifies rho(a)B with (J.comap f)(U), and the affine ideal-product
formula identifies this submodule with the image of the ideal-product inclusion on X.
Pullback preserves quasi-coherence: identify tensor pullback with the standard pullback
by uniqueness of left adjoints to pushforward and transport its quasi-coherence instance.
The ideal-product formula gives quasi-coherence of JG. The image/cokernel theorem applied
to the pulled-back inclusion therefore gives quasi-coherence and the sectionwise-image
formula. The product formula gives the same for the inclusion on X. Thus their sections
on these affine opens are their
sectionwise images. Such opens form a basis: choose an affine neighborhood of f(x), then
an affine neighborhood of x inside its preimage and the given open. Equality on this
basis implies equality of the subobjects, since membership is local and sections glue.
This also covers the zero ideal, unit ideal, zero module, and empty affine opens. -/
theorem modulePullbackIdealProductImage {X Y : Scheme.{v}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (G : Y.Modules) (hG : G.IsQuasicoherent) :
    imageSubobject ((Scheme.Modules.tensorPullback f).map
      (Scheme.idealModuleProductι J.toModulesι G)) =
      imageSubobject (Scheme.idealModuleProductι (J.comap f).toModulesι
        ((Scheme.Modules.tensorPullback f).obj G)) := by
  have : G.IsQuasicoherent := hG
  have hJG : (Scheme.idealModuleProduct J.toModulesι G).IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J G).1
  let e : Scheme.Modules.tensorPullback f ≅ Scheme.Modules.pullback f :=
    CategoryTheory.Adjunction.leftAdjointUniq
      (Scheme.Modules.nonempty_tensorPullbackAdjunction f).some
      (Scheme.Modules.pullbackPushforwardAdjunction f)
  have hTG : ((Scheme.Modules.tensorPullback f).obj G).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (e.app G).symm
      (Scheme.Modules.isQuasicoherent_pullback f G)
  have hTJG : ((Scheme.Modules.tensorPullback f).obj
      (Scheme.idealModuleProduct J.toModulesι G)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (e.app (Scheme.idealModuleProduct J.toModulesι G)).symm
      (Scheme.Modules.isQuasicoherent_pullback f _)
  have hK : (Scheme.idealModuleProduct (J.comap f).toModulesι
      ((Scheme.Modules.tensorPullback f).obj G)).IsQuasicoherent :=
    (Scheme.Modules.ideal_times_quasiCoherent_affine_sections (J.comap f)
      ((Scheme.Modules.tensorPullback f).obj G)).1
  let i := (Scheme.Modules.tensorPullback f).map
    (Scheme.idealModuleProductι J.toModulesι G)
  let j := Scheme.idealModuleProductι (J.comap f).toModulesι
    ((Scheme.Modules.tensorPullback f).obj G)
  have hr (V : Y.affineOpens) (U : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
      Set.range ((image.ι i).app U.1) = Set.range ((image.ι j).app U.1) := by
    rw [Scheme.image_range_affine i U, Scheme.image_range_affine j U]
    exact modulePullbackIdealProductImage_affine_range f J G hG V U hUV
  exact le_antisymm
    (subobject_le_of_paired_affine_range f (image.ι i) (image.ι j)
      (fun V U hUV ↦ (hr V U hUV).subset))
    (subobject_le_of_paired_affine_range f (image.ι j) (image.ι i)
      (fun V U hUV ↦ (hr V U hUV).symm.subset))

end AlgebraicGeometry
