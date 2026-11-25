/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.Tensor.TensorIdealSectionLocalMultiplication
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Homogeneous quotient multiplication on the degree kernels

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-homogeneous-kernel-action).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Multiply an ideal tensor by a section of a pulled-back tensor power.
All maps are explicit; the equality h merely identifies the output degree.
Source: Stacks Project, Tag 09MS, multiplication in the graded ideal sequence.
(blueprint: lem-sc-tensor-homogeneous-kernel-action). -/
def tensorIdealSectionMultiply {X Z : Scheme.{u}} (j : Z ⟶ X) (L : X.Modules)
    (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a)) :
    (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d) ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow t) :=
  (ρ_ _).inv ≫ ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow d)) ◁ s ≫
    (boundaryPullbackTensorIso j (j.ker.toModules ⊗ L.tensorPow d)
      (L.tensorPow a)).inv ≫
    (tensorPullback j).map ((α_ _ _ _).hom ≫
      j.ker.toModules ◁ (L.tensorPowAddIso d a).inv ≫
      j.ker.toModules ◁ eqToHom (congrArg L.tensorPow h))

/-- Transport homogeneous ideal multiplication to the kernels using their canonical
inclusion comparisons and the unit on the annihilated ideal tensor.
Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-tensor-homogeneous-kernel-action). -/
def tensorHomogeneousKernelMap {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a)) :
    kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
      kernel (tensorGradedUnit j (L.tensorPow t)) := by
  letI := square_zero_ideal_tensor_unit_isIso j L hI t
  exact (boundaryIdealKernelIso j (L.tensorPow d)).inv ≫
    (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow d) ≫
    (pushforward j).map (tensorIdealSectionMultiply j L a d t h s) ≫
    inv ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow t)) ≫
    (boundaryIdealKernelIso j (L.tensorPow t)).hom

/-- The raw quotient action on a homogeneous kernel is ideal tensor multiplication.
This statement has arbitrary degrees and no coefficient-degree comparison, block size,
or cohomology data.
Source: Stacks Project, Tag 09MS, graded ideal sequence; Tag 0B8S, quotient action.
(blueprint: lem-sc-tensor-homogeneous-kernel-action).
Proof: The closed-immersion unit on L^a is an epimorphism, so lift the
restriction of s(1) locally to x in L^a. The equation b_quotient identifies
c_a(s(1)) with p(b_a(x)) on that cover. Apply hglobal and hlocal to compute the
quotient action after the monic inclusion i. The source k_inclusion equation
and commutativity in B express this as b_d(kernel inclusion y) times b_a(x).
Apply b_multiply in degrees d and a. The proved local ideal-tensor multiplication
formula computes the target kernel inclusion of tensorHomogeneousKernelMap as
exactly the degree-d+a tensor product of kernel inclusion y with x, transported
along h. Apply the target k_inclusion and eliminate the degree transport by
equality induction. Cancel i on sections. Naturality of both global morphisms
and sheaf separation on the local lifting cover give the equality globally.
No global lift or restriction law for arbitrary quotient sections is needed;
hglobal supplies the restrictions of the one global quotient section used.
Zero degrees and empty opens use the same unitors and separation argument. -/
theorem tensorHomogeneousKernel_action {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (T : TensorGradedPresentation j L) (a d t : ℕ) (h : d + a = t)
    (s : 𝟙_ Z.Modules ⟶ (tensorPullback j).obj (L.tensorPow a))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    T.k d ≫ (μ ((T.c a).app ⊤ (s.app ⊤ (1 : Γ(Z, ⊤))))).asHom =
      tensorHomogeneousKernelMap j L hI a d t h s ≫ T.k t := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    let m := tensorHomogeneousKernelMap j L hI a d t h s
    let s₀ := s.app ⊤ (1 : Γ(Z, ⊤))
    let η := tensorGradedUnit j (L.tensorPow a)
    let g := (T.c a).app ⊤ s₀
    let w := (μ g).asHom
    change T.k d ≫ w = m ≫ T.k t
    have hi : Mono T.i := T.shortExact.mono_f
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
    let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
    have : Epi (adj.unit.app (L.tensorPow a)) := closedImmersion_unit_epi j _
    have : Epi η := by
      unfold η tensorGradedUnit
      rw [← adj.unit_leftAdjointUniq_hom_app adj' (L.tensorPow a)]
      exact epi_comp _ _
    let S := SheafOfModules.toSheaf.{u} X.ringCatSheaf
    have : Epi (S.map η) := inferInstance
    have hl := (TopCat.Presheaf.isLocallySurjective_iff
      ((PresheafOfModules.toPresheaf _).map η.val)).mp
      ((TopCat.Sheaf.isLocallySurjective_iff_epi (S.map η)).mpr inferInstance)
    have hdeg : d + a = t := h
    have hcast (r q : ℕ) (h : r = q) (U : X.Opens) (z : Γ(L.tensorPow r, U)) :
        (T.b q).app U ((eqToHom (congrArg L.tensorPow h)).app U z) =
          (T.b r).app U z := by
      subst q
      rfl
    have hcalc (V : X.Opens) (x : Γ(L.tensorPow a, V))
        (ht : η.app V x =
          ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
            (homOfLE le_top).op s₀)
        (y : Γ(kernel (tensorGradedUnit j (L.tensorPow d)), V)) :
        w.val.app (op V) ((T.k d).app V y) = (T.k t).app V (m.app V y) := by
      have hp : T.p.right.hom.app (op V) ((T.b a).app V x) =
          T.C.right.obj.map (homOfLE le_top).op g := by
        have hb := congrArg (fun f ↦ f.app V x) (T.b_quotient a)
        change T.p.right.hom.app (op V) ((T.b a).app V x) =
          (T.c a).app V (η.app V x) at hb
        rw [hb, ht]
        exact Hom.app_presheaf_map (T.c a) (homOfLE le_top) s₀
      have hki := congrArg (fun f ↦ f.app V y) (T.k_inclusion d)
      change T.i.val.app (op V) ((T.k d).app V y) =
        (T.b d).app V ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V y) at hki
      have hko := congrArg (fun f ↦ f.app V (m.app V y)) (T.k_inclusion t)
      change T.i.val.app (op V) ((T.k t).app V (m.app V y)) =
        (T.b t).app V
          ((kernel.ι (tensorGradedUnit j (L.tensorPow t))).app V (m.app V y)) at hko
      have hc := tensorIdealSection_local_multiplication j L hI a d t h s V x ht y
      change (kernel.ι (tensorGradedUnit j (L.tensorPow t))).app V (m.app V y) =
        (eqToHom (congrArg L.tensorPow hdeg)).app V
          ((L.tensorPowAddIso d a).inv.app V
            (tmulSection ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V y) x)) at hc
      have hinj := (ModuleCat.mono_iff_injective
        ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i)).mp
        (inferInstance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i))
      apply hinj
      change T.i.val.app (op V) (w.val.app (op V) ((T.k d).app V y)) =
        T.i.val.app (op V) ((T.k t).app V (m.app V y))
      rw [hko, hc, hcast (d + a) t hdeg]
      change T.i.val.app (op V) ((μ g).asHom.val.app (op V) ((T.k d).app V y)) = _
      rw [hglobal, ← hp]
      have hh := hlocal V ((T.b a).app V x) ((T.k d).app V y)
      change T.i.val.app (op V) (σ V (T.p.right.hom.app (op V) ((T.b a).app V x))
        ((T.k d).app V y)) =
          @id (T.B.right.obj.obj (op V)) ((T.b a).app V x) *
            @id (T.B.right.obj.obj (op V))
              (T.i.val.app (op V) ((T.k d).app V y)) at hh
      rw [hh, hki]
      rw [mul_comm]
      exact T.b_multiply V d a _ x
    ext U y
    choose V hVU hlt hxV using fun z : U ↦ hl U
      (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
        (homOfLE le_top).op s₀) z.val z.property
    choose x ht using hlt
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.I.val.presheaf, T.I.isSheaf⟩ V U
      (fun z ↦ homOfLE (hVU z)) ?_ _ _ ?_
    · intro z hz
      exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩
    · intro z
      have ht' : η.app (V z) (x z) =
          ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
            (homOfLE le_top).op s₀ := by
        have htt := ht z
        change η.app (V z) (x z) =
          ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
            (homOfLE (hVU z)).op
            (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
              (homOfLE le_top).op s₀) at htt
        rw [htt, ← PresheafOfModules.map_comp_apply]
        rfl
      change T.I.val.map (homOfLE (hVU z)).op ((T.k d ≫ w).val.app (op U) y) =
        T.I.val.map (homOfLE (hVU z)).op ((m ≫ T.k t).val.app (op U) y)
      rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
      exact hcalc (V z) (x z) ht' _

end
end AlgebraicGeometry.Scheme.Modules
