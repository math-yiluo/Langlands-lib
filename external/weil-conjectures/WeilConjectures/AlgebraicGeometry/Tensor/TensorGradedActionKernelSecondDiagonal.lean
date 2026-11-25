/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorBoundaryKernelMapNaturality
import WeilConjectures.AlgebraicGeometry.Tensor.TensorBoundaryKernelMapLocalMultiplication
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # The canonical tensor action on the surviving ideal summand

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-graded-action-kernel-second-diagonal).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- On the degree-n summand, homogeneous quotient multiplication is the
canonical transported tensor-by-x map followed by the output inclusion.
This statement concerns one summand only, before applying any degree projection.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum;
Tag 0B8S, cohomology-lemma-boundary-derivation-over-cup-product, first proof paragraph.
(blueprint: lem-sc-tensor-graded-action-kernel-second-diagonal).
Proof: Substitute hD and locally lift the canonically transported x(1)
through the epi degree-n(e+1) unit. Use the local kernel-map multiplication
formula to compute the target kernel inclusion as the tensorPowAddIso product
of this lift with the input kernel inclusion. Apply k_inclusion at the output;
the arithmetic equality n(e+1)+n=n(e+2) commutes with b by equality elimination.
On the action side, hglobal, hlocal, b_quotient and k_inclusion compute the
included action as the product of the two homogeneous sections, and b_multiply
identifies it with exactly the preceding tensor product. Cancel the mono i.
Naturality of both global morphisms and sheaf separation glue the equality
on the local lifting cover. This uses only the degree-n summand; when n=0
the same calculation uses degree-zero tensor unitors and needs no distinct
degree assumption. Zero sections, zero ideals and empty opens are included. -/
theorem tensorGradedAction_kernel_second_diagonal {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
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
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    T.k (n * (0 + 1)) ≫ (μ (tensorGradedSection T D e x)).asHom =
      tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x) ≫
        T.k (n * ((e + 1) + 1))  := by
  classical
  subst D
  dsimp only
  let a := n * (e + 1)
  let d := n * (0 + 1)
  let b := n * ((e + 1) + 1)
  let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
  let m := tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x)
  let s := (x ≫ (boundarySectionDegreeIso j L n e).inv).app ⊤ (1 : Γ(Z, ⊤))
  let η := tensorGradedUnit j (L.tensorPow a)
  let g := (T.c a).app ⊤ s
  let w := (μ g).asHom
  change T.k d ≫ w = m ≫ T.k b
  have hi : Mono T.i := T.shortExact.mono_f
  obtain ⟨_, hη, _⟩ := closedImmersion_unit_quotient j
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  have he : Epi (adj.unit.app (L.tensorPow (n * (e + 1)))) := (hη _).1
  have : Epi η := by
    have eq : adj.unit.app (L.tensorPow (n * (e + 1))) ≫
        (pushforward j).map ((adj.leftAdjointUniq adj').hom.app (L.tensorPow (n * (e + 1)))) = η :=
      Adjunction.unit_leftAdjointUniq_hom_app adj adj' _
    rw [← eq]
    infer_instance
  let S := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : Epi (S.map η) := inferInstance
  have hl := (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map η.val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (S.map η)).mpr inferInstance)
  have hdeg : a + d = b := by
    simp only [a, d, b, Nat.mul_add, Nat.mul_one, Nat.mul_zero, Nat.zero_add]
  have hcast (r q : ℕ) (h : r = q) (U : X.Opens) (z : Γ(L.tensorPow r, U)) :
      (T.b q).app U ((eqToHom (congrArg L.tensorPow h)).app U z) =
        (T.b r).app U z := by
    subst q
    rfl
  have hcalc (V : X.Opens) (t : Γ(L.tensorPow a, V))
      (ht : η.app V t =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE le_top).op s)
      (y : Γ(kernel (tensorGradedUnit j (L.tensorPow d)), V)) :
      w.val.app (op V) ((T.k d).app V y) = (T.k b).app V (m.app V y) := by
    have hp : T.p.right.hom.app (op V) ((T.b a).app V t) =
        T.C.right.obj.map (homOfLE le_top).op g := by
      have hb := congrArg (fun f ↦ f.app V t) (T.b_quotient a)
      change T.p.right.hom.app (op V) ((T.b a).app V t) =
        (T.c a).app V (η.app V t) at hb
      rw [hb, ht]
      exact Hom.app_presheaf_map (T.c a) (homOfLE le_top) s
    have hki := congrArg (fun f ↦ f.app V y) (T.k_inclusion d)
    change T.i.val.app (op V) ((T.k d).app V y) =
      (T.b d).app V ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V y) at hki
    have hko := congrArg (fun f ↦ f.app V (m.app V y)) (T.k_inclusion b)
    change T.i.val.app (op V) ((T.k b).app V (m.app V y)) =
      (T.b b).app V
        ((kernel.ι (tensorGradedUnit j (L.tensorPow b))).app V (m.app V y)) at hko
    have hc := tensorBoundaryKernelMap_local_multiplication j L hI n e x V t ht y
    change (kernel.ι (tensorGradedUnit j (L.tensorPow b))).app V (m.app V y) =
      (eqToHom (congrArg L.tensorPow hdeg)).app V
        ((L.tensorPowAddIso a d).inv.app V
          (tmulSection t ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V y))) at hc
    have hinj := (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i)).mp
      (inferInstance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i))
    apply hinj
    change T.i.val.app (op V) (w.val.app (op V) ((T.k d).app V y)) =
      T.i.val.app (op V) ((T.k b).app V (m.app V y))
    rw [hko, hc, hcast (a + d) b hdeg]
    change T.i.val.app (op V) ((μ g).asHom.val.app (op V) ((T.k d).app V y)) = _
    rw [hglobal, ← hp]
    have hh := hlocal V ((T.b a).app V t) ((T.k d).app V y)
    change T.i.val.app (op V) (σ V (T.p.right.hom.app (op V) ((T.b a).app V t))
      ((T.k d).app V y)) =
        @id (T.B.right.obj.obj (op V)) ((T.b a).app V t) *
          @id (T.B.right.obj.obj (op V))
            (T.i.val.app (op V) ((T.k d).app V y)) at hh
    rw [hh, hki]
    exact T.b_multiply V a d t _
  ext U y
  choose V hVU hlt hxV using fun z : U ↦ hl U
    (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
      (homOfLE le_top).op s) z.val z.property
  choose t ht using hlt
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.I.val.presheaf, T.I.isSheaf⟩ V U
    (fun z ↦ homOfLE (hVU z)) ?_ _ _ ?_
  · intro z hz
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩
  · intro z
    have ht' : η.app (V z) (t z) =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE le_top).op s := by
      have htt := ht z
      change η.app (V z) (t z) =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE (hVU z)).op
          (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
            (homOfLE le_top).op s) at htt
      rw [htt, ← PresheafOfModules.map_comp_apply]
      rfl
    change T.I.val.map (homOfLE (hVU z)).op ((T.k d ≫ w).val.app (op U) y) =
      T.I.val.map (homOfLE (hVU z)).op ((m ≫ T.k b).val.app (op U) y)
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    exact hcalc (V z) (t z) ht' _

end
end AlgebraicGeometry.Scheme.Modules
