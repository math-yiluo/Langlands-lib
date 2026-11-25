/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorKernelSectionProduct
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi

/-! # Homogeneous action has the expected degree support

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-tensor-coefficient-action-support).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem unit_local_lift {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (M : X.Modules) (U : X.Opens)
    (s : Γ((pushforward j).obj ((tensorPullback j).obj M), U)) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens) (hV : V ≤ U),
      (∃ t : Γ(M, V), (tensorGradedUnit j M).app V t =
        ((pushforward j).obj ((tensorPullback j).obj M)).val.map (homOfLE hV).op s) ∧
      x ∈ V := by
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  have : Epi (adj.unit.app M) := closedImmersion_unit_epi j M
  have : Epi (tensorGradedUnit j M) := by
    unfold tensorGradedUnit
    rw [← adj.unit_leftAdjointUniq_hom_app adj' M]
    exact epi_comp _ _
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : Epi (F.map (tensorGradedUnit j M)) := inferInstance
  exact (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map (tensorGradedUnit j M).val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi
      (F.map (tensorGradedUnit j M))).mpr inferInstance) U s x hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homogeneous_action_support {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (T : TensorGradedPresentation j L) (a d : ℕ)
    (s : Γ((tensorPullback j).obj (L.tensorPow a), ⊤))
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
    ∃ v : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
        kernel (tensorGradedUnit j (L.tensorPow (a + d))),
      T.k d ≫ (μ ((T.c a).app ⊤ s)).asHom = v ≫ T.k (a + d) := by
  let r := T.k d ≫ (μ ((T.c a).app ⊤ s)).asHom
  let π := (T.degree (a + d)).τ₁
  refine ⟨r ≫ π, ?_⟩
  change r = (r ≫ π) ≫ T.k (a + d)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext y
  apply (AlgebraicGeometry.Scheme.Modules.isSheaf (show X.Modules from T.I)).section_ext
  intro x hx
  obtain ⟨V, hV, ⟨t, ht⟩, hxV⟩ :=
    unit_local_lift j (L.tensorPow a) U.unop
      (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
        (homOfLE le_top).op s) x hx
  refine ⟨V, hV, hxV, ?_⟩
  let yV := (kernel (tensorGradedUnit j (L.tensorPow d))).val.map (homOfLE hV).op y
  obtain ⟨z, hz⟩ := tensorKernel_section_product j L a d V t yV
  have ht' : (tensorGradedUnit j (L.tensorPow a)).app V t =
      (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
        (homOfLE le_top).op s) := by
    rw [ht, ← PresheafOfModules.map_comp_apply]
    rfl
  have hbq := congrArg (fun φ ↦ φ.app V t) (T.b_quotient a)
  change T.p.right.hom.app (op V) ((T.b a).app V t) =
    (T.c a).app V ((tensorGradedUnit j (L.tensorPow a)).app V t) at hbq
  have hg : T.C.right.obj.map (homOfLE le_top).op ((T.c a).app ⊤ s) =
      T.p.right.hom.app (op V) ((T.b a).app V t) := by
    rw [hbq, ht']
    exact (Hom.app_presheaf_map (T.c a) (homOfLE le_top) s).symm
  have hki (e : ℕ) (w : Γ(kernel (tensorGradedUnit j (L.tensorPow e)), V)) :
      T.i.val.app (op V) ((T.k e).app V w) =
        (T.b e).app V ((kernel.ι (tensorGradedUnit j (L.tensorPow e))).app V w) :=
    congrArg (fun φ ↦ φ.app V w) (T.k_inclusion e)
  have haction : r.val.app (op V) yV = (T.k (a + d)).app V z := by
    have : Mono T.i := T.shortExact.mono_f
    have hinj := (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i)).mp inferInstance
    apply hinj
    change T.i.val.app (op V) (r.val.app (op V) yV) = T.i.val.app (op V) ((T.k (a + d)).app V z)
    change T.i.val.app (op V) ((μ ((T.c a).app ⊤ s)).asHom.val.app (op V) ((T.k d).app V yV)) = _
    rw [hglobal, hg]
    have hl := hlocal V ((T.b a).app V t) ((T.k d).app V yV)
    dsimp only [id] at hl
    rw [hl, hki d yV, hki (a + d) z, hz]
    exact T.b_multiply V a d t
      ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V yV)
  have hπ := congrArg (fun φ ↦ φ.app V z) (T.k_projection (a + d))
  change π.val.app (op V) ((T.k (a + d)).app V z) = z at hπ
  change T.I.val.map (homOfLE hV).op (r.val.app U y) =
    T.I.val.map (homOfLE hV).op (((r ≫ π) ≫ T.k (a + d)).val.app U y)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  change r.val.app (op V) yV = (T.k (a + d)).app V (π.val.app (op V) (r.val.app (op V) yV))
  rw [haction, hπ]

/-- A homogeneous quotient section of degree n carries the d-th ideal summand
into the (n+d)-th ideal summand. No coefficient transport or projection is asserted.
Source: Stacks Project, Tag 09MS, graded ideal sequence; Tag 0B8S, quotient action.
(blueprint: lem-sc-tensor-coefficient-action-support).
Proof: Set r to the degree-d inclusion followed by the given global action, and
set v to r followed by the degree-(n+d) projection. Locally lift the homogeneous
quotient section along the epimorphic tensor-pullback unit. The ideal-kernel
comparison shows that multiplying this lift by a degree-d kernel section lies in
the degree-(n+d) kernel. The identities b_quotient, k_inclusion, b_multiply, hlocal
and hglobal identify its image in I with r; cancel the monomorphism i to obtain
this equality. The identity k_projection then gives r = v followed by k_(n+d)
locally. Naturality and sheaf separation give the equality globally. Specialize
to the section defining tensorGradedSection and simplify n*(0+1) to n. The argument
uses no independence of lifts or gluing of newly chosen maps; v was explicit from
the start. Tensor unit coherence covers zero degrees and empty opens. -/
theorem tensorGradedCoefficient_action_support {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (d : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    ∃ v : kernel (tensorGradedUnit j (L.tensorPow d)) ⟶
        kernel (tensorGradedUnit j (L.tensorPow (n + d))),
      T.k d ≫ (μ (tensorGradedSection T D 0 (tensorPowSection f 1))).asHom =
        v ≫ T.k (n + d) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have _ := hD
    have _ := hrestrict
    have h := homogeneous_action_support j L T (n * (0 + 1)) d
      ((tensorPowSection f 1 ≫ (D.a 0).inv).app ⊤ (1 : Γ(Z, ⊤)))
      σ μ hlocal hglobal
    unfold tensorGradedSection
    generalize he : n * (0 + 1) + d = b at h
    have hb : b = n + d := by omega
    rw [hb] at h
    exact h

end
end AlgebraicGeometry.Scheme.Modules
