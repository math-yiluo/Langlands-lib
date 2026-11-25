/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Mathlib.Topology.Sheaves.LocallySurjective

/-! # Degree support of the quotient action

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-graded-quotient-action-homogeneous).
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

/-- A homogeneous quotient section sends each ideal summand into the summand
whose degree is increased by the degree of that section. This assertion uses no
canonical coefficient comparison and no output projection.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum;
Tag 0B8S, cohomology-lemma-boundary-derivation-over-cup-product, first proof paragraph.
(blueprint: lem-sc-tensor-graded-quotient-action-homogeneous).
Proof: Use the epi closed-immersion unit to lift s locally to t in L^a.
For a degree-d kernel section y, b_quotient identifies b_a(t) as a lift of
c_a(s). The equations hglobal, hlocal, k_inclusion and b_multiply identify
i of the acted-on section with b_(a+d)(z), where z is the tensor product of t
and kernel.ι(y) under tensorPowAddIso. Apply p. Since p i=0, b_quotient gives
c_(a+d)(unit(z))=0. The left inverse c_projection makes c_(a+d) mono, so
unit(z)=0. Sections preserve kernels, giving z' in the degree-(a+d) kernel
with kernel.ι(z')=z. By k_inclusion and monicity of i, the acted-on section
is k_(a+d)(z'). Define v globally as k_d followed by the given action and
then degree_(d+a).tau1. The left inverse k_projection identifies its value
locally with z', so k_d;action=v;k_(d+a) locally. Naturality of the global
action and sheaf separation prove this equality globally. This proof never
chooses a global lift and does not require restriction compatibility of sigma.
It works for a=0 or d=0 and for the empty open; if s=0 or the ideal is zero,
the same formula for v is the zero map. -/
theorem tensorGradedQuotientAction_homogeneous {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible]
    (T : TensorGradedPresentation j L) (a d : ℕ)
    (s : Γ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a)), ⊤))
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
        kernel (tensorGradedUnit j (L.tensorPow (d + a))),
      T.k d ≫ (μ ((T.c a).app ⊤ s)).asHom = v ≫ T.k (d + a)  := by
  classical
  let η := tensorGradedUnit j (L.tensorPow a)
  let g := (T.c a).app ⊤ s
  let w := μ g
  let v := T.k d ≫ (w).asHom ≫ (T.degree (d + a)).τ₁
  refine ⟨v, ?_⟩
  have hi : Mono T.i := T.shortExact.mono_f
  have hc : Mono (T.c (a + d)) := mono_of_mono_fac (T.c_projection (a + d))
  obtain ⟨_, hη, _⟩ := closedImmersion_unit_quotient j
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction j)
  let adj' := Classical.choose (exists_tensorPullbackAdjunction j)
  have he : Epi (adj.unit.app (L.tensorPow a)) := (hη _).1
  have : Epi η := by
    have eq : adj.unit.app (L.tensorPow a) ≫
        (pushforward j).map ((adj.leftAdjointUniq adj').hom.app (L.tensorPow a)) = η :=
      Adjunction.unit_leftAdjointUniq_hom_app adj adj' _
    rw [← eq]
    infer_instance
  let S := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : Epi (S.map η) := inferInstance
  have hl := (TopCat.Presheaf.isLocallySurjective_iff
    ((PresheafOfModules.toPresheaf _).map η.val)).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi (S.map η)).mpr inferInstance)
  have hcalc (V : X.Opens) (t : Γ(L.tensorPow a, V))
      (ht : η.app V t =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE le_top).op s)
      (y : Γ(kernel (tensorGradedUnit j (L.tensorPow d)), V)) :
      ∃ z : Γ(kernel (tensorGradedUnit j (L.tensorPow (d + a))), V),
        w.asHom.val.app (op V) ((T.k d).app V y) = (T.k (d + a)).app V z := by
    rw [Nat.add_comm d a]
    let z := (L.tensorPowAddIso a d).inv.app V
      (tmulSection t ((kernel.ι (tensorGradedUnit j (L.tensorPow d))).app V y))
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
    have ha : T.i.val.app (op V) (w.asHom.val.app (op V) ((T.k d).app V y)) =
        (T.b (a + d)).app V z := by
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
    have hz : (tensorGradedUnit j (L.tensorPow (a + d))).app V z = 0 := by
      have hzero : T.p.right.hom.app (op V) ((T.b (a + d)).app V z) = 0 := by
        rw [← ha]
        exact congrArg (fun f ↦ f.val.app (op V)
          (w.asHom.val.app (op V) ((T.k d).app V y))) T.hw
      have hb := congrArg (fun f ↦ f.app V z) (T.b_quotient (a + d))
      change T.p.right.hom.app (op V) ((T.b (a + d)).app V z) =
        (T.c (a + d)).app V
          ((tensorGradedUnit j (L.tensorPow (a + d))).app V z) at hb
      have hinj := (ModuleCat.mono_iff_injective
        ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map (T.c (a + d)))).mp
        (inferInstance : Mono
          ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map (T.c (a + d))))
      apply hinj
      change (T.c (a + d)).app V _ = (T.c (a + d)).app V 0
      rw [map_zero, ← hb, hzero]
    obtain ⟨z', hz'⟩ := (Set.ext_iff.mp
      (range_map_kernelι V (tensorGradedUnit j (L.tensorPow (a + d)))) z).mpr hz
    change (kernel.ι (tensorGradedUnit j (L.tensorPow (a + d)))).app V z' = z at hz'
    have hki' := congrArg (fun f ↦ f.app V z') (T.k_inclusion (a + d))
    change T.i.val.app (op V) ((T.k (a + d)).app V z') =
      (T.b (a + d)).app V
        ((kernel.ι (tensorGradedUnit j (L.tensorPow (a + d)))).app V z') at hki'
    rw [hz'] at hki'
    have hinj := (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i)).mp
      (inferInstance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op V)).map T.i))
    have hres : w.asHom.val.app (op V) ((T.k d).app V y) = (T.k (a + d)).app V z' :=
      hinj (ha.trans hki'.symm)
    exact ⟨z', hres⟩
  ext U y
  choose V hVU hlt hxV using fun x : U ↦ hl U
    (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
      (homOfLE le_top).op s) x.val x.property
  choose t ht using hlt
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.I.val.presheaf, T.I.isSheaf⟩ V U
    (fun x ↦ homOfLE (hVU x)) ?_ _ _ ?_
  · intro x hx
    exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  · intro x
    have ht' : η.app (V x) (t x) =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE le_top).op s := by
      have htt := ht x
      change η.app (V x) (t x) =
        ((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
          (homOfLE (hVU x)).op
          (((pushforward j).obj ((tensorPullback j).obj (L.tensorPow a))).val.map
            (homOfLE le_top).op s) at htt
      rw [htt, ← PresheafOfModules.map_comp_apply]
      rfl
    let y' := (kernel (tensorGradedUnit j (L.tensorPow d))).val.map
      (homOfLE (hVU x)).op y
    obtain ⟨z, hz⟩ := hcalc (V x) (t x) ht' y'
    have hproj := congrArg (fun f ↦ f.app (V x) z) (T.k_projection (d + a))
    change (T.degree (d + a)).τ₁.val.app (op (V x)) ((T.k (d + a)).app (V x) z) = z at hproj
    change T.I.val.map (homOfLE (hVU x)).op
        ((T.k d ≫ (w).asHom).val.app (op U) y) =
      T.I.val.map (homOfLE (hVU x)).op
        ((v ≫ T.k (d + a)).val.app (op U) y)
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    change w.asHom.val.app (op (V x)) ((T.k d).app (V x) y') =
      (T.k (d + a)).app (V x)
        ((T.degree (d + a)).τ₁.val.app (op (V x))
          (w.asHom.val.app (op (V x)) ((T.k d).app (V x) y')))
    rw [hz, hproj]

end
end AlgebraicGeometry.Scheme.Modules
