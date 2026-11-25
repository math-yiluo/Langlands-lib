/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

import WeilConjectures.AlgebraicGeometry.ConductorIdealZeroIntersection
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.Modules.Dual
import WeilConjectures.AlgebraicGeometry.IdealTensorImageComparison

/-! # Additive restriction on conductor tensor sections

Source: Stacks Project, Varieties Remark 09NW and Lemma 09NX, displayed conductor equality.
(blueprint: lem-sc-conductor-sections-restriction).
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def tensorPowCongr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) :
    ∀ m : ℕ, A.tensorPow m ≅ B.tensorPow m
  | 0 => Iso.refl _
  | m + 1 => e ⊗ᵢ tensorPowCongr e m

/-- Restriction on conductor tensor sections is an additive bijection compatible with
inclusion into the ambient tensor power.

Source: Stacks Project, Varieties Remark 09NW and the displayed equality in Lemma 09NX.
(blueprint: lem-sc-conductor-sections-restriction).

Proof: use conductorIdealZeroIntersection on the component cover. Identify the image of
its adjoint ideal map with the module of the ideal comap using
ideal_tensor_image_comparison. Compare tensorPullback with the source pullback by
uniqueness of left adjoints, and use nonempty_pullback_tensorPow_iso and tensorPowCongr
to obtain the tensor-power comparison. Transport the bijection of image sheaves through it. The
ideal multiplication maps are monomorphisms because the tensor powers are invertible,
so their corestrictions to their categorical images are isomorphisms. Evaluate these
isomorphisms and the conductor restriction morphism on the top open. Their composite is
an additive bijection between the ideal tensor sections. The commutative square in the
zero-intersection theorem, transported through the comparisons, gives compatibility
with the canonical unit of tensor pullback. The canonical unit is fixed by its explicit
section formula, so the restriction used here is the stated one. -/
theorem conductor_sections_restriction {Y : Scheme.{u}} [IsReduced Y] {ι : Type v} [Finite ι]
    (C : ι → Scheme.{u}) (i : ∀ b : ι, C b ⟶ Y)
    [∀ b : ι, IsReduced (C b)] [∀ b : ι, IsClosedImmersion (i b)]
    (hcomponents : ∀ b : ι, Set.range (i b) ∈ irreducibleComponents Y)
    (hdistinct : Function.Injective fun b : ι => Set.range (i b))
    (hcover : (⋃ b : ι, Set.range (i b)) = Set.univ) (a : ι)
    {Z : Scheme.{u}} [IsReduced Z] (j : Z ⟶ Y) [IsClosedImmersion j]
    (hZ : Set.range j = ⋃ b : ι, ⋃ (_ : b ≠ a), Set.range (i b))
    (M : Y.Modules) [M.IsInvertible] (m : ℕ) :
    let N := M.tensorPow m
    let N₁ := (tensorPullback (i a)).obj N
    let adj₁ := Classical.choose (exists_tensorPullbackAdjunction (i a))
    let res₁ : Γ(N, ⊤) → Γ(N₁, ⊤) := fun t ↦ (adj₁.unit.app N).val.app (op ⊤) t
    let I := j.ker
    let I₁ := I.comap (i a)
    let μ : I.toModules ⊗ N ⟶ N := I.toModulesι ▷ N ≫ (λ_ N).hom
    let μ₁ : I₁.toModules ⊗ N₁ ⟶ N₁ := I₁.toModulesι ▷ N₁ ≫ (λ_ N₁).hom
    ∃ r : Γ(I.toModules ⊗ N, ⊤) →+ Γ(I₁.toModules ⊗ N₁, ⊤),
      Function.Bijective r ∧ ∀ s, μ₁.app ⊤ (r s) = res₁ (μ.app ⊤ s) := by
  classical
  dsimp only
  let adj := Classical.choice (nonempty_tensorPullbackAdjunction (i a))
  let c := adj.leftAdjointUniq (Classical.choose (exists_tensorPullbackAdjunction (i a)))
  let d := adj.leftAdjointUniq (pullbackPushforwardAdjunction (i a))
  obtain ⟨e₀⟩ := nonempty_pullback_tensorPow_iso (i a) M m
  let e := d.app (M.tensorPow m) ≪≫ e₀ ≪≫ tensorPowCongr (d.app M).symm m
  have hpb : ((tensorPullback (i a)).obj M).IsInvertible :=
    IsInvertible.of_iso (d.app M).symm
  obtain ⟨_, hρ⟩ := AlgebraicGeometry.conductorIdealZeroIntersection C i hcomponents
    hdistinct hcover a j hZ
  obtain ⟨ρ, hcomm, hbij⟩ := hρ M m e
  let φ := (adj.homEquiv j.ker.toModules (SheafOfModules.unit (C a).ringCatSheaf)).symm
    (j.ker.toModulesι ≫ SheafOfModules.unitToPushforwardObjUnit (i a).toRingCatSheafHom)
  let P := ((tensorPullback (i a)).obj M).tensorPow m
  let μP := Limits.image.ι φ ▷ P ≫ (λ_ P).hom
  let μ := j.ker.toModulesι ▷ M.tensorPow m ≫ (λ_ (M.tensorPow m)).hom
  have : Mono μ := inferInstance
  let p := ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)).mapIso
    (Limits.imageMonoIsoSource μ).symm).toLinearEquiv.toAddEquiv
  obtain ⟨q, hq⟩ := ideal_tensor_image_comparison (i a) j.ker (M.tensorPow m)
    (((tensorPullback (i a)).obj M).tensorPow m) adj e
  let r := q.toAddMonoidHom.comp ((ρ.app ⊤).hom.comp p.toAddMonoidHom)
  refine ⟨r, q.bijective.comp ((hbij ⊤).comp p.bijective), ?_⟩
  intro s
  refine (hq (ρ.app ⊤ (p s))).trans ?_
  have hc := congrArg (fun t ↦ t.app ⊤ (p s)) hcomm
  have hp := congrArg (fun t ↦ t.app ⊤ s) (Limits.imageMonoIsoSource_inv_ι μ)
  have hu := congrArg (fun t ↦ t.app ⊤ (μ.app ⊤ s))
    (adj.unit_leftAdjointUniq_hom_app
      (Classical.choose (exists_tensorPullbackAdjunction (i a))) (M.tensorPow m))
  change (Limits.image.ι μP).app ⊤ (ρ.app ⊤ (p s)) =
    e.hom.app ⊤ ((adj.unit.app (M.tensorPow m)).app ⊤ ((Limits.image.ι μ).app ⊤ (p s))) at hc
  change (Limits.image.ι μ).app ⊤ (p s) = μ.app ⊤ s at hp
  change (c.app (M.tensorPow m)).hom.app ⊤
    ((adj.unit.app (M.tensorPow m)).app ⊤ (μ.app ⊤ s)) = _ at hu
  rw [hp] at hc
  have hi := congrArg (fun t ↦ e.inv.app ⊤ t) hc
  have hei := congrArg (fun t ↦ t.app ⊤
    ((adj.unit.app (M.tensorPow m)).app ⊤ (μ.app ⊤ s))) e.hom_inv_id
  change e.inv.app ⊤ (e.hom.app ⊤ _) = _ at hei
  rw [hei] at hi
  exact (congrArg (fun t ↦ (c.app (M.tensorPow m)).hom.app ⊤ t) hi).trans hu

end AlgebraicGeometry.Scheme.Modules
