/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.Dual

import WeilConjectures.AlgebraicGeometry.SelfTorConormalDualChart
import WeilConjectures.AlgebraicGeometry.SelfExtTorDualChart

/-! # Naturality of the regular affine Koszul comparisons

Source: Stacks Project, Tags 0BQY and 062I.
(blueprint: new-s3-koszul-conormal-nested-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Restriction preserves composition, hence invertibility of both factors. -/
private theorem over_comp_isIso {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (W : X.Opens)
    [IsIso (f.over W)] [IsIso (g.over W)] : IsIso ((f ≫ g).over W) := by
  change IsIso (f.over W ≫ g.over W)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Inverses of restrictions of one morphism agree on every common subopen. -/
private theorem compatible_inverse_family
    {X : Scheme.{u}} {F T : X.Modules} {I : Type*}
    (W : I → X.Opens) (φ : T ⟶ F) (hφ : ∀ j, IsIso (φ.over (W j))) :
    ∃ c : ∀ j, F.over (W j) ≅ T.over (W j),
      ∀ (j k : I) (A : X.Opens) (hj : A ≤ W j) (hk : A ≤ W k),
        (c j).hom.val.app (op (Over.mk (homOfLE hj))) =
          (c k).hom.val.app (op (Over.mk (homOfLE hk))) := by
  let c := fun j ↦ (@asIso _ _ _ _ (φ.over (W j)) (hφ j)).symm
  refine ⟨c, ?_⟩
  intro j k A hj hk
  let gj : F.val.obj (op A) ⟶ T.val.obj (op A) :=
    (c j).hom.val.app (op (Over.mk (homOfLE hj)))
  let gk : F.val.obj (op A) ⟶ T.val.obj (op A) :=
    (c k).hom.val.app (op (Over.mk (homOfLE hk)))
  let f := φ.val.app (op A)
  have hjf : gj ≫ f = 𝟙 (F.val.obj (op A)) :=
    congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hj)))) (c j).hom_inv_id
  have hfk : f ≫ gk = 𝟙 (T.val.obj (op A)) :=
    congrArg (fun t ↦ t.val.app (op (Over.mk (homOfLE hk)))) (c k).inv_hom_id
  change gj = gk
  calc
    gj = gj ≫ (f ≫ gk) := by rw [hfk, Category.comp_id]
    _ = gk := by rw [← Category.assoc, hjf, Category.id_comp]

/-- The normalized chart comparisons respect inclusions of regular affine charts.

Source: Stacks Project, Tag 0BQY, the zero-differential Hom calculation,
and Tag 062I, the conormal basis.
(blueprint: new-s3-koszul-conormal-nested-charts).

Proof: Factor the comparison through the actual self-Tor sheaf
Q = i*H^{-n}(B[0] tensor^L B[0]), using the fixed derived tensor on Y.
The canonical exterior-to-Tor map τ has invertible dual on each regular affine
chart, by the Koszul wedge calculation (09PQ and 062I). The Ext--Tor cap pairing
likewise gives a global map ε: i*G -> dual(Q), invertible there by finite free
Koszul evaluation (0BQY). Restrict ε followed by dualMap(τ) to V to obtain one
morphism φ: T -> F whose restriction to every such chart is an isomorphism.
For each chart choose its inverse as the desired comparison F -> T.
On a common subopen the forward components are the same component f of φ.
If g₀ and g₁ are the two inverse components, their inverse identities give
g₀ = g₀ ≫ (f ≫ g₁) = (g₀ ≫ f) ≫ g₁ = g₁. This proves the stated nested
compatibility, and actually works for any common subopen without nesting.
All choices occur in the theorem proof. No chart object or definition is chosen
from an unproved existence theorem. Degree zero, degree above the generator
length, generator length zero, zero quotients and empty charts are covered by
the two comparison lemmas. No regularity on V or additional derived-category
instance is assumed. -/
theorem koszulRegularImmersion_self_ext_conormal_nested_charts
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let T := (Scheme.Modules.restrictFunctor V.ι).obj
      ((Scheme.Modules.tensorPullback i).obj G)
    let F := (Scheme.Modules.restrictFunctor V.ι).obj
      (Scheme.Modules.dual (Scheme.Modules.exteriorPower
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules) n))
    ∃ c : ∀ (U : Y.affineOpens)
      (_hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f),
        F.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)) ≅ T.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1)),
      ∀ (U₀ U₁ : Y.affineOpens)
        (h₀ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₀.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₀ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (h₁ : ∃ (m : ℕ) (f : Fin m → Γ(Y, U₁.1)),
          Ideal.span (Set.range f) = i.ker.ideal U₁ ∧
            RingTheory.Sequence.IsKoszulRegular f)
        (_h : U₀.1 ≤ U₁.1) (A : V.toScheme.Opens)
        (hA₀ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₀.1))
        (hA₁ : A ≤ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U₁.1)),
        (c U₀ h₀).hom.val.app (op (Over.mk (homOfLE hA₀))) =
          (c U₁ h₁).hom.val.app (op (Over.mk (homOfLE hA₁))) := by
  classical
  intro B S H G T F
  obtain ⟨τ, hκ⟩ := selfTor_conormal_dual_chart.{u, w} i n
  let κ := Scheme.Modules.dualMap τ
  obtain ⟨ε, hε⟩ := selfExt_tor_dual_chart.{u, w} i n
  let R := Scheme.Modules.restrictFunctor V.ι
  let φ : T ⟶ F := R.map ε ≫ R.map κ
  have hφ (U : Y.affineOpens)
      (hU : ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f) :
      IsIso (φ.over (V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.1))) := by
    have := hκ V U hU
    have := hε V U hU
    exact over_comp_isIso (R.map ε) (R.map κ) _
  let I := {U : Y.affineOpens // ∃ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    Ideal.span (Set.range f) = i.ker.ideal U ∧ RingTheory.Sequence.IsKoszulRegular f}
  obtain ⟨d, hd⟩ := compatible_inverse_family
    (fun U : I ↦ V.ι ⁻¹ᵁ (i ⁻¹ᵁ U.val.1)) φ (fun U ↦ hφ U.val U.property)
  refine ⟨fun U hU ↦ d ⟨U, hU⟩, ?_⟩
  intro U₀ U₁ h₀ h₁ _h A hA₀ hA₁
  exact hd ⟨U₀, h₀⟩ ⟨U₁, h₁⟩ A hA₀ hA₁

end AlgebraicGeometry
