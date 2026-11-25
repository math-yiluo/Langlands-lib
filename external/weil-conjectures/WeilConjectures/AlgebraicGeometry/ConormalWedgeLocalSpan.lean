/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Local generation of conormal wedges by affine ideal sections

Source: Stacks Project, Tags 01R3 and 0096, and affine module localization.
(blueprint: new-e3-conormal-wedge-local-span). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
open Scheme.Modules (wedge)

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_section_map {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (f : V ⟶ U) (a : Fin n → M.val.obj (op U)) :
    (Scheme.Modules.exteriorPower M n).val.map f.op
        (wedge (M := M) (r := n) (U := U) a) =
      wedge (M := M) (r := n) (U := V) (fun j ↦ M.val.map f.op (a j)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  have hn := PresheafOfModules.naturality_apply η f.op
    (exteriorPower.ιMulti (X.presheaf.obj (op U)) n a)
  have hr := (_root_.PresheafOfModules.exteriorPower_map_ιMulti (R := _) M.val n f.op) a
  exact hn.symm.trans (congrArg (η.app (op V)) hr)

set_option backward.isDefEq.respectTransparency false in
private theorem exterior_section_smul {X : Scheme.{u}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) (r : Fin n → X.presheaf.obj (op U))
    (a : Fin n → M.val.obj (op U)) :
    wedge (M := M) (r := n) (U := U) (fun j ↦ r j • a j) =
      (∏ j, r j) • wedge (M := M) (r := n) (U := U) a := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 X.ringCatSheaf.obj)).unit.app (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)
  change η.app (op U) (exteriorPower.ιMulti (X.presheaf.obj (op U)) n
    (fun j ↦ r j • a j)) = _
  rw [AlternatingMap.map_smul_univ, (η.app (op U)).hom.map_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A pure wedge of local conormal sections is locally in the span of wedges of the
pullback-unit images of ideal sections on a fixed ambient affine chart.
Source: Stacks Project, Tags 01R3 and 0096, and affine module localization.
(blueprint: new-e3-conormal-wedge-local-span).

Proof: The closed inverse image of V = Spec A is affine with coordinate ring A/I.
The conormal sections theorem, including its unit equation, identifies N on this chart
with the associated module I/I² and the unit images with classes of elements of I.
Choose a principal neighbourhood of x inside W in this closed affine chart. Each of
the finitely many sections a(j) is a fraction in the localization of I/I² on a smaller
principal neighbourhood. Refine the finitely many neighbourhoods to a common principal
neighbourhood W' and lift every numerator to I, using surjectivity of I → I/I².
Thus each restricted a(j) is a finite linear combination of restrictions of unit images
of ideal sections on V, with coefficients in O_Z(W'). Expand their wedge using
multilinearity; each resulting summand is a scalar multiple of a wedge of those unit
images. The exterior sheaf restriction and sheafification unit preserve these wedges
and scalar combinations. This proves the asserted span membership. For n=0 the empty
wedge is itself one of the generators and W'=W works. A point in W rules out the empty
chart, while a zero conormal module causes no difficulty. No finite generation of I,
regular immersion hypothesis, or general-section sheafification argument is used. -/
theorem conormal_wedge_mem_span_locally
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] (n : ℕ)
    (V : Y.affineOpens) (W : Z.Opens) (hW : W ≤ i ⁻¹ᵁ V.1)
    (a : Fin n → ((Scheme.Modules.tensorPullback i).obj i.ker.toModules).val.obj (op W))
    (x : Z) (hx : x ∈ W) :
    let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
    let E := Scheme.Modules.exteriorPower N n
    let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules
    ∃ (W' : Z.Opens) (hW' : W' ≤ W), x ∈ W' ∧
      E.val.map (homOfLE hW').op (wedge (M := N) (r := n) (U := W) a) ∈
        Submodule.span (Z.presheaf.obj (op W'))
          (Set.range (fun b : Fin n → i.ker.toModules.val.obj (op V.1) ↦
            wedge (M := N) (r := n) (U := W')
              (fun j ↦ N.val.map (homOfLE (hW'.trans hW)).op
                (η.val.app (op V.1) (b j))))) := by
  classical
  dsimp only
  let N := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let _ (P : _root_.PresheafOfModules.{u} Z.ringCatSheaf.obj)
      {U V : Z.Opens} (g : V ⟶ U) :
      Module Γ(Z, V)
        ((ModuleCat.restrictScalars (Z.ringCatSheaf.obj.map g.op).hom).obj
          (P.obj (op V))) :=
    inferInstanceAs (Module Γ(Z, V) (P.obj (op V)))
  let E := Scheme.Modules.exteriorPower N n
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
    i.ker.toModules
  have hqc := (Scheme.Modules.affine_conormal_sections.{u, u} i).1
  let : N.IsQuasicoherent := hqc
  let O := i ⁻¹ᵁ V.1
  have hO : IsAffineOpen O := V.2.preimage i
  obtain ⟨f, hfW, hxf⟩ := hO.exists_basicOpen_le ⟨x, hx⟩ (hW hx)
  let D := Z.basicOpen f
  have hDO : D ≤ O := Z.basicOpen_le f
  have hglob : Function.Surjective (η.val.app (op V.1)) := by
    obtain ⟨e, he⟩ := (Scheme.Modules.affine_conormal_sections.{u, u} i).2
      V (Γ(Y, V.1) : Type u) (RingEquiv.refl _) (i.ker.ideal V) (by
        simp)
    intro q
    obtain ⟨a, ha⟩ := (i.ker.ideal V).toCotangent_surjective (e.symm q)
    have ha' : (a : Γ(Y, V.1)) ∈ Set.range (i.ker.toModulesι.app V.1) := by
      rw [i.ker.range_toModulesι_app V]
      exact a.property
    obtain ⟨b, hb⟩ := ha' 
    refine ⟨b, ?_⟩
    exact (he a b hb).symm.trans ((congrArg e ha).trans (e.apply_symm_apply q))
  have hden : ∀ j : Fin n, ∃ (m : ℕ) (t : N.val.obj (op O)),
      N.val.map (homOfLE hDO).op t =
        Z.presheaf.map (homOfLE hDO).op f ^ m •
          N.val.map (homOfLE hfW).op (a j) := by
    intro j
    exact Scheme.Modules.exists_map_eq_pow_smul_of_isAffineOpen N hO f
      (N.val.map (homOfLE hfW).op (a j))
  choose m t ht using hden
  choose b hb using fun j ↦ hglob (t j)
  let u : Fin n → (Z.presheaf.obj (op D))ˣ :=
    fun j ↦ (Z.toRingedSpace.isUnit_res_basicOpen f).unit ^ m j
  have hu (j : Fin n) : (u j : Z.presheaf.obj (op D)) =
      Z.presheaf.map (homOfLE hDO).op f ^ m j := by
    simp only [u, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rfl
  have hfac (j : Fin n) : N.val.map (homOfLE hfW).op (a j) =
      ((u j)⁻¹ : (Z.presheaf.obj (op D))ˣ) •
        N.val.map (homOfLE hDO).op (η.val.app (op V.1) (b j)) := by
    rw [hb j, ht j, ← hu j]
    exact (inv_smul_smul (u j) _).symm
  refine ⟨D, hfW, hxf, ?_⟩
  rw [exterior_section_map N n (homOfLE hfW)]
  have htuple : (fun j ↦ N.val.map (homOfLE hfW).op (a j)) =
      (fun j ↦ (↑((u j)⁻¹) : Z.presheaf.obj (op D)) •
        N.val.map (homOfLE hDO).op (η.val.app (op V.1) (b j))) := by
    funext j
    exact hfac j
  rw [htuple, exterior_section_smul]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨b, rfl⟩


end AlgebraicGeometry
