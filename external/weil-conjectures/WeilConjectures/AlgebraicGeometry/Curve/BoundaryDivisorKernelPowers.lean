/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-!
# Powers in the kernel of the boundary divisor map

Source: blueprint
sec-curve-estimates/sbc-thm-algebraically-closed-invariance/thm-sc-constant-invariance, affine-case
proof, divisor kernel and constants paragraph.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A unit with zero boundary divisor is an nth power.

Source: blueprint
sec-curve-estimates/sbc-thm-algebraically-closed-invariance/thm-sc-constant-invariance, affine-case
proof, divisor kernel and constants paragraph (blueprint: lem-sc-boundary-divisor-kernel-powers).

Proof: The germ compatibility identifies φ with restriction to the function field through
the open immersion c.i. At every point of C both the unit and its inverse have regular germs,
so their valuations are zero. At a boundary closed point the assumed boundary divisor is
zero. Thus the rational function and its inverse have no poles anywhere on the smooth
proper curve c.Z, and extend to global sections by
Scheme.exists_isUnit_germToFunctionField_eq_of_ord_eq_zero (the local DVR criterion followed
by gluing regular rational functions). They are
inverse global sections, hence give a global unit. Global functions on a smooth proper
connected curve over an algebraically closed field are precisely the constants. Therefore
the original unit is a nonzero constant from k. Choose an nth root of that constant in k,
which is nonzero since n ≥ 1, and restrict it to C. Its nth power is the original unit.
No affineness or prime-to-characteristic assumption is needed. -/
theorem boundary_divisor_kernel_powers
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    (φ : Γ(C, ⊤) →+* c.Z.functionField)
    (hφ : ∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
      c.i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
        φ s = algebraMap (c.Z.presheaf.stalk (c.i.base x)) c.Z.functionField y)
    (n : ℕ) (hn : 1 ≤ n) (a : Γ(C, ⊤)ˣ)
    (ha : Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦
      P.val ∉ Set.range c.i.base) (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom a))) = 0) :
    ∃ b : Γ(C, ⊤)ˣ, b ^ n = a := by
  classical
  have := c.isOpenImmersion
  have := c.isProper
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : SmoothOfRelativeDimension 1 c.g :=
    (smoothOfRelativeDimension_iff_topologicalKrullDim_eq c.g 1).mpr
      (IsConnectedCurve.krullDim_eq_one (f := c.g))
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : IsProper (c.Z ↘ Spec (.of k)) := c.isProper
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 c.g›
  obtain ⟨x₀⟩ := IsConnectedCurve.nonempty f
  let V : c.Z.Opens := c.i ''ᵁ ⊤
  have : Nonempty V := ⟨⟨c.i x₀, x₀, trivial, rfl⟩⟩
  have : Nonempty (⊤ : c.Z.Opens) := ⟨⟨c.i x₀, trivial⟩⟩
  let ρ : Γ(C, ⊤) ⟶ c.Z.functionField := (c.i.appIso ⊤).inv ≫ c.Z.germToFunctionField V
  have hρ (s : Γ(C, ⊤)) : φ s = ρ s := by
    let y := c.Z.presheaf.germ V (c.i x₀) ⟨x₀, trivial, rfl⟩ ((c.i.appIso ⊤).inv s)
    have hy : c.i.stalkMap x₀ y = C.presheaf.germ ⊤ x₀ trivial s := by
      dsimp [y, V]
      erw [Scheme.Hom.germ_stalkMap_apply, ← CommRingCat.comp_apply (c.i.appIso ⊤).inv,
        Scheme.Hom.appIso_inv_app, TopCat.Presheaf.germ_res_apply]
    rw [hφ x₀ s y hy]
    exact Scheme.algebraMap_germ_eq_germToFunctionField (X := c.Z) (U := V)
      (x := c.i x₀) (show c.i x₀ ∈ V from ⟨x₀, trivial, rfl⟩) _
  have hinj : Function.Injective φ := by
    intro s t h
    apply (c.i.appIso ⊤).commRingCatIsoToRingEquiv.symm.injective
    apply c.Z.germToFunctionField_injective V
    exact (hρ s).symm.trans (h.trans (hρ t))
  have h0 : φ (a : Γ(C, ⊤)) ≠ 0 := (a.isUnit.map φ).ne_zero
  have hord (x : c.Z) (_ : x ∈ (⊤ : c.Z.Opens)) :
      c.Z.ord (φ (a : Γ(C, ⊤))) x = 0 := by
    by_cases hx : x ∈ V
    · rw [hρ]
      exact Scheme.ord_of_isUnit (a.isUnit.map (c.i.appIso ⊤).inv.hom) hx
    · by_contra hne
      have hclosed := Scheme.isClosed_of_ord_ne_zero k hne
      have hnot : x ∉ Set.range c.i.base := by
        rintro ⟨y, rfl⟩
        exact hx ⟨y, trivial, rfl⟩
      exact hne (congrArg (fun D ↦ D ⟨⟨x, hclosed⟩, hnot⟩) ha)
  obtain ⟨s, -, hs⟩ :=
    Scheme.exists_isUnit_germToFunctionField_eq_of_ord_eq_zero c.g h0 hord
  obtain ⟨a₀, rfl⟩ := (Scheme.GlobalSectionsBijective.bijective_globalSectionsRingHom
    (k := k) (X := c.Z)).2 s
  let κ : k →+* Γ(C, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  have hκ (b : k) : ρ (κ b) =
      c.Z.germToFunctionField ⊤ (Scheme.globalSectionsRingHom k (X := c.Z) b) := by
    have e : c.Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ (c.i.appIso ⊤).hom =
        c.i.appTop := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appTop,
        Scheme.Hom.app_eq_appLE]
      rfl
    have e' : (c.i.appIso ⊤).inv (κ b) =
        c.Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
          (Scheme.globalSectionsRingHom k (X := c.Z) b) := by
      rw [← Iso.eq_comp_inv] at e
      change (c.i.appIso ⊤).inv (f.appTop _) = _
      rw [congrArg Scheme.Hom.appTop c.comm, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        ← CommRingCat.comp_apply _ (c.i.appIso ⊤).inv, ← e]
      rfl
    change c.Z.germToFunctionField V ((c.i.appIso ⊤).inv (κ b)) = _
    rw [e']
    exact c.Z.presheaf.germ_res_apply _ _ _ _
  have ha₀ : (a : Γ(C, ⊤)) = κ a₀ := by
    apply hinj
    rw [hρ (κ a₀), hκ]
    exact hs.symm
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a₀ (Nat.zero_lt_of_lt hn)
  have hb0 : b ≠ 0 := by
    rintro rfl
    apply h0
    rw [ha₀, ← hb, zero_pow (Nat.zero_lt_of_lt hn).ne', map_zero, map_zero]
  refine ⟨(hb0.isUnit.map κ).unit, ?_⟩
  ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow, hb, ha₀]

end AlgebraicGeometry
