/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard

/-! # Boundary divisors of units as a Picard kernel

Source: blueprint proposition-cohomology-smooth-affine-curve, affine-case unit quotient paragraph.
(blueprint: lem-sc-boundary-divisor-pic-kernel).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Boundary divisors of units are precisely the divisors with trivial Picard class
when extended by zero to the compactification.
Source: blueprint proposition-cohomology-smooth-affine-curve, affine-case unit quotient paragraph;
the upstream point-ideal divisor-class equivalence and the local DVR unit criterion.
(blueprint: lem-sc-boundary-divisor-pic-kernel).

Proof: the germ condition identifies φ with restriction through the open immersion:
choose a point of the nonempty C, use the inverse of c.i.appIso to lift a section to
c.i(C), and compare its germ with its image in the function field. A unit and its
inverse have regular germs on this open, so every order there is zero. Its full
principal divisor is therefore the extension by zero of its boundary divisor.
The divisor-to-Picard homomorphism annihilates principal divisors, giving one inclusion.
Conversely, the divisor-class/Picard equivalence says that an extended divisor with
trivial Picard class is div(r) for a nonzero rational function r. Its orders on c.i(C)
are all zero: closed points there have zero coefficient by extension by zero, and
orders at nonclosed points vanish on a smooth curve. The local DVR criterion and
sheaf gluing (exists_isUnit_germToFunctionField_eq_of_ord_eq_zero on c.i(C)) produce a
unit section with rational image r. Transport it by c.i.appIso to C and use the germ
comparison already proved to identify its image under φ. Restriction of div(r) to the
boundary returns the original divisor. For empty boundary both sides are the singleton
zero. For a singleton boundary, properness and degree zero force its coefficient to be
zero; the unit one represents that divisor. No field extension or descent is used. -/
theorem boundary_divisor_pic_kernel
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [IsIntegral c.Z] [IsNoetherian c.Z]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    (φ : Γ(C, ⊤) →+* c.Z.functionField)
    (hφ : ∀ (x : C) (s : Γ(C, ⊤)) (y : c.Z.presheaf.stalk (c.i.base x)),
      c.i.stalkMap x y = C.presheaf.germ ⊤ x trivial s →
        φ s = algebraMap (c.Z.presheaf.stalk (c.i.base x)) c.Z.functionField y) :
    Set.range (fun a : Γ(C, ⊤)ˣ ↦
      Finsupp.subtypeDomain (fun P : closedPoints c.Z ↦ P.val ∉ Set.range c.i.base)
        (c.Z.div (Additive.ofMul (Units.map φ.toMonoidHom a)))) =
      {D | (@Scheme.Divisor.toPic k _ c.Z ⟨c.g⟩ hsm
        (Finsupp.embDomain (.subtype _) D)).toMul = 1} := by
  classical
  have := c.isOpenImmersion
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  have : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := hsm
  have : IsCurve (c.Z ↘ Spec (.of k)) := inferInstanceAs (IsCurve c.g)
  obtain ⟨x₀⟩ := IsConnectedCurve.nonempty f
  let V : c.Z.Opens := c.i ''ᵁ ⊤
  have : Nonempty V := ⟨⟨c.i x₀, x₀, trivial, rfl⟩⟩
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
  obtain ⟨E, hE⟩ := Scheme.exists_divisorClassGroup_addEquiv_pic (k := k) (C := c.Z)
  have hprincipal (D : c.Z.Divisor) :
      (Scheme.Divisor.toPic k c.Z D).toMul = 1 ↔ ∃ r, c.Z.div r = D := by
    rw [toMul_eq_one, ← hE D, E.map_eq_zero_iff]
    exact QuotientAddGroup.eq_zero_iff D
  ext D
  constructor
  · rintro ⟨a, rfl⟩
    apply (hprincipal _).2
    refine ⟨Additive.ofMul (Units.map φ.toMonoidHom a), ?_⟩
    symm
    rw [← Finsupp.extendDomain_eq_embDomain_subtype]
    apply Finsupp.extendDomain_subtypeDomain
    intro P hP
    by_contra hx
    have hV : P.val ∈ V := by
      obtain ⟨x, hx'⟩ := hx
      exact ⟨x, trivial, hx'⟩
    have hz : c.Z.ord (φ (a : Γ(C, ⊤))) P.val = 0 := by
      rw [hρ]
      exact Scheme.ord_of_isUnit (a.isUnit.map (c.i.appIso ⊤).inv.hom) hV
    exact (Finsupp.mem_support_iff.mp hP) hz
  · intro hD
    obtain ⟨r, hr⟩ := (hprincipal _).1 hD
    have hord (x : c.Z) (hx : x ∈ V) : c.Z.ord (r.toMul : c.Z.functionField) x = 0 := by
      by_contra hne
      have hc := Scheme.isClosed_of_ord_ne_zero k hne
      have hn : ¬ (⟨x, hc⟩ : closedPoints c.Z).val ∉ Set.range c.i.base := by
        change ¬ x ∉ Set.range c.i.base
        obtain ⟨y, _, hy⟩ := hx
        exact not_not.mpr ⟨y, hy⟩
      have hv := congrArg (fun F : c.Z.Divisor ↦ F ⟨x, hc⟩) hr
      rw [Scheme.div_apply, Finsupp.embDomain_of_notMem_range] at hv
      · exact hne hv
      · simpa using hn
    obtain ⟨s, hs, hsr⟩ := Scheme.exists_isUnit_germToFunctionField_eq_of_ord_eq_zero
      c.g r.toMul.ne_zero hord
    obtain ⟨v, hv⟩ := hs
    let a : Γ(C, ⊤)ˣ := Units.map (c.i.appIso ⊤).hom.hom.toMonoidHom v
    have ha : φ (a : Γ(C, ⊤)) = (r.toMul : c.Z.functionField) := by
      rw [hρ]
      change c.Z.germToFunctionField V
        ((c.i.appIso ⊤).inv ((c.i.appIso ⊤).hom (v : Γ(c.Z, V)))) = _
      rw [CommRingCat.inv_hom_apply, hv, hsr]
    refine ⟨a, ?_⟩
    have hur : Additive.ofMul (Units.map φ.toMonoidHom a) = r := by
      apply Additive.toMul.injective
      exact Units.ext ha
    dsimp only
    rw [hur, hr, ← Finsupp.extendDomain_eq_embDomain_subtype]
    exact Finsupp.subtypeDomain_extendDomain D


end AlgebraicGeometry
