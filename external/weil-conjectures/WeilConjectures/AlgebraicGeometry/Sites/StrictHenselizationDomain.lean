/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal

/-!
# The strict henselization of a regular scheme is a domain

Let `S` be a regular scheme and `s: Spec Ω ⟶ S` a geometric point. The strict henselization
`𝒪^{sh}_{S,s}` is the filtered colimit of the rings `Γ(V, 𝒪_V)` of the affine pointed étale
neighbourhoods `(V, v)` of `s`. A product `ab` vanishing in the colimit vanishes in some
`Γ(V, 𝒪_V)`; the local ring of `V` at `v` is regular (`V` is étale over the regular `S`), hence a
domain, so `a` or `b` is killed by a section not vanishing at `v`, which becomes a unit in the
colimit (the strict henselization is local), hence vanishes in the colimit. So `𝒪^{sh}_{S,s}` is a
domain and the strict localization is integral.

## Main statements

- `AlgebraicGeometry.Scheme.isDomain_strictHenselization_of_isRegular`
- `AlgebraicGeometry.Scheme.irreducibleSpace_strictLocalization_of_isRegular`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ S}

omit [IsSepClosed Ω] in
/-- A global section of an affine scheme `V` whose germ at the image of a point `p` under
`v : Spec Ω ⟶ V` vanishes is killed by a global section with nonzero pullback along `v`. -/
lemma exists_mul_eq_zero_of_germ_eq_zero {V : Scheme.{u}} [IsAffine V] (v : Spec (.of Ω) ⟶ V)
    (p : Spec (.of Ω)) (c : Γ(V, ⊤)) (h : V.presheaf.germ ⊤ (v p) trivial c = 0) :
    ∃ m : Γ(V, ⊤), m * c = 0 ∧ v.app ⊤ m ≠ 0 := by
  have hU : IsAffineOpen (⊤ : V.Opens) := isAffineOpen_top V
  let := V.presheaf.algebra_section_stalk (U := ⊤) ⟨v p, trivial⟩
  have := hU.isLocalization_stalk ⟨v p, trivial⟩
  obtain ⟨⟨m, hm⟩, hmc⟩ := (IsLocalization.map_eq_zero_iff
    (hU.primeIdealOf ⟨v p, trivial⟩).asIdeal.primeCompl _ c).mp h
  refine ⟨m, hmc, fun h0 ↦ ?_⟩
  have hpt : p ∈ v ⁻¹ᵁ V.basicOpen m :=
    (V.mem_basicOpen m (v p) trivial).mpr (IsLocalization.map_units _ ⟨m, hm⟩)
  rw [Scheme.preimage_basicOpen, h0, Scheme.basicOpen_zero] at hpt
  exact hpt

set_option backward.isDefEq.respectTransparency false in
/-- A section of an affine pointed étale neighbourhood `(V, v)` whose germ at `v` vanishes
vanishes in the strict henselization: it is killed by a section not vanishing at `v`, whose image
in the strict henselization is a unit. -/
lemma colimit_ι_strictHenselizationDiagram_eq_zero_of_germ_eq_zero
    (x : AffinePointedEtaleNeighborhood s) (c : Γ(x.obj.1.left, ⊤)) (p : Spec (.of Ω))
    (h : x.obj.1.left.presheaf.germ ⊤ (x.obj.2.left p) trivial c = 0) :
    colimit.ι (strictHenselizationDiagram s) (op x) c = 0 := by
  obtain ⟨m, hmc, hne⟩ := exists_mul_eq_zero_of_germ_eq_zero (V := x.obj.1.left) x.obj.2.left p c h
  have hunit : IsUnit (colimit.ι (strictHenselizationDiagram s) (op x) m) := by
    rw [isUnit_iff_strictHenselizationEval_ne_zero]
    have e := congr($(ι_strictHenselizationEval s x) m)
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at e
    exact fun h0 ↦ hne ((Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.map_eq_zero_iff.mp
      (e.symm.trans h0))
  rw [← hunit.mul_right_eq_zero, ← map_mul, hmc, map_zero]

variable [IsRegular S] (s)

/-- The strict henselization of a regular scheme at a geometric point is a domain. -/
theorem isDomain_strictHenselization_of_isRegular : IsDomain (strictHenselization s) := by
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_forall_mem_range_colimit_ι 2 ![a, b]
  obtain ⟨a', rfl⟩ := hx 0
  obtain ⟨b', rfl⟩ := hx 1
  have hab' : colimit.ι (strictHenselizationDiagram s) (op x) (a' * b') =
      colimit.ι (strictHenselizationDiagram s) (op x) 0 := by
    rw [map_mul, map_zero]
    exact hab
  obtain ⟨k, f, g, hf⟩ := Concrete.colimit_exists_of_rep_eq.{u} _ _ _ hab'
  rw [map_zero, map_mul] at hf
  have hw (c) : colimit.ι (strictHenselizationDiagram s) k ((strictHenselizationDiagram s).map f c)
      = colimit.ι (strictHenselizationDiagram s) (op x) c := by
    rw [← CommRingCat.comp_apply, colimit.w]
  have : Etale k.unop.obj.1.hom := k.unop.obj.1.prop
  have : IsDomain
      (k.unop.obj.1.left.presheaf.stalk (k.unop.obj.2.left (default : Spec (.of Ω)))) := by
    have := isRegularLocalRing_stalk_of_etale (X := k.unop.obj.1.left) (Y := S) k.unop.obj.1.hom
      (fun y ↦ IsRegular.isRegularLocalRing_stalk (X := S) y)
      (k.unop.obj.2.left (default : Spec (.of Ω)))
    infer_instance
  have h0 := congrArg (k.unop.obj.1.left.presheaf.germ ⊤
    (k.unop.obj.2.left (default : Spec (.of Ω))) trivial) hf
  rw [map_mul, map_zero] at h0
  rw [← hw, ← hw]
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl (colimit_ι_strictHenselizationDiagram_eq_zero_of_germ_eq_zero k.unop _ _ h)
  · exact Or.inr (colimit_ι_strictHenselizationDiagram_eq_zero_of_germ_eq_zero k.unop _ _ h)

/-- The strict localization of a regular scheme at a geometric point is irreducible. -/
theorem irreducibleSpace_strictLocalization_of_isRegular :
    IrreducibleSpace (strictLocalization s) := by
  have := isDomain_strictHenselization_of_isRegular s
  infer_instance

end AlgebraicGeometry.Scheme
