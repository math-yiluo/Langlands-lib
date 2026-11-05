import Langlands.Geometry.Building.HalfWallRootFactorization
import Langlands.Geometry.Building.ChamberWallFiltration
import Langlands.Geometry.Building.ChamberExchange

/-! # Root containment across a chamber-simple wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]

/-- Equality of the reduced apartment forms implies equality of their
pullbacks to the real cocharacter space. -/
theorem eval_eq_smul_of_rootForm_eq_smul {a b : relativeRoots i} {c : ℝ}
    (h : rootForm i b = c • rootForm i a) :
    eval S b = c • eval S a := by
  apply LinearMap.ext
  intro w
  exact congrArg (fun l : TranslationSpace i →ₗ[ℝ] ℝ =>
    l (Submodule.Quotient.mk w)) h

namespace KPApartmentData

variable [Mono i.hom.hom.left] {ω : kˣ → ℝ} (D : KPApartmentData i ω)
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {c : ℝ} (hc : c < 0) {b : relativeRoots i}
    (hlin : (c • psi).linear = rootForm i b)

include hAS4 hpsi hc hlin

/-- A negative multiple of the simple wall describes the chamber fixer
by the strict affine root group in its own derivative direction. -/
theorem rootFixer_eq_affineRootGroupPlus_of_neg_smul_simpleAffineRoot :
    D.rootFixer b C = D.affineRootGroupPlus b (c • psi) := by
  obtain ⟨x, y, hxC, hy, hzero⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hpsi
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self D.affineRoots x
  apply D.rootFixer_eq_affineRootGroupPlus_of_mem_facetClosure hAS4 hpsi.2.2.1
    hx hy hlin
  · change c * psi y = 0
    rw [hzero, mul_zero]
  · exact mul_neg_of_neg_of_pos hc (hpsi.1.2 x hx)

/-- On the reflected chamber, a negative multiple of the wall gives
the nonstrict affine root group in the same derivative direction. -/
theorem rootFixer_reflection_eq_affineRootGroup_of_neg_smul_simpleAffineRoot
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) =
      D.affineRootGroup b (c • psi) := by
  obtain ⟨x, y, hxC, hy, hzero⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hpsi
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self D.affineRoots x
  let s := AffineRootSystem.affineReflection psi hv.1
  have hsy : s y = y := AffineRootSystem.affineReflection_apply_of_mem psi hv.1 hzero
  have hyref : y ∈ AffineRootSystem.facetClosure D.affineRoots (s x) := by
    intro xi hxi
    have hcomp : xi.comp (s : D.Apartment →ᵃ[ℝ] D.Apartment) ∈ D.affineRoots := by
      rw [show s = AffineRootSystem.affineReflection psi hv.1 from rfl,
        AffineRootSystem.comp_affineReflection]
      exact hv.2 xi hxi
    have h := hy _ hcomp
    simpa only [AffineMap.comp_apply, AffineEquiv.coe_toAffineMap, hsy] using h
  apply D.rootFixer_eq_affineRootGroup_of_mem_facetClosure hAS4
    (Set.mem_image_of_mem s hx) hyref hlin
  · change c * psi y = 0
    rw [hzero, mul_zero]
  · rintro z ⟨w, hw, rfl⟩
    change 0 ≤ c * psi (s w)
    rw [show s = AffineRootSystem.affineReflection psi hv.1 from rfl,
      AffineRootSystem.apply_affineReflection]
    exact (mul_pos_of_neg_of_neg hc (neg_neg_of_pos (hpsi.1.2 w hw))).le

/-- The chamber fixer in a negative wall direction is contained in
the reflected-chamber fixer in that same direction. -/
theorem rootFixer_le_reflection_of_neg_smul_simpleAffineRoot
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b C ≤
      D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) := by
  rw [D.rootFixer_eq_affineRootGroupPlus_of_neg_smul_simpleAffineRoot hAS4 hpsi hc hlin,
    D.rootFixer_reflection_eq_affineRootGroup_of_neg_smul_simpleAffineRoot
      hAS4 hpsi hc hlin hv]
  exact D.affineRootGroupPlus_le b (c • psi)

omit hc hlin in
/-- Choosing the wall derivative positive in an integral positive system
puts every negative root fixer inside the reflected fixer. -/
theorem rootFixer_le_reflection_of_pairing_neg
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    {nu : cocharacterLattice S} (ha : 0 < latticePairing S a nu)
    (hb : latticePairing S b nu < 0)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b C ≤
      D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) := by
  by_cases hprop : ∃ c : ℝ, rootForm i b = c • psi.linear
  · obtain ⟨t, ht⟩ := hprop
    have heval := eval_eq_smul_of_rootForm_eq_smul (ht.trans (by rw [hwall]))
    have hp := congrArg (fun l => l ((1 : ℝ) ⊗ₜ[ℤ] nu)) heval
    simp only [LinearMap.smul_apply, eval_tmul, one_mul, smul_eq_mul] at hp
    have haR : (0 : ℝ) < (latticePairing S a nu : ℝ) := by exact_mod_cast ha
    have hbR : (latticePairing S b nu : ℝ) < 0 := by exact_mod_cast hb
    have htneg : t < 0 := by nlinarith
    exact D.rootFixer_le_reflection_of_neg_smul_simpleAffineRoot hAS4 hpsi htneg
      (by rw [AffineMap.smul_linear, ← ht]) hv
  · exact (D.rootFixer_eq_simpleReflection_of_not_proportional hsys hAS4
      hpsi.2.2.1 hpsi hv hprop).1.le

omit hc hlin in
/-- The inclusion for a negative root is the identity on ambient
rational points and respects multiplication. -/
def negativeRootFixerReflectionInclusion
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    {nu : cocharacterLattice S} (ha : 0 < latticePairing S a nu)
    (hb : latticePairing S b nu < 0)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b C →*
      D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) :=
  Subgroup.inclusion
    (D.rootFixer_le_reflection_of_pairing_neg hAS4 hpsi hsys hwall ha hb hv)

omit hAS4 hpsi hc hlin in
/-- Two indivisible roots positive on the same cocharacter and with
proportional apartment forms are equal. Reducedness is not assumed. -/
theorem indivisiblePositiveRoot_eq_of_rootForm_eq_smul
    (hT : IsSplitTorus S.toGrp)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    {nu : cocharacterLattice S} {a b : characterLattice S}
    (ha : a ∈ RelativeRoot.indivisiblePositiveRoots i nu)
    (hb : b ∈ RelativeRoot.indivisiblePositiveRoots i nu)
    {t : ℝ} (h : rootForm i ⟨b, hb.1.1⟩ = t • rootForm i ⟨a, ha.1.1⟩) :
    b = a := by
  have heval := eval_eq_smul_of_rootForm_eq_smul h
  have hp := congrArg (fun l => l ((1 : ℝ) ⊗ₜ[ℤ] nu)) heval
  simp only [LinearMap.smul_apply, eval_tmul, one_mul, smul_eq_mul] at hp
  have haR : (0 : ℝ) < (latticePairing S a nu : ℝ) := by exact_mod_cast ha.2
  have hbR : (0 : ℝ) < (latticePairing S b nu : ℝ) := by exact_mod_cast hb.2
  have ht : 0 < t := by nlinarith
  rcases D.eq_or_double_of_eval_eq_smul hT hsys hderiv ha.1.1 hb.1.1 ht heval with
    heq | heq | heq
  · exact heq
  · exact False.elim (hb.1.2 a ha.1.1 2 (by norm_num) heq.symm)
  · exact False.elim (ha.1.2 b hb.1.1 2 (by norm_num) heq.symm)

omit hc hlin in
/-- Every other positive indivisible root has the same chamber fixer
after reflection in the simple wall. -/
theorem rootFixer_eq_reflection_of_indivisible_ne
    (hT : IsSplitTorus S.toGrp)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    {nu : cocharacterLattice S} {a0 : characterLattice S}
    (ha0 : a0 ∈ RelativeRoot.indivisiblePositiveRoots i nu)
    {d : ℝ} (hwall : psi.linear = d • rootForm i ⟨a0, ha0.1.1⟩)
    (hb : (b : characterLattice S) ∈ RelativeRoot.indivisiblePositiveRoots i nu)
    (hne : (b : characterLattice S) ≠ a0)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    D.rootFixer b C =
      D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) := by
  apply (D.rootFixer_eq_simpleReflection_of_not_proportional hsys hAS4
    hpsi.2.2.1 hpsi hv ?_).1
  rintro ⟨t, ht⟩
  apply hne
  apply D.indivisiblePositiveRoot_eq_of_rootForm_eq_smul hT hext hderiv ha0 hb
  simpa only [hwall, smul_smul] using ht

omit hc hlin in
/-- The exceptional indivisible ray has the required wall factor,
whether the wall derivative is primitive or twice primitive. -/
theorem rootFixer_subset_reflection_mul_wall_of_eq_or_double
    {a : relativeRoots i} (hwall : psi.linear = rootForm i a)
    (hcase : (a : characterLattice S) = b ∨ (a : characterLattice S) = 2 • b)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    (D.rootFixer b C : Set (rationalPoints G)) ⊆
      (D.rootFixer b (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
      (D.affineRootGroup a psi : Set (rationalPoints G)) := by
  rcases hcase with h | h
  · have hab : a = b := Subtype.ext h
    subst a
    rw [D.rootFixer_eq_affineRootGroup_of_simpleAffineRoot hAS4 hpsi hwall]
    intro g hg
    exact ⟨1, Subgroup.one_mem _, g, hg, one_mul g⟩
  · have h2b : 2 • (b : characterLattice S) ∈ relativeRoots i := h ▸ a.property
    have hab : a = ⟨2 • (b : characterLattice S), h2b⟩ := Subtype.ext h
    subst a
    exact D.rootFixer_half_subset_reflection_mul_affineRootGroup
      hAS4 hpsi h2b hwall hv

end KPApartmentData
end Langlands.Geometry.Building
