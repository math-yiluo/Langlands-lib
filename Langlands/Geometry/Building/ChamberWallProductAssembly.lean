import Langlands.Geometry.Building.ChamberWallRootContainment

/-! # Positive chamber products across a simple affine wall -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Collection with the exceptional primitive root last puts the generated
positive subgroup in the reflected sharp fixer times the wall root group. -/
theorem positiveChamberRootGroups_subset_reflection_mul_wall
    (hT : IsSplitTorus S.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {alpha : relativeRoots i} (hwall : psi.linear = rootForm i alpha)
    {nu : cocharacterLattice S} (hpos : 0 < latticePairing S alpha nu)
    {x : D.Apartment} (hx : x ∈ C)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    ((⨆ b : positiveRelativeRoots i nu, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) ⊆
      (D.sharpFixer (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
      (D.affineRootGroup alpha psi : Set (rationalPoints G)) := by
  classical
  obtain ⟨a0, ha0, hcase⟩ :=
    D.exists_indivisiblePositiveRoot_eq_or_double hext hderiv nu ⟨alpha.property, hpos⟩
  let b0 : relativeRoots i := ⟨a0, ha0.1.1⟩
  have hwall0 : ∃ d : ℝ, psi.linear = d • rootForm i b0 := by
    rcases hcase with h | h
    · exact ⟨1, by rw [one_smul, hwall]; exact congrArg (rootForm i) (Subtype.ext h)⟩
    · refine ⟨2, ?_⟩
      rw [hwall]
      have h2 : 2 • a0 ∈ relativeRoots i := h ▸ alpha.property
      calc
        rootForm i alpha = rootForm i ⟨2 • a0, h2⟩ :=
          congrArg (rootForm i) (Subtype.ext h)
        _ = (2 : ℝ) • rootForm i b0 := rootForm_nsmul ha0.1.1 2 h2
  obtain ⟨d, hd⟩ := hwall0
  have hfin : (RelativeRoot.indivisiblePositiveRoots i nu \ {a0}).Finite :=
    hfinite.subset fun b hb => hb.1.1.1
  obtain ⟨n, a, _, harange⟩ := hfin.fin_param
  let apos : Fin (n + 1) → characterLattice S := Fin.lastCases a0 a
  have hapos_cast (j : Fin n) : apos j.castSucc = a j := by simp [apos]
  have hapos_last : apos (Fin.last n) = a0 := by simp [apos]
  have haprefix (j : Fin n) :
      a j ∈ RelativeRoot.indivisiblePositiveRoots i nu ∧ a j ≠ a0 := by
    have h : a j ∈ RelativeRoot.indivisiblePositiveRoots i nu \ {a0} :=
      harange ▸ Set.mem_range_self j
    simpa only [Set.mem_sdiff, Set.mem_singleton_iff] using h
  have hrange : Set.range apos = RelativeRoot.indivisiblePositiveRoots i nu := by
    ext b
    constructor
    · rintro ⟨j, rfl⟩
      refine Fin.lastCases ?_ (fun l => ?_) j
      · simpa only [hapos_last] using ha0
      · simpa only [hapos_cast] using (haprefix l).1
    · intro hb
      by_cases h : b = a0
      · exact ⟨Fin.last n, hapos_last.trans h.symm⟩
      · obtain ⟨j, hj⟩ := (show b ∈ Set.range a by
          rw [harange]
          exact ⟨hb, h⟩)
        exact ⟨j.castSucc, (hapos_cast j).trans hj⟩
  intro g hg
  obtain ⟨t, rfl⟩ := (show g ∈ Set.range
      (RelativeRoot.CentralExtension.orderedProduct
        (fun j => (D.chamberRootGroup x false (apos j)).subtype)) by
    rw [D.range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup
      hext hderiv x false nu apos hrange]
    exact hg)
  let R := AffineRootSystem.affineReflection psi hv.1 '' C
  have htroot (j : Fin (n + 1)) :
      (t j : rationalPoints G) ∈ D.rootFixer (apos j) C := by
    rw [(D.rootFixer_eq_filtration_of_isFacet hAS4 hpsi.2.2.1.isFacet hx
      (show apos j ∈ relativeRoots i from
        (show apos j ∈ RelativeRoot.indivisiblePositiveRoots i nu from
          hrange ▸ Set.mem_range_self j).1.1)).1]
    exact (t j).property
  have hprefix :
      (List.ofFn fun j : Fin n => (t j.castSucc : rationalPoints G)).prod ∈
        D.sharpFixer R := by
    apply Subgroup.list_prod_mem
    intro z hz
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    have htC : (t j.castSucc : rationalPoints G) ∈ D.rootFixer (a j) C := by
      simpa only [hapos_cast] using htroot j.castSucc
    have heq := D.rootFixer_eq_reflection_of_indivisible_ne hAS4 hpsi hT hsys hext
      hderiv ha0 hd (b := ⟨a j, (haprefix j).1.1.1⟩)
      (haprefix j).1 (haprefix j).2 hv
    exact D.rootFixer_le_sharpFixer ⟨a j, (haprefix j).1.1.1⟩ R (heq ▸ htC)
  have hlast : (t (Fin.last n) : rationalPoints G) ∈ D.rootFixer b0 C := by
    simpa only [hapos_last] using htroot (Fin.last n)
  obtain ⟨w, hw, u, hu, hwu⟩ :=
    D.rootFixer_subset_reflection_mul_wall_of_eq_or_double hAS4 hpsi hwall hcase hv hlast
  refine ⟨(List.ofFn fun j : Fin n => (t j.castSucc : rationalPoints G)).prod * w,
    (D.sharpFixer R).mul_mem hprefix (D.rootFixer_le_sharpFixer b0 R hw),
    u, hu, ?_⟩
  unfold RelativeRoot.CentralExtension.orderedProduct
  rw [List.ofFn_succ', List.prod_concat]
  simp only [Subgroup.subtype_apply]
  rw [← hwu, mul_assoc]

/-- The positive generated-group inclusion retains the ambient rational point. -/
def positiveChamberWallProductInclusion
    (hT : IsSplitTorus S.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hsys : AffineRootSystem.IsAffineRootSystemWithRankZero D.affineRoots)
    (hext : AffineRootSystem.IsAffineRootSystemWithRankZero D.extendedAffineRoots)
    (hderiv : AffineRootSystem.derivativeRoots D.extendedAffineRoots =
      Set.range (rootForm i))
    (hAS4 : ∀ eta ∈ D.extendedAffineRoots,
      eta ∈ D.affineRoots ∨ (2 : ℝ) • eta ∈ D.affineRoots)
    {C : Set D.Apartment} {psi : D.Apartment →ᵃ[ℝ] ℝ}
    (hpsi : psi ∈ AffineRootSystem.simpleAffineRoots D.affineRoots C)
    {alpha : relativeRoots i} (hwall : psi.linear = rootForm i alpha)
    {nu : cocharacterLattice S} (hpos : 0 < latticePairing S alpha nu)
    {x : D.Apartment} (hx : x ∈ C)
    {v : TranslationSpace i} (hv : AffineRootSystem.IsCoroot D.affineRoots psi v) :
    ↥(⨆ b : positiveRelativeRoots i nu, D.chamberRootGroup x false b :
        Subgroup (rationalPoints G)) →
      ↥((D.sharpFixer (AffineRootSystem.affineReflection psi hv.1 '' C) :
        Set (rationalPoints G)) *
        (D.affineRootGroup alpha psi : Set (rationalPoints G))) :=
  fun g => ⟨g, D.positiveChamberRootGroups_subset_reflection_mul_wall hT hfinite
    hsys hext hderiv hAS4 hpsi hwall hpos hx hv g.property⟩

end Langlands.Geometry.Building.KPApartmentData
