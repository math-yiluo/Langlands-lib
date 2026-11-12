import Langlands.Geometry.Building.IwahoriDecompositionAxiomStatement
import Langlands.Geometry.Building.ChamberIwahoriProof
import Langlands.Geometry.Building.IwahoriWeylNormalizerAffineWeylReduction
import Langlands.Geometry.Building.RootGroupZeroFixer
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.BuildingFacetPartition
import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-!
# KP Axiom 4.1.16 from the range part of KP Theorem 7.5.3(2)

KP Axiom 4.1.16 (Iwahori decomposition, `IwahoriDecompositionAxiomStatement`) follows from
`SimplyConnectedNormalizerAffineWeylStatement` (KP Theorem 7.5.3(2)). Only one step uses that
statement: an element of `N(F) ∩ G(F)^0` that maps a chamber `C` onto itself lies in `Z(F)^0`.
Everything else is unconditional.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type*} {A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- For every affine root `ψ` and every point `p` there is an affine root with the derivative
of `ψ` that is positive at `p`. -/
theorem IsAffineRootSystemWithRankZero.exists_parallel_root_pos
    (hΨ : IsAffineRootSystemWithRankZero Ψ) (p : A) {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ) :
    ∃ χ ∈ Ψ, χ.linear = ψ.linear ∧ 0 < χ p := by
  obtain ⟨θ, ⟨hθ, hlin⟩, hout⟩ := (hΨ.infinite_fiber ψ hψ).exists_notMem_finite
    (hΨ.finite_bounded_at p (fun _ => 2 * |ψ p| + 1))
  have hlarge : 2 * |ψ p| + 1 < |θ p| := by
    by_contra h
    exact hout ⟨hθ, le_of_not_gt h⟩
  obtain ⟨v, hv⟩ := hΨ.exists_isCoroot ψ hψ
  rcases lt_or_ge 0 (θ p) with hp | hn
  · exact ⟨θ, hθ, hlin, hp⟩
  · refine ⟨-(θ - (2 : ℝ) • ψ), hΨ.neg_mem ?_, ?_, ?_⟩
    · have h := hv.2 θ hθ
      rwa [hlin, hv.1] at h
    · change -(θ.linear - (2 : ℝ) • ψ.linear) = ψ.linear
      rw [hlin, two_smul]
      abel
    · change 0 < -(θ p - (2 : ℝ) • ψ p)
      rw [abs_of_nonpos hn] at hlarge
      simp only [smul_eq_mul]
      linarith [neg_abs_le (ψ p)]

end AffineRootSystem

section ProductTransfer

/-- Ordered products out of two families of equal subsets of a monoid have the same
injectivity and the same range. -/
theorem ofFn_prod_injective_range_congr {M : Type*} [Monoid M] {n : ℕ}
    {s t : Fin n → Set M} (h : ∀ j, s j = t j) :
    (Function.Injective (fun u : (∀ j, s j) => (List.ofFn fun j => (u j : M)).prod) ↔
      Function.Injective (fun u : (∀ j, t j) => (List.ofFn fun j => (u j : M)).prod)) ∧
    Set.range (fun u : (∀ j, s j) => (List.ofFn fun j => (u j : M)).prod) =
      Set.range (fun u : (∀ j, t j) => (List.ofFn fun j => (u j : M)).prod) := by
  obtain rfl : s = t := funext h
  exact ⟨Iff.rfl, rfl⟩

/-- Three-factor products `(h, z, k) ↦ h f(z) k` over equal pairs of subgroups have the same
injectivity and the same range. -/
theorem mul_mul_injective_range_congr {M Z : Type*} [Group M] [Group Z] (f : Z →* M)
    (Z₀ : Subgroup Z) {H₁ H₂ K₁ K₂ : Subgroup M} (hH : H₁ = H₂) (hK : K₁ = K₂) :
    (Function.Injective (fun p : H₁ × Z₀ × K₁ => (p.1 : M) * f (p.2.1 : Z) * (p.2.2 : M)) ↔
      Function.Injective
        (fun p : H₂ × Z₀ × K₂ => (p.1 : M) * f (p.2.1 : Z) * (p.2.2 : M))) ∧
    Set.range (fun p : H₁ × Z₀ × K₁ => (p.1 : M) * f (p.2.1 : Z) * (p.2.2 : M)) =
      Set.range (fun p : H₂ × Z₀ × K₂ => (p.1 : M) * f (p.2.1 : Z) * (p.2.2 : M)) := by
  subst hH hK
  exact ⟨Iff.rfl, rfl⟩

end ProductTransfer

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-! ### The functionals `ψ_a` and the factors `U_{ψ_a}` -/

/-- The smallest affine functional `ψ_a` of KP Axiom 4.1.16 exists for every root `a` and every
chamber `C`: take an affine root `χ` with derivative `a` that is positive at a point of `C`
(hence on `C`) and subtract the infimum of `χ` on `C`. -/
theorem exists_isLeastNonnegativeFunctional (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (α : relativeRoots P.i) : ∃ ψ, P.IsLeastNonnegativeFunctional α C ψ := by
  obtain ⟨p, -, rfl⟩ := hC
  have hα : rootForm P.i α ∈ AffineRootSystem.derivativeRoots P.affineRoots := by
    rw [hP.derivativeRoots_affineRoots]
    exact ⟨α, rfl⟩
  obtain ⟨θ, hθ, hθα⟩ := hα
  obtain ⟨χ, hχ, hχlin, hχp⟩ :=
    hP.isAffineRootSystem_affineRoots.exists_parallel_root_pos p hθ
  have hχα : χ.linear = rootForm P.i α := hχlin.trans hθα
  have hpos : ∀ z ∈ AffineRootSystem.facet P.affineRoots p, 0 < χ z := by
    intro z hz
    have h := AffineRootSystem.mem_facet.1 hz χ hχ
    rw [sign_pos hχp] at h
    exact sign_eq_one_iff.mp h.symm
  have hbdd : BddBelow (χ '' AffineRootSystem.facet P.affineRoots p) :=
    ⟨0, by
      rintro _ ⟨z, hz, rfl⟩
      exact (hpos z hz).le⟩
  have hne : (χ '' AffineRootSystem.facet P.affineRoots p).Nonempty :=
    ⟨χ p, p, AffineRootSystem.mem_facet_self _ p, rfl⟩
  refine ⟨χ - AffineMap.const ℝ P.Apartment (sInf (χ '' AffineRootSystem.facet P.affineRoots p)),
    ?_, ?_, ?_⟩
  · change χ.linear - (AffineMap.const ℝ P.Apartment _).linear = _
    rw [AffineMap.const_linear, sub_zero, hχα]
  · intro z hz
    change 0 ≤ χ z - sInf (χ '' AffineRootSystem.facet P.affineRoots p)
    exact sub_nonneg.2 (csInf_le hbdd ⟨z, hz, rfl⟩)
  · intro ψ' hψ' hnn x
    change χ x - sInf (χ '' AffineRootSystem.facet P.affineRoots p) ≤ ψ' x
    have hconst : ∀ y, ψ' y - χ y = ψ' p - χ p := fun y =>
      AffineRootSystem.apply_eq_apply_of_linear_eq_zero (f := ψ' - χ)
        (by
          change ψ'.linear - χ.linear = 0
          rw [hψ', hχα, sub_self]) y p
    have hle : χ p - ψ' p ≤ sInf (χ '' AffineRootSystem.facet P.affineRoots p) :=
      le_csInf hne (by
        rintro _ ⟨z, hz, rfl⟩
        have h1 := hnn z hz
        have h2 := hconst z
        linarith)
    have h3 := hconst x
    linarith

/-- For `x ∈ C` and the smallest functional `ψ_a` of KP Axiom 4.1.16, `U_{ψ_a}` is the
depth-zero chamber root block `U_{a,x,0}` (KP Lemma 6.3.20 and AS 4). -/
theorem coe_affineRootGroup_eq_chamberRootBlock (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {x : P.Apartment} (hx : x ∈ C) {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hψ : P.IsLeastNonnegativeFunctional α C ψ) :
    (P.affineRootGroup α ψ : Set (rationalPoints G)) =
      P.apartment.chamberRootBlock x false α := by
  have h1 := (P.apartment.rootFixer_eq_filtration_of_isFacet hP.mem_or_two_smul_mem
    hC.isFacet hx α.2).1
  have h2 := P.rootFixer_eq_affineRootGroup_of_isLeast hψ.1 hψ.2.1
    (fun ψ' _ h₁ h₂ => hψ.2.2 ψ' h₁ h₂)
  rw [P.apartment.chamberRootBlock_eq_rootGroup x false α.2]
  change ((P.affineRootGroup α ψ : Subgroup (rationalPoints G)) : Set (rationalPoints G)) =
    ((P.apartment.filtration x α 0 : Subgroup (rationalPoints G)) : Set (rationalPoints G))
  rw [← h2]
  exact congrArg _ h1

/-! ### The Iwahori subgroup as a stabilizer -/

/-- If every element of `N(F) ∩ G(F)^0` stabilizing the chamber `C` lies in `Z(F)^0`, then
the stabilizer of the image of `C` in `G(F)^0` lies in `P_C`. -/
theorem zeroStabilizer_le_parahoric (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {x : P.Apartment} (hx : x ∈ C) (hxC : P.parahoricAt x ≤ P.parahoric C)
    (hkey : ∀ n : normalizerPoints P.i, n ∈ P.normalizerZeroComponent → n • C = C →
      n ∈ P.normalizerZero) :
    P.zeroStabilizer (P.apartmentMap '' C) ≤ P.parahoric C := by
  intro g hg
  obtain ⟨hg0, hgC⟩ := (P.mem_zeroStabilizer).1 hg
  have hmem : g • P.apartmentMap x ∈ P.apartmentMap '' C := by
    rw [← hgC]
    exact Set.smul_mem_smul_set ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  have hq : ApartmentQuotient.mk P.apartment.sharpFixerFamily (g, x) =
      ApartmentQuotient.mk P.apartment.sharpFixerFamily (1, y) := by
    rw [ApartmentQuotient.mk_eq_smul_apartment]
    exact hyx.symm
  obtain ⟨n, hnx, hs⟩ := (ApartmentQuotient.mk_eq_mk_iff _ g 1 x y).1 hq
  have hs' : g⁻¹ * 1 * (n : rationalPoints G) ∈ P.sharpFixer {x} := hs
  rw [mul_one] at hs'
  have hsP : g⁻¹ * (n : rationalPoints G) ∈ P.parahoric C :=
    hxC (P.sharpFixer_le_parahoric {x} hs')
  have hn0 : (n : rationalPoints G) ∈ P.zeroSubgroup := by
    have h := P.zeroSubgroup.mul_mem hg0
      (P.parahoric_le_zeroSubgroup hP {x} (P.sharpFixer_le_parahoric {x} hs'))
    rwa [mul_inv_cancel_left] at h
  have hnC : n • C = C :=
    (P.normalizer_smul_isChamber hP hC n).isFacet.eq_of_mem_mem hC.isFacet
      (hnx ▸ Set.smul_mem_smul_set hx) hy
  have hnZ := (P.mem_normalizerZero_iff).1 (hkey n (Subgroup.mem_subgroupOf.2 hn0) hnC)
  have hnP : (n : rationalPoints G) ∈ P.parahoric C := P.map_centralizerZero_le_parahoric C hnZ
  have hg : g = (n : rationalPoints G) * (g⁻¹ * (n : rationalPoints G))⁻¹ := by group
  rw [hg]
  exact (P.parahoric C).mul_mem hnP ((P.parahoric C).inv_mem hsP)

/-- Under KP 7.8.2 for the chamber `C`, an element of `N(F) ∩ G(F)^0` stabilizing `C` lies in
`Z(F)^0`: its class lies in `W_aff ∩ W̃^0_C = 1`. -/
theorem mem_normalizerZero_of_iwahoriWeylChamberSplitting {C : Set P.Apartment}
    (h : P.IwahoriWeylChamberSplitting C) (n : normalizerPoints P.i)
    (hn : n ∈ P.normalizerZeroComponent) (hnC : n • C = C) : n ∈ P.normalizerZero := by
  obtain ⟨hN, -, -, hc, -⟩ := h
  have h1 : QuotientGroup.mk' P.normalizerZero n ∈ P.affinePart := ⟨n, hn, rfl⟩
  have h2 : QuotientGroup.mk' P.normalizerZero n ∈ P.chamberStabilizer C :=
    ⟨n, (P.mem_normalizerStabilizer).2 hnC, rfl⟩
  exact (QuotientGroup.eq_one_iff n).1 (Subgroup.disjoint_def.1 hc.disjoint h1 h2)

/-! ### Assembly -/

/-- The ordered-product clause of KP Axiom 4.1.16 for the positive system of `κ`, from the
fixed-sign clause of `ChamberIwahoriConclusion` at depth `0`. -/
theorem isOrderedRootProductBijective_of_conclusion (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {x : P.Apartment} (hx : x ∈ C) {κ : cocharacterLattice P.S}
    (hconc : P.ChamberIwahoriConclusion C x κ)
    (hU : P.zeroStabilizerUnipotentPoints κ (P.apartmentMap '' C) =
      P.iwahoriUnipotentPoints κ C) :
    P.IsOrderedRootProductBijective C κ := by
  intro ψ hψ n a ha hrange
  have := P.isConnectedReductive.smooth
  have hS : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨m, b, hb, hbr⟩ := ((hS.finite_relativeRoots P.i).subset
    (fun _ h => h.1.1 :
      RelativeRoot.indivisiblePositiveRoots P.i (-κ) ⊆ relativeRoots P.i)).fin_param
  have h := hconc.2.2.2.2.2.2 false m n b (fun j => (a j : characterLattice P.S)) hb hbr
    (Subtype.val_injective.comp ha) hrange
  have hset : ∀ j, (P.affineRootGroup (a j) (ψ (a j)) : Set (rationalPoints G)) =
      P.apartment.chamberRootBlock x false (a j) := fun j => by
    have hj : (a j : characterLattice P.S) ∈ RelativeRoot.indivisiblePositiveRoots P.i κ :=
      hrange ▸ Set.mem_range_self j
    exact P.coe_affineRootGroup_eq_chamberRootBlock hP hC hx (hψ (a j) hj.1)
  have hcongr := ofFn_prod_injective_range_congr hset
  refine ⟨hcongr.1.2 h.2.2.1, hcongr.2.trans (h.2.2.2.1.trans ?_)⟩
  rw [hU]

/-- KP Axiom 4.1.16 at the chamber `C` and the generic cocharacter `ν`, given that every element
of `N(F) ∩ G(F)^0` stabilizing `C` lies in `Z(F)^0`. -/
theorem isIwahoriDecompositionAt_of_forall_mem_normalizerZero
    (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (hkey : ∀ n : normalizerPoints P.i, n ∈ P.normalizerZeroComponent → n • C = C →
      n ∈ P.normalizerZero)
    {ν : cocharacterLattice P.S} (hν : IsGenericCocharacter P.i ν) :
    P.IsIwahoriDecompositionAt C ν := by
  obtain ⟨x, hx⟩ : C.Nonempty := by
    obtain ⟨p, -, rfl⟩ := hC
    exact ⟨p, AffineRootSystem.mem_facet_self _ p⟩
  have hν' : IsGenericCocharacter P.i (-ν) := fun α hα => by
    simpa only [map_neg, neg_ne_zero] using hν α hα
  have hpos := (P.chamberIwahoriDecomposition hP C x ν hC hx hν).2.1
  have hneg := (P.chamberIwahoriDecomposition hP C x (-ν) hC hx hν').2.1
  have hstab : P.zeroStabilizer (P.apartmentMap '' C) = P.parahoric C :=
    le_antisymm (P.zeroStabilizer_le_parahoric hP hC hx hpos.1.ge hkey)
      ((P.parahoric_le_zeroFixer hP C).trans (P.zeroFixer_le_zeroStabilizer C))
  have hU : ∀ κ, P.zeroStabilizerUnipotentPoints κ (P.apartmentMap '' C) =
      P.iwahoriUnipotentPoints κ C := fun κ => by
    rw [zeroStabilizerUnipotentPoints, iwahoriUnipotentPoints, hstab]
  have htriple := mul_mul_injective_range_congr (rationalPoints.map P.centralizer.j)
    P.centralizerZero ((hU ν).trans (congrArg (P.iwahoriUnipotentPoints · C) (neg_neg ν).symm))
    (hU (-ν))
  exact
    { injective_product := htriple.1.2 hneg.2.2.2.2.1
      range_product := htriple.2.trans (hneg.2.2.2.2.2.1.trans (by rw [hstab]))
      exists_isLeastNonnegativeFunctional := fun α _ =>
        P.exists_isLeastNonnegativeFunctional hP hC α
      orderedProduct_pos := P.isOrderedRootProductBijective_of_conclusion hP hC hx hpos (hU ν)
      orderedProduct_neg :=
        P.isOrderedRootProductBijective_of_conclusion hP hC hx hneg (hU (-ν)) }

/-- KP Axiom 4.1.16 for `P`, given KP 7.8.2 for every chamber of `A(S)`. -/
theorem hasIwahoriDecomposition_of_iwahoriWeylChamberSplitting
    (hP : P.SatisfiesApartmentAxioms)
    (h : ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
      P.IwahoriWeylChamberSplitting C) :
    P.HasIwahoriDecomposition := fun C hC _ hν =>
  P.isIwahoriDecompositionAt_of_forall_mem_normalizerZero hP hC
    (fun n hn hnC => P.mem_normalizerZero_of_iwahoriWeylChamberSplitting (h C hC) n hn hnC) hν

end ParahoricBuildingData

/-- KP 7.8.2 (`IwahoriWeylChamberSplittingStatement`) implies KP Axiom 4.1.16. -/
theorem iwahoriDecompositionAxiom_of_iwahoriWeylChamberSplitting
    (h : IwahoriWeylChamberSplittingStatement.{u}) : IwahoriDecompositionAxiomStatement.{u} := by
  intro F _ _ _ _ G _ P hP
  exact P.hasIwahoriDecomposition_of_iwahoriWeylChamberSplitting hP (h F G P hP)

/-- The range part of KP Theorem 7.5.3(2) (`SimplyConnectedNormalizerAffineWeylStatement`:
`N(F) ∩ G(F)^♮` acts on the apartment through exactly `W(Ψ)`, for all actual building data)
implies KP Axiom 4.1.16 (`IwahoriDecompositionAxiomStatement`) for all actual building data. -/
def IwahoriDecompositionAxiomReductionStatement : Prop :=
  SimplyConnectedNormalizerAffineWeylStatement.{u} → IwahoriDecompositionAxiomStatement.{u}

/-- The reduction holds, through KP 7.8.2 (`iwahoriWeylNormalizerAffineWeylReduction`). -/
theorem iwahoriDecompositionAxiomReduction :
    IwahoriDecompositionAxiomReductionStatement.{u} := fun hW =>
  iwahoriDecompositionAxiom_of_iwahoriWeylChamberSplitting
    (iwahoriWeylNormalizerAffineWeylReduction hW).2

end Langlands.Geometry.Building
