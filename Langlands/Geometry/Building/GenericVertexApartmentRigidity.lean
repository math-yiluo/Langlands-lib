import Langlands.Geometry.Building.GenericRootFixerIntersection
import Langlands.Geometry.Building.ChamberFiltration
import Langlands.Geometry.Building.IntegerValuationBuildingData
import Mathlib.LinearAlgebra.AffineSpace.Midpoint

/-! # Vertex rigidity inside the actual apartment -/

noncomputable section

universe u uV uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- A vertex is the only point in the formal closure of its sign facet. -/
theorem IsVertex.eq_of_mem_facetClosure {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    {x y : A} (hx : IsVertex Ψ x) (hy : y ∈ facetClosure Ψ x) : y = x := by
  have hm : midpoint ℝ x y ∈ facet Ψ x := by
    intro ψ hψ
    have heval : ψ (midpoint ℝ x y) = (ψ x + ψ y) / 2 := by
      rw [AffineMap.map_midpoint, midpoint_eq_smul_add]
      simp [invOf_eq_inv, div_eq_mul_inv, mul_comm]
    rcases lt_trichotomy (ψ x) 0 with hneg | hzero | hpos
    · have hyle : ψ y ≤ 0 := by
        rcases hy ψ hψ with h | h
        · exact le_of_eq (sign_eq_zero_iff.mp h)
        · exact le_of_lt (sign_eq_neg_one_iff.mp (h.trans (sign_neg hneg)))
      rw [sign_neg hneg, sign_neg (show ψ (midpoint ℝ x y) < 0 by
        rw [heval]; linarith)]
    · have hyzero : ψ y = 0 := by
        rcases hy ψ hψ with h | h
        · exact sign_eq_zero_iff.mp h
        · exact sign_eq_zero_iff.mp (by simpa [hzero] using h)
      simp [heval, hzero, hyzero]
    · have hyge : 0 ≤ ψ y := by
        rcases hy ψ hψ with h | h
        · exact le_of_eq (sign_eq_zero_iff.mp h).symm
        · exact le_of_lt (sign_eq_one_iff.mp (h.trans (sign_pos hpos)))
      rw [sign_pos hpos, sign_pos (show 0 < ψ (midpoint ℝ x y) by
        rw [heval]; linarith)]
  rw [hx] at hm
  exact ((midpoint_eq_left_iff ℝ).mp (Set.mem_singleton_iff.mp hm)).symm

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Every extended affine root has an actual root element whose value equals
the affine root at every point of the apartment. -/
theorem exists_rootPoint_of_extendedAffineRoot
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    ∃ (a : relativeRoots i), ψ.linear = rootForm i a ∧
      ∃ g : rationalPoints G, g ∈ rootGroupPoints i a ∧ g ≠ 1 ∧
        ∀ x : D.Apartment, x.val a g = ((ψ x : ℝ) : WithTop ℝ) := by
  obtain ⟨a, hlin, hjump⟩ := hψ
  have hnot : ¬ D.affineRootGroup a ψ ≤ D.affineRootGroupPlus a ψ :=
    fun hle => hjump (le_antisymm (D.affineRootGroupPlus_le a ψ) hle)
  change ¬ ∀ g, g ∈ D.affineRootGroup a ψ → g ∈ D.affineRootGroupPlus a ψ at hnot
  push Not at hnot
  obtain ⟨g, hg, hgn⟩ := hnot
  have hgroot := D.affineRootGroup_le_rootGroupPoints a ψ hg
  refine ⟨a, hlin, g, hgroot, ?_, fun x => ?_⟩
  · rintro rfl
    exact hgn (D.affineRootGroupPlus a ψ).one_mem
  · apply le_antisymm
    · exact le_of_not_gt fun hlt =>
        hgn ((D.mem_affineRootGroupPlus_iff hlin x).mpr ⟨hgroot, hlt⟩)
    · exact ((D.mem_affineRootGroup_iff hlin x).mp hg).2

/-- Opposite factors show that the extended affine roots are closed under
negation, without any extra apartment axiom. -/
theorem neg_mem_extendedAffineRoots
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    -ψ ∈ D.extendedAffineRoots := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨a, hlin, g, hg, hg1, hval⟩ := D.exists_rootPoint_of_extendedAffineRoot hψ
  obtain ⟨p, hp⟩ := ((rootRankOneFactorization k G hG S i hi a a.2 g hg hg1).1).exists
  have hflip := hp.weylAction_eq_neg i hi.isSplitSubtorus.1 a.2.1 hg hg1
  have hnega : -a.val ∈ relativeRoots i := by
    rw [← hflip]
    exact weylAction_mapsTo_relativeRoots i _ a.2
  let b : relativeRoots i := ⟨-a.val, hnega⟩
  let x : D.Apartment := Classical.arbitrary D.Apartment
  have hpval := x.isValuation.opposite a a.2 g hg hg1
    p.1 hp.1 p.2 hp.2.1 hp.2.2
  rw [hval x] at hpval
  have hpt : x.val b p.1 = ((-ψ x : ℝ) : WithTop ℝ) :=
    withTop_eq_neg_of_add_eq_zero hpval
  have hroot := D.affineFunctional_mem_extendedAffineRoots (a := b) hp.1 hpt
  have heq : D.affineFunctional b x (-ψ x) = -ψ := by
    apply AffineMap.ext_linear (p := x)
    · rw [D.affineFunctional_linear, AffineMap.neg_linear, hlin]
      apply LinearMap.ext
      intro v
      refine Submodule.Quotient.induction_on _ v fun w => ?_
      simp only [rootForm_mk, b, eval_neg_char, LinearMap.neg_apply]
    · simp [D.affineFunctional_apply]
  rwa [heq] at hroot

/-- A nonnegative extended root at `x` stays nonnegative at any apartment
point fixed by the sharp fixer of `x`. -/
theorem extendedAffineRoot_nonneg_of_fixed_by_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {x y : D.Apartment}
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} →
      g • D.apartmentMap y = D.apartmentMap y)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots)
    (hx : 0 ≤ ψ x) : 0 ≤ ψ y := by
  obtain ⟨a, -, g, hg, -, hval⟩ := D.exists_rootPoint_of_extendedAffineRoot hψ
  have hgx : g ∈ D.filtration x a 0 := by
    refine ⟨hg, ?_⟩
    rw [hval x]
    exact WithTop.coe_le_coe.mpr hx
  have hgy := D.mem_filtration_of_mem_rootGroup_of_fixing_apartmentMap hG hi y a.2 hg
    (hfix g (D.filtration_le_sharpFixer x a.2 hgx))
  have hle := hgy.2
  rw [hval y, WithTop.coe_le_coe] at hle
  exact hle

/-- The apartment fixed locus of the sharp fixer of `x` is contained in the
formal closure of the facet of `x`. -/
theorem mem_facetClosure_of_fixed_by_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {x y : D.Apartment}
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} →
      g • D.apartmentMap y = D.apartmentMap y) :
    y ∈ AffineRootSystem.facetClosure D.affineRoots x := by
  intro ψ hψ
  have hψext := D.affineRoots_subset_extendedAffineRoots hψ
  have hψneg := D.neg_mem_extendedAffineRoots hG hi hψext
  rcases lt_trichotomy (ψ x) 0 with hneg | hzero | hpos
  · have hy : ψ y ≤ 0 := by
      have h := D.extendedAffineRoot_nonneg_of_fixed_by_sharpFixer hG hi hfix
        hψneg (show 0 ≤ (-ψ) x by change 0 ≤ -ψ x; linarith)
      change 0 ≤ -ψ y at h
      linarith
    rcases lt_or_eq_of_le hy with hyneg | hyzero
    · exact Or.inr ((sign_neg hyneg).trans (sign_neg hneg).symm)
    · exact Or.inl (by rw [hyzero, sign_zero])
  · have hyle := D.extendedAffineRoot_nonneg_of_fixed_by_sharpFixer hG hi hfix
      hψext (by rw [hzero])
    have hyge := D.extendedAffineRoot_nonneg_of_fixed_by_sharpFixer hG hi hfix
      hψneg (show 0 ≤ (-ψ) x by change 0 ≤ -ψ x; rw [hzero, neg_zero])
    change 0 ≤ -ψ y at hyge
    exact Or.inl (sign_eq_zero_iff.mpr (by linarith))
  · have hy := D.extendedAffineRoot_nonneg_of_fixed_by_sharpFixer hG hi hfix hψext hpos.le
    rcases eq_or_lt_of_le hy with hyzero | hypos
    · exact Or.inl (by rw [← hyzero, sign_zero])
    · exact Or.inr ((sign_pos hypos).trans (sign_pos hpos).symm)

/-- A vertex is the only point of the base apartment fixed by its sharp
fixer. This uses neither local compactness nor extra apartment axioms. -/
theorem eq_of_vertex_of_fixed_by_sharpFixer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {x y : D.Apartment} (hx : AffineRootSystem.IsVertex D.affineRoots x)
    (hfix : ∀ g : rationalPoints G, g ∈ D.sharpFixer {x} →
      g • D.apartmentMap y = D.apartmentMap y) : y = x :=
  hx.eq_of_mem_facetClosure (D.mem_facetClosure_of_fixed_by_sharpFixer hG hi hfix)

/-- Every sharp fixer lies in every character-valuation kernel. -/
theorem sharpFixer_le_characterValuationKernel
    (hS : IsSplitTorus S.toGrp) {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation k Γ₀) (Ω : Set D.Apartment) :
    D.sharpFixer Ω ≤ characterValuationKernel v G := by
  apply iSup_le
  intro a g hg
  exact rootGroupPoints_le_characterValuationKernel hS i a a.2.1 v
    (D.mem_rootFixer.mp hg).1

end KPApartmentData

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {v : Valuation k (WithZero (Multiplicative ℤ))}
    (B : IntegerValuationBuildingData v G)

/-- The sharp fixer of an apartment point lies in its actual one-stabilizer. -/
theorem sharpFixer_le_oneStabilizer (x : B.Apartment) :
    B.sharpFixer {x} ≤ B.oneStabilizer (B.apartmentMap x) :=
  le_inf (B.apartment.sharpFixer_le_characterValuationKernel
    B.isMaximalSplitTorus.isSplitSubtorus.1 v {x}) (B.sharpFixer_le_fixer x)

/-- The actual one-stabilizer of a vertex fixes no other point of its
displayed apartment. -/
theorem eq_of_vertex_of_fixed_by_oneStabilizer
    {x y : B.Apartment} (hx : AffineRootSystem.IsVertex B.affineRoots x)
    (hfix : ∀ g : rationalPoints G, g ∈ B.oneStabilizer (B.apartmentMap x) →
      g • B.apartmentMap y = B.apartmentMap y) : y = x :=
  B.apartment.eq_of_vertex_of_fixed_by_sharpFixer B.isConnectedReductive
    B.isMaximalSplitTorus hx (fun g hg => hfix g (B.sharpFixer_le_oneStabilizer x hg))

end IntegerValuationBuildingData

/-- The actual one-stabilizer of any apartment vertex fixes no other
apartment point, over an arbitrary integer-valued field. -/
def ApartmentVertexRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    (B : IntegerValuationBuildingData v G) (x y : B.Apartment),
    AffineRootSystem.IsVertex B.affineRoots x →
    (∀ g : rationalPoints G, g ∈ B.oneStabilizer (B.apartmentMap x) →
      g • B.apartmentMap y = B.apartmentMap y) →
    y = x

/-- Apartment vertex rigidity follows from the root-jump and opposite-factor
arguments above. -/
theorem apartmentVertexRigidity : ApartmentVertexRigidityStatement.{u} := by
  intro k _ G _ v B x y hx hfix
  exact B.eq_of_vertex_of_fixed_by_oneStabilizer hx hfix

end Langlands.Geometry.Building
