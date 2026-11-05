import Langlands.Geometry.Building.AffineIwahoriTitsProjection
import Langlands.Geometry.Building.AffineRankOneTwoCellStatement
import Langlands.Geometry.Building.AffineChamberWallComparisonStatement
import Langlands.Geometry.Building.AffineChamberSeparation
import Langlands.Geometry.Building.IwahoriDoubleCosetComponents
import Langlands.Geometry.Building.ParahoricBuildingAxioms
import Langlands.Group.TitsSystemMulCell
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-!
# Assembling the actual affine Iwahori–Tits system on `G(F)^0`

The proof of KP Theorem 7.5.1, carried out directly on `G(F)^0` with `B = P_C ∩ G(F)^0`,
`N = N(F) ∩ G(F)^0` and the literal projection to `P.affinePart`. The group-theoretic facts
used by the source proof are collected, unproved, in the Prop structure
`AffineIwahoriTitsInputs`; `affineIwahoriTitsWith_of_inputs` derives every Tits axiom and
saturation from them, the apartment axioms and a comparison realizing the apartment action.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type*} {A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A root that is positive at a point of the closure of the facet of `x` is positive on the
whole facet of `x`. -/
theorem pos_of_mem_facetClosure {x y : A} (hy : y ∈ facetClosure Ψ x) {f : A →ᵃ[ℝ] ℝ}
    (hf : f ∈ Ψ) (hpos : 0 < f y) {z : A} (hz : z ∈ facet Ψ x) : 0 < f z := by
  have h1 : SignType.sign (f y) = 1 := sign_pos hpos
  have hx : SignType.sign (f x) = 1 := by
    rcases hy f hf with h | h
    · rw [h1] at h
      exact absurd h (by decide)
    · rw [← h, h1]
  have hz' := hz f hf
  rw [hx, eq_comm, sign_eq_one_iff] at hz'
  exact hz'

/-- A chamber-simple root vanishes at some point of the closure of the chamber. -/
theorem exists_mem_facetClosure_of_mem_simpleAffineRoots {C : Set A} {ψ : A →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ simpleAffineRoots Ψ C) :
    ∃ x y, facet Ψ x = C ∧ y ∈ facetClosure Ψ x ∧ ψ y = 0 := by
  obtain ⟨Fa, ⟨⟨y, rfl⟩, x, hxC, hsub⟩, hspan⟩ := hψ.2.2.2.2
  refine ⟨x, y, hxC, hsub (mem_facet_self Ψ y), ?_⟩
  have hy : y ∈ affineSpan ℝ (facet Ψ y) := subset_affineSpan ℝ _ (mem_facet_self Ψ y)
  rw [hspan] at hy
  exact mem_hyperplane.1 hy

end AffineRootSystem

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- If the apartment form of `β` is minus that of `α`, then `β = -α`: the lattice pairing of
the split torus `S` is perfect. -/
theorem coe_eq_neg_of_rootForm_eq_neg {α β : relativeRoots P.i}
    (h : rootForm P.i β = -rootForm P.i α) :
    (β : characterLattice P.S) = -(α : characterLattice P.S) := by
  have hT : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  have hpp := hT.isPerfPair_latticePairing
  have hzero : latticePairing P.S ((β : characterLattice P.S) + α) = 0 := by
    ext ν
    have hν := congrArg (fun f => f (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν))) h
    simp only [LinearMap.neg_apply, rootForm_mk, RealTorusSpace.eval_tmul, one_mul] at hν
    rw [map_add, LinearMap.add_apply, LinearMap.zero_apply]
    have hr : ((latticePairing P.S (β : characterLattice P.S) ν : ℤ) : ℝ) +
        (latticePairing P.S (α : characterLattice P.S) ν : ℤ) = 0 := by
      rw [hν]
      ring
    exact_mod_cast hr
  exact eq_neg_of_add_eq_zero_left (hpp.bijective_left.injective (hzero.trans (map_zero _).symm))

/-- Under the apartment axioms the actual relative roots are stable under negation, with the
negated apartment form. -/
theorem exists_neg_relativeRoot (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (α : relativeRoots P.i) :
    ∃ β : relativeRoots P.i, (β : characterLattice P.S) = -(α : characterLattice P.S) ∧
      rootForm P.i β = -rootForm P.i α := by
  have hα : rootForm P.i α ∈ AffineRootSystem.derivativeRoots P.affineRoots := by
    rw [hA.derivativeRoots_affineRoots]
    exact ⟨α, rfl⟩
  obtain ⟨ψ, hψ, hlin⟩ := AffineRootSystem.mem_derivativeRoots.1 hα
  have hβ : (-ψ).linear ∈ AffineRootSystem.derivativeRoots P.affineRoots :=
    AffineRootSystem.linear_mem_derivativeRoots (hA.isAffineRootSystem_affineRoots.neg_mem hψ)
  rw [hA.derivativeRoots_affineRoots] at hβ
  obtain ⟨β, hβ⟩ := hβ
  have hform : rootForm P.i β = -rootForm P.i α := by
    rw [hβ, ← hlin]
    rfl
  exact ⟨β, P.coe_eq_neg_of_rootForm_eq_neg hform, hform⟩

/-- `U_ψ ⊆ P_Ω` when `ψ` has derivative `α` and is non-negative on `Ω`. -/
theorem affineRootGroup_le_parahoric {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm P.i α) {Ω : Set P.Apartment} (hΩ : ∀ x ∈ Ω, 0 ≤ ψ x) :
    P.apartment.affineRootGroup α ψ ≤ P.parahoric Ω :=
  (P.toValuationBuildingData.affineRootGroup_le_rootFixer hψ hΩ).trans
    (P.rootFixer_le_parahoric α Ω)

/-- For a chamber-simple root `ψ` with derivative `α`, `U_{-ψ+} ⊆ P_C`: every nontrivial
`u ∈ U_{-ψ+}` has a functional `ψ^u_{-a} ∈ Ψ′` with `ψ^u_{-a} > -ψ`, which is positive at a
point of the wall `ψ = 0` in the closure of `C` and hence, by AS 4, positive on `C`. -/
theorem affineRootGroupPlus_neg_le_parahoric
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) {C : Set P.Apartment}
    {ψ : P.Apartment →ᵃ[ℝ] ℝ} (hψs : ψ ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C)
    {α : relativeRoots P.i} (hψ : ψ.linear = rootForm P.i α) :
    P.apartment.affineRootGroupPlus (-(α : characterLattice P.S)) (-ψ) ≤ P.parahoric C := by
  obtain ⟨β, hβ, hform⟩ := P.exists_neg_relativeRoot hA α
  have hlin : (-ψ).linear = rootForm P.i β := by
    rw [hform, ← hψ]
    rfl
  rw [← hβ]
  intro u hu
  rcases (P.toValuationBuildingData.mem_affineRootGroupPlus_iff_reflectionFunctional hlin).1 hu
    with rfl | ⟨hu, h1, hlt⟩
  · exact one_mem _
  have hf : P.toValuationBuildingData.reflectionFunctional β u ∈
      P.apartment.extendedAffineRoots := by
    rw [← P.toValuationBuildingData.reflectionAffineRoots_eq]
    exact ⟨β, u, hu, h1, rfl⟩
  obtain ⟨x, y, hxC, hy, hψy⟩ :=
    AffineRootSystem.exists_mem_facetClosure_of_mem_simpleAffineRoots hψs
  have hfy : 0 < P.toValuationBuildingData.reflectionFunctional β u y := by
    have h := hlt y
    simp only [AffineMap.coe_neg, Pi.neg_apply, hψy, neg_zero] at h
    exact h
  have hpos : ∀ z ∈ C, 0 ≤ P.toValuationBuildingData.reflectionFunctional β u z := by
    intro z hz
    rw [← hxC] at hz
    rcases hA.mem_or_two_smul_mem _ hf with h | h
    · exact (AffineRootSystem.pos_of_mem_facetClosure hy h hfy hz).le
    · have h2 := AffineRootSystem.pos_of_mem_facetClosure hy h
        (by simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul]; linarith) hz
      simp only [AffineMap.coe_smul, Pi.smul_apply, smul_eq_mul] at h2
      linarith
  have hmem : u ∈ P.toValuationBuildingData.affineRootGroup β
      (P.toValuationBuildingData.reflectionFunctional β u) :=
    (P.toValuationBuildingData.mem_affineRootGroup_iff_reflectionFunctional
      (P.toValuationBuildingData.reflectionFunctional_linear β u)).2
      (Or.inr ⟨hu, h1, fun _ => le_rfl⟩)
  exact P.affineRootGroup_le_parahoric (P.toValuationBuildingData.reflectionFunctional_linear β u)
    hpos hmem

/-! ### The normalizer action on parahoric subgroups -/

/-- The image of `Z(F)^0` in `G(F)` consists of normalizer points. -/
theorem map_centralizerZero_le_normalizerPoints :
    P.centralizerZero.map (rationalPoints.map P.centralizer.j) ≤ normalizerPoints P.i := by
  rintro _ ⟨z, -, rfl⟩
  exact (P.centralizer.toNormalizer z).2

/-- The pointwise image `n • Ω` is the image under the actual affine action of `n`. -/
theorem smul_set_eq_image (n : normalizerPoints P.i) (Ω : Set P.Apartment) :
    n • Ω = P.apartment.normalizerAffineEquiv n '' Ω :=
  rfl

variable [P.normalizerZero.Normal]

/-- `n P_Ω n⁻¹ ⊆ P_{n • Ω}`. -/
theorem conj_mem_parahoric_smul (n : normalizerPoints P.i) {Ω : Set P.Apartment}
    {g : rationalPoints G} (hg : g ∈ P.parahoric Ω) :
    (n : rationalPoints G) * g * (n : rationalPoints G)⁻¹ ∈ P.parahoric (n • Ω) := by
  rw [← P.map_parahoric_conj n Ω]
  exact ⟨g, hg, by simp [MulAut.conj_apply]⟩

/-- `g ∈ P_{n • Ω}` if and only if `n⁻¹ g n ∈ P_Ω`. -/
theorem mem_parahoric_smul_iff (n : normalizerPoints P.i) (Ω : Set P.Apartment)
    (g : rationalPoints G) :
    g ∈ P.parahoric (n • Ω) ↔
      (n : rationalPoints G)⁻¹ * g * (n : rationalPoints G) ∈ P.parahoric Ω := by
  constructor
  · intro hg
    have h := P.conj_mem_parahoric_smul n⁻¹ hg
    simpa only [inv_smul_smul, Subgroup.coe_inv, inv_inv] using h
  · intro hg
    have h := P.conj_mem_parahoric_smul n hg
    have he : (n : rationalPoints G) * ((n : rationalPoints G)⁻¹ * g * (n : rationalPoints G)) *
        (n : rationalPoints G)⁻¹ = g := by
      group
    rwa [he] at h

/-! ### The projection to the affine part -/

/-- The underlying normalizer point of an element of `N(F) ∩ G(F)^0`. -/
abbrev normalizerPoint (n : P.normalizerInZero) : normalizerPoints P.i :=
  (P.normalizerInZeroEquiv n : normalizerPoints P.i)

/-- Under the comparison `e`, every representative acts through its image in `W_aff`. -/
theorem normalizerAffineEquiv_eq_of_comparison
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) (n : P.normalizerInZero) :
    P.apartment.normalizerAffineEquiv (P.normalizerPoint n) =
      (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) :=
  (hact (P.normalizerInZeroEquiv n)).symm

/-! ### The actual inputs -/

omit [P.normalizerZero.Normal] in
/-- The actual inputs from which the Iwahori–Tits system on `G(F)^0` is assembled, for a
chamber `C`. They transcribe to `G(F)^0` the facts used in the proof of KP Theorem 7.5.1 and
Lemma 7.5.2. Each is a hypothesis here; none is proved in this module. -/
structure AffineIwahoriTitsInputs (C : Set P.Apartment) : Prop where
  /-- Every generated parahoric lies in `G(F)^0`. -/
  parahoric_le_zeroSubgroup : ∀ Ω : Set P.Apartment, P.parahoric Ω ≤ P.zeroSubgroup
  /-- `P_C ∩ N(F) ⊆ Z(F)^0` (KP Lemma 7.5.2(1), from Corollary 7.4.9). -/
  mem_normalizerZero_of_mem_parahoric : ∀ n : normalizerPoints P.i,
    (n : rationalPoints G) ∈ P.parahoric C → n ∈ P.normalizerZero
  /-- `P_C` and `N(F) ∩ G(F)^0` generate `G(F)^0`. -/
  zeroSubgroup_le_sup :
    P.zeroSubgroup ≤ P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)
  /-- The chamber-simple reflections generate `W(Ψ)` (KP Proposition 1.3.22(1)). -/
  closure_chamberSimpleReflections :
    Subgroup.closure (AffineRootSystem.chamberSimpleReflections P.affineRoots C) = ⊤
  /-- The filtered rank-one two-cell decomposition (KP Lemma 7.1.5(3)) for `P`. -/
  twoCell : ∀ (α : relativeRoots P.i) (ψ : P.Apartment →ᵃ[ℝ] ℝ),
    ψ.linear = rootForm P.i α →
      P.apartment.affineRootGroupPlus α ψ ≠ P.apartment.affineRootGroup α ψ →
        ∃ m : normalizerPoints P.i,
          (m : rationalPoints G) ∈ P.affineRankOneSubgroup α ψ ∧
          (∀ (v : TranslationSpace P.i) (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v),
            P.apartment.normalizerAffineEquiv m = AffineRootSystem.affineReflection ψ hv.1) ∧
          (P.affineRankOneSubgroup α ψ : Set (rationalPoints G)) =
            P.affineRankOneBaseCell α ψ ∪
              P.affineRankOneReflectionCell α ψ (m : rationalPoints G)
  /-- `P_C ⊆ P_{r C} U_ψ` for a chamber-simple root `ψ` with reflection `r`: the inclusion
  `s I ⊆ I s U_α` of KP (7.5.1). -/
  simpleFactorization : ∀ ψ ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C,
    ∀ α : relativeRoots P.i, ψ.linear = rootForm P.i α →
      ∀ (v : TranslationSpace P.i) (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v),
        ∀ b ∈ P.parahoric C,
          ∃ b' ∈ P.parahoric (AffineRootSystem.affineReflection ψ hv.1 '' C),
            ∃ u ∈ P.apartment.affineRootGroup α ψ, b = b' * u
  /-- `U_a(F) ∩ P_x ⊆ U_{a,x,0}` (KP Proposition 7.3.12). -/
  rootGroup_inf_parahoricAt_le : ∀ (α : relativeRoots P.i) (x : P.Apartment),
    rootGroupPoints P.i α ⊓ P.parahoricAt x ≤ P.apartment.filtration x α 0
  /-- `⋂_{n ∈ N(F) ∩ G(F)^0} P_{n C} ⊆ Z(F)^0` (the saturation step of KP Theorem 7.5.1). -/
  mem_centralizerZero_of_forall_mem_parahoric : ∀ g : rationalPoints G,
    (∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) →
        g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j)

/-! ### The Tits axioms -/

/-- If `P_C ∩ N(F) ⊆ Z(F)^0`, the kernel of the projection is `B ∩ N`. -/
theorem ker_affineTitsProjection {C : Set P.Apartment}
    (h : ∀ n : normalizerPoints P.i,
      (n : rationalPoints G) ∈ P.parahoric C → n ∈ P.normalizerZero) :
    P.affineTitsProjection.ker = (P.parahoricInZero C).subgroupOf P.normalizerInZero := by
  ext t
  rw [MonoidHom.mem_ker, P.affineTitsProjection_eq_one_iff, centralizerZeroInZero, Subgroup.mem_subgroupOf,
    parahoricInZero, Subgroup.mem_subgroupOf]
  exact ⟨fun ht => P.map_centralizerZero_le_parahoric C ht,
    fun ht => P.mem_normalizerZero_iff.1 (h (P.normalizerPoint t) ht)⟩

omit [P.normalizerZero.Normal] in
/-- If `P_C ⊆ G(F)^0` and `G(F)^0 ⊆ P_C ⊔ (N(F) ∩ G(F)^0)`, then `B` and `N` generate
`G(F)^0`. -/
theorem parahoricInZero_sup_normalizerInZero {C : Set P.Apartment}
    (hle : P.parahoric C ≤ P.zeroSubgroup)
    (hgen : P.zeroSubgroup ≤ P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup)) :
    P.parahoricInZero C ⊔ P.normalizerInZero = ⊤ := by
  have key : (P.parahoricInZero C ⊔ P.normalizerInZero).map P.zeroSubgroup.subtype =
      P.parahoric C ⊔ (normalizerPoints P.i ⊓ P.zeroSubgroup) := by
    rw [Subgroup.map_sup, P.parahoricInZero_map C hle, normalizerInZero,
      Subgroup.subgroupOf_map_subtype]
  rw [eq_top_iff]
  intro g _
  have hg : (g : rationalPoints G) ∈
      (P.parahoricInZero C ⊔ P.normalizerInZero).map P.zeroSubgroup.subtype :=
    key ▸ hgen g.2
  obtain ⟨x, hx, hxg⟩ := hg
  rwa [show x = g from Subtype.ext hxg] at hx

/-- Generation of `W(Ψ)` by the chamber-simple reflections transfers along `e`. -/
theorem closure_chamberSimpleInAffinePart {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hgen : Subgroup.closure (AffineRootSystem.chamberSimpleReflections P.affineRoots C) = ⊤) :
    Subgroup.closure (P.chamberSimpleInAffinePart e C) = ⊤ := by
  have himage : P.chamberSimpleInAffinePart e C =
      e.symm.toMonoidHom '' AffineRootSystem.chamberSimpleReflections P.affineRoots C := by
    ext s
    constructor
    · intro hs
      exact ⟨e s, hs, e.symm_apply_apply s⟩
    · rintro ⟨t, ht, rfl⟩
      show e (e.symm t) ∈ AffineRootSystem.chamberSimpleReflections P.affineRoots C
      rwa [e.apply_symm_apply]
  rw [himage, ← MonoidHom.map_closure, hgen]
  exact Subgroup.map_top_of_surjective _ e.symm.surjective

/-- The transported chamber-simple elements are involutions. -/
theorem chamberSimpleInAffinePart_mul_self {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots} {s : P.affinePart}
    (hs : s ∈ P.chamberSimpleInAffinePart e C) : s * s = 1 :=
  e.injective (by rw [map_mul, map_one]; exact AffineRootSystem.chamberSimpleReflection_mul_self hs)

/-- The transported chamber-simple elements are nontrivial. -/
theorem chamberSimpleInAffinePart_ne_one {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots} {s : P.affinePart}
    (hs : s ∈ P.chamberSimpleInAffinePart e C) : s ≠ 1 := by
  rintro rfl
  have h1 : e 1 ∈ AffineRootSystem.chamberSimpleReflections P.affineRoots C := hs
  rw [map_one] at h1
  exact AffineRootSystem.one_notMem_chamberSimpleReflections C h1

/-- The data of a chamber-simple element of `W_aff`: its simple root, derivative, jump and
coroot reflection. -/
theorem exists_simple_data {C : Set P.Apartment}
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots} {s : P.affinePart}
    (hs : e s ∈ AffineRootSystem.chamberSimpleReflections P.affineRoots C) :
    ∃ ψ ∈ AffineRootSystem.simpleAffineRoots P.affineRoots C, ∃ α : relativeRoots P.i,
      ψ.linear = rootForm P.i α ∧
      P.apartment.affineRootGroupPlus α ψ ≠ P.apartment.affineRootGroup α ψ ∧
      ∃ (v : TranslationSpace P.i) (hv : AffineRootSystem.IsCoroot P.affineRoots ψ v),
        (e s : P.Apartment ≃ᵃ[ℝ] P.Apartment) = AffineRootSystem.affineReflection ψ hv.1 := by
  obtain ⟨ψ, hψs, v, hv, hes⟩ := hs
  obtain ⟨α, hψ, hnot⟩ := hψs.1.1
  refine ⟨ψ, hψs, α, hψ, fun heq => hnot fun u hu => ?_, v, hv, hes⟩
  refine ⟨u, ?_, 1, one_mem _, mul_one u⟩
  rw [SetLike.mem_coe, heq]
  exact hu

omit [P.normalizerZero.Normal] in
/-- The subgroup generated by `U_ψ`, `U_{-ψ}` and `Z(F)^0` lies in `G(F)^0` once every
generated parahoric does. -/
theorem affineRankOneSubgroup_le_zeroSubgroup
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hle : ∀ Ω : Set P.Apartment, P.parahoric Ω ≤ P.zeroSubgroup)
    {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ.linear = rootForm P.i α) :
    P.affineRankOneSubgroup α ψ ≤ P.zeroSubgroup := by
  obtain ⟨β, hβ, hform⟩ := P.exists_neg_relativeRoot hA α
  have hlin : (-ψ).linear = rootForm P.i β := by
    rw [hform, ← hψ]
    rfl
  refine sup_le (sup_le ?_ ?_) ((P.map_centralizerZero_le_parahoric ∅).trans (hle ∅))
  · exact (P.affineRootGroup_le_parahoric hψ (Ω := {x | 0 ≤ ψ x}) fun x hx => hx).trans (hle _)
  · rw [← hβ]
    exact (P.affineRootGroup_le_parahoric hlin (Ω := {x | 0 ≤ (-ψ) x}) fun x hx => hx).trans
      (hle _)

omit [P.normalizerZero.Normal] in
/-- An element of `N(F)` lying in `G(F)^0`, as an element of `N(F) ∩ G(F)^0`. -/
def toNormalizerInZero (m : normalizerPoints P.i)
    (hm : (m : rationalPoints G) ∈ P.zeroSubgroup) : P.normalizerInZero :=
  ⟨⟨m, hm⟩, Subgroup.mem_subgroupOf.2 m.2⟩

omit [P.normalizerZero.Normal] in
@[simp] theorem normalizerPoint_toNormalizerInZero (m : normalizerPoints P.i)
    (hm : (m : rationalPoints G) ∈ P.zeroSubgroup) :
    P.normalizerPoint (P.toNormalizerInZero m hm) = m :=
  rfl

/-- Under the comparison `e`, a representative `n` moves a subset `Ω` by `e (π n)`. -/
theorem normalizerPoint_smul_eq
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) (n : P.normalizerInZero) (Ω : Set P.Apartment) :
    P.normalizerPoint n • Ω =
      (e (P.affineTitsProjection n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' Ω := by
  rw [smul_set_eq_image, P.normalizerAffineEquiv_eq_of_comparison hact n]

/-- A representative acting on the apartment as `e s` projects to `s`. -/
theorem affineTitsProjection_eq_of_action
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) {n : P.normalizerInZero} {s : P.affinePart}
    (h : P.apartment.normalizerAffineEquiv (P.normalizerPoint n) =
      (e s : P.Apartment ≃ᵃ[ℝ] P.Apartment)) :
    P.affineTitsProjection n = s := by
  apply e.injective
  apply Subtype.ext
  rw [← P.normalizerAffineEquiv_eq_of_comparison hact n, h]

/-- **The Tits multiplication axiom.** For a chamber-simple `s` with simple root `ψ` and
reflection `r`, apply `TitsSystem.forall_mul_mem_cell_of_rankOne` with `B' = P_{r C}`,
`U = U_ψ` and `P = {w | ψ ≥ 0 on e(w) C}`. The rank-one two-cell decomposition places
`n U_ψ n⁻¹` in `U_{-ψ+} Z(F)^0 U_ψ ⊆ P_C` or in `U_ψ m Z(F)^0 U_ψ ⊆ B s B`. -/
theorem mul_mem_cell_of_inputs (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) (h : P.AffineIwahoriTitsInputs C) :
    ∀ s ∈ P.chamberSimpleInAffinePart e C, ∀ n m : P.normalizerInZero,
      P.affineTitsProjection n = s → ∀ b ∈ P.parahoricInZero C,
        (n : P.zeroSubgroup) * b * m ∈
          Langlands.Group.TitsSystem.cell (P.parahoricInZero C) P.affineTitsProjection
              (P.affineTitsProjection m) ∪
            Langlands.Group.TitsSystem.cell (P.parahoricInZero C) P.affineTitsProjection
              (s * P.affineTitsProjection m) := by
  refine Langlands.Group.TitsSystem.forall_mul_mem_cell_of_rankOne
    (fun s hs => P.chamberSimpleInAffinePart_mul_self hs) ?_
  intro s hs
  obtain ⟨ψ, hψs, α, hψ, hjump, v, hv, hes⟩ := P.exists_simple_data hs
  obtain ⟨m, hmL, hmact, hcarrier⟩ := h.twoCell α ψ hψ hjump
  have hpos : ∀ x ∈ C, 0 < ψ x := hψs.1.2
  have hUC : P.apartment.affineRootGroup α ψ ≤ P.parahoric C :=
    P.affineRootGroup_le_parahoric hψ fun x hx => (hpos x hx).le
  have hU0 : P.apartment.affineRootGroup α ψ ≤ P.zeroSubgroup :=
    hUC.trans (h.parahoric_le_zeroSubgroup C)
  have hL0 := P.affineRankOneSubgroup_le_zeroSubgroup hA h.parahoric_le_zeroSubgroup hψ
  have hrr : AffineRootSystem.affineReflection ψ hv.1 ''
      (AffineRootSystem.affineReflection ψ hv.1 '' C) = C := by
    rw [Set.image_image]
    simp only [AffineRootSystem.affineReflection_involutive ψ hv.1 _, Set.image_id']
  have hm0 : P.affineTitsProjection (P.toNormalizerInZero m (hL0 hmL)) = s :=
    P.affineTitsProjection_eq_of_action hact ((hmact v hv).trans hes.symm)
  refine ⟨{g | (g : rationalPoints G) ∈
      P.parahoric (AffineRootSystem.affineReflection ψ hv.1 '' C)},
    {g | (g : rationalPoints G) ∈ P.apartment.affineRootGroup α ψ},
    {w | ∀ x ∈ C, 0 ≤ ψ ((e w : P.Apartment ≃ᵃ[ℝ] P.Apartment) x)}, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb', u, hu, hbu⟩ :=
      h.simpleFactorization ψ hψs α hψ v hv b (Subgroup.mem_subgroupOf.1 hb)
    refine ⟨b * (⟨u, hU0 hu⟩ : P.zeroSubgroup)⁻¹, ?_, ⟨u, hU0 hu⟩, hu, by group⟩
    show ((b * (⟨u, hU0 hu⟩ : P.zeroSubgroup)⁻¹ : P.zeroSubgroup) : rationalPoints G) ∈
      P.parahoric (AffineRootSystem.affineReflection ψ hv.1 '' C)
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hbu, mul_inv_cancel_right]
    exact hb'
  · intro n hn b' hb'
    rw [parahoricInZero, Subgroup.mem_subgroupOf]
    have h1 := P.conj_mem_parahoric_smul (P.normalizerPoint n) hb'
    rwa [P.normalizerPoint_smul_eq hact, hn, hes, hrr] at h1
  · intro n hn u hu
    have ht : P.affineTitsProjection (n * (P.toNormalizerInZero m (hL0 hmL))⁻¹) = 1 := by
      rw [map_mul, map_inv, hn, hm0, mul_inv_cancel]
    rw [P.affineTitsProjection_eq_one_iff] at ht
    have hnL : ((n : P.zeroSubgroup) : rationalPoints G) ∈ P.affineRankOneSubgroup α ψ := by
      have hn' : ((n : P.zeroSubgroup) : rationalPoints G) =
          (((n * (P.toNormalizerInZero m (hL0 hmL))⁻¹ : P.normalizerInZero) :
            P.zeroSubgroup) : rationalPoints G) * m := by
        simp [toNormalizerInZero]
      rw [hn']
      exact mul_mem (P.map_centralizerZero_le_affineRankOneSubgroup α ψ ht) hmL
    have hx : ((n : P.zeroSubgroup) : rationalPoints G) * u *
        ((n : P.zeroSubgroup) : rationalPoints G)⁻¹ ∈ P.affineRankOneSubgroup α ψ :=
      mul_mem (mul_mem hnL (P.affineRootGroup_le_affineRankOneSubgroup α ψ hu)) (inv_mem hnL)
    rw [← SetLike.mem_coe, hcarrier] at hx
    rcases hx with hx | hx
    · left
      show _ ∈ (P.parahoric C).subgroupOf P.zeroSubgroup
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨_, ⟨a, ha, z, hz, rfl⟩, u', hu', hx⟩ := hx
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hx]
      exact mul_mem (mul_mem (P.affineRootGroupPlus_neg_le_parahoric hA hψs hψ ha)
        (P.map_centralizerZero_le_parahoric C hz)) (hUC hu')
    · right
      obtain ⟨_, ⟨_, ⟨u1, hu1, _, rfl, rfl⟩, z, hz, rfl⟩, u2, hu2, hx⟩ := hx
      have hz0 : z ∈ P.zeroSubgroup :=
        (P.map_centralizerZero_le_parahoric C).trans (h.parahoric_le_zeroSubgroup C) hz
      have hz1 : P.affineTitsProjection
          (P.toNormalizerInZero ⟨z, P.map_centralizerZero_le_normalizerPoints hz⟩ hz0) = 1 :=
        (P.affineTitsProjection_eq_one_iff _).2 hz
      refine ⟨P.toNormalizerInZero m (hL0 hmL) *
          P.toNormalizerInZero ⟨z, P.map_centralizerZero_le_normalizerPoints hz⟩ hz0,
        by rw [map_mul, hm0, hz1, mul_one], ⟨u1, hU0 hu1⟩,
        Subgroup.mem_subgroupOf.2 (hUC hu1), ⟨u2, hU0 hu2⟩,
        Subgroup.mem_subgroupOf.2 (hUC hu2), ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hx]
      simp [toNormalizerInZero, mul_assoc]
  · intro w hw m' hm' u hu
    rw [parahoricInZero, Subgroup.mem_subgroupOf]
    have h1 : (u : rationalPoints G) ∈ P.parahoric (P.normalizerPoint m' • C) := by
      rw [P.normalizerPoint_smul_eq hact, hm']
      refine P.affineRootGroup_le_parahoric hψ ?_ hu
      rintro _ ⟨x, hx, rfl⟩
      exact hw x hx
    have h2 := (P.mem_parahoric_smul_iff (P.normalizerPoint m') C u).1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact h2
  · intro w
    have hD := AffineRootSystem.IsChamber.image_affineWeylGroup hC (e w)
    rcases AffineRootSystem.IsChamber.mem_positiveRoots_or_mem_negativeRoots hD hψs.1.1
      with hp | hn
    · left
      intro x hx
      exact (hp.2 _ ⟨x, hx, rfl⟩).le
    · right
      intro x hx
      have h1 : ((e (s * w) : AffineRootSystem.affineWeylGroup P.affineRoots) :
          P.Apartment ≃ᵃ[ℝ] P.Apartment) x =
          AffineRootSystem.affineReflection ψ hv.1
            ((e w : P.Apartment ≃ᵃ[ℝ] P.Apartment) x) := by
        rw [map_mul, Subgroup.coe_mul, hes]
        rfl
      rw [h1, AffineRootSystem.apply_affineReflection]
      exact (neg_pos.2 (hn.2 _ ⟨x, hx, rfl⟩)).le

/-- **The Tits nondegeneracy axiom.** For a chamber-simple `s` with simple root `ψ` take
`u ∈ U_ψ ∖ U_{ψ+}`. If `n u n⁻¹ ∈ P_C` then `u ∈ P_{r C}`, so `u ∈ P_y` at the point `y = r x`
for `x ∈ C`, where `ψ y < 0`; KP Proposition 7.3.12 then gives `x_α(u) ≥ 0` at `y`, while
`x_α(u) = ψ(y)` there. -/
theorem conj_not_le_of_inputs {C : Set P.Apartment}
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) (h : P.AffineIwahoriTitsInputs C) :
    ∀ s ∈ P.chamberSimpleInAffinePart e C, ∀ n : P.normalizerInZero,
      P.affineTitsProjection n = s → ∃ b ∈ P.parahoricInZero C,
        (n : P.zeroSubgroup) * b * (n : P.zeroSubgroup)⁻¹ ∉ P.parahoricInZero C := by
  intro s hs n hn
  obtain ⟨ψ, hψs, α, hψ, hjump, v, hv, hes⟩ := P.exists_simple_data hs
  have hUC : P.apartment.affineRootGroup α ψ ≤ P.parahoric C :=
    P.affineRootGroup_le_parahoric hψ fun x hx => (hψs.1.2 x hx).le
  obtain ⟨u, hu, hu'⟩ : ∃ u ∈ P.apartment.affineRootGroup α ψ,
      u ∉ P.apartment.affineRootGroupPlus α ψ := by
    by_contra hcon
    exact hjump (le_antisymm (KPApartmentData.affineRootGroupPlus_le (D := P.apartment) _ _)
      fun u hu => by_contra fun hu' => hcon ⟨u, hu, hu'⟩)
  have hu0 : u ∈ P.zeroSubgroup := h.parahoric_le_zeroSubgroup C (hUC hu)
  refine ⟨⟨u, hu0⟩, Subgroup.mem_subgroupOf.2 (hUC hu), fun hcontra => ?_⟩
  rw [parahoricInZero, Subgroup.mem_subgroupOf] at hcontra
  have h1 : u ∈ P.parahoric ((P.normalizerPoint n)⁻¹ • C) := by
    rw [P.mem_parahoric_smul_iff, Subgroup.coe_inv, inv_inv]
    exact hcontra
  have hset : (P.normalizerPoint n)⁻¹ • C = AffineRootSystem.affineReflection ψ hv.1 '' C := by
    rw [show (P.normalizerPoint n)⁻¹ = P.normalizerPoint n⁻¹ from rfl,
      P.normalizerPoint_smul_eq hact, map_inv, hn,
      inv_eq_of_mul_eq_one_right (P.chamberSimpleInAffinePart_mul_self hs), hes]
  rw [hset] at h1
  obtain ⟨x, -, hxC⟩ := hC
  have hx : x ∈ C := hxC ▸ AffineRootSystem.mem_facet_self P.affineRoots x
  have hy : u ∈ P.parahoricAt (AffineRootSystem.affineReflection ψ hv.1 x) :=
    P.parahoric_anti (Ω' := AffineRootSystem.affineReflection ψ hv.1 '' C)
      (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ hx)) h1
  have hfil := h.rootGroup_inf_parahoricAt_le α (AffineRootSystem.affineReflection ψ hv.1 x)
    (Subgroup.mem_inf.2
      ⟨KPApartmentData.affineRootGroup_le_rootGroupPoints (D := P.apartment) _ _ hu, hy⟩)
  rw [KPApartmentData.mem_filtration] at hfil
  have hle := ((KPApartmentData.mem_affineRootGroup_iff (D := P.apartment) hψ
    (AffineRootSystem.affineReflection ψ hv.1 x)).1 hu).2
  have hnlt := fun hlt => hu' ((KPApartmentData.mem_affineRootGroupPlus_iff (D := P.apartment) hψ
    (AffineRootSystem.affineReflection ψ hv.1 x)).2 ⟨hfil.1, hlt⟩)
  have heq := le_antisymm (not_lt.1 hnlt) hle
  have h0 := hfil.2
  rw [heq, AffineRootSystem.apply_affineReflection, WithTop.coe_le_coe] at h0
  linarith [hψs.1.2 x hx]

/-- If `g ∈ G(F)^0` lies in `n P_C n⁻¹` for every `n ∈ N(F) ∩ G(F)^0`, then `g ∈ Z(F)^0`. -/
theorem mem_centralizerZero_of_mem_iInf {C : Set P.Apartment}
    (h : P.AffineIwahoriTitsInputs C) {g : P.zeroSubgroup}
    (hg : g ∈ ⨅ n : P.normalizerInZero,
      (P.parahoricInZero C).map (MulAut.conj (n : P.zeroSubgroup)).toMonoidHom) :
    (g : rationalPoints G) ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  refine h.mem_centralizerZero_of_forall_mem_parahoric g fun n' hn' => ?_
  obtain ⟨b, hb, hbg⟩ := Subgroup.mem_iInf.1 hg (P.toNormalizerInZero n' hn')
  rw [← hbg]
  exact P.conj_mem_parahoric_smul n' (Subgroup.mem_subgroupOf.1 hb)

/-- **Saturation** (TS 5 of KP Definition 1.4.1). -/
theorem isSaturated_of_inputs {C : Set P.Apartment} (h : P.AffineIwahoriTitsInputs C) :
    Langlands.Group.TitsSystem.IsSaturated (P.parahoricInZero C) P.normalizerInZero := by
  have hker := P.ker_affineTitsProjection h.mem_normalizerZero_of_mem_parahoric
  apply le_antisymm
  · intro g hg
    have hZ := P.mem_centralizerZero_of_mem_iInf h hg
    exact ⟨Subgroup.mem_subgroupOf.2 (P.map_centralizerZero_le_parahoric C hZ),
      Subgroup.mem_subgroupOf.2 (P.map_centralizerZero_le_normalizerPoints hZ)⟩
  · rintro g ⟨hgB, hgN⟩
    refine Subgroup.mem_iInf.2 fun n => ?_
    have hg1 : (⟨g, hgN⟩ : P.normalizerInZero) ∈ P.affineTitsProjection.ker := by
      rw [hker]
      exact Subgroup.mem_subgroupOf.2 hgB
    have hc : n⁻¹ * ⟨g, hgN⟩ * n ∈ P.affineTitsProjection.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, MonoidHom.mem_ker.1 hg1, mul_one, map_inv,
        inv_mul_cancel]
    rw [hker, Subgroup.mem_subgroupOf] at hc
    refine ⟨_, hc, ?_⟩
    show (n : P.zeroSubgroup) * ((n : P.zeroSubgroup)⁻¹ * g * n) * (n : P.zeroSubgroup)⁻¹ = g
    group

/-- **Assembly.** The actual inputs, the apartment axioms and a comparison `e` realizing the
apartment action give the actual affine Iwahori–Tits system on `G(F)^0` for the chamber `C`. -/
theorem affineIwahoriTitsWith_of_inputs
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) {C : Set P.Apartment}
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots}
    (hact : P.IsAffineWeylComparison e) (h : P.AffineIwahoriTitsInputs C) :
    P.AffineIwahoriTitsWith C e where
  parahoric_le_zero := h.parahoric_le_zeroSubgroup C
  action_compatible := hact
  tits :=
    { surjective := P.affineTitsProjection_surjective
      ker_eq := P.ker_affineTitsProjection h.mem_normalizerZero_of_mem_parahoric
      sup_eq := P.parahoricInZero_sup_normalizerInZero (h.parahoric_le_zeroSubgroup C)
        h.zeroSubgroup_le_sup
      closure_eq := P.closure_chamberSimpleInAffinePart h.closure_chamberSimpleReflections
      ne_one := fun _ hs => P.chamberSimpleInAffinePart_ne_one hs
      mul_self := fun _ hs => P.chamberSimpleInAffinePart_mul_self hs
      mul_mem_cell := P.mul_mem_cell_of_inputs hA hC hact h
      conj_not_le := P.conj_not_le_of_inputs hC hact h }
  saturated := P.isSaturated_of_inputs h

/-- The existential form: a comparison realizing the apartment action, together with the
actual inputs, gives `P.AffineIwahoriTits C`. -/
theorem affineIwahoriTits_of_inputs
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) {C : Set P.Apartment}
    (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (hcmp : ∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
      P.IsAffineWeylComparison e)
    (h : P.AffineIwahoriTitsInputs C) : P.AffineIwahoriTits C := by
  obtain ⟨e, hact⟩ := hcmp
  exact ⟨e, P.affineIwahoriTitsWith_of_inputs hA hC hact h⟩

end ParahoricBuildingData

end Langlands.Geometry.Building
