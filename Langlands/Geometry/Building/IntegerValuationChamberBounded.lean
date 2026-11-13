import Langlands.Geometry.Building.RootFunctionNontriviality
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Facets and chambers of supplied integer-valuation building data are bounded

For supplied building data `B` of `G` over a field with a nontrivial integer-valued
valuation, every facet of the apartment `A(S)` for the affine roots `Ψ` is bounded:
every real affine function is bounded above on it. In particular a chamber of the
reduced building is the translate of a nonempty bounded subset of `A(S)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace IntegerValuationBuildingData

variable {k : Type u} [Field k] {v : Valuation k (WithZero (Multiplicative ℤ))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (B : IntegerValuationBuildingData v G)

/-- A subset `Ω` of the apartment `A(S)` is bounded: every real affine function on
`A(S)` is bounded above on `Ω`. This is the boundedness hypothesis of the parahoric
model statements. -/
def IsBoundedApartmentSubset (Ω : Set B.Apartment) : Prop :=
  ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)

omit [IsAffineHom G.X.hom] in
/-- The real order of an integral power. -/
theorem order_zpow (b : kˣ) (n : ℤ) :
    IntegerValuation.order v (b ^ n) = n * IntegerValuation.order v b := by
  rw [IntegerValuation.order, IntegerValuation.order, map_zpow, toAdd_zpow, smul_eq_mul,
    Int.cast_mul]

/-- Conjugating one root-group point of finite value by integral powers of a torus
point gives root-group points whose values at `x` are `r - n δ` with `δ ≠ 0`. -/
theorem exists_rootValue_sub_mul (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x : B.Apartment) (α : relativeRoots B.i) :
    ∃ r δ : ℝ, δ ≠ 0 ∧ ∀ n : ℤ, ∃ u ∈ B.rootGroup α,
      x.val α u = ((r - n * δ : ℝ) : WithTop ℝ) := by
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨u, hu, hne⟩ := x.isValuation.exists_ne_top α.2
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨b, hb⟩ := hv
  obtain ⟨D, hD, c, hc⟩ := hS.exists_pairing_eq_pos α.2.1
  let s := CocharacterUniformizer.cocharacterPoints k B.S c b
  let δ : ℝ := IntegerValuation.order v
    (rationalCharacterEval ((rationalCharacters.equivCharacterLattice B.S).symm α) s)
  have hδ : δ ≠ 0 := by
    dsimp [δ, s]
    rw [CocharacterUniformizer.rationalCharacterEval_cocharacterPoints, order_zpow, hc]
    simpa only [Int.cast_natCast] using
      mul_ne_zero (by exact_mod_cast hD.ne' : (D : ℝ) ≠ 0) hb
  refine ⟨r, δ, hδ, fun n => ⟨(rationalPoints.map B.i (s ^ n))⁻¹ * u *
    rationalPoints.map B.i (s ^ n), ?_, ?_⟩⟩
  · have h := RelativeRoot.subgroup_isStable B.i α (Over.mk (𝟙 _)) ((s ^ n)⁻¹) u hu
    simpa only [rootGroupPoints, AutomorphicAction.conjugation_act,
      ← rationalPoints.map_apply, map_inv, inv_inv] using h
  · rw [x.isSplitTorusCompatible α α.2 (s ^ n) u hu, ← hr, map_zpow, order_zpow,
      ← WithTop.coe_add]
    congr 1

/-- If `2β` is not a root, every finite value `c = x_β(u)` of a point `u ∈ U_β(k)`
gives the affine root with derivative `β` and value `c` at `x`
(KP Definition 6.3.4, with `U_{2β}(k) = {1}`). -/
theorem affineFunctional_mem_affineRoots {β : relativeRoots B.i}
    (hβ : 2 • (β : characterLattice B.S) ∉ relativeRoots B.i) (x : B.Apartment)
    {u : rationalPoints G} (hu : u ∈ B.rootGroup β) {c : ℝ}
    (hc : x.val β u = (c : WithTop ℝ)) :
    B.apartment.affineFunctional β x c ∈ B.affineRoots := by
  have hlin := KPApartmentData.affineFunctional_linear (D := B.apartment) β x c
  have hx : B.apartment.affineFunctional β x c x = c := by
    rw [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add]
  refine ⟨β, hlin, fun hsub => ?_⟩
  have hmem : u ∈ B.apartment.affineRootGroup β (B.apartment.affineFunctional β x c) := by
    rw [KPApartmentData.mem_affineRootGroup_iff hlin x, hx, hc]
    exact ⟨hu, le_rfl⟩
  obtain ⟨w, hw, z, hz, hwz⟩ := Set.mem_mul.mp (hsub hmem)
  have hbot : doubleRootGroupPoints B.i (β : characterLattice B.S) = ⊥ := by
    simp only [doubleRootGroupPoints, hβ, ↓reduceIte]
  rw [SetLike.mem_coe, hbot, Subgroup.mem_bot] at hz
  rw [hz, mul_one] at hwz
  subst hwz
  rw [SetLike.mem_coe, KPApartmentData.mem_affineRootGroupPlus_iff hlin x, hx, hc] at hw
  exact lt_irrefl _ hw.2

/-- On the facet of `x₀`, the root form of a root `β` with `2β ∉ Φ` is bounded:
affine roots with derivative `β` of both signs at `x₀` keep their signs on the facet. -/
theorem exists_abs_rootForm_le_of_not_double (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x₀ : B.Apartment) {β : relativeRoots B.i}
    (hβ : 2 • (β : characterLattice B.S) ∉ relativeRoots B.i) :
    ∃ M : ℝ, ∀ y ∈ AffineRootSystem.facet B.affineRoots x₀,
      |rootForm B.i β (y -ᵥ x₀)| ≤ M := by
  obtain ⟨r, δ, hδ, hval⟩ := B.exists_rootValue_sub_mul hv x₀ β
  obtain ⟨n, hn⟩ := exists_nat_gt (|r| / |δ|)
  have hnδ : |r| < n * |δ| := by
    rwa [div_lt_iff₀ (abs_pos.mpr hδ)] at hn
  obtain ⟨u₁, hu₁, h₁⟩ := hval n
  obtain ⟨u₂, hu₂, h₂⟩ := hval (-n)
  have hψ₁ := B.affineFunctional_mem_affineRoots hβ x₀ hu₁ h₁
  have hψ₂ := B.affineFunctional_mem_affineRoots hβ x₀ hu₂ h₂
  refine ⟨|r| + n * |δ|, fun y hy => ?_⟩
  have e₁ := (AffineRootSystem.mem_facet.mp hy) _ hψ₁
  have e₂ := (AffineRootSystem.mem_facet.mp hy) _ hψ₂
  simp only [KPApartmentData.affineFunctional_apply, vsub_self, map_zero, zero_add] at e₁ e₂
  set t := rootForm B.i β (y -ᵥ x₀)
  push_cast at e₁ e₂
  rw [abs_le]
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · rw [abs_of_neg hneg] at hnδ ⊢
    have ha : 0 < r - n * δ := by
      have := le_abs_self r
      have := neg_abs_le r
      nlinarith
    have hb : r - -(n : ℝ) * δ < 0 := by
      have := le_abs_self r
      have := neg_abs_le r
      nlinarith
    rw [sign_pos ha, eq_comm, sign_eq_one_iff] at e₁
    rw [sign_neg hb, eq_comm, sign_eq_neg_one_iff] at e₂
    have := le_abs_self r
    have := neg_abs_le r
    constructor <;> nlinarith
  · rw [abs_of_pos hpos] at hnδ ⊢
    have ha : r - n * δ < 0 := by
      have := le_abs_self r
      have := neg_abs_le r
      nlinarith
    have hb : 0 < r - -(n : ℝ) * δ := by
      have := le_abs_self r
      have := neg_abs_le r
      nlinarith
    rw [sign_neg ha, eq_comm, sign_eq_neg_one_iff] at e₁
    rw [sign_pos hb, eq_comm, sign_eq_one_iff] at e₂
    have := le_abs_self r
    have := neg_abs_le r
    constructor <;> nlinarith

/-- The root form of a positive multiple of a root. -/
theorem rootForm_nsmul_apply (α : relativeRoots B.i) {N : ℕ}
    (hN : N • (α : characterLattice B.S) ∈ relativeRoots B.i) (w : TranslationSpace B.i) :
    rootForm B.i ⟨N • (α : characterLattice B.S), hN⟩ w = N * rootForm B.i α w :=
  Submodule.Quotient.induction_on _ w fun w => by
    rw [rootForm_mk, rootForm_mk, eval_nsmul_char]

/-- On the facet of `x₀`, every root form is bounded. -/
theorem exists_abs_rootForm_le (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x₀ : B.Apartment) (α : relativeRoots B.i) :
    ∃ M : ℝ, ∀ y ∈ AffineRootSystem.facet B.affineRoots x₀,
      |rootForm B.i α (y -ᵥ x₀)| ≤ M := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  obtain ⟨N, hN, hroot, hhigh⟩ := RelativeRoot.exists_maximal_root_multiple hS B.i α.2
  have hβ : 2 • ((⟨N • (α : characterLattice B.S), hroot⟩ : relativeRoots B.i) :
      characterLattice B.S) ∉ relativeRoots B.i := hhigh 2 le_rfl
  obtain ⟨M, hM⟩ := B.exists_abs_rootForm_le_of_not_double hv x₀ hβ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨M / N, fun y hy => ?_⟩
  have h := hM y hy
  rw [rootForm_nsmul_apply, abs_mul, Nat.abs_cast] at h
  rw [le_div_iff₀ hNpos]
  linarith

/-- The root forms have no common kernel on `TranslationSpace i = V(S)/V(S)^Φ`. -/
theorem iInf_ker_rootForm_eq_bot :
    ⨅ α : relativeRoots B.i, LinearMap.ker (rootForm B.i α) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_iInf] at hw
  rw [Submodule.mem_bot]
  induction w using Submodule.Quotient.induction_on with
  | H w =>
    rw [Submodule.Quotient.mk_eq_zero, mem_rootAnnihilator]
    intro a ha
    have h := LinearMap.mem_ker.mp (hw ⟨a, ha⟩)
    rwa [rootForm_mk] at h

/-- **Facets are bounded.** For a nontrivial integer-valued valuation, every real
affine function on the apartment is bounded above on the facet of any point. -/
theorem isBoundedApartmentSubset_facet (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    (x₀ : B.Apartment) :
    B.IsBoundedApartmentSubset (AffineRootSystem.facet B.affineRoots x₀) := by
  intro f
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  have : Fintype (relativeRoots B.i) := (hS.finite_relativeRoots B.i).fintype
  choose M hM using B.exists_abs_rootForm_le hv x₀
  have hspan : f.linear ∈ Submodule.span ℝ (Set.range (rootForm B.i)) := by
    refine mem_span_of_iInf_ker_le_ker ?_
    rw [B.iInf_ker_rootForm_eq_bot]
    exact bot_le
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hspan
  refine ⟨∑ α, |c α| * M α + f x₀, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hfy : f y = f.linear (y -ᵥ x₀) + f x₀ := by
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, sub_add_cancel]
  rw [hfy, ← hc, LinearMap.sum_apply]
  refine add_le_add (Finset.sum_le_sum fun α _ => ?_) le_rfl
  rw [LinearMap.smul_apply, smul_eq_mul]
  calc c α * rootForm B.i α (y -ᵥ x₀) ≤ |c α * rootForm B.i α (y -ᵥ x₀)| := le_abs_self _
    _ = |c α| * |rootForm B.i α (y -ᵥ x₀)| := abs_mul _ _
    _ ≤ |c α| * M α := mul_le_mul_of_nonneg_left (hM α y hy) (abs_nonneg _)

/-- Every facet of the apartment for the affine roots is bounded. -/
theorem isBoundedApartmentSubset_of_isFacet (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    {Fa : Set B.Apartment} (h : AffineRootSystem.IsFacet B.affineRoots Fa) :
    B.IsBoundedApartmentSubset Fa := by
  obtain ⟨x₀, rfl⟩ := h
  exact B.isBoundedApartmentSubset_facet hv x₀

/-- Every chamber of the apartment for the affine roots is nonempty and bounded. -/
theorem nonempty_and_isBoundedApartmentSubset_of_isChamber
    (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    {Ca : Set B.Apartment} (h : AffineRootSystem.IsChamber B.affineRoots Ca) :
    Ca.Nonempty ∧ B.IsBoundedApartmentSubset Ca := by
  obtain ⟨x₀, -, rfl⟩ := h
  exact ⟨⟨x₀, AffineRootSystem.mem_facet_self _ x₀⟩, B.isBoundedApartmentSubset_facet hv x₀⟩

/-- A chamber of the reduced building is a `G(k)`-translate of the image of a nonempty
bounded subset of the apartment. -/
theorem IsChamber.exists_nonempty_isBoundedApartmentSubset
    (hv : ∃ b : kˣ, IntegerValuation.order v b ≠ 0)
    {Y : Set B.ReducedBuilding} (hY : B.IsChamber Y) :
    ∃ (g : rationalPoints G) (Ca : Set B.Apartment), Ca.Nonempty ∧
      B.IsBoundedApartmentSubset Ca ∧ Y = (fun x => g • B.apartmentMap x) '' Ca := by
  obtain ⟨g, Ca, hCa, rfl⟩ := hY
  obtain ⟨hne, hb⟩ := B.nonempty_and_isBoundedApartmentSubset_of_isChamber hv hCa
  exact ⟨g, Ca, hne, hb, rfl⟩

end IntegerValuationBuildingData

namespace MaximalUnramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

variable (F) in
/-- The normalized valuation of the maximal unramified extension is nontrivial: the
image of a uniformizer of `F` has order one. -/
theorem exists_order_ne_zero :
    ∃ b : (inertiaFixedField F)ˣ, IntegerValuation.order (valuation F) b ≠ 0 := by
  refine ⟨Units.map (algebraMap F (inertiaFixedField F)).toMonoidHom
    (SplitTorusValuation.uniformizerUnit F), ?_⟩
  rw [IntegerValuation.order, orderUnits_base_eq_fieldOrderUnits,
    SplitTorusValuation.fieldOrderUnits_uniformizerUnit]
  norm_num

/-- **Chambers of supplied building data over the maximal unramified extension are
bounded.** A chamber `Y` of `C` is `g · Ca` for a nonempty subset `Ca` of the apartment on
which every real affine function is bounded above; these are the hypotheses on `Ω` of
`UnramifiedParahoricModelStatement`. -/
theorem isChamber_exists_bounded
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom G.X.hom]
    (C : BuildingData F G) {Y : Set C.ReducedBuilding} (hY : C.IsChamber Y) :
    ∃ (g : rationalPoints G) (Ca : Set C.Apartment), Ca.Nonempty ∧
      (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ca)) ∧
      Y = (fun x => g • C.apartmentMap x) '' Ca :=
  IntegerValuationBuildingData.IsChamber.exists_nonempty_isBoundedApartmentSubset C
    (exists_order_ne_zero F) hY

end MaximalUnramified

end Langlands.Geometry.Building
