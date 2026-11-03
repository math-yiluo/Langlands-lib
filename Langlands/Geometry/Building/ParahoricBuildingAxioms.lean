import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Geometry.Building.KPParahoric
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement

/-!
# The reflections `m(u)` and Axiom 4.1.8 (2), (3) of Kaletha–Prasad

For building data `B : ValuationBuildingData G` over a nonarchimedean local field `F`, this
module states AS 1 of KP Axiom 4.1.6 with the actual elements `m(u) = u′ u u″` of KP
Proposition 2.11.17 (`RelativeRoot.IsOppositeFactorPair`). It relates the forms of AS 2 and AS 3
that use `m(u)` to the published sets `Ψ′`, `Ψ` and groups `U_ψ` of the data.

* `B.reflectionElement hp`: `m(u) = u′ u u″ ∈ N(F)` for an opposite factor pair `(u′, u″)`.
* `B.reflectionHyperplane α u`: `H_u = {x ∈ A | x_a(u) = 0}` (KP §6.2).
* `B.reflectionFunctional α u`: `ψ^u_a`, the affine functional with derivative `a` and
  `ψ^u_a(x) = x_a(u)` for `u ∈ U_a(F) ∖ {1}`. `H_u` is its zero set.
* `B.HasRootReflections`: AS 1, `m(u)` fixes `H_u` pointwise.
* `reflectionAffineRoots_eq`: `{ψ^u_a | a ∈ Φ, u ∈ U_a(F) ∖ {1}}` is the published `Ψ′`
  (KP Remark 4.1.7). So AS 2 in its `m(u)`-form is the published AS 2 field.
* `mem_affineRootGroup_iff_reflectionFunctional`: `U_ψ = {u | ψ^u_a ≥ ψ} ∪ {1}`, the corrected AS 3.

For `P : ParahoricBuildingData G`, with `G(F)^0` and `Z(F)^0` of KP Definition 2.6.23:

* `P.zeroFixer Ω`: `G(F)^0_Ω`, the elements of `G(F)^0` that fix the image of `Ω ⊆ A` in
  `B(G)` pointwise (KP §4.1, before Axiom 4.1.8). It is distinct from `P.parahoric Ω`.
* `P.HasZeroFixerGenerators`: Axiom 4.1.8 (2).
* `P.HasRootZeroFixers`: Axiom 4.1.8 (3), with `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}`.
  `HasRootZeroFixers.rootGroup_inf_zeroFixer_eq` gives KP's form with the smallest `ψ ∈ Ψ′`.

These predicates are conditions. Nothing here asserts that they hold, or that data exist.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-! ### Values of root elements on the apartment -/

/-- `y_a(u) = x_a(u) + a(y - x)` for points `x, y` of the apartment: the translation action
`φ_{v,a}(u) = φ_a(u) + a(v)` of KP §6.1, stated before Lemma 6.1.6. -/
theorem val_apply_eq_add (x y : B.Apartment) (α : relativeRoots B.i) (u : rationalPoints G) :
    y.val α u = x.val α u + ((rootForm B.i α (y -ᵥ x) : ℝ) : WithTop ℝ) := by
  have key : ∀ v : TranslationSpace B.i,
      (v +ᵥ x).val α u = x.val α u + ((rootForm B.i α v : ℝ) : WithTop ℝ) :=
    fun v => Submodule.Quotient.induction_on _ v fun w => by
      rw [KPApartmentData.val_mk_vadd, RootFunctionFamily.vadd_apply, rootForm_mk]
  rw [← key, vsub_vadd]

/-- `x_a(1) = ∞` (KP axiom V 1). -/
theorem val_apply_one (α : relativeRoots B.i) (x : B.Apartment) :
    x.val α 1 = ⊤ :=
  (x.isValuation.eq_top_iff α α.2 1 (B.rootGroup α).one_mem).2 rfl

/-- `x_a(u) < ∞` for `u ∈ U_a(F) ∖ {1}` (KP axiom V 1). -/
theorem val_apply_ne_top {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) (x : B.Apartment) : x.val α u ≠ ⊤ :=
  fun h => h1 ((x.isValuation.eq_top_iff α α.2 u hu).1 h)

/-! ### The elements `m(u)`, the hyperplanes `H_u` and the functionals `ψ^u_a` -/

/-- KP's `m(u) = u′ u u″ ∈ N(F)` (Proposition 2.11.17) for an opposite factor pair
`p = (u′, u″)` of `u`. -/
def reflectionElement {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    normalizerPoints B.i :=
  ⟨p.1 * u * p.2, hp.2.2⟩

@[simp] theorem coe_reflectionElement {α : relativeRoots B.i} {u : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p) :
    (B.reflectionElement hp : rationalPoints G) = p.1 * u * p.2 :=
  rfl

/-- Under KP Proposition 2.11.17 (`RootRankOneFactorizationStatement`, not proved in the
Library), every `u ∈ U_a(F) ∖ {1}` has an opposite factor pair. -/
theorem exists_isOppositeFactorPair (h : RootRankOneFactorizationStatement.{u})
    {α : relativeRoots B.i} {u : rationalPoints G} (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) :
    ∃ p, RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p :=
  ((h F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus) α α.2 u hu h1).1.exists

/-- KP's hyperplane `H_u = {x ∈ A | x_a(u) = 0}` (KP §6.2, before Proposition 6.2.1). -/
def reflectionHyperplane (α : relativeRoots B.i) (u : rationalPoints G) : Set B.Apartment :=
  {x | x.val α u = 0}

/-- KP's `ψ^u_a`: the affine functional with derivative `a` whose value at a fixed base point
`x₀` is `x₀_a(u)` (with `0` for `x₀_a(u) = ∞`). For `u ∈ U_a(F) ∖ {1}` its value at every
point `x` is `x_a(u)` (`coe_reflectionFunctional_apply`), so it vanishes exactly on `H_u`. -/
def reflectionFunctional (α : relativeRoots B.i) (u : rationalPoints G) :
    B.Apartment →ᵃ[ℝ] ℝ :=
  B.apartment.affineFunctional α (Classical.arbitrary B.Apartment)
    (((Classical.arbitrary B.Apartment).val α u).untopD 0)

@[simp] theorem reflectionFunctional_linear (α : relativeRoots B.i) (u : rationalPoints G) :
    (B.reflectionFunctional α u).linear = rootForm B.i α :=
  rfl

/-- `ψ^u_a(x) = x_a(u)` for `u ∈ U_a(F) ∖ {1}`. -/
theorem coe_reflectionFunctional_apply {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) (y : B.Apartment) :
    ((B.reflectionFunctional α u y : ℝ) : WithTop ℝ) = y.val α u := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1
    (B.val_apply_ne_top hu h1 (Classical.arbitrary B.Apartment))
  rw [reflectionFunctional, KPApartmentData.affineFunctional_apply,
    B.val_apply_eq_add (Classical.arbitrary B.Apartment) y, ← ht, WithTop.untopD_coe,
    add_comm, WithTop.coe_add]

/-- `H_u` is the zero set of `ψ^u_a`, an affine functional with derivative `a`. -/
theorem reflectionHyperplane_eq {α : relativeRoots B.i} {u : rationalPoints G}
    (hu : u ∈ B.rootGroup α) (h1 : u ≠ 1) :
    B.reflectionHyperplane α u = {x | B.reflectionFunctional α u x = 0} := by
  ext x
  change x.val α u = 0 ↔ B.reflectionFunctional α u x = 0
  rw [← B.coe_reflectionFunctional_apply hu h1 x, ← WithTop.coe_zero, WithTop.coe_eq_coe]

/-! ### AS 1 -/

/-- AS 1 of KP Axiom 4.1.6: for `a ∈ Φ`, `u ∈ U_a(F) ∖ {1}` and every opposite factor pair
`(u′, u″)` of `u`, the element `m(u) = u′ u u″` fixes the hyperplane `H_u` pointwise. -/
def HasRootReflections : Prop :=
  ∀ (α : relativeRoots B.i) (u : rationalPoints G), u ∈ B.rootGroup α → u ≠ 1 →
    ∀ (p : rationalPoints G × rationalPoints G)
      (hp : RelativeRoot.IsOppositeFactorPair B.i (α : characterLattice B.S) u p),
      ∀ x ∈ B.reflectionHyperplane α u, B.reflectionElement hp • x = x

/-! ### AS 2 and AS 3 in terms of `ψ^u_a` -/

/-- KP's `Ψ′ = {ψ^u_a | a ∈ Φ, u ∈ U_a(F) ∖ {1}}` of AS 2. -/
def reflectionAffineRoots : Set (B.Apartment →ᵃ[ℝ] ℝ) :=
  {ψ | ∃ (α : relativeRoots B.i) (u : rationalPoints G), u ∈ B.rootGroup α ∧ u ≠ 1 ∧
    ψ = B.reflectionFunctional α u}

/-- The `ψ^u_a` are exactly the jumps of the filtrations: `Ψ′` of AS 2 is the published
`extendedAffineRoots` (KP Remark 4.1.7 and Definition 6.3.4). -/
theorem reflectionAffineRoots_eq :
    B.reflectionAffineRoots = B.apartment.extendedAffineRoots := by
  ext ψ
  constructor
  · rintro ⟨α, u, hu, h1, rfl⟩
    refine ⟨α, rfl, fun heq => ?_⟩
    have x : B.Apartment := Classical.arbitrary B.Apartment
    have hmem : u ∈ B.apartment.affineRootGroup α (B.reflectionFunctional α u) :=
      (KPApartmentData.mem_affineRootGroup_iff rfl x).2
        ⟨hu, (B.coe_reflectionFunctional_apply hu h1 x).le⟩
    rw [← heq, KPApartmentData.mem_affineRootGroupPlus_iff rfl x,
      B.coe_reflectionFunctional_apply hu h1 x] at hmem
    exact lt_irrefl _ hmem.2
  · rintro ⟨α, hψ, hne⟩
    have x : B.Apartment := Classical.arbitrary B.Apartment
    obtain ⟨u, hu, hnu⟩ : ∃ u ∈ B.apartment.affineRootGroup α ψ,
        u ∉ B.apartment.affineRootGroupPlus α ψ := by
      by_contra hcon
      push Not at hcon
      exact hne (le_antisymm (B.apartment.affineRootGroupPlus_le α ψ) hcon)
    rw [KPApartmentData.mem_affineRootGroup_iff hψ x] at hu
    rw [KPApartmentData.mem_affineRootGroupPlus_iff hψ x] at hnu
    have heq : x.val α u = ψ x := le_antisymm (not_lt.1 fun h => hnu ⟨hu.1, h⟩) hu.2
    have h1 : u ≠ 1 := by
      rintro rfl
      rw [B.val_apply_one] at heq
      exact WithTop.top_ne_coe heq
    refine ⟨α, u, hu.1, h1, AffineMap.ext_linear (hψ.trans rfl) (p := x) ?_⟩
    exact WithTop.coe_injective ((B.coe_reflectionFunctional_apply hu.1 h1 x).trans heq).symm

/-- AS 2 in its `m(u)`-form follows from the published AS 2 field: `{ψ^u_a}` is an affine root
system with derivative set `Φ`. -/
theorem SatisfiesApartmentAxioms.isAffineRootSystem_reflectionAffineRoots
    {B : ValuationBuildingData G} (h : B.SatisfiesApartmentAxioms) :
    AffineRootSystem.IsAffineRootSystemWithRankZero B.reflectionAffineRoots ∧
      AffineRootSystem.derivativeRoots B.reflectionAffineRoots = Set.range (rootForm B.i) := by
  rw [reflectionAffineRoots_eq]
  exact ⟨h.isAffineRootSystem_extendedAffineRoots, h.derivativeRoots_extendedAffineRoots⟩

/-- The corrected AS 3: `U_ψ = {u ∈ U_a(F) ∖ {1} | ψ^u_a ≥ ψ} ∪ {1}`. -/
theorem mem_affineRootGroup_iff_reflectionFunctional {α : relativeRoots B.i}
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ.linear = rootForm B.i α) {u : rationalPoints G} :
    u ∈ B.affineRootGroup α ψ ↔
      u = 1 ∨ (u ∈ B.rootGroup α ∧ u ≠ 1 ∧ ∀ x, ψ x ≤ B.reflectionFunctional α u x) := by
  constructor
  · intro h
    by_cases h1 : u = 1
    · exact Or.inl h1
    · have hu := (KPApartmentData.mem_affineRootGroup_iff hψ
        (Classical.arbitrary B.Apartment)).1 h
      refine Or.inr ⟨hu.1, h1, fun x => ?_⟩
      have hx := ((KPApartmentData.mem_affineRootGroup_iff hψ x).1 h).2
      rw [← B.coe_reflectionFunctional_apply hu.1 h1 x] at hx
      exact WithTop.coe_le_coe.1 hx
  · rintro (rfl | ⟨hu, h1, hle⟩)
    · exact (B.affineRootGroup α ψ).one_mem
    · have x : B.Apartment := Classical.arbitrary B.Apartment
      refine (KPApartmentData.mem_affineRootGroup_iff hψ x).2 ⟨hu, ?_⟩
      rw [← B.coe_reflectionFunctional_apply hu h1 x]
      exact WithTop.coe_le_coe.2 (hle x)

/-- The corrected AS 3 for `U_{ψ+}`: `U_{ψ+} = {u ∈ U_a(F) ∖ {1} | ψ^u_a > ψ} ∪ {1}`. -/
theorem mem_affineRootGroupPlus_iff_reflectionFunctional {α : relativeRoots B.i}
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ.linear = rootForm B.i α) {u : rationalPoints G} :
    u ∈ B.apartment.affineRootGroupPlus α ψ ↔
      u = 1 ∨ (u ∈ B.rootGroup α ∧ u ≠ 1 ∧ ∀ x, ψ x < B.reflectionFunctional α u x) := by
  constructor
  · intro h
    by_cases h1 : u = 1
    · exact Or.inl h1
    · have hu := (KPApartmentData.mem_affineRootGroupPlus_iff hψ
        (Classical.arbitrary B.Apartment)).1 h
      refine Or.inr ⟨hu.1, h1, fun x => ?_⟩
      have hx := ((KPApartmentData.mem_affineRootGroupPlus_iff hψ x).1 h).2
      rw [← B.coe_reflectionFunctional_apply hu.1 h1 x] at hx
      exact WithTop.coe_lt_coe.1 hx
  · rintro (rfl | ⟨hu, h1, hlt⟩)
    · exact (B.apartment.affineRootGroupPlus α ψ).one_mem
    · have x : B.Apartment := Classical.arbitrary B.Apartment
      refine (KPApartmentData.mem_affineRootGroupPlus_iff hψ x).2 ⟨hu, ?_⟩
      rw [← B.coe_reflectionFunctional_apply hu h1 x]
      exact WithTop.coe_lt_coe.2 (hlt x)

/-! ### Bounded subsets of the apartment -/

/-- `Ω ⊆ A` is bounded: every affine functional on `A` is bounded above on `Ω`. -/
def IsBoundedSubset (Ω : Set B.Apartment) : Prop :=
  ∀ f : B.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω)

/-- `U_ψ ⊆ U_{a,Ω,0}` when `ψ` has derivative `a` and is non-negative on `Ω`. -/
theorem affineRootGroup_le_rootFixer {Ω : Set B.Apartment} {α : relativeRoots B.i}
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ.linear = rootForm B.i α) (hΩ : ∀ x ∈ Ω, 0 ≤ ψ x) :
    B.affineRootGroup α ψ ≤ B.rootFixer α Ω := by
  intro u h
  rw [B.apartment.mem_rootFixer]
  have hu := (KPApartmentData.mem_affineRootGroup_iff hψ (Classical.arbitrary B.Apartment)).1 h
  refine ⟨hu.1, fun x hx => KPApartmentData.mem_filtration.2 ⟨hu.1, ?_⟩⟩
  have hle := ((KPApartmentData.mem_affineRootGroup_iff hψ x).1 h).2
  exact le_trans (WithTop.coe_le_coe.2 (hΩ x hx)) hle

/-- `U_{a,Ω,0} = U_ψ` when `ψ` has derivative `a`, is non-negative on `Ω`, and lies below every
element of `Ψ′` with these two properties. The smallest such element of `Ψ′` in KP Axiom 4.1.8 (3)
is one such `ψ`. -/
theorem rootFixer_eq_affineRootGroup_of_isLeast {Ω : Set B.Apartment} {α : relativeRoots B.i}
    {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ.linear = rootForm B.i α) (hΩ : ∀ x ∈ Ω, 0 ≤ ψ x)
    (hleast : ∀ ψ' ∈ B.apartment.extendedAffineRoots, ψ'.linear = rootForm B.i α →
      (∀ x ∈ Ω, 0 ≤ ψ' x) → ∀ x, ψ x ≤ ψ' x) :
    B.rootFixer α Ω = B.affineRootGroup α ψ := by
  ext u
  rw [B.apartment.mem_rootFixer]
  constructor
  · rintro ⟨hu, hΩu⟩
    rw [B.mem_affineRootGroup_iff_reflectionFunctional hψ]
    by_cases h1 : u = 1
    · exact Or.inl h1
    · refine Or.inr ⟨hu, h1, hleast _ ?_ rfl fun x hx => ?_⟩
      · rw [← reflectionAffineRoots_eq]
        exact ⟨α, u, hu, h1, rfl⟩
      · have h0 := (KPApartmentData.mem_filtration.1 (hΩu x hx)).2
        rw [← B.coe_reflectionFunctional_apply hu h1 x] at h0
        exact WithTop.coe_le_coe.1 h0
  · intro h
    exact (B.apartment.mem_rootFixer).1 (B.affineRootGroup_le_rootFixer hψ hΩ h)

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-! ### Axiom 4.1.8 (2) and (3) -/

/-- `G(F)^0_Ω` in the sense of KP §4.1 (before Axiom 4.1.8): the elements of `G(F)^0` that fix
the image of `Ω ⊆ A` in `B(G)` pointwise. This is not `P.parahoric Ω` (KP Definition 7.4.1). -/
def zeroFixer (Ω : Set P.Apartment) : Subgroup (rationalPoints G) :=
  P.zeroSubgroup ⊓ P.pointwiseFixer (P.apartmentMap '' Ω)

theorem mem_zeroFixer {Ω : Set P.Apartment} {g : rationalPoints G} :
    g ∈ P.zeroFixer Ω ↔ g ∈ P.zeroSubgroup ∧ ∀ x ∈ Ω, g • P.apartmentMap x = P.apartmentMap x := by
  rw [zeroFixer, Subgroup.mem_inf, P.apartment.mem_pointwiseFixer, Set.forall_mem_image]

/-- The subgroup of `G(F)` generated by `Z(F)^0` and the `U_ψ` for `ψ ∈ Ψ` with
`ψ(Ω) ⊆ ℝ_{≥0}`: the right-hand side of KP Axiom 4.1.8 (2). -/
def nonnegativeRootSubgroup (Ω : Set P.Apartment) : Subgroup (rationalPoints G) :=
  P.centralizerZero.map (rationalPoints.map P.centralizer.j) ⊔
    Subgroup.closure (⋃ (α : relativeRoots P.i) (ψ ∈ P.affineRoots)
      (_ : ψ.linear = rootForm P.i α) (_ : ∀ x ∈ Ω, 0 ≤ ψ x),
      (P.affineRootGroup α ψ : Set (rationalPoints G)))

/-- The generators of Axiom 4.1.8 (2) lie in `P_Ω = Z(F)^0 · G(F)^♯_Ω`, since `U_ψ ⊆ U_{a,Ω,0}`
for `ψ` non-negative on `Ω`. -/
theorem nonnegativeRootSubgroup_le_parahoric (Ω : Set P.Apartment) :
    P.nonnegativeRootSubgroup Ω ≤ P.parahoric Ω := by
  refine sup_le_sup_left ((Subgroup.closure_le _).2 ?_) _
  simp only [Set.iUnion_subset_iff]
  intro α ψ _ hψ hΩ
  exact ((P.affineRootGroup_le_rootFixer hψ hΩ).trans
    (P.apartment.rootFixer_le_sharpFixer α Ω) :)

/-- KP Axiom 4.1.8 (2), with the corrected hypothesis that `Ω` is non-empty and bounded: for
`Ω ⊆ A`, `G(F)^0_Ω` is generated by `Z(F)^0` and the `U_ψ` for `ψ ∈ Ψ` with `ψ(Ω) ⊆ ℝ_{≥0}`. -/
def HasZeroFixerGenerators : Prop :=
  ∀ Ω : Set P.Apartment, Ω.Nonempty → P.IsBoundedSubset Ω →
    P.zeroFixer Ω = P.nonnegativeRootSubgroup Ω

/-- Under Axiom 4.1.8 (2), `G(F)^0_Ω ⊆ P_Ω` for non-empty bounded `Ω`. -/
theorem HasZeroFixerGenerators.zeroFixer_le_parahoric {P : ParahoricBuildingData G}
    (h : P.HasZeroFixerGenerators) {Ω : Set P.Apartment} (hne : Ω.Nonempty)
    (hb : P.IsBoundedSubset Ω) : P.zeroFixer Ω ≤ P.parahoric Ω :=
  (h Ω hne hb).le.trans (P.nonnegativeRootSubgroup_le_parahoric Ω)

/-- KP Axiom 4.1.8 (3), for non-empty bounded `Ω ⊆ A`, in the form
`U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}`. `rootGroup_inf_zeroFixer_eq` gives KP's form with the
smallest `ψ ∈ Ψ′`. -/
def HasRootZeroFixers : Prop :=
  ∀ Ω : Set P.Apartment, Ω.Nonempty → P.IsBoundedSubset Ω →
    ∀ α : relativeRoots P.i, P.rootGroup α ⊓ P.zeroFixer Ω = P.rootFixer α Ω

/-- KP's literal Axiom 4.1.8 (3): `U_a(F) ∩ G(F)^0_Ω = U_ψ` for the smallest `ψ ∈ Ψ′` with
derivative `a` that is non-negative on `Ω`. -/
theorem HasRootZeroFixers.rootGroup_inf_zeroFixer_eq {P : ParahoricBuildingData G}
    (h : P.HasRootZeroFixers) {Ω : Set P.Apartment} (hne : Ω.Nonempty)
    (hb : P.IsBoundedSubset Ω) {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm P.i α) (hΩ : ∀ x ∈ Ω, 0 ≤ ψ x)
    (hleast : ∀ ψ' ∈ P.apartment.extendedAffineRoots, ψ'.linear = rootForm P.i α →
      (∀ x ∈ Ω, 0 ≤ ψ' x) → ∀ x, ψ x ≤ ψ' x) :
    P.rootGroup α ⊓ P.zeroFixer Ω = P.affineRootGroup α ψ := by
  rw [h Ω hne hb α]
  exact P.rootFixer_eq_affineRootGroup_of_isLeast hψ hΩ hleast

/-! ### The bundle of the stated clauses -/

/-- The clauses of the corrected KP Definition 4.1.26 that are stated in the Library for the
building data `P`, as conditions on `P`:

* V 7 and AS 2–AS 5 (with V 6 part of the data), `apartmentAxioms`;
* AS 1 for the actual elements `m(u)`, `hasRootReflections`;
* AS 6, `hasCompatibleApartmentFacets`;
* the clause of Axiom 4.1.1 that the stabilizer of `A(S)` is `N(F)`,
  `hasNormalizerApartmentStabilizer`;
* Axiom 4.1.2, `hasBoundedOpenStabilizers`;
* Axiom 4.1.8 (2) and (3), `hasZeroFixerGenerators` and `hasRootZeroFixers`.

Axiom 4.1.4 (A 1), Axiom 4.1.8 (1) and the corrected AS 3 hold for all data by construction.
The other clauses of Definition 4.1.26 (the rest of 4.1.1, Axioms 4.1.9, 4.1.16, 4.1.17,
4.1.20 and 4.1.22) are not part of this predicate, so it is strictly weaker than
Definition 4.1.26. -/
structure SatisfiesPartialBuildingAxioms : Prop where
  /-- V 7 and AS 2–AS 5 for the class `A(S)` (KP Definition 6.1.2 and Axiom 4.1.6). -/
  apartmentAxioms : P.SatisfiesApartmentAxioms
  /-- AS 1: `m(u)` fixes `H_u` pointwise (KP Axiom 4.1.6). -/
  hasRootReflections : P.HasRootReflections
  /-- AS 6: `A(S)` embeds into `B(G)` compatibly with facets (KP Axiom 4.1.6). -/
  hasCompatibleApartmentFacets : P.HasCompatibleApartmentFacets
  /-- The stabilizer of `A(S)` in `G(F)` is `N(F)` (part of KP Axiom 4.1.1). -/
  hasNormalizerApartmentStabilizer : P.HasNormalizerApartmentStabilizer
  /-- Every `K_y` is a bounded open subgroup of `G(F)` (KP Axiom 4.1.2). -/
  hasBoundedOpenStabilizers : P.HasBoundedOpenStabilizers
  /-- `G(F)^0_Ω` is generated by `Z(F)^0` and the `U_ψ`, `ψ ∈ Ψ`, `ψ(Ω) ≥ 0`
  (KP Axiom 4.1.8 (2)). -/
  hasZeroFixerGenerators : P.HasZeroFixerGenerators
  /-- `U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}` (KP Axiom 4.1.8 (3)). -/
  hasRootZeroFixers : P.HasRootZeroFixers

end ParahoricBuildingData

section

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]

/-- Building data for `G` (`ParahoricBuildingData G`) that satisfy the clauses of KP
Definition 4.1.26 bundled in `ParahoricBuildingData.SatisfiesPartialBuildingAxioms`. Only part
of Definition 4.1.26 is required. -/
structure PartiallyValidParahoricBuildingData extends ParahoricBuildingData G where
  /-- The bundled clauses of KP Definition 4.1.26. -/
  satisfiesPartialBuildingAxioms : toParahoricBuildingData.SatisfiesPartialBuildingAxioms

end

namespace PartiallyValidParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : PartiallyValidParahoricBuildingData G)

/-- `{ψ^u_a}` is an affine root system with derivative set `Φ` (AS 2 in its `m(u)`-form). -/
theorem isAffineRootSystem_reflectionAffineRoots :
    AffineRootSystem.IsAffineRootSystemWithRankZero P.reflectionAffineRoots ∧
      AffineRootSystem.derivativeRoots P.reflectionAffineRoots = Set.range (rootForm P.i) :=
  P.satisfiesPartialBuildingAxioms.apartmentAxioms.isAffineRootSystem_reflectionAffineRoots

/-- `G(F)^0_Ω ⊆ P_Ω` for non-empty bounded `Ω`. -/
theorem zeroFixer_le_parahoric {Ω : Set P.Apartment} (hne : Ω.Nonempty)
    (hb : P.IsBoundedSubset Ω) : P.zeroFixer Ω ≤ P.parahoric Ω :=
  P.satisfiesPartialBuildingAxioms.hasZeroFixerGenerators.zeroFixer_le_parahoric hne hb

/-- KP's literal Axiom 4.1.8 (3) with the smallest `ψ ∈ Ψ′`. -/
theorem rootGroup_inf_zeroFixer_eq {Ω : Set P.Apartment} (hne : Ω.Nonempty)
    (hb : P.IsBoundedSubset Ω) {α : relativeRoots P.i} {ψ : P.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ.linear = rootForm P.i α) (hΩ : ∀ x ∈ Ω, 0 ≤ ψ x)
    (hleast : ∀ ψ' ∈ P.apartment.extendedAffineRoots, ψ'.linear = rootForm P.i α →
      (∀ x ∈ Ω, 0 ≤ ψ' x) → ∀ x, ψ x ≤ ψ' x) :
    P.rootGroup α ⊓ P.zeroFixer Ω = P.affineRootGroup α ψ :=
  P.satisfiesPartialBuildingAxioms.hasRootZeroFixers.rootGroup_inf_zeroFixer_eq hne hb hψ hΩ
    hleast

end PartiallyValidParahoricBuildingData

end Langlands.Geometry.Building
