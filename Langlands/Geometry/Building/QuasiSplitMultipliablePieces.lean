import Langlands.Geometry.Building.QuasiSplitApartmentOpposite
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Root pieces over a multipliable relative root -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace TensorProduct

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

section Combinatorics

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  (f : S ⟶ T) {J : Type*} [Finite J]
  (P : RootDatum J (characterLattice T) (cocharacterLattice T)) (a : characterLattice S)

/-- The roots restricting to a multiple of `a` restrict to `±a` or `±2a`. -/
def RestrictsToMultipliableLine : Prop :=
  ∀ (l : J) (n : ℤ), f ≫ P.root l = n • a → n = 1 ∨ n = 2 ∨ n = -1 ∨ n = -2

omit [Finite J] in
/-- Restriction of a reflected root. -/
theorem comp_root_reflectionPerm (l l' : J) :
    f ≫ P.root (P.reflectionPerm l' l) =
      f ≫ P.root l - P.pairing l l' • (f ≫ P.root l') := by
  rw [P.root_reflectionPerm, P.reflection_apply_root, Preadditive.comp_sub,
    Preadditive.comp_zsmul]

omit [Finite J] in
/-- The pairing with a coroot is linear in the root. -/
theorem pairing_eq_of_root_eq {l : J} {χ : characterLattice T} (h : P.root l = χ) (l' : J) :
    P.pairing l l' = P.toLinearMap χ (P.coroot l') := by
  rw [← h, P.root_coroot_eq_pairing]

variable {f P a}

omit [Finite J] in
/-- **Reflection bound.** If `α` restricts to `a` and `χ` to `c • a`, then
`c - ⟨χ, α^∨⟩` is `±1` or `±2`. -/
theorem sub_pairing_mem_of_restrictsToMultipliableLine (hline : RestrictsToMultipliableLine f P a)
    {l l' : J} (hl' : f ≫ P.root l' = a) {c : ℤ} (hl : f ≫ P.root l = c • a) :
    c - P.pairing l l' = 1 ∨ c - P.pairing l l' = 2 ∨ c - P.pairing l l' = -1 ∨
      c - P.pairing l l' = -2 := by
  apply hline (P.reflectionPerm l' l)
  rw [comp_root_reflectionPerm, hl, hl', sub_smul]

/-- Two distinct roots over `a` pair to `0` or `-1`. -/
theorem pairing_eq_zero_or_neg_one (hline : RestrictsToMultipliableLine f P a)
    {l l' : J} (hne : l ≠ l') (hl : f ≫ P.root l = a) (hl' : f ≫ P.root l' = a) :
    P.pairing l l' = 0 ∨ P.pairing l l' = -1 := by
  have h := sub_pairing_mem_of_restrictsToMultipliableLine hline hl'
    (c := 1) (by rw [one_smul, hl])
  have hpos : ¬ 0 < P.pairing l l' := by
    intro hp
    have hp' : 0 < P.pairingIn ℤ l l' := by
      rwa [← P.algebraMap_pairingIn ℤ, Algebra.algebraMap_self, RingHom.id_apply] at hp
    obtain ⟨l'', hl''⟩ := P.root_sub_root_mem_of_pairingIn_pos hp' hne
    have h0 := hline l'' 0 (by rw [hl'', Preadditive.comp_sub, hl, hl', sub_self, zero_smul])
    omega
  omega

/-- Two distinct roots over `a` have a root as sum exactly when they pair to `-1`. -/
theorem exists_root_add_iff (hline : RestrictsToMultipliableLine f P a)
    {l l' : J} (hne : l ≠ l') (hl : f ≫ P.root l = a) (hl' : f ≫ P.root l' = a) :
    (∃ m, P.root m = P.root l + P.root l') ↔ P.pairing l l' = -1 := by
  constructor
  · rintro ⟨m, hm⟩
    rcases pairing_eq_zero_or_neg_one hline hne hl hl' with h0 | h1
    · exfalso
      have hpm : P.pairing m l' = 2 := by
        rw [pairing_eq_of_root_eq P hm, map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
          P.root_coroot_eq_pairing, h0, P.pairing_same]
        rfl
      have hb := sub_pairing_mem_of_restrictsToMultipliableLine hline hl' (l := m) (c := 2)
        (by rw [hm, Preadditive.comp_add, hl, hl', two_smul])
      omega
    · exact h1
  · intro h
    refine ⟨P.reflectionPerm l' l, ?_⟩
    rw [P.root_reflectionPerm, P.reflection_apply_root, h, neg_smul, one_smul, sub_neg_eq_add]

/-- A root over `a` has at most one partner over `a` whose sum with it is a root. -/
theorem partner_unique (hline : RestrictsToMultipliableLine f P a)
    {l l₁ l₂ : J} (hl : f ≫ P.root l = a) (hl₁ : f ≫ P.root l₁ = a) (hl₂ : f ≫ P.root l₂ = a)
    (h₁ : l ≠ l₁) (hp₁ : P.pairing l l₁ = -1) (hp₂ : P.pairing l l₂ = -1) :
    l₁ = l₂ := by
  by_contra hne
  obtain ⟨m, hm⟩ := (exists_root_add_iff hline h₁ hl hl₁).mpr hp₁
  have h12 := pairing_eq_zero_or_neg_one hline hne hl₁ hl₂
  have hpm : P.pairing m l₂ = P.pairing l l₂ + P.pairing l₁ l₂ := by
    rw [pairing_eq_of_root_eq P hm, map_add, LinearMap.add_apply, P.root_coroot_eq_pairing,
      P.root_coroot_eq_pairing]
  have hb := sub_pairing_mem_of_restrictsToMultipliableLine hline hl₂ (l := m) (c := 2)
    (by rw [hm, Preadditive.comp_add, hl, hl₁, two_smul])
  omega

/-- The partner relation is symmetric. -/
theorem pairing_symm_of_neg_one (hline : RestrictsToMultipliableLine f P a)
    {l l' : J} (hne : l ≠ l') (hl : f ≫ P.root l = a) (hl' : f ≫ P.root l' = a)
    (h : P.pairing l l' = -1) : P.pairing l' l = -1 := by
  obtain ⟨m, hm⟩ := (exists_root_add_iff hline hne hl hl').mpr h
  exact (exists_root_add_iff hline (Ne.symm hne) hl' hl).mp ⟨m, by rw [hm, add_comm]⟩

omit [Finite J] in
/-- **Linear bound for combinations.** Let `ξ` be a root over `a`, and `α`, `δ` characters
restricting to `cα • a`, `cδ • a` and pairing to `sα`, `sδ` with `ξ^∨`. If
`n • α + l • δ` is a root, then its restriction coefficient `n cα + l cδ` and the difference
`(n cα + l cδ) - (n sα + l sδ)` are both `±1` or `±2`. -/
theorem combination_bounds (hline : RestrictsToMultipliableLine f P a) {lξ : J}
    (hξ : f ≫ P.root lξ = a) {α δ : characterLattice T} {cα cδ sα sδ : ℤ}
    (hcα : f ≫ α = cα • a) (hcδ : f ≫ δ = cδ • a)
    (hsα : P.toLinearMap α (P.coroot lξ) = sα) (hsδ : P.toLinearMap δ (P.coroot lξ) = sδ)
    (n l : ℕ) (hρ : n • α + l • δ ∈ Set.range P.root) :
    ((n : ℤ) * cα + l * cδ = 1 ∨ (n : ℤ) * cα + l * cδ = 2 ∨ (n : ℤ) * cα + l * cδ = -1 ∨
        (n : ℤ) * cα + l * cδ = -2) ∧
      (((n : ℤ) * cα + l * cδ) - ((n : ℤ) * sα + l * sδ) = 1 ∨
        ((n : ℤ) * cα + l * cδ) - ((n : ℤ) * sα + l * sδ) = 2 ∨
        ((n : ℤ) * cα + l * cδ) - ((n : ℤ) * sα + l * sδ) = -1 ∨
        ((n : ℤ) * cα + l * cδ) - ((n : ℤ) * sα + l * sδ) = -2) := by
  obtain ⟨ρ, hρ⟩ := hρ
  have hc : f ≫ P.root ρ = ((n : ℤ) * cα + l * cδ) • a := by
    rw [hρ, Preadditive.comp_add, Preadditive.comp_nsmul, Preadditive.comp_nsmul, hcα, hcδ,
      add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul]
  have hs : P.pairing ρ lξ = (n : ℤ) * sα + l * sδ := by
    rw [pairing_eq_of_root_eq P hρ, map_add, map_nsmul, map_nsmul, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smul_apply, hsα, hsδ, nsmul_eq_mul, nsmul_eq_mul]
  refine ⟨hline ρ _ hc, ?_⟩
  have h := sub_pairing_mem_of_restrictsToMultipliableLine hline hξ hc
  rwa [hs] at h

omit [Finite J] in
/-- A combination whose restriction coefficient or pairing with some coroot is nonzero is
nonzero. -/
theorem combination_ne_zero {α δ : characterLattice T} {sα sδ : ℤ} {lξ : J}
    (hsα : P.toLinearMap α (P.coroot lξ) = sα) (hsδ : P.toLinearMap δ (P.coroot lξ) = sδ)
    (n l : ℕ) (h : (n : ℤ) * sα + l * sδ ≠ 0) : n • α + l • δ ≠ 0 := by
  intro h0
  apply h
  have := congrArg (fun χ => P.toLinearMap χ (P.coroot lξ)) h0
  simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, hsα, hsδ,
    nsmul_eq_mul, map_zero, LinearMap.zero_apply] at this
  exact this

end Combinatorics

section Groups

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]

/-- If the only root among the strictly positive combinations of `α` and `δ` is `α + δ`,
the commutator of points of `U_α` and `U_δ` lies in `U_{α+δ}`. -/
theorem commutator_mem_of_only_root_combination (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) {α δ : characterLattice T}
    (hα : α ≠ 0) (hδ : δ ≠ 0)
    (hcomb : ∀ n l : ℕ, 0 < n → 0 < l → n • α + l • δ ≠ 0 ∧
      (n • α + l • δ ∈ relativeRoots j → n = 1 ∧ l = 1))
    (hroot : α + δ ∈ relativeRoots j) {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j α) (hy : y ∈ rootGroupPoints j δ) :
    x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (α + δ) := by
  let action := AutomorphicAction.conjugation j
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail α 1)).carrier (Over.mk (𝟙 _)) := by
    change x ∈ (RelativeRoot.weightFiltration action α 1).carrier _
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT j α hα]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail δ 1)).carrier (Over.mk (𝟙 _)) := by
    change y ∈ (RelativeRoot.weightFiltration action δ 1).carrier _
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT j δ hδ]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G inferInstance inferInstance
    T hT action (RelativeRoot.cyclicTail α 1) (RelativeRoot.cyclicTail δ 1) _ x y hx' hy'
  set A := RelativeRoot.semigroupSum (RelativeRoot.cyclicTail α 1)
    (RelativeRoot.cyclicTail δ 1) with hA
  have hzero : (0 : characterLattice T) ∉ A := by
    rintro ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨l, _, hl, rfl⟩, h0⟩
    exact (hcomb n l hn hl).1 h0
  have hrange : Set.range (fun _ : Fin 1 => α + δ) =
      RelativeRoot.semigroupIndivisibleRoots j A := by
    ext ρ
    constructor
    · rintro ⟨_, rfl⟩
      refine ⟨hroot, ⟨α, ⟨1, le_rfl, one_pos, one_smul ℕ α⟩, δ,
        ⟨1, le_rfl, one_pos, one_smul ℕ δ⟩, rfl⟩, ?_⟩
      rintro b hb ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨l, _, hl, rfl⟩, rfl⟩ m hm hmb
      obtain ⟨rfl, rfl⟩ := (hcomb n l hn hl).2 hb
      rw [one_smul, one_smul] at hmb
      have h2 : (m - 1) • (α + δ) = 0 := by
        have : (m - 1) • (α + δ) + (α + δ) = α + δ := by
          rw [← succ_nsmul, Nat.sub_add_cancel (by omega), hmb]
        simpa using this
      exact hT.nsmul_ne_zero hroot.1 (by omega) h2
    · rintro ⟨hρ, ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨l, _, hl, rfl⟩, rfl⟩, -⟩
      obtain ⟨rfl, rfl⟩ := (hcomb n l hn hl).2 hρ
      exact ⟨0, by simp⟩
  have hinj : Function.Injective (fun _ : Fin 1 => α + δ) := fun a b _ => Subsingleton.elim a b
  obtain ⟨X, hX, -⟩ := (RelativeRoot.mem_semigroupSubgroup_iff_existsUnique_rootPointsProduct
    j hT hE A hzero _ hinj hrange _ _).mp h
  rw [← hX]
  simp [RelativeRoot.rootPointsProduct]

omit [Smooth G.X.hom] [Mono j.hom.hom.left] in
/-- Two root groups whose characters pair with opposite signs with some cocharacter meet
trivially. -/
theorem eq_one_of_mem_rootGroupPoints_of_pairing {δ ε : characterLattice T}
    (ν : cocharacterLattice T) (h1 : 0 < latticePairing T δ ν) (h2 : latticePairing T ε ν < 0)
    {x : rationalPoints G} (hx : x ∈ rootGroupPoints j δ) (hx' : x ∈ rootGroupPoints j ε) :
    x = 1 := by
  apply RelativeRoot.eq_one_of_mem_subgroup_of_mem_negative_parabolic j ν h1 hx
  apply Dynamic.unipotent_le_parabolic
  apply RelativeRoot.subgroup_le_dynamicUnipotent j (-ν) _ _ hx'
  rw [map_neg]
  omega

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- **Reflection–commutator identity.** Let `X ∈ U_α` be nontrivial with opposite pair
`(A, B)` and `μ = A X B`, and let `μ` carry `δ` to `ε`. Suppose `U_{-α}` commutes with
`U_δ`, `U_δ` commutes with `U_ε`, `[U_α, U_δ] ⊆ U_ε`, `[U_{-α}, U_ε] ⊆ U_δ` and
`U_δ ∩ U_ε = 1`. Then conjugation by `μ` on `U_δ` is the commutator with `X`. -/
theorem conj_eq_commutator_of_oppositeFactorPair {α δ ε : characterLattice T}
    {X : rationalPoints G} {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair j α X p)
    (hw : weylAction j (⟨p.1 * X * p.2, hp.2.2⟩ : normalizerPoints j) δ = ε)
    (hcommAδ : ∀ A ∈ rootGroupPoints j (-α), ∀ Z ∈ rootGroupPoints j δ, Commute A Z)
    (hcommδε : ∀ Z ∈ rootGroupPoints j δ, ∀ E ∈ rootGroupPoints j ε, Commute Z E)
    (hαδ : ∀ Z ∈ rootGroupPoints j δ, X * Z * X⁻¹ * Z⁻¹ ∈ rootGroupPoints j ε)
    (hαε : ∀ A ∈ rootGroupPoints j (-α), ∀ E ∈ rootGroupPoints j ε,
      A * E * A⁻¹ * E⁻¹ ∈ rootGroupPoints j δ)
    (hsep : ∀ x ∈ rootGroupPoints j δ, x ∈ rootGroupPoints j ε → x = 1)
    {Z : rationalPoints G} (hZ : Z ∈ rootGroupPoints j δ) :
    (p.1 * X * p.2) * Z * (p.1 * X * p.2)⁻¹ = X * Z * X⁻¹ * Z⁻¹ := by
  have hmem : (p.1 * X * p.2) * Z * (p.1 * X * p.2)⁻¹ ∈ rootGroupPoints j ε := by
    have h := RelativeRoot.normalizer_conj_mem j δ (⟨p.1 * X * p.2, hp.2.2⟩ : normalizerPoints j) hZ
    simp only [G.constantPoint_self, hw] at h
    exact h
  set E := X * Z * X⁻¹ * Z⁻¹ with hEdef
  have hE : E ∈ rootGroupPoints j ε := hαδ Z hZ
  set c := p.1 * E * p.1⁻¹ * E⁻¹ with hcdef
  have hc : c ∈ rootGroupPoints j δ := hαε p.1 hp.1 E hE
  have h2 : p.2 * Z = Z * p.2 := (hcommAδ p.2 hp.2.1 Z hZ).eq
  have h1 : p.1 * Z = Z * p.1 := (hcommAδ p.1 hp.1 Z hZ).eq
  have hcomp : (p.1 * X * p.2) * Z * (p.1 * X * p.2)⁻¹ = E * (c * Z) := by
    have hcE : c * E = E * c := (hcommδε c hc E hE).eq
    calc (p.1 * X * p.2) * Z * (p.1 * X * p.2)⁻¹
        = p.1 * X * (p.2 * Z) * p.2⁻¹ * X⁻¹ * p.1⁻¹ := by group
      _ = p.1 * (X * Z * X⁻¹) * p.1⁻¹ := by rw [h2]; group
      _ = p.1 * E * p.1⁻¹ * (p.1 * Z * p.1⁻¹) := by rw [hEdef]; group
      _ = (c * E) * Z := by rw [h1, hcdef]; group
      _ = E * (c * Z) := by rw [hcE, mul_assoc]
  have hcZε : c * Z ∈ rootGroupPoints j ε := by
    have : c * Z = E⁻¹ * ((p.1 * X * p.2) * Z * (p.1 * X * p.2)⁻¹) := by
      rw [hcomp]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE) hmem
  have hcZ := hsep (c * Z) (Subgroup.mul_mem _ hc hZ) hcZε
  rw [hcomp, hcZ, mul_one]

end Groups

section Reflection

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
  [IsAffineHom G.X.hom] {ω : kˣ → ℝ} (D : KPApartmentData i ω)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)

include hG hi in
/-- The displacement of an apartment point under the product of an opposite pair is the
negative root value times the pair coroot class. -/
theorem KPApartmentData.oppositeFactorPair_smul_vsub {α : relativeRoots i}
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)
    (x : D.Apartment) {t : ℝ} (ht : x.val α u = t) :
    (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) • x -ᵥ x =
      (-t) • oppositeFactorPairCorootClass hi.isSplitSubtorus.1 hu h1 hp := by
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  set c := oppositeFactorPairCorootClass hS hu h1 hp with hcdef
  have hc := rootForm_oppositeFactorPairCorootClass hS hu h1 hp
  set d : TranslationSpace i := (-(t / 2)) • c with hd
  have hdα : rootForm i α d = -t := by
    rw [hd, map_smul, hc, smul_eq_mul]
    ring
  set x0 : D.Apartment := d +ᵥ x with hx0
  have hx0α : x0.val α u = 0 := by
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ d
    rw [hx0, ← hw, val_mk_vadd, RootFunctionFamily.vadd_apply, ht]
    rw [← hw, rootForm_mk] at hdα
    rw [hdα, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero]
  have hfix := D.oppositeFactorPair_smul_eq_self hG hi hu h1 hp x0 hx0α
  have hx : x = (-d) +ᵥ x0 := by rw [hx0, neg_vadd_vadd]
  set m : normalizerPoints i := ⟨p.1 * u * p.2, hp.2.2⟩ with hm
  have hmx : m • x = translationAction i m (-d) +ᵥ x0 := by
    calc m • x = m • ((-d) +ᵥ x0) := congrArg (fun y : D.Apartment => m • y) hx
      _ = _ := by rw [KPApartmentData.smul_vadd, hfix]
  calc m • x -ᵥ x = (translationAction i m (-d) +ᵥ x0) -ᵥ ((-d) +ᵥ x0) := by rw [← hmx, ← hx]
    _ = translationAction i m (-d) - (-d) := vadd_vsub_vadd_cancel_right _ _ _
    _ = (-t) • c := by
      rw [translationAction_oppositeFactorPair hS hu h1 hp, map_neg, hdα]
      simp only [neg_neg, neg_smul]
      rw [← hcdef]
      abel

include hG hi in
/-- **Reflection formula for values.** Conjugation by the product `μ` of an opposite pair of
`u ∈ U_α` shifts values by the pairing with the pair coroot `ν`:
`φ_δ(Z) = φ_{μδ}(μ Z μ⁻¹) + φ_α(u) ⟨δ, ν⟩`. -/
theorem KPApartmentData.val_eq_val_conj_oppositeFactorPair {α : relativeRoots i}
    {u : rationalPoints G} (hu : u ∈ rootGroupPoints i α) (h1 : u ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i (α : characterLattice S) u p)
    (x : D.Apartment) {t : ℝ} (ht : x.val α u = t) (δ : characterLattice S)
    (Z : rationalPoints G) :
    x.val δ Z =
      x.val (weylAction i (⟨p.1 * u * p.2, hp.2.2⟩ : normalizerPoints i) δ)
          ((p.1 * u * p.2) * Z * (p.1 * u * p.2)⁻¹) +
        ((t * latticePairing S δ
          (hp.coroot i hi.isSplitSubtorus.1 α.property.1 hu h1) : ℝ) : WithTop ℝ) := by
  have hS : IsSplitTorus S.toGrp := hi.isSplitSubtorus.1
  set m : normalizerPoints i := ⟨p.1 * u * p.2, hp.2.2⟩ with hm
  set ν := hp.coroot i hS α.property.1 hu h1 with hν
  obtain ⟨hν2, hr⟩ := hp.coroot_spec i hS α.property.1 hu h1
  have hdisp := D.oppositeFactorPair_smul_vsub hG hi hu h1 hp x ht
  have hval : (m • x).val = ((-t) • ((1 : ℝ) ⊗ₜ[ℤ] ν)) +ᵥ x.val := by
    have h := vsub_vadd (m • x) x
    rw [hdisp] at h
    rw [← h]
    change (((-t) • Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν) : TranslationSpace i) +ᵥ x).val = _
    rw [← Submodule.Quotient.mk_smul, val_mk_vadd]
  have h := congrArg (fun φ : RootFunctionFamily S G =>
    φ (weylAction i m δ) ((m : rationalPoints G) * Z * (m : rationalPoints G)⁻¹)) hval
  simp only [KPApartmentData.val_smul, RootFunctionFamily.smul_apply,
    RootFunctionFamily.vadd_apply] at h
  have hinv : weylAction i m⁻¹ (weylAction i m δ) = δ := by
    rw [map_inv]
    exact (weylAction i m).symm_apply_apply δ
  have hconj : (m : rationalPoints G)⁻¹ * ((m : rationalPoints G) * Z *
      (m : rationalPoints G)⁻¹) * (m : rationalPoints G) = Z := by group
  rw [hinv, hconj] at h
  rw [h, map_smul, eval_tmul, one_mul]
  congr 2
  have hpair : latticePairing S (weylAction i m δ) ν = -latticePairing S δ ν := by
    rw [hr δ, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply, hν2, smul_eq_mul]
    ring
  rw [smul_eq_mul, hpair]
  push_cast
  ring

end Reflection

section PiecePairings

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {f : S ⟶ T} {J : Type*} [Finite J]
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {a : characterLattice S}
  (hline : RestrictsToMultipliableLine f P a) {lp lq lm : J}
  (hp : f ≫ P.root lp = a) (hq : f ≫ P.root lq = a) (hpq : lp ≠ lq)
  (hm : P.root lm = P.root lp + P.root lq)

include hline hp hq hpq hm

/-- Partners pair to `-1`. -/
theorem piece_pairing_pq : P.pairing lp lq = -1 :=
  (exists_root_add_iff hline hpq hp hq).mp ⟨lm, hm⟩

/-- Partners pair to `-1`, in the other order. -/
theorem piece_pairing_qp : P.pairing lq lp = -1 :=
  pairing_symm_of_neg_one hline hpq hp hq (piece_pairing_pq hline hp hq hpq hm)

/-- The coroot of the partner sum is the sum of the coroots. -/
theorem piece_coroot_m : P.coroot lm = P.coroot lp + P.coroot lq := by
  have hpq' := piece_pairing_pq hline hp hq hpq hm
  have hqp' := piece_pairing_qp hline hp hq hpq hm
  have hidx : lm = P.reflectionPerm lq lp := by
    apply P.root.injective
    rw [hm, P.root_reflectionPerm, P.reflection_apply_root, hpq', neg_smul, one_smul,
      sub_neg_eq_add]
  rw [hidx, P.coroot_reflectionPerm, P.coreflection_apply_coroot, hqp', neg_smul, one_smul,
    sub_neg_eq_add, add_comm]

end PiecePairings

section PieceGroups

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {f : S ⟶ T} {J : Type*} [Finite J]
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {a : characterLattice S}
  (hT : IsSplitTorus T.toGrp) (hE : RelativeRoot.HasOppositeFactorPairs j)
  (hP : IsRootDatumOf j P)
  (hline : RestrictsToMultipliableLine f P a) {lp lq lm : J}
  (hp : f ≫ P.root lp = a) (hq : f ≫ P.root lq = a) (hpq : lp ≠ lq)
  (hm : P.root lm = P.root lp + P.root lq)

omit [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
include hP in
/-- Roots of a root datum of `j` lie in `relativeRoots j`. -/
theorem root_mem_relativeRoots (l : J) : P.root l ∈ relativeRoots j := by
  change P.root l ∈ roots j
  rw [← hP.2.1]
  exact Set.mem_range_self l

omit [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
include hP in
theorem mem_range_root_of_mem_relativeRoots {χ : characterLattice T}
    (hχ : χ ∈ relativeRoots j) : χ ∈ Set.range P.root := by
  rw [hP.2.1]
  exact hχ

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] in
include hline hp hq hpq hm in
/-- The pairings inside a piece. -/
theorem piece_pairings :
    P.toLinearMap (P.root lp) (P.coroot lp) = 2 ∧ P.toLinearMap (P.root lq) (P.coroot lq) = 2 ∧
    P.toLinearMap (P.root lq) (P.coroot lp) = -1 ∧ P.toLinearMap (P.root lp) (P.coroot lq) = -1 ∧
    P.toLinearMap (P.root lm) (P.coroot lp) = 1 ∧ P.toLinearMap (P.root lm) (P.coroot lq) = 1 ∧
    P.toLinearMap (P.root lp) (P.coroot lm) = 1 ∧ P.toLinearMap (P.root lq) (P.coroot lm) = 1 ∧
    P.toLinearMap (P.root lm) (P.coroot lm) = 2 := by
  have hpq' := piece_pairing_pq hline hp hq hpq hm
  have hqp' := piece_pairing_qp hline hp hq hpq hm
  have hcm := piece_coroot_m hline hp hq hpq hm
  have h11 : P.toLinearMap (P.root lp) (P.coroot lp) = 2 := by
    rw [P.root_coroot_eq_pairing, P.pairing_same]
  have h22 : P.toLinearMap (P.root lq) (P.coroot lq) = 2 := by
    rw [P.root_coroot_eq_pairing, P.pairing_same]
  have h21 : P.toLinearMap (P.root lq) (P.coroot lp) = -1 := by
    rw [P.root_coroot_eq_pairing, hqp']
  have h12 : P.toLinearMap (P.root lp) (P.coroot lq) = -1 := by
    rw [P.root_coroot_eq_pairing, hpq']
  refine ⟨h11, h22, h21, h12, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, map_add, LinearMap.add_apply, h11, h21]; norm_num
  · rw [hm, map_add, LinearMap.add_apply, h12, h22]; norm_num
  · rw [hcm, map_add, h11, h12]; norm_num
  · rw [hcm, map_add, h21, h22]; norm_num
  · rw [hm, hcm, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h11, h12, h21,
      h22]; norm_num

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
include hp hq hm in
/-- The restrictions inside a piece. -/
theorem piece_restrictions :
    f ≫ P.root lp = (1 : ℤ) • a ∧ f ≫ P.root lq = (1 : ℤ) • a ∧ f ≫ P.root lm = (2 : ℤ) • a ∧
    f ≫ (-P.root lp) = (-1 : ℤ) • a ∧ f ≫ (-P.root lq) = (-1 : ℤ) • a ∧
    f ≫ (-P.root lm) = (-2 : ℤ) • a := by
  have hm' : f ≫ P.root lm = (2 : ℤ) • a := by
    rw [hm, Preadditive.comp_add, hp, hq, two_zsmul]
  refine ⟨by rw [hp, one_smul], by rw [hq, one_smul], hm', ?_, ?_, ?_⟩
  · rw [Preadditive.comp_neg, hp, neg_smul, one_smul]
  · rw [Preadditive.comp_neg, hq, neg_smul, one_smul]
  · rw [Preadditive.comp_neg, hm', neg_smul]

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] [Mono j.hom.hom.left] [Finite J] in
theorem toLinearMap_neg_root (l l' : J) :
    P.toLinearMap (-P.root l) (P.coroot l') = -P.toLinearMap (P.root l) (P.coroot l') := by
  rw [map_neg, LinearMap.neg_apply]

include hT hE hP hline hp hq hpq hm

/-- Inside a piece, `[U_p, U_q] ⊆ U_m`. -/
theorem piece_commutator_mem_pq {x y : rationalPoints G} (hx : x ∈ rootGroupPoints j (P.root lp))
    (hy : y ∈ rootGroupPoints j (P.root lq)) :
    x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (P.root lm) := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have h := commutator_mem_of_only_root_combination j hT hE
    (root_mem_relativeRoots j hP lp).1 (root_mem_relativeRoots j hP lq).1 ?_
    (by rw [← hm]; exact root_mem_relativeRoots j hP lm) hx hy
  · rwa [← hm] at h
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lm) h1m h2m n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hp rp rq h11 h21 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

omit [Mono j.hom.hom.left] hE in
/-- Inside a piece, `U_{-p}` and `U_q` commute. -/
theorem piece_commute_neg_p_q {x y : rationalPoints G} (hx : x ∈ rootGroupPoints j (-P.root lp))
    (hy : y ∈ rootGroupPoints j (P.root lq)) : Commute x y := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have hs1 := toLinearMap_neg_root (P := P) lp lp
  rw [h11] at hs1
  apply commute_of_no_strict_root_combinations j hT _ _
    (neg_ne_zero.mpr (root_mem_relativeRoots j hP lp).1) (root_mem_relativeRoots j hP lq).1 _ hx hy
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lp) hs1 h21 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hp rnp rq hs1 h21 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

omit [Mono j.hom.hom.left] hE in
/-- Inside a piece, `U_m` and `U_q` commute. -/
theorem piece_commute_m_q {x y : rationalPoints G} (hx : x ∈ rootGroupPoints j (P.root lm))
    (hy : y ∈ rootGroupPoints j (P.root lq)) : Commute x y := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  apply commute_of_no_strict_root_combinations j hT _ _
    (root_mem_relativeRoots j hP lm).1 (root_mem_relativeRoots j hP lq).1 _ hx hy
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lq) hm2 h22 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hq rm rq hm2 h22 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

omit [Mono j.hom.hom.left] hE in
/-- Inside a piece, `U_{-m}` and `U_{-p}` commute. -/
theorem piece_commute_neg_m_neg_p {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (-P.root lm)) (hy : y ∈ rootGroupPoints j (-P.root lp)) :
    Commute x y := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have hs1 := toLinearMap_neg_root (P := P) lm lp
  have hs2 := toLinearMap_neg_root (P := P) lp lp
  rw [hm1] at hs1
  rw [h11] at hs2
  apply commute_of_no_strict_root_combinations j hT _ _
    (neg_ne_zero.mpr (root_mem_relativeRoots j hP lm).1)
    (neg_ne_zero.mpr (root_mem_relativeRoots j hP lp).1) _ hx hy
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lp) hs1 hs2 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hp rnm rnp hs1 hs2 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

/-- Inside a piece, `[U_{-p}, U_m] ⊆ U_q`. -/
theorem piece_commutator_mem_neg_p_m {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (-P.root lp)) (hy : y ∈ rootGroupPoints j (P.root lm)) :
    x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (P.root lq) := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have hs1 := toLinearMap_neg_root (P := P) lp lp
  have hs2 := toLinearMap_neg_root (P := P) lp lq
  rw [h11] at hs1
  rw [h12] at hs2
  have hsum : -P.root lp + P.root lm = P.root lq := by rw [hm]; abel
  have h := commutator_mem_of_only_root_combination j hT hE
    (neg_ne_zero.mpr (root_mem_relativeRoots j hP lp).1) (root_mem_relativeRoots j hP lm).1 ?_
    (by rw [hsum]; exact root_mem_relativeRoots j hP lq) hx hy
  · rwa [hsum] at h
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lq) hs2 hm2 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hp rnp rm hs1 hm1 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

/-- Inside a piece, `[U_m, U_{-p}] ⊆ U_q`. -/
theorem piece_commutator_mem_m_neg_p {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lm)) (hy : y ∈ rootGroupPoints j (-P.root lp)) :
    x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (P.root lq) := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have hs1 := toLinearMap_neg_root (P := P) lp lp
  have hs2 := toLinearMap_neg_root (P := P) lp lq
  rw [h11] at hs1
  rw [h12] at hs2
  have hsum : P.root lm + -P.root lp = P.root lq := by rw [hm]; abel
  have h := commutator_mem_of_only_root_combination j hT hE
    (root_mem_relativeRoots j hP lm).1 (neg_ne_zero.mpr (root_mem_relativeRoots j hP lp).1) ?_
    (by rw [hsum]; exact root_mem_relativeRoots j hP lq) hx hy
  · rwa [hsum] at h
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lq) hm2 hs2 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hp rm rnp hm1 hs1 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

/-- Inside a piece, `[U_{-m}, U_q] ⊆ U_{-p}`. -/
theorem piece_commutator_mem_neg_m_q {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (-P.root lm)) (hy : y ∈ rootGroupPoints j (P.root lq)) :
    x * y * x⁻¹ * y⁻¹ ∈ rootGroupPoints j (-P.root lp) := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨rp, rq, rm, rnp, rnq, rnm⟩ := piece_restrictions hp hq hm
  have hs1 := toLinearMap_neg_root (P := P) lm lq
  have hs2 := toLinearMap_neg_root (P := P) lm lp
  rw [hm2] at hs1
  rw [hm1] at hs2
  have hsum : -P.root lm + P.root lq = -P.root lp := by rw [hm]; abel
  have hnp : -P.root lp ∈ relativeRoots j :=
    neg_mem_relativeRoots_of_isRootDatumOf j hP (root_mem_relativeRoots j hP lp)
  have h := commutator_mem_of_only_root_combination j hT hE
    (neg_ne_zero.mpr (root_mem_relativeRoots j hP lm).1) (root_mem_relativeRoots j hP lq).1 ?_
    (by rw [hsum]; exact hnp) hx hy
  · rwa [hsum] at h
  intro n l hn hl
  refine ⟨combination_ne_zero (lξ := lp) hs2 h21 n l (by omega), fun hρ => ?_⟩
  have hb := combination_bounds hline hq rnm rq hs1 h22 n l
    (mem_range_root_of_mem_relativeRoots j hP hρ)
  omega

omit [Smooth G.X.hom] [Mono j.hom.hom.left] hT hE in
/-- Inside a piece, `U_q ∩ U_m = 1`. -/
theorem piece_eq_one_of_mem_q_of_mem_m {x : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lq)) (hx' : x ∈ rootGroupPoints j (P.root lm)) :
    x = 1 := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  apply eq_one_of_mem_rootGroupPoints_of_pairing j (-P.coroot lp) _ _ hx hx'
  · rw [← hP.1, map_neg, h21]; norm_num
  · rw [← hP.1, map_neg, hm1]; norm_num

omit [Smooth G.X.hom] [Mono j.hom.hom.left] hT hE in
/-- Inside a piece, `U_q ∩ U_{-p} = 1`. -/
theorem piece_eq_one_of_mem_q_of_mem_neg_p {x : rationalPoints G}
    (hx : x ∈ rootGroupPoints j (P.root lq)) (hx' : x ∈ rootGroupPoints j (-P.root lp)) :
    x = 1 := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  apply eq_one_of_mem_rootGroupPoints_of_pairing j (P.coroot lm) _ _ hx hx'
  · rw [← hP.1, h2m]; norm_num
  · rw [← hP.1, map_neg, LinearMap.neg_apply, h1m]; norm_num

end PieceGroups

section PieceReflections

variable {k : Type u} [Field k] {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  (j : T.toGrp ⟶ G) [Mono j.hom.hom.left]
  {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  (hT : IsSplitTorus T.toGrp) (hjc : IsClosedSubgroup j) (hP : IsRootDatumOf j P)

omit [Smooth G.X.hom] [Finite J] in
include hT hjc hP in
/-- The integral coroot of an opposite pair of a nontrivial point of `U_{P.root l}` is the
coroot of `l`. -/
theorem IsOppositeFactorPair.coroot_eq_rootDatum (l : J) {X : rationalPoints G}
    (hX : X ∈ rootGroupPoints j (P.root l)) (hX1 : X ≠ 1)
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root l) X pr) :
    hpr.coroot j hT (root_mem_relativeRoots j hP l).1 hX hX1 = P.coroot l := by
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Finite (weylImage j) := splitTorusWeylImageFinite k G T hT j hjc
  obtain ⟨hν, hr⟩ := hpr.coroot_spec j hT (root_mem_relativeRoots j hP l).1 hX hX1
  exact IsRootDatumOf.coroot_eq_of_weylAction_of_finite_weylImage j hP l _ hν _ hr

omit [Smooth G.X.hom] [Finite J] in
include hT hjc hP in
/-- The product of an opposite pair of a nontrivial point of `U_{P.root l}` acts on characters
by the reflection of `P` in `l`. -/
theorem weylAction_oppositeFactorPair_eq (l : J) {X : rationalPoints G}
    (hX : X ∈ rootGroupPoints j (P.root l)) (hX1 : X ≠ 1)
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root l) X pr) (χ : characterLattice T) :
    weylAction j (⟨pr.1 * X * pr.2, hpr.2.2⟩ : normalizerPoints j) χ =
      χ - P.toLinearMap χ (P.coroot l) • P.root l := by
  obtain ⟨-, hr⟩ := hpr.coroot_spec j hT (root_mem_relativeRoots j hP l).1 hX hX1
  rw [hr χ, IsOppositeFactorPair.coroot_eq_rootDatum j hT hjc hP l hX hX1 hpr, ← hP.1]

variable {S : CommGroupScheme (Spec (CommRingCat.of k))} {f : S ⟶ T} {a : characterLattice S}
  (hE : RelativeRoot.HasOppositeFactorPairs j)
  (hline : RestrictsToMultipliableLine f P a) {lp lq lm : J}
  (hp : f ≫ P.root lp = a) (hq : f ≫ P.root lq = a) (hpq : lp ≠ lq)
  (hm : P.root lm = P.root lp + P.root lq)

include hT hjc hP hE hline hp hq hpq hm

/-- Inside a piece, conjugation of `U_q` by the opposite-pair product of `X ∈ U_p` is the
commutator with `X`, and lands in `U_m`. -/
theorem piece_conj_eq_commutator_p {X : rationalPoints G}
    (hX : X ∈ rootGroupPoints j (P.root lp)) (hX1 : X ≠ 1)
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (P.root lp) X pr)
    {Z : rationalPoints G} (hZ : Z ∈ rootGroupPoints j (P.root lq)) :
    (pr.1 * X * pr.2) * Z * (pr.1 * X * pr.2)⁻¹ = X * Z * X⁻¹ * Z⁻¹ := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  have hw : weylAction j (⟨pr.1 * X * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lq) =
      P.root lm := by
    rw [weylAction_oppositeFactorPair_eq j hT hjc hP lp hX hX1 hpr, h21, hm]
    simp only [neg_smul, one_smul, sub_neg_eq_add, add_comm]
  exact conj_eq_commutator_of_oppositeFactorPair j hpr hw
    (fun A hA Z hZ => piece_commute_neg_p_q j hT hP hline hp hq hpq hm hA hZ)
    (fun Z hZ E hEm => (piece_commute_m_q j hT hP hline hp hq hpq hm hEm hZ).symm)
    (fun Z hZ => piece_commutator_mem_pq j hT hE hP hline hp hq hpq hm hX hZ)
    (fun A hA E hEm => piece_commutator_mem_neg_p_m j hT hE hP hline hp hq hpq hm hA hEm)
    (fun x hx hx' => piece_eq_one_of_mem_q_of_mem_m j hP hline hp hq hpq hm hx hx') hZ

/-- Inside a piece, conjugation of `U_q` by the opposite-pair product of `Y ∈ U_{-m}` is the
commutator with `Y`, and lands in `U_{-p}`. -/
theorem piece_conj_eq_commutator_neg_m {Y : rationalPoints G}
    (hY : Y ∈ rootGroupPoints j (-P.root lm)) (hY1 : Y ≠ 1)
    {pr : rationalPoints G × rationalPoints G}
    (hpr : RelativeRoot.IsOppositeFactorPair j (-P.root lm) Y pr)
    {Z : rationalPoints G} (hZ : Z ∈ rootGroupPoints j (P.root lq)) :
    (pr.1 * Y * pr.2) * Z * (pr.1 * Y * pr.2)⁻¹ = Y * Z * Y⁻¹ * Z⁻¹ := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  set ln := P.reflectionPerm lm lm with hln
  have hroot : P.root ln = -P.root lm := by
    rw [hln, P.root_reflectionPerm, P.reflection_apply_self]
  have hcoroot : P.coroot ln = -P.coroot lm := by
    rw [hln, P.coroot_reflectionPerm, P.coreflection_apply_self]
  rw [← hroot] at hY hpr
  have hw : weylAction j (⟨pr.1 * Y * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lq) =
      -P.root lp := by
    rw [weylAction_oppositeFactorPair_eq j hT hjc hP ln hY hY1 hpr, hcoroot, map_neg, h2m,
      hroot, hm]
    simp only [neg_smul, one_smul, neg_neg, smul_neg]
    abel
  rw [hroot] at hY hpr
  have hnn : -(-P.root lm) = P.root lm := neg_neg _
  exact conj_eq_commutator_of_oppositeFactorPair j hpr hw
    (fun A hA Z hZ => piece_commute_m_q j hT hP hline hp hq hpq hm (hnn ▸ hA) hZ)
    (fun Z hZ E hEm => (piece_commute_neg_p_q j hT hP hline hp hq hpq hm hEm hZ).symm)
    (fun Z hZ => piece_commutator_mem_neg_m_q j hT hE hP hline hp hq hpq hm hY hZ)
    (fun A hA E hEm => piece_commutator_mem_m_neg_p j hT hE hP hline hp hq hpq hm (hnn ▸ hA) hEm)
    (fun x hx hx' => piece_eq_one_of_mem_q_of_mem_neg_p j hP hline hp hq hpq hm hx hx') hZ

/-- **Exact commutator values in a piece.** For `X ∈ U_p` nontrivial and `Z ∈ U_q`, the value
of `[X, Z] ∈ U_m` at any point of a normalizer-stable apartment class is the sum of the values
of `X` and `Z`. -/
theorem piece_val_commutator {ω : kˣ → ℝ} (D : KPApartmentData j ω)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus j) (x : D.Apartment)
    {X : rationalPoints G} (hX : X ∈ rootGroupPoints j (P.root lp)) (hX1 : X ≠ 1)
    {Z : rationalPoints G} (hZ : Z ∈ rootGroupPoints j (P.root lq)) :
    x.val (P.root lm) (X * Z * X⁻¹ * Z⁻¹) = x.val (P.root lq) Z + x.val (P.root lp) X := by
  obtain ⟨h11, h22, h21, h12, hm1, hm2, h1m, h2m, hmm⟩ := piece_pairings hline hp hq hpq hm
  obtain ⟨pr, hpr⟩ := hE (P.root lp) (root_mem_relativeRoots j hP lp) X hX hX1
  obtain ⟨t, ht⟩ : ∃ t : ℝ, x.val (P.root lp) X = t := by
    have hne : x.val (P.root lp) X ≠ ⊤ := fun htop =>
      hX1 ((x.isValuation.eq_top_iff _ (root_mem_relativeRoots j hP lp) X hX).mp htop)
    obtain ⟨t, htt⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨t, htt.symm⟩
  have hRC := piece_conj_eq_commutator_p j hT hjc hP hE hline hp hq hpq hm hX hX1 hpr hZ
  have hRF := D.val_eq_val_conj_oppositeFactorPair hG hi
    (α := ⟨P.root lp, root_mem_relativeRoots j hP lp⟩) hX hX1 hpr x ht (P.root lq) Z
  have hcor := IsOppositeFactorPair.coroot_eq_rootDatum j hT hjc hP lp hX hX1 hpr
  have hw : weylAction j (⟨pr.1 * X * pr.2, hpr.2.2⟩ : normalizerPoints j) (P.root lq) =
      P.root lm := by
    rw [weylAction_oppositeFactorPair_eq j hT hjc hP lp hX hX1 hpr, h21, hm]
    simp only [neg_smul, one_smul, sub_neg_eq_add, add_comm]
  change x.val (P.root lq) Z = x.val (weylAction j _ (P.root lq)) _ +
    ((t * latticePairing T (P.root lq) (hpr.coroot j _ _ hX hX1) : ℝ) : WithTop ℝ) at hRF
  rw [hw, hRC, hcor, ← hP.1, h21] at hRF
  rw [hRF, ht, add_assoc, ← WithTop.coe_add]
  norm_num

end PieceReflections

end Langlands.Geometry.Building
