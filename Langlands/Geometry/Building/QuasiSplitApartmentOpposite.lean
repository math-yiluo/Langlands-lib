import Langlands.Geometry.Building.QuasiSplitApartmentShifts
import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction
import Langlands.GroupScheme.Rational.RootFiberTransitivity
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport
import Langlands.Geometry.Building.RootFunctionGaloisAction

/-! # The opposite-pair axiom for the descended quasi-split family -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

section Commutation

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (i : T.toGrp ⟶ G)

/-- Root subgroups of a split torus commute when no strictly positive
combination of the two characters is zero or a root. -/
theorem commute_of_no_strict_root_combinations (hT : IsSplitTorus T.toGrp)
    (c d : characterLattice T) (hc : c ≠ 0) (hd : d ≠ 0)
    (hcd : ∀ n m : ℕ, 0 < n → 0 < m →
      n • c + m • d ≠ 0 ∧ n • c + m • d ∉ relativeRoots i)
    {Z : Over (Spec (CommRingCat.of k))} {x y : Z ⟶ G.X}
    (hx : x ∈ (RelativeRoot.subgroup i c).carrier Z)
    (hy : y ∈ (RelativeRoot.subgroup i d).carrier Z) :
    Commute x y := by
  let action := AutomorphicAction.conjugation i
  have hbot : RelativeRoot.semigroupSubgroup action
      (RelativeRoot.semigroupSum (RelativeRoot.cyclicTail c 1)
        (RelativeRoot.cyclicTail d 1)) = ⊥ := by
    apply RelativeRoot.semigroupSubgroup_eq_bot_of_noAmbientWeights_without_realization
      action hT
    rintro χ ⟨_, ⟨n, _, hn, rfl⟩, _, ⟨m, _, hm, rfl⟩, rfl⟩ hweight
    obtain ⟨hzero, hroot⟩ := hcd n m hn hm
    exact hroot ((RelativeRoot.mem_actionWeightSupport_conjugation_iff i hzero).mp hweight)
  have hx' : x ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail c 1)).carrier Z := by
    change x ∈ (RelativeRoot.weightFiltration action c 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT i c hc]
    exact hx
  have hy' : y ∈ (RelativeRoot.semigroupSubgroup action
      (RelativeRoot.cyclicTail d 1)).carrier Z := by
    change y ∈ (RelativeRoot.weightFiltration action d 1).carrier Z
    rw [RelativeRoot.weightFiltration_one_eq_subgroup hT i d hd]
    exact hy
  have h := RelativeRoot.semigroupCommutator k G inferInstance inferInstance
    T hT action (RelativeRoot.cyclicTail c 1) (RelativeRoot.cyclicTail d 1) Z x y hx' hy'
  rw [hbot] at h
  have heq : x * y * x⁻¹ * y⁻¹ = 1 := h
  exact commutatorElement_eq_one_iff_commute.mp heq

end Commutation

section RootPairing

/-- In a finite root datum, two distinct roots `αᵢ ≠ -αⱼ` such that no `p αᵢ + q αⱼ`
(`p, q > 0`) is a root and `αᵢ - αⱼ` is not a root are orthogonal, so no `p αᵢ - q αⱼ`
(`p, q > 0`) is zero or a root. -/
theorem rootDatum_nsmul_sub_nsmul_notMem {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Finite J] (P : RootDatum J M N) {i₁ i₂ : J} (hne : i₁ ≠ i₂)
    (hneg : P.root i₁ ≠ -P.root i₂)
    (hadd : ∀ p q : ℕ, 0 < p → 0 < q → p • P.root i₁ + q • P.root i₂ ∉ Set.range P.root)
    (hsub : P.root i₁ - P.root i₂ ∉ Set.range P.root)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    p • P.root i₁ - q • P.root i₂ ≠ 0 ∧ p • P.root i₁ - q • P.root i₂ ∉ Set.range P.root := by
  have h0 : P.pairing i₁ i₂ = 0 :=
    P.pairing_eq_zero_of_add_notMem_of_sub_notMem hne hneg
      (by simpa using hadd 1 1 one_pos one_pos) hsub
  have hpair : P.toLinearMap (p • P.root i₁ - q • P.root i₂) (P.coroot i₂) =
      -(2 * (q : ℤ)) := by
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply,
      P.root_coroot_eq_pairing, h0, P.pairing_same, smul_zero, zero_sub, nsmul_eq_mul]
    ring
  have hrefl : P.reflection i₂ (p • P.root i₁ - q • P.root i₂) =
      p • P.root i₁ + q • P.root i₂ := by
    rw [map_sub, map_nsmul, map_nsmul, P.reflection_apply_root, P.reflection_apply_self, h0,
      zero_smul, sub_zero, smul_neg, sub_neg_eq_add]
  constructor
  · intro hz
    rw [hz, map_zero, LinearMap.zero_apply] at hpair
    omega
  · rintro ⟨m, hm⟩
    apply hadd p q hp hq
    rw [← hrefl, ← hm, ← P.root_reflectionPerm]
    exact Set.mem_range_self _

end RootPairing

/-- No strictly positive combination of `c` and `d` is zero or a root of `i`. -/
def NoStrictRootCombinations {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (c d : characterLattice T) : Prop :=
  ∀ n m : ℕ, 0 < n → 0 < m → n • c + m • d ≠ 0 ∧ n • c + m • d ∉ relativeRoots i

section Fiber

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (j : T.toGrp ⟶ G)

/-- Without roots over higher multiples of `β`, the selected indivisible roots over the
positive ray of `β` are exactly the roots restricting to `β`. -/
theorem semigroupIndivisibleRoots_preimage_eq_fiber (hS : IsSplitTorus S.toGrp)
    (f : S ⟶ T) (β : characterLattice S) (hβ : β ≠ 0)
    (hhigh : ∀ χ ∈ relativeRoots j, ∀ n : ℕ, 2 ≤ n → f ≫ χ ≠ n • β) :
    RelativeRoot.semigroupIndivisibleRoots j
        (RelativeRoot.characterSemigroupPreimage f (RelativeRoot.cyclicTail β 1)) =
      {χ | χ ∈ relativeRoots j ∧ f ≫ χ = β} := by
  ext χ
  constructor
  · rintro ⟨hχ, ⟨m, _, hm, heq⟩, _⟩
    change m • β = f ≫ χ at heq
    refine ⟨hχ, ?_⟩
    rcases Nat.lt_or_ge m 2 with h | h
    · obtain rfl : m = 1 := by omega
      simpa using heq.symm
    · exact absurd heq.symm (hhigh χ hχ m h)
  · rintro ⟨hχ, heq⟩
    refine ⟨hχ, ⟨1, le_rfl, one_pos, ?_⟩, ?_⟩
    · change 1 • β = f ≫ χ
      rw [one_smul, heq]
    rintro b _ ⟨m', _, hm', hb'⟩ m hm hmb
    change m' • β = f ≫ b at hb'
    have h1 : β = (m * m') • β := by
      calc β = f ≫ χ := heq.symm
        _ = f ≫ (m • b) := by rw [hmb]
        _ = m • (f ≫ b) := by rw [Preadditive.comp_nsmul]
        _ = m • (m' • β) := by rw [hb']
        _ = (m * m') • β := smul_smul _ _ _
    have h2 : (m * m' - 1) • β = 0 := by
      have hle : 1 ≤ m * m' := Nat.one_le_iff_ne_zero.mpr (by positivity)
      have : (m * m' - 1) • β + β = β := by
        rw [← succ_nsmul, Nat.sub_add_cancel hle, ← h1]
      simpa using this
    have hne : m * m' - 1 ≠ 0 := by
      have : 2 ≤ m * m' := le_trans hm (Nat.le_mul_of_pos_right m hm')
      omega
    exact hS.nsmul_ne_zero hβ hne h2

variable {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

omit [Finite J] in
/-- Roots of a root datum of `j` are closed under negation. -/
theorem neg_mem_relativeRoots_of_isRootDatumOf (hP : IsRootDatumOf j P)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots j) : -χ ∈ relativeRoots j := by
  change χ ∈ roots j at hχ
  change -χ ∈ roots j
  rw [← hP.2.1] at hχ ⊢
  obtain ⟨m, rfl⟩ := hχ
  exact P.neg_root_mem m

variable (hS : IsSplitTorus S.toGrp) (f : S ⟶ T) {β : characterLattice S}
  (hβ : β ≠ 0) (hhigh : ∀ χ ∈ relativeRoots j, ∀ n : ℕ, 2 ≤ n → f ≫ χ ≠ n • β)
  {χ χ' : characterLattice T} (hχ : χ ∈ relativeRoots j) (hχ' : χ' ∈ relativeRoots j)
  (hfχ : f ≫ χ = β) (hfχ' : f ≫ χ' = β)

include hS hβ hhigh hfχ hfχ' in
/-- Two roots in one fibre over `β` have no strict positive combination. -/
theorem noStrictRootCombinations_fiber_pos :
    NoStrictRootCombinations j χ χ' := by
  intro n m hn hm
  have hres : f ≫ (n • χ + m • χ') = (n + m) • β := by
    rw [Preadditive.comp_add, Preadditive.comp_nsmul, Preadditive.comp_nsmul, hfχ, hfχ',
      add_nsmul]
  refine ⟨fun hz => ?_, fun hr => ?_⟩
  · rw [hz, Limits.comp_zero] at hres
    exact hS.nsmul_ne_zero hβ (by omega) hres.symm
  · exact hhigh _ hr (n + m) (by omega) hres

omit [Finite J] in
include hS hβ hhigh hfχ hfχ' in
/-- Negatives of two roots in one fibre over `β` have no strict positive combination. -/
theorem noStrictRootCombinations_fiber_neg (hP : IsRootDatumOf j P) :
    NoStrictRootCombinations j (-χ) (-χ') := by
  intro n m hn hm
  obtain ⟨hz, hr⟩ := noStrictRootCombinations_fiber_pos j hS f hβ hhigh hfχ hfχ' n m hn hm
  have heq : n • (-χ) + m • (-χ') = -(n • χ + m • χ') := by
    rw [smul_neg, smul_neg, neg_add]
  rw [heq]
  refine ⟨neg_ne_zero.mpr hz, fun h => hr ?_⟩
  simpa using neg_mem_relativeRoots_of_isRootDatumOf j hP h

include hS hβ hhigh hχ hχ' hfχ hfχ' in
/-- Two distinct roots in one fibre over `β` are orthogonal, so a root and the negative of
another have no strict positive combination. -/
theorem noStrictRootCombinations_fiber_pos_neg (hP : IsRootDatumOf j P)
    (hzero : ∀ ψ ∈ relativeRoots j, f ≫ ψ ≠ 0) (hne : χ ≠ χ') :
    NoStrictRootCombinations j χ (-χ') := by
  have hroots : relativeRoots j = Set.range P.root := hP.2.1.symm
  obtain ⟨i₁, rfl⟩ : χ ∈ Set.range P.root := hroots ▸ hχ
  obtain ⟨i₂, rfl⟩ : χ' ∈ Set.range P.root := hroots ▸ hχ'
  have hi : i₁ ≠ i₂ := fun h => hne (by rw [h])
  have hneg : P.root i₁ ≠ -P.root i₂ := by
    intro h
    have h2 : f ≫ P.root i₁ = -(f ≫ P.root i₂) := by rw [h, Preadditive.comp_neg]
    rw [hfχ, hfχ'] at h2
    have : 2 • β = 0 := by rw [two_nsmul]; nth_rewrite 1 [h2]; exact neg_add_cancel β
    exact hS.nsmul_ne_zero hβ two_ne_zero this
  have hadd : ∀ p q : ℕ, 0 < p → 0 < q →
      p • P.root i₁ + q • P.root i₂ ∉ Set.range P.root := by
    intro p q hp hq
    rw [← hroots]
    exact (noStrictRootCombinations_fiber_pos j hS f hβ hhigh hfχ hfχ' p q hp hq).2
  have hsub : P.root i₁ - P.root i₂ ∉ Set.range P.root := by
    rw [← hroots]
    intro h
    apply hzero _ h
    rw [Preadditive.comp_sub, hfχ, hfχ', sub_self]
  intro n m hn hm
  have heq : n • P.root i₁ + m • (-P.root i₂) = n • P.root i₁ - m • P.root i₂ := by
    rw [smul_neg, sub_eq_add_neg]
  rw [heq, hroots]
  exact rootDatum_nsmul_sub_nsmul_notMem P hi hneg hadd hsub n m hn hm

end Fiber

/-- The condition `NoStrictRootCombinations` is symmetric. -/
theorem NoStrictRootCombinations.symm {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {i : T.toGrp ⟶ G} {c d : characterLattice T} (h : NoStrictRootCombinations i c d) :
    NoStrictRootCombinations i d c := by
  intro n m hn hm
  rw [add_comm]
  exact h m n hm hn

/-- An ordered product of triple products splits into the three ordered products when the
factors with different indices commute. -/
theorem list_ofFn_prod_mul_mul {M : Type*} [Monoid M] : ∀ {n : ℕ} (A B C : Fin n → M),
    (∀ l m, l ≠ m → Commute (B l) (A m) ∧ Commute (C l) (A m) ∧ Commute (C l) (B m)) →
    (List.ofFn fun l => A l * B l * C l).prod =
      (List.ofFn A).prod * (List.ofFn B).prod * (List.ofFn C).prod
  | 0, _, _, _, _ => by simp
  | n + 1, A, B, C, h => by
    have ih := list_ofFn_prod_mul_mul (fun l : Fin n => A l.succ) (fun l => B l.succ)
      (fun l => C l.succ)
      (fun l m hlm => h l.succ m.succ (fun e => hlm (Fin.succ_injective _ e)))
    have hcomm : ∀ (D : Fin (n + 1) → M) (x : M),
        (∀ m : Fin n, Commute x (D m.succ)) →
          Commute x (List.ofFn fun l : Fin n => D l.succ).prod := by
      intro D x hx
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨m, rfl⟩ := (List.mem_ofFn' _ _).mp hy
      exact hx m
    have hBA := hcomm A (B 0) (fun m => (h 0 m.succ (Fin.succ_ne_zero m).symm).1)
    have hCA := hcomm A (C 0) (fun m => (h 0 m.succ (Fin.succ_ne_zero m).symm).2.1)
    have hCB := hcomm B (C 0) (fun m => (h 0 m.succ (Fin.succ_ne_zero m).symm).2.2)
    simp only [List.ofFn_succ, List.prod_cons]
    rw [ih]
    set PA := (List.ofFn fun l : Fin n => A l.succ).prod
    set PB := (List.ofFn fun l : Fin n => B l.succ).prod
    set PC := (List.ofFn fun l : Fin n => C l.succ).prod
    calc A 0 * B 0 * C 0 * (PA * PB * PC)
        = A 0 * (B 0 * ((C 0 * PA) * PB * PC)) := by simp only [mul_assoc]
      _ = A 0 * (B 0 * ((PA * C 0) * PB * PC)) := by rw [hCA.eq]
      _ = A 0 * ((B 0 * PA) * ((C 0 * PB) * PC)) := by simp only [mul_assoc]
      _ = A 0 * ((PA * B 0) * ((PB * C 0) * PC)) := by rw [hBA.eq, hCB.eq]
      _ = A 0 * PA * (B 0 * PB) * (C 0 * PC) := by simp only [mul_assoc]

/-- An element of `WithTop ℝ` adding to zero with a real number is its negative. -/
theorem withTop_eq_neg_of_add_coe_eq_zero {x : WithTop ℝ} {c : ℝ}
    (h : x + (c : WithTop ℝ) = 0) : x = ((-c : ℝ) : WithTop ℝ) := by
  induction x using WithTop.recTopCoe with
  | top => simp at h
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_eq_zero] at h
    rw [WithTop.coe_inj]
    linarith

section Separation

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- A point normalizing a torus which is a product of points of two opposite root groups of a
split torus mapping to it is the identity. -/
theorem normalizer_eq_one_of_mul_opposite_torusHom (j : T.toGrp ⟶ G)
    (hS : IsSplitTorus S.toGrp) (f : S ⟶ T) {α : characterLattice S} (hα : α ≠ 0)
    (n : normalizerPoints j) {x y : rationalPoints G}
    (hx : x ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) α)
    (hy : y ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hn : n.val = x * y) : n = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, hD, ν, hν⟩ := hS.exists_pairing_eq_pos hα
  have hpos : 0 < latticePairing S α ν := by omega
  have hneg : 0 < latticePairing S (-α) (-ν) := by simpa using hpos
  have hcomp : CommGroupScheme.groupHom ((-ν) ≫ f) ≫ j =
      CommGroupScheme.groupHom (-ν) ≫ (CommGroupScheme.groupHom f ≫ j) :=
    Category.assoc (CommGroupScheme.groupHom (-ν)) (CommGroupScheme.groupHom f) j
  apply normalizer_eq_one_of_unipotent_product j ((-ν) ≫ f) n ⟨x, ?_⟩ ⟨y, ?_⟩ hn
  · change x ∈ (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ((-ν) ≫ f) ≫ j))).carrier _
    rw [hcomp, ← groupHom_neg_comp_eq_oppositeCocharacter, neg_neg]
    exact RelativeRoot.subgroup_le_dynamicUnipotent _ ν hpos _ hx
  · change y ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ((-ν) ≫ f) ≫ j)).carrier _
    rw [hcomp]
    exact RelativeRoot.subgroup_le_dynamicUnipotent _ (-ν) hneg _ hy

/-- Conjugating by the inverse of the normalizer of an opposite factor pair carries the
opposite root group into the root group. -/
theorem IsOppositeFactorPair.inv_conj_mem (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) {α : characterLattice S} (hα : α ≠ 0)
    {x : rationalPoints G} (hx : x ∈ rootGroupPoints i α) (hx1 : x ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : RelativeRoot.IsOppositeFactorPair i α x p)
    {y : rationalPoints G} (hy : y ∈ rootGroupPoints i (-α)) :
    (p.1 * x * p.2)⁻¹ * y * (p.1 * x * p.2) ∈ rootGroupPoints i α := by
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hflip : weylAction i n α = -α := hp.weylAction_eq_neg i hS hα hx hx1
  have hinv : weylAction i n⁻¹ (-α) = α := by
    calc weylAction i n⁻¹ (-α) = weylAction i n⁻¹ (weylAction i n α) := by rw [hflip]
      _ = α := by
        rw [map_inv]
        exact (weylAction i n).symm_apply_apply α
  have h := RelativeRoot.normalizer_conj_mem i (-α) n⁻¹ hy
  simp only [G.constantPoint_self, Subgroup.coe_inv, inv_inv, hinv] at h
  exact h

end Separation

section Opposite

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {j : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono j.hom.hom.left]
  {φ : RootFunctionFamily T G} [Smooth G.X.hom]

/-- If no root restricts to a higher multiple of `α` and all intrinsic coordinates of a point
over the fibre of `α` have the same upper value `c`, then its restricted value is `c`. -/
theorem torusRestrictedRootFunctionFamily_eq_of_coordinates
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) {α : characterLattice S}
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hhigh : ∀ χ ∈ relativeRoots j, ∀ n : ℕ, 2 ≤ n → f ≫ χ ≠ n • α)
    {n : ℕ} (hn : 0 < n) (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (hrange : Set.range a = {χ | χ ∈ relativeRoots j ∧ f ≫ χ = α})
    (X : ∀ l, (RelativeRoot.subgroup j (a l)).carrier (Over.mk (𝟙 _)))
    (c : ℝ) (hc : ∀ l, φ (a l) (X l).val = c) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α
      (RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X) = c := by
  have hα0 : α ≠ 0 := hα.1
  have hrange' := hrange.trans
    (semigroupIndivisibleRoots_preimage_eq_fiber j hS f α hα0 hhigh).symm
  have hrestrict : ∀ l, f ≫ a l = (fun _ => 1) l • α := by
    intro l
    have hl : a l ∈ {χ | χ ∈ relativeRoots j ∧ f ≫ χ = α} := hrange ▸ Set.mem_range_self l
    simpa using hl.2
  have hbounds := fun r => mem_torusRestrictedRootDepthSubgroup_iff_coordinate_bounds
    hS hT hE hφ f α hα0 r a (fun _ => 1) hinj hrange' hrestrict X _ rfl
  have hmem : RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) α := by
    apply torusRestrictedRootDepthSubgroup_le_rootGroupPoints hS hT hφ f α hα0 c
    rw [hbounds c]
    intro l
    simp [hc l]
  have hiff : ∀ r : ℝ, (r : WithTop ℝ) ≤ torusRestrictedRootFunctionFamily hS hT hE hφ f α
      (RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X) ↔ r ≤ c := by
    intro r
    rw [le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα _ hmem r, hbounds r]
    simp only [hc, Nat.cast_one, one_mul, WithTop.coe_le_coe]
    exact ⟨fun h => h ⟨0, hn⟩, fun h _ => h⟩
  generalize torusRestrictedRootFunctionFamily hS hT hE hφ f α
    (RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X) = v at hiff ⊢
  induction v using WithTop.recTopCoe with
  | top =>
    have h := (hiff (c + 1)).mp le_top
    linarith
  | coe t =>
    have h1 : t ≤ c := (hiff t).mp le_rfl
    have h2 : (c : WithTop ℝ) ≤ t := (hiff c).mpr le_rfl
    rw [WithTop.coe_le_coe] at h2
    rw [le_antisymm h1 h2]

/-- An ordered product of root points for roots of `T` restricting to `β` is a point of the
restricted root group of `β`. -/
theorem list_ofFn_prod_mem_rootGroupPoints_comp
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (f : S ⟶ T) {β : characterLattice S}
    (hβ : β ≠ 0) {n : ℕ} (b : Fin n → characterLattice T)
    (hb : ∀ l, b l ∈ relativeRoots j ∧ f ≫ b l = β)
    (W : Fin n → rationalPoints G) (hW : ∀ l, W l ∈ rootGroupPoints j (b l)) :
    (List.ofFn W).prod ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) β := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hx
  have hcar := RelativeRoot.subgroup_comp_torusHom_carrier_eq_iSup hS hT f j hE β hβ
    (Over.mk (𝟙 _))
  have hmem : f ≫ b l ∈ RelativeRoot.cyclicTail β 1 :=
    ⟨1, le_rfl, one_pos, by rw [one_smul, (hb l).2]⟩
  have hle := le_iSup (fun χ : {χ : characterLattice T |
      χ ∈ relativeRoots j ∧ f ≫ χ ∈ RelativeRoot.cyclicTail β 1} =>
    (RelativeRoot.subgroup j χ.val).carrier (Over.mk (𝟙 _))) ⟨b l, (hb l).1, hmem⟩
  have h := hle (hW l)
  rw [← hcar] at h
  exact h

/-- **Opposite pairs over a fibre.** Let `g` be the ordered product of points `X l` of the
root groups of all roots `a l` of `T` restricting to `α`, all with the same upper value `c`.
If `g' g g''`, with `g', g''` in the opposite restricted root group, normalizes both `T` and
`S`, then the restricted value of `g'` is `-c`. -/
theorem torusRestrictedRootFunctionFamily_neg_eq_of_fiber
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs j) (hφ : IsRootDatumValuation j φ)
    (f : S ⟶ T) [Mono (CommGroupScheme.groupHom f ≫ j).hom.hom.left]
    {J : Type*} [Finite J] {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf j P) {α : characterLattice S}
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j))
    (hzero : ∀ ψ ∈ relativeRoots j, f ≫ ψ ≠ 0)
    (hhigh : ∀ χ ∈ relativeRoots j, ∀ n : ℕ, 2 ≤ n → f ≫ χ ≠ n • α)
    {n : ℕ} (a : Fin n → characterLattice T) (hinj : Function.Injective a)
    (hrange : Set.range a = {χ | χ ∈ relativeRoots j ∧ f ≫ χ = α})
    (X : ∀ l, (RelativeRoot.subgroup j (a l)).carrier (Over.mk (𝟙 _)))
    (c : ℝ) (hc : ∀ l, φ (a l) (X l).val = c)
    {g' g'' : rationalPoints G}
    (hg' : g' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hg'' : g'' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α))
    (hN : g' * RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X * g'' ∈
      normalizerPoints j)
    (hN' : g' * RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X * g'' ∈
      normalizerPoints (CommGroupScheme.groupHom f ≫ j)) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f (-α) g' = ((-c : ℝ) : WithTop ℝ) := by
  classical
  have hα0 : α ≠ 0 := hα.1
  have hfib : ∀ l, a l ∈ relativeRoots j ∧ f ≫ a l = α := fun l =>
    (show a l ∈ {χ | χ ∈ relativeRoots j ∧ f ≫ χ = α} from hrange ▸ Set.mem_range_self l)
  have hneg : ∀ l, -(a l) ∈ relativeRoots j ∧ f ≫ (-(a l)) = -α := fun l =>
    ⟨neg_mem_relativeRoots_of_isRootDatumOf j hP (hfib l).1,
      by rw [Preadditive.comp_neg, (hfib l).2]⟩
  -- the fibre is nonempty
  have hn : 0 < n := by
    obtain ⟨-, χ, hχ, hfχ⟩ := (mem_roots_comp_iff hT hS f j α).mp hα
    obtain ⟨l, -⟩ : χ ∈ Set.range a := hrange ▸ ⟨hχ, hfχ⟩
    exact l.pos
  have hX1 : ∀ l, (X l).val ≠ 1 := by
    intro l h
    have htop := (hφ.eq_top_iff (a l) (hfib l).1 (X l).val (X l).prop).mpr h
    rw [hc l] at htop
    exact WithTop.coe_ne_top htop
  -- upper opposite pairs and the upper axiom V 5
  choose p hp using fun l => hE (a l) (hfib l).1 (X l).val (X l).prop (hX1 l)
  have hY : ∀ l, φ (-(a l)) (p l).1 = ((-c : ℝ) : WithTop ℝ) := by
    intro l
    have h := hφ.opposite (a l) (hfib l).1 (X l).val (X l).prop (hX1 l) (p l).1 (hp l).1
      (p l).2 (hp l).2.1 (hp l).2.2
    rw [hc l] at h
    exact withTop_eq_neg_of_add_coe_eq_zero h
  -- factors with different indices commute
  have hroot : ∀ l, a l ≠ 0 := fun l => (hfib l).1.1
  have hcomm : ∀ l m, l ≠ m → Commute (X l).val (p m).1 ∧ Commute (p l).2 (p m).1 ∧
      Commute (p l).2 (X m).val := by
    intro l m hlm
    have hne : a l ≠ a m := fun h => hlm (hinj h)
    refine ⟨?_, ?_, ?_⟩
    · exact commute_of_no_strict_root_combinations j hT (a l) (-(a m)) (hroot l)
        (neg_ne_zero.mpr (hroot m))
        (noStrictRootCombinations_fiber_pos_neg j hS f hα0 hhigh (hfib l).1 (hfib m).1
          (hfib l).2 (hfib m).2 hP hzero hne)
        (X l).prop (hp m).1
    · exact commute_of_no_strict_root_combinations j hT (-(a l)) (-(a m))
        (neg_ne_zero.mpr (hroot l)) (neg_ne_zero.mpr (hroot m))
        (noStrictRootCombinations_fiber_neg j hS f hα0 hhigh (hfib l).2 (hfib m).2 hP)
        (hp l).2.1 (hp m).1
    · exact commute_of_no_strict_root_combinations j hT (-(a l)) (a m)
        (neg_ne_zero.mpr (hroot l)) (hroot m)
        (noStrictRootCombinations_fiber_pos_neg j hS f hα0 hhigh (hfib m).1 (hfib l).1
          (hfib m).2 (hfib l).2 hP hzero (Ne.symm hne)).symm
        (hp l).2.1 (X m).prop
  -- the product of the upper normalizers
  let Y : Fin n → rationalPoints G := fun l => (p l).1
  let Z : Fin n → rationalPoints G := fun l => (p l).2
  let Xv : Fin n → rationalPoints G := fun l => (X l).val
  have hprod : (List.ofFn fun l => Y l * Xv l * Z l).prod =
      (List.ofFn Y).prod * RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X *
        (List.ofFn Z).prod :=
    list_ofFn_prod_mul_mul Y Xv Z hcomm
  have hNprod : (List.ofFn Y).prod * RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X *
      (List.ofFn Z).prod ∈ normalizerPoints j := by
    rw [← hprod]
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨l, rfl⟩ := (List.mem_ofFn' _ _).mp hx
    exact (hp l).2.2
  have hY' : (List.ofFn Y).prod ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    list_ofFn_prod_mem_rootGroupPoints_comp hS hT hE f (neg_ne_zero.mpr hα0) _ hneg Y
      (fun l => (hp l).1)
  have hZ' : (List.ofFn Z).prod ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    list_ofFn_prod_mem_rootGroupPoints_comp hS hT hE f (neg_ne_zero.mpr hα0) _ hneg Z
      (fun l => (hp l).2.1)
  have hgmem : RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X ∈
      rootGroupPoints (CommGroupScheme.groupHom f ≫ j) α :=
    list_ofFn_prod_mem_rootGroupPoints_comp hS hT hE f hα0 a hfib Xv (fun l => (X l).prop)
  -- the product `g` is not the identity, by uniqueness of coordinates
  have hrange' := hrange.trans
    (semigroupIndivisibleRoots_preimage_eq_fiber j hS f α hα0 hhigh).symm
  have hg1 : RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X ≠ 1 := by
    intro h1
    obtain ⟨x, -, huniq⟩ :=
      (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct hS hT f j
        hE α hα0 a hinj hrange' (Over.mk (𝟙 _)) 1).mp (Subgroup.one_mem _)
    have e : X = fun l => ⟨1, Subgroup.one_mem _⟩ :=
      (huniq X h1).trans (huniq _ (by simp [RelativeRoot.rootPointsProduct])).symm
    exact hX1 ⟨0, hn⟩ (congrArg (fun F => (F ⟨0, hn⟩).val) e)
  -- separation: the two normalizers agree
  set g := RelativeRoot.rootPointsProduct j a (Over.mk (𝟙 _)) X with hg
  set Y' := (List.ofFn Y).prod with hY'def
  set Z' := (List.ofFn Z).prod with hZ'def
  have hA : (g' * Y'⁻¹)⁻¹ ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    Subgroup.inv_mem _ (Subgroup.mul_mem _ hg' (Subgroup.inv_mem _ hY'))
  have hconj := IsOppositeFactorPair.inv_conj_mem (CommGroupScheme.groupHom f ≫ j) hS hα0
    hgmem hg1 (p := (g', g'')) ⟨hg', hg'', hN'⟩ hA
  have hkey : (g' * g * g'')⁻¹ * (Y' * g * Z') =
      ((g' * g * g'')⁻¹ * (g' * Y'⁻¹)⁻¹ * (g' * g * g'')) * (g''⁻¹ * Z') := by
    group
  have hy : g''⁻¹ * Z' ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ j) (-α) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg'') hZ'
  have hone := normalizer_eq_one_of_mul_opposite_torusHom j hS f hα0
    ⟨(g' * g * g'')⁻¹ * (Y' * g * Z'), Subgroup.mul_mem _ (Subgroup.inv_mem _ hN) hNprod⟩
    hconj hy hkey
  have hval : (g' * g * g'')⁻¹ * (g' * Y'⁻¹)⁻¹ * (g' * g * g'') * (g''⁻¹ * Z') = 1 := by
    rw [← hkey]
    simpa using congrArg Subtype.val hone
  have hx_eq := eq_inv_of_mul_eq_one_left hval
  have hx1 := RelativeRoot.eq_one_of_mem_subgroup_of_mem_opposite
    (CommGroupScheme.groupHom f ≫ j) hS hα0 hconj (hx_eq ▸ Subgroup.inv_mem _ hy)
  have hA1 : (g' * Y'⁻¹)⁻¹ = 1 := by
    have h2 : (g' * g * g'')⁻¹ * (g' * Y'⁻¹)⁻¹ = (g' * g * g'')⁻¹ * 1 := by
      rw [mul_one]
      exact mul_eq_one_iff_eq_inv.mp hx1
    exact mul_left_cancel h2
  have hgY : g' = Y' := mul_inv_eq_one.mp (inv_eq_one.mp hA1)
  -- the value of `g'` from its coordinates
  have hαneg : -α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ j) :=
    (mem_roots_comp_iff hT hS f j (-α)).mpr
      ⟨neg_ne_zero.mpr hα0, -(a ⟨0, hn⟩), (hneg _).1, (hneg _).2⟩
  have hhighneg : ∀ χ ∈ relativeRoots j, ∀ m : ℕ, 2 ≤ m → f ≫ χ ≠ m • (-α) := by
    intro χ hχ m hm h
    apply hhigh (-χ) (neg_mem_relativeRoots_of_isRootDatumOf j hP hχ) m hm
    rw [Preadditive.comp_neg, h, smul_neg, neg_neg]
  have hrangeneg : Set.range (fun l => -(a l)) =
      {χ | χ ∈ relativeRoots j ∧ f ≫ χ = -α} := by
    ext χ
    constructor
    · rintro ⟨l, rfl⟩
      exact hneg l
    · rintro ⟨hχ, hfχ⟩
      obtain ⟨l, hl⟩ : -χ ∈ Set.range a := by
        rw [hrange]
        exact ⟨neg_mem_relativeRoots_of_isRootDatumOf j hP hχ,
          by rw [Preadditive.comp_neg, hfχ, neg_neg]⟩
      exact ⟨l, by simp only [hl, neg_neg]⟩
  have hY'eq : Y' = RelativeRoot.rootPointsProduct j (fun l => -(a l)) (Over.mk (𝟙 _))
      (fun l => ⟨(p l).1, (hp l).1⟩) := rfl
  rw [hgY, hY'eq]
  exact torusRestrictedRootFunctionFamily_eq_of_coordinates hS hT hE hφ f hαneg hhighneg hn
    (fun l => -(a l)) (neg_injective.comp hinj) hrangeneg _ (-c) hY

end Opposite

section Galois

open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency.types false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (t : S ⟶ T) (jT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "S_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) S
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "j_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) jT
local notation "t_K" => CategoryTheory.Functor.map (CommGroupScheme.baseChange b) t
local notation "a_K" a => characterLattice.baseChange b S a

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

private instance extendedSmooth : Smooth (G_K).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable [Mono (CategoryTheory.Functor.map
    (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left]

/-- **Galois transport of fibre coordinates.** If the ordered product of root points over
the fibre of `a_K α` is the scalar extension of an original point, then a Galois
automorphism carries the coordinate at a root to the coordinate at the transported root. -/
theorem rationalConjugate_fiber_coordinate
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {α : characterLattice S} (hα : (a_K α) ≠ 0)
    (hhigh : ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ n : ℕ, 2 ≤ n → t_K ≫ χ ≠ n • (a_K α))
    {n : ℕ} (a : Fin n → characterLattice T_K) (hinj : Function.Injective a)
    (hrange : Set.range a = {χ | χ ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ χ = a_K α})
    (X : ∀ l, (RelativeRoot.subgroup (S := T_K) j_K (a l)).carrier (Over.mk (𝟙 _)))
    {g : rationalPoints G}
    (hX : RelativeRoot.rootPointsProduct (T := T_K) j_K a (Over.mk (𝟙 _)) X =
      rationalExtend k K G g)
    (σ : K ≃ₐ[k] K) {l m : Fin n}
    (hlm : characterLattice.galoisRepresentation k K T σ (a l) = a m) :
    rationalConjugate k K G σ (X l).val = (X m).val := by
  classical
  have hSK : IsSplitTorus (S_K).toGrp := hS.baseChange b
  have hfib : ∀ l, a l ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ a l = a_K α := fun l =>
    (show a l ∈ {χ | χ ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ χ = a_K α} from
      hrange ▸ Set.mem_range_self l)
  -- the Galois automorphism permutes the fibre
  have hσfib : ∀ l, characterLattice.galoisRepresentation k K T σ (a l) ∈ Set.range a := by
    intro l
    rw [hrange]
    refine ⟨(mem_roots_galois_iff k K jT σ (a l)).mpr (hfib l).1, ?_⟩
    rw [← characterLattice.galoisRepresentation_precompose, (hfib l).2,
      characterLattice.galoisRepresentation_baseChange]
  choose π hπ using hσfib
  have hπinj : Function.Injective π := by
    intro l₁ l₂ h
    apply hinj
    have h1 : characterLattice.galoisRepresentation k K T σ (a l₁) =
        characterLattice.galoisRepresentation k K T σ (a l₂) := by
      rw [← hπ, ← hπ, h]
    have h2 := congrArg (characterLattice.galoisRepresentation k K T σ⁻¹) h1
    rwa [Representation.inv_self_apply, Representation.inv_self_apply] at h2
  let e : Equiv.Perm (Fin n) := Equiv.ofBijective π (Finite.injective_iff_bijective.mp hπinj)
  have he : ∀ l, e l = π l := fun _ => rfl
  -- conjugated coordinates, reindexed along the fibre
  have hmemσ : ∀ l, rationalConjugate k K G σ (X l).val ∈
      (RelativeRoot.subgroup (S := T_K) j_K (a (π l))).carrier (Over.mk (𝟙 _)) := by
    intro l
    rw [hπ l]
    exact (RelativeRoot.rationalConjugate_mem_subgroup_iff k K jT σ (a l) (X l).val).mpr
      (X l).prop
  let Y : ∀ m, (RelativeRoot.subgroup (S := T_K) j_K (a m)).carrier (Over.mk (𝟙 _)) :=
    fun m => ⟨rationalConjugate k K G σ (X (e.symm m)).val, by
      have h := hmemσ (e.symm m)
      rwa [← he, e.apply_symm_apply] at h⟩
  -- distinct coordinates commute
  have hroot : ∀ l, a l ≠ 0 := fun l => (hfib l).1.1
  have hcommX : ∀ l₁ l₂, l₁ ≠ l₂ → Commute (X l₁).val (X l₂).val := by
    intro l₁ l₂ _
    exact commute_of_no_strict_root_combinations (T := T_K) j_K hT (a l₁) (a l₂) (hroot l₁)
      (hroot l₂)
      (noStrictRootCombinations_fiber_pos (S := S_K) (T := T_K) j_K hSK t_K hα hhigh
        (hfib l₁).2 (hfib l₂).2)
      (X l₁).prop (X l₂).prop
  have hpair : (List.ofFn fun m => rationalConjugate k K G σ (X (e.symm m)).val).Pairwise
      Commute := by
    rw [List.pairwise_ofFn]
    intro m₁ m₂ hm
    exact (hcommX _ _ (fun h => (ne_of_lt hm) (e.symm.injective h))).map
      (rationalConjugate k K G σ)
  have hY : RelativeRoot.rootPointsProduct (T := T_K) j_K a (Over.mk (𝟙 _)) Y =
      rationalExtend k K G g := by
    have hperm := Equiv.Perm.ofFn_comp_perm e.symm
      (fun l => rationalConjugate k K G σ (X l).val)
    have hprod : (List.ofFn fun m => rationalConjugate k K G σ (X (e.symm m)).val).prod =
        (List.ofFn fun l => rationalConjugate k K G σ (X l).val).prod := hperm.prod_eq' hpair
    change (List.ofFn fun m => rationalConjugate k K G σ (X (e.symm m)).val).prod = _
    rw [hprod, ← rationalConjugate_rationalExtend k K G σ g, ← hX]
    unfold RelativeRoot.rootPointsProduct
    rw [map_list_prod, List.map_ofFn]
    rfl
  -- uniqueness of coordinates
  have hrange' := hrange.trans
    (semigroupIndivisibleRoots_preimage_eq_fiber (S := S_K) (T := T_K) j_K hSK t_K (a_K α) hα
      hhigh).symm
  have hgmem : rationalExtend k K G g ∈
      (RelativeRoot.subgroup (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (a_K α)).carrier
        (Over.mk (𝟙 _)) := by
    rw [← hX]
    exact list_ofFn_prod_mem_rootGroupPoints_comp (S := S_K) (T := T_K) hSK hT hE t_K hα a hfib _
      (fun l => (X l).prop)
  obtain ⟨x, -, huniq⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct (S := S_K)
      (T := T_K)
      hSK hT t_K j_K hE (a_K α) hα a hinj hrange' (Over.mk (𝟙 _))
      (rationalExtend k K G g)).mp hgmem
  have hYX : Y = X := (huniq Y hY).trans (huniq X hX).symm
  have hπl : π l = m := hinj ((hπ l).trans hlm)
  have h : rationalConjugate k K G σ (X (e.symm m)).val = (X m).val :=
    congrArg (fun F => (F m).val) hYX
  have hsymm : e.symm m = l := by
    rw [← hπl, ← he]
    exact e.symm_apply_apply l
  rw [hsymm] at h
  exact h

/-- Galois-fixed upper families take equal values on Galois-transported fibre coordinates. -/
theorem fiber_coordinate_value_eq_of_galois
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ : RootFunctionFamily T_K G_K}
    (hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    {α : characterLattice S} (hα : (a_K α) ≠ 0)
    (hhigh : ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ n : ℕ, 2 ≤ n → t_K ≫ χ ≠ n • (a_K α))
    {n : ℕ} (a : Fin n → characterLattice T_K) (hinj : Function.Injective a)
    (hrange : Set.range a = {χ | χ ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ χ = a_K α})
    (X : ∀ l, (RelativeRoot.subgroup (S := T_K) j_K (a l)).carrier (Over.mk (𝟙 _)))
    {g : rationalPoints G}
    (hX : RelativeRoot.rootPointsProduct (T := T_K) j_K a (Over.mk (𝟙 _)) X =
      rationalExtend k K G g)
    (σ : K ≃ₐ[k] K) {l m : Fin n}
    (hlm : characterLattice.galoisRepresentation k K T σ (a l) = a m) :
    φ (a m) (X m).val = φ (a l) (X l).val := by
  have hc := rationalConjugate_fiber_coordinate t jT hS hT hE hα hhigh a hinj hrange X hX σ hlm
  calc φ (a m) (X m).val
      = φ (characterLattice.galoisRepresentation k K T σ (a l))
          (rationalConjugate k K G σ (X l).val) := by rw [hc, hlm]
    _ = RootFunctionFamily.galoisAction k K T G σ φ
          (characterLattice.galoisRepresentation k K T σ (a l))
          (rationalConjugate k K G σ (X l).val) := by rw [hfix σ]
    _ = φ (a l) (X l).val :=
      RootFunctionFamily.galoisAction_apply_conjugate k K T G σ φ (a l) (X l).val

omit [IsAffineHom G.X.hom] [Smooth G.X.hom]
  [Mono (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) jT).hom.hom.left]
  in
private theorem rationalExtend_injective_of_affineHom [IsAffineHom G.X.hom] :
    Function.Injective (rationalExtend k K G) := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro x y h
  apply (rationalCoeffEquiv k G).injective
  apply GaloisPoint.extend_injective k K G
  simpa only [baseChangeCoeffEquiv_rationalExtend] using
    congrArg (baseChangeCoeffEquiv k K G) h

/-- **The opposite-pair axiom for non-multipliable roots.** Let `S ⊆ T` be split over `k`,
with `T_K` split over a Galois extension `K`, and let `φ` be a Galois-fixed root datum
valuation of `T_K`. If the roots of `T_K` restricting to one relative root form a single
Galois orbit, none restricts to zero, and the original normalizer of `S` normalizes `T`,
then the torus-then-field restriction of `φ` satisfies axiom V 5 at every relative root
`a` whose double is not a root. -/
theorem torusFieldRestrictedRootFunctionFamily_opposite_of_two_not_mem
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    [Mono (CommGroupScheme.groupHom t_K ≫ j_K).hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus (T_K).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs (T := T_K) j_K)
    {φ : RootFunctionFamily T_K G_K} (hφ : IsRootDatumValuation (S := T_K) j_K φ)
    (hfix : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    (hfactor : CommGroupScheme.groupHom t_K ≫ j_K =
      CategoryTheory.Functor.map (GroupScheme.baseChange b) i)
    {J : Type*} [Finite J] {P : RootDatum J (characterLattice T_K) (cocharacterLattice T_K)}
    (hP : IsRootDatumOf (T := T_K) j_K P)
    (hzero : ∀ ψ ∈ relativeRoots (T := T_K) j_K, t_K ≫ ψ ≠ 0)
    (hnorm : ∀ n : normalizerPoints i, n.val ∈ normalizerPoints jT)
    (hEbase : RelativeRoot.HasOppositeFactorPairs i)
    {a : characterLattice S} (ha : a ∈ relativeRoots i) (h2a : (2 : ℤ) • a ∉ relativeRoots i)
    (horbit : ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ ψ ∈ relativeRoots (T := T_K) j_K,
      t_K ≫ χ = (a_K a) → t_K ≫ ψ = (a_K a) →
        ∃ σ : K ≃ₐ[k] K, characterLattice.galoisRepresentation k K T σ χ = ψ)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i a) (hg1 : g ≠ 1)
    {g' g'' : rationalPoints G} (hg' : g' ∈ rootGroupPoints i (-a))
    (hg'' : g'' ∈ rootGroupPoints i (-a)) (hN : g' * g * g'' ∈ normalizerPoints i) :
    torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE hφ t_K
        (-a) g' +
      torusFieldRestrictedRootFunctionFamily (G := G) (T := T_K) (j := j_K) hS hT hE hφ t_K
        a g = 0 := by
  classical
  have hSK : IsSplitTorus (S_K).toGrp := hS.baseChange b
  have haK : (a_K a) ∈ relativeRoots (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) := by
    rw [hfactor]
    exact (mem_roots_baseChange_iff (K := K) G S hS i a).mpr ha
  have hαK : (a_K a) ≠ 0 := haK.1
  -- no root of `T_K` restricts to a higher multiple of `a`
  have hnohigh := hEbase.hasNoHigherRoots_of_two_not_mem i hS h2a
  have hhigh : ∀ χ ∈ relativeRoots (T := T_K) j_K, ∀ n : ℕ, 2 ≤ n →
      t_K ≫ χ ≠ n • (a_K a) := by
    intro χ hχ n hn h
    apply hnohigh n hn
    have hmem : n • (a_K a) ∈ roots (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) :=
      (mem_roots_comp_iff (T := T_K) (T' := S_K) hT hSK t_K j_K _).mpr
        ⟨hSK.nsmul_ne_zero hαK (by omega), χ, hχ, h⟩
    rw [hfactor, ← map_nsmul] at hmem
    exact (mem_roots_baseChange_iff (K := K) G S hS i (n • a)).mp hmem
  -- enumerate the fibre of `a`
  have hFfin : {χ | χ ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ χ = a_K a}.Finite := by
    apply (Set.finite_range P.root).subset
    intro χ hχ
    rw [hP.2.1]
    exact hχ.1
  obtain ⟨n, e, he⟩ := hFfin.fin_embedding
  have hfib : ∀ l, e l ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ e l = a_K a := fun l =>
    (show e l ∈ {χ | χ ∈ relativeRoots (T := T_K) j_K ∧ t_K ≫ χ = a_K a} from
      he ▸ Set.mem_range_self l)
  -- coordinates of the scalar extension of `g`
  have hgK : rationalExtend k K G g ∈
      (RelativeRoot.subgroup (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (a_K a)).carrier
        (Over.mk (𝟙 _)) := by
    rw [hfactor]
    exact rationalExtend_mem_rootGroupPoints (K := K) i a hg
  have hrange' := he.trans
    (semigroupIndivisibleRoots_preimage_eq_fiber (S := S_K) (T := T_K) j_K hSK t_K (a_K a) hαK
      hhigh).symm
  obtain ⟨X, hX, -⟩ :=
    (RelativeRoot.mem_subgroup_comp_torusHom_iff_existsUnique_rootPointsProduct (S := S_K)
      (T := T_K) hSK hT t_K j_K hE (a_K a) hαK e e.injective hrange' (Over.mk (𝟙 _))
      (rationalExtend k K G g)).mp hgK
  -- some coordinate is nontrivial, and all coordinates have one common value
  have hex : ∃ l, (X l).val ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hg1
    apply rationalExtend_injective_of_affineHom (K := K)
    rw [map_one, ← hX]
    simp [RelativeRoot.rootPointsProduct, hall]
  obtain ⟨l₀, hl₀⟩ := hex
  obtain ⟨c, hc₀⟩ : ∃ c : ℝ, φ (e l₀) (X l₀).val = c := by
    have hne : φ (e l₀) (X l₀).val ≠ ⊤ := fun htop =>
      hl₀ ((hφ.eq_top_iff (e l₀) (hfib l₀).1 (X l₀).val (X l₀).prop).mp htop)
    obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hne
    exact ⟨c, hc.symm⟩
  have hc : ∀ l, φ (e l) (X l).val = c := by
    intro l
    obtain ⟨σ, hσ⟩ := horbit _ (hfib l₀).1 _ (hfib l).1 (hfib l₀).2 (hfib l).2
    rw [fiber_coordinate_value_eq_of_galois t jT hS hT hE hfix hαK hhigh e e.injective he X
      hX σ hσ, hc₀]
  -- scalar extensions of the opposite points and of the normalizer
  have hg'K : rationalExtend k K G g' ∈
      rootGroupPoints (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (-(a_K a)) := by
    rw [hfactor, ← map_neg]
    exact rationalExtend_mem_rootGroupPoints (K := K) i (-a) hg'
  have hg''K : rationalExtend k K G g'' ∈
      rootGroupPoints (S := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) (-(a_K a)) := by
    rw [hfactor, ← map_neg]
    exact rationalExtend_mem_rootGroupPoints (K := K) i (-a) hg''
  have hNK : rationalExtend k K G g' *
      RelativeRoot.rootPointsProduct (T := T_K) j_K e (Over.mk (𝟙 _)) X *
        rationalExtend k K G g'' ∈ normalizerPoints (T := T_K) j_K := by
    rw [hX, ← map_mul, ← map_mul]
    exact (normalizerPointsFieldExtend (K := K) jT ⟨_, hnorm ⟨_, hN⟩⟩).prop
  have hN'K : rationalExtend k K G g' *
      RelativeRoot.rootPointsProduct (T := T_K) j_K e (Over.mk (𝟙 _)) X *
        rationalExtend k K G g'' ∈
          normalizerPoints (T := S_K) (CommGroupScheme.groupHom t_K ≫ j_K) := by
    rw [hX, ← map_mul, ← map_mul, hfactor]
    exact (normalizerPointsFieldExtend (K := K) i ⟨_, hN⟩).prop
  have hneg := torusRestrictedRootFunctionFamily_neg_eq_of_fiber (S := S_K) (T := T_K)
    hSK hT hE hφ t_K hP haK hzero hhigh e e.injective he X c hc hg'K hg''K hNK hN'K
  have hpos := torusRestrictedRootFunctionFamily_eq_of_coordinates (S := S_K) (T := T_K)
    hSK hT hE hφ t_K haK hhigh l₀.pos e e.injective he X c hc
  rw [hX] at hpos
  simp only [torusFieldRestrictedRootFunctionFamily, RootFunctionFamily.fieldRestrict_apply,
    map_neg]
  rw [hneg, hpos, ← WithTop.coe_add, neg_add_cancel, WithTop.coe_zero]

end Galois

end Langlands.Geometry.Building
