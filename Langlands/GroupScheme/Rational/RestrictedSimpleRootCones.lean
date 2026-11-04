import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.Geometry.Building.RealTorusDuality
import Mathlib.Geometry.Convex.Cone.Pointed

/-! # Actual restricted simple roots and their positive root-combination cones -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped Finset

namespace Langlands.GroupScheme

/-! ### Positive and nonnegative combinations of a finite set of vectors -/

namespace RootCombination

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

/-- All sums over the whole finite set `S`, each vector of `S` occurring once, with
every real coefficient strictly positive. -/
def positive (S : Set M) (hS : S.Finite) : Set M :=
  {x | ∃ c : M → ℝ, (∀ y ∈ S, 0 < c y) ∧ ∑ y ∈ hS.toFinset, c y • y = x}

/-- All sums over the whole finite set `S`, each vector of `S` occurring once, with
every real coefficient nonnegative. -/
def nonneg (S : Set M) (hS : S.Finite) : Set M :=
  {x | ∃ c : M → ℝ, (∀ y ∈ S, 0 ≤ c y) ∧ ∑ y ∈ hS.toFinset, c y • y = x}

variable {S : Set M} (hS : S.Finite) {x y : M}

theorem mem_positive :
    x ∈ positive S hS ↔ ∃ c : M → ℝ, (∀ y ∈ S, 0 < c y) ∧ ∑ y ∈ hS.toFinset, c y • y = x :=
  Iff.rfl

theorem mem_nonneg :
    x ∈ nonneg S hS ↔ ∃ c : M → ℝ, (∀ y ∈ S, 0 ≤ c y) ∧ ∑ y ∈ hS.toFinset, c y • y = x :=
  Iff.rfl

/-- Fiberwise reindexing: coefficients on the distinct vectors of `S` and coefficients on
any finite family enumerating `S`, possibly with repetitions, give the same sums. The
coefficient condition is only required to be stable under sums and under division by a
positive integer. -/
private theorem exists_iff_exists_family {ι : Type*} (P : ℝ → Prop)
    (hadd : ∀ a b, P a → P b → P (a + b)) (hdiv : ∀ a (n : ℕ), 0 < n → P a → P (a / n))
    (s : Finset ι) (v : ι → M) (hv : v '' ↑s = S) (x : M) :
    (∃ c : M → ℝ, (∀ y ∈ S, P (c y)) ∧ ∑ y ∈ hS.toFinset, c y • y = x) ↔
      ∃ d : ι → ℝ, (∀ i ∈ s, P (d i)) ∧ ∑ i ∈ s, d i • v i = x := by
  classical
  have ht : hS.toFinset = s.image v := by
    apply Finset.coe_injective
    rw [Set.Finite.coe_toFinset, Finset.coe_image, hv]
  have hmaps : ∀ i ∈ s, v i ∈ s.image v := fun i hi => Finset.mem_image_of_mem v hi
  have hfiber : ∀ i ∈ s, 0 < #{j ∈ s | v j = v i} := fun i hi =>
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  rw [ht]
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c (v i) / (#{j ∈ s | v j = v i} : ℕ), fun i hi =>
      hdiv _ _ (hfiber i hi) (hc _ (hv ▸ ⟨i, hi, rfl⟩)), ?_⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun y hy => ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    have hn : ((#{j ∈ s | v j = v i} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (hfiber i hi).ne'
    calc ∑ j ∈ s with v j = v i, (c (v j) / (#{l ∈ s | v l = v j} : ℕ)) • v j
        = ∑ j ∈ s with v j = v i, (c (v i) / (#{l ∈ s | v l = v i} : ℕ)) • v i :=
          Finset.sum_congr rfl fun j hj => by rw [(Finset.mem_filter.mp hj).2]
      _ = c (v i) • v i := by
          rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_div_cancel₀ _ hn]
  · rintro ⟨d, hd, rfl⟩
    refine ⟨fun y => ∑ i ∈ s with v i = y, d i, fun y hy => ?_, ?_⟩
    · rw [← hv] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact Finset.sum_induction_nonempty _ P hadd ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
        fun j hj => hd j (Finset.mem_filter.mp hj).1
    · rw [← Finset.sum_fiberwise_of_maps_to hmaps]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.sum_smul]
      exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]

/-- Strictly positive combinations of any finite family `v` enumerating `S` over `s`,
repetitions allowed, form exactly the strictly positive cone of `S`. -/
theorem mem_positive_iff_family {ι : Type*} (s : Finset ι) (v : ι → M) (hv : v '' ↑s = S) :
    x ∈ positive S hS ↔ ∃ d : ι → ℝ, (∀ i ∈ s, 0 < d i) ∧ ∑ i ∈ s, d i • v i = x :=
  exists_iff_exists_family hS (0 < ·) (fun _ _ => add_pos)
    (fun _ _ hn ha => div_pos ha (Nat.cast_pos.mpr hn)) s v hv x

/-- Nonnegative combinations of any finite family `v` enumerating `S` over `s`,
repetitions allowed, form exactly the nonnegative cone of `S`. -/
theorem mem_nonneg_iff_family {ι : Type*} (s : Finset ι) (v : ι → M) (hv : v '' ↑s = S) :
    x ∈ nonneg S hS ↔ ∃ d : ι → ℝ, (∀ i ∈ s, 0 ≤ d i) ∧ ∑ i ∈ s, d i • v i = x :=
  exists_iff_exists_family hS (0 ≤ ·) (fun _ _ => add_nonneg)
    (fun _ _ _ ha => div_nonneg ha (Nat.cast_nonneg _)) s v hv x

/-- Every finite index type enumerating `S` describes the same strictly positive cone. -/
theorem mem_positive_iff_fintype {ι : Type*} [Fintype ι] (v : ι → M) (hv : Set.range v = S) :
    x ∈ positive S hS ↔ ∃ d : ι → ℝ, (∀ i, 0 < d i) ∧ ∑ i, d i • v i = x := by
  rw [mem_positive_iff_family hS Finset.univ v (by rw [Finset.coe_univ, Set.image_univ, hv])]
  simp only [Finset.mem_univ, true_implies]

/-- Every finite index type enumerating `S` describes the same nonnegative cone. -/
theorem mem_nonneg_iff_fintype {ι : Type*} [Fintype ι] (v : ι → M) (hv : Set.range v = S) :
    x ∈ nonneg S hS ↔ ∃ d : ι → ℝ, (∀ i, 0 ≤ d i) ∧ ∑ i, d i • v i = x := by
  rw [mem_nonneg_iff_family hS Finset.univ v (by rw [Finset.coe_univ, Set.image_univ, hv])]
  simp only [Finset.mem_univ, true_implies]

/-- Any finset with underlying set `S` computes the strictly positive cone. -/
theorem mem_positive_iff_finset (t : Finset M) (ht : ↑t = S) :
    x ∈ positive S hS ↔ ∃ c : M → ℝ, (∀ y ∈ t, 0 < c y) ∧ ∑ y ∈ t, c y • y = x :=
  mem_positive_iff_family hS t id (by rw [Set.image_id, ht])

/-- Any finset with underlying set `S` computes the nonnegative cone. -/
theorem mem_nonneg_iff_finset (t : Finset M) (ht : ↑t = S) :
    x ∈ nonneg S hS ↔ ∃ c : M → ℝ, (∀ y ∈ t, 0 ≤ c y) ∧ ∑ y ∈ t, c y • y = x :=
  mem_nonneg_iff_family hS t id (by rw [Set.image_id, ht])

/-- The strictly positive cone as an enumeration-free finite sum over `S`. -/
theorem mem_positive_iff_finsum :
    x ∈ positive S hS ↔ ∃ c : M → ℝ, (∀ y ∈ S, 0 < c y) ∧ ∑ᶠ y ∈ S, c y • y = x := by
  simp only [mem_positive, finsum_mem_eq_finite_toFinset_sum _ hS]

/-- The nonnegative cone as an enumeration-free finite sum over `S`. -/
theorem mem_nonneg_iff_finsum :
    x ∈ nonneg S hS ↔ ∃ c : M → ℝ, (∀ y ∈ S, 0 ≤ c y) ∧ ∑ᶠ y ∈ S, c y • y = x := by
  simp only [mem_nonneg, finsum_mem_eq_finite_toFinset_sum _ hS]

/-- Strictly positive combinations are nonnegative combinations. -/
theorem positive_subset_nonneg : positive S hS ⊆ nonneg S hS := by
  rintro x ⟨c, hc, rfl⟩
  exact ⟨c, fun y hy => (hc y hy).le, rfl⟩

theorem zero_mem_nonneg : (0 : M) ∈ nonneg S hS :=
  ⟨0, fun _ _ => le_rfl, by simp⟩

theorem add_mem_nonneg (hx : x ∈ nonneg S hS) (hy : y ∈ nonneg S hS) :
    x + y ∈ nonneg S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  refine ⟨c + d, fun z hz => add_nonneg (hc z hz) (hd z hz), ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem smul_mem_nonneg {r : ℝ} (hr : 0 ≤ r) (hx : x ∈ nonneg S hS) :
    r • x ∈ nonneg S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨r • c, fun z hz => mul_nonneg hr (hc z hz), ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

theorem add_mem_positive (hx : x ∈ positive S hS) (hy : y ∈ positive S hS) :
    x + y ∈ positive S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  refine ⟨c + d, fun z hz => add_pos (hc z hz) (hd z hz), ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

/-- Adding a nonnegative combination to a strictly positive one stays strictly positive. -/
theorem add_mem_positive_of_mem_nonneg (hx : x ∈ positive S hS) (hy : y ∈ nonneg S hS) :
    x + y ∈ positive S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  refine ⟨c + d, fun z hz => add_pos_of_pos_of_nonneg (hc z hz) (hd z hz), ?_⟩
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem smul_mem_positive {r : ℝ} (hr : 0 < r) (hx : x ∈ positive S hS) :
    r • x ∈ positive S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨r • c, fun z hz => mul_pos hr (hc z hz), ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

/-- Every vector of `S` is a nonnegative combination. -/
theorem subset_nonneg : S ⊆ nonneg S hS := by
  classical
  intro y hy
  refine ⟨fun z => if z = y then 1 else 0, fun z _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Set.Finite.mem_toFinset, hy,
    ite_true]

/-- For the empty index set, the strictly positive cone is `{0}`. -/
theorem positive_empty (h : (∅ : Set M).Finite) : positive ∅ h = {0} := by
  ext x
  simp only [mem_positive, Set.Finite.toFinset_empty, Finset.sum_empty, Set.mem_empty_iff_false,
    false_implies, implies_true, true_and, exists_const, Set.mem_singleton_iff, eq_comm]

/-- For the empty index set, the nonnegative cone is `{0}`. -/
theorem nonneg_empty (h : (∅ : Set M).Finite) : nonneg ∅ h = {0} := by
  ext x
  simp only [mem_nonneg, Set.Finite.toFinset_empty, Finset.sum_empty, Set.mem_empty_iff_false,
    false_implies, implies_true, true_and, exists_const, Set.mem_singleton_iff, eq_comm]

/-- A linear map carries the strictly positive cone of `S` onto that of its image. No
injectivity is needed: coefficients of vectors with equal images are added. -/
theorem image_positive (L : M →ₗ[ℝ] N) :
    L '' positive S hS = positive (L '' S) (hS.image L) := by
  ext x
  rw [mem_positive_iff_family (hS.image L) hS.toFinset L (by rw [hS.coe_toFinset])]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, fun y hy => hc y (hS.mem_toFinset.mp hy), by simp only [map_sum, map_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, fun y hy => hc y (hS.mem_toFinset.mpr hy), rfl⟩,
      by simp only [map_sum, map_smul]⟩

/-- A linear map carries the nonnegative cone of `S` onto that of its image. -/
theorem image_nonneg (L : M →ₗ[ℝ] N) :
    L '' nonneg S hS = nonneg (L '' S) (hS.image L) := by
  ext x
  rw [mem_nonneg_iff_family (hS.image L) hS.toFinset L (by rw [hS.coe_toFinset])]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, fun y hy => hc y (hS.mem_toFinset.mp hy), by simp only [map_sum, map_smul]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, fun y hy => hc y (hS.mem_toFinset.mpr hy), rfl⟩,
      by simp only [map_sum, map_smul]⟩

/-- The strictly positive cone, bundled as a convex cone in Mathlib's sense. -/
def positiveCone : ConvexCone ℝ M where
  carrier := positive S hS
  smul_mem' _ hr _ hx := smul_mem_positive hS hr hx
  add_mem' _ hx _ hy := add_mem_positive hS hx hy

@[simp] theorem coe_positiveCone : (positiveCone hS : Set M) = positive S hS := rfl

/-- The nonnegative cone, bundled as a pointed cone in Mathlib's sense. -/
def nonnegCone : PointedCone ℝ M where
  carrier := nonneg S hS
  zero_mem' := zero_mem_nonneg hS
  add_mem' hx hy := add_mem_nonneg hS hx hy
  smul_mem' r _ hx := smul_mem_nonneg hS r.2 hx

@[simp] theorem coe_nonnegCone : (nonnegCone hS : Set M) = nonneg S hS := rfl

/-- The nonnegative cone is Mathlib's cone hull of `S`. -/
theorem nonnegCone_eq_hull : nonnegCone hS = PointedCone.hull ℝ S := by
  apply le_antisymm
  · rintro _ ⟨c, hc, rfl⟩
    exact Submodule.sum_mem _ fun y hy =>
      PointedCone.smul_mem _ (hc y (hS.mem_toFinset.mp hy))
        (PointedCone.subset_hull (hS.mem_toFinset.mp hy))
  · exact Submodule.span_le.mpr (subset_nonneg hS)

end RootCombination

/-! ### Restricted simple roots -/

variable {k : Type u} [Field k]
  {A A' T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

open RealTorusSpace

/-- The restriction along `f : A ⟶ T` of an actual character of `T`, as the image of
`1 ⊗ α` under the existing real character restriction. -/
def restrictedRootVector (f : A ⟶ T) (α : characterLattice T) : Vstar A :=
  rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ((1 : ℝ) ⊗ₜ[ℤ] α)

theorem restrictedRootVector_eq_tmul (f : A ⟶ T) (α : characterLattice T) :
    restrictedRootVector f α = (1 : ℝ) ⊗ₜ[ℤ] (f ≫ α) := rfl

/-- Evaluating a restricted root on a real cocharacter of `A` evaluates the original
character on its image in the real cocharacter space of `T`. -/
theorem pair_restrictedRootVector (f : A ⟶ T) (α : characterLattice T) (v : V A) :
    pair A (restrictedRootVector f α) v = eval T α (cocharacterMapReal f v) := by
  rw [restrictedRootVector, ← pair_cocharacterMapReal, eval_eq_pair]

/-- Restriction is compatible with composition: pulling back a restriction along
`g : A ⟶ A'` restricts along `g ≫ f'`. -/
theorem rationalCharacterRestrictReal_restrictedRootVector {f : A ⟶ T} (g : A ⟶ A')
    {f' : A' ⟶ T} (hg : g ≫ f' = f) (α : characterLattice T) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) (restrictedRootVector f' α) =
      restrictedRootVector f α := by
  subst hg
  rw [restrictedRootVector_eq_tmul, restrictedRootVector_eq_tmul,
    rationalCharacterRestrictReal_tmul]
  rfl

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (J : Set (characterLattice T)) (f : A ⟶ T)

/-- The restrictions along `f` of the actual simple roots outside `J`: the source's
`Δ(P) = {α|_{𝔞_M} | α ∈ Δ_∅ \ Δ_∅^M}`, as a set of distinct real characters of `A`. -/
def restrictedSimpleRoots : Set (Vstar A) :=
  restrictedRootVector f '' (simpleRelativeRoots i ν \ J)

theorem mem_restrictedSimpleRoots {x : Vstar A} :
    x ∈ restrictedSimpleRoots i ν J f ↔
      ∃ α ∈ simpleRelativeRoots i ν, α ∉ J ∧ restrictedRootVector f α = x := by
  simp only [restrictedSimpleRoots, Set.mem_image, Set.mem_sdiff, and_assoc]

theorem restrictedRootVector_mem_restrictedSimpleRoots {α : characterLattice T}
    (hα : α ∈ simpleRelativeRoots i ν) (hJ : α ∉ J) :
    restrictedRootVector f α ∈ restrictedSimpleRoots i ν J f :=
  ⟨α, ⟨hα, hJ⟩, rfl⟩

/-- Finitely many actual simple roots have finitely many restrictions. -/
theorem finite_restrictedSimpleRoots (hfin : (simpleRelativeRoots i ν).Finite) :
    (restrictedSimpleRoots i ν J f).Finite :=
  (hfin.sdiff).image _

/-- The empty index set occurs exactly when `J` contains every actual simple root. -/
theorem restrictedSimpleRoots_eq_empty_iff :
    restrictedSimpleRoots i ν J f = ∅ ↔ simpleRelativeRoots i ν ⊆ J := by
  rw [restrictedSimpleRoots, Set.image_eq_empty, Set.sdiff_eq_empty]

/-- The restricted integral characters `f ≫ α` of the simple roots outside `J`. -/
def restrictedSimpleCharacters : Set (characterLattice A) :=
  (fun α : characterLattice T => f ≫ α) '' (simpleRelativeRoots i ν \ J)

/-- The restricted real roots are the images `1 ⊗ χ` of the restricted integral
characters. -/
theorem restrictedSimpleRoots_eq_image_restrictedSimpleCharacters :
    restrictedSimpleRoots i ν J f =
      (fun χ : characterLattice A => (1 : ℝ) ⊗ₜ[ℤ] χ) '' restrictedSimpleCharacters i ν J f := by
  rw [restrictedSimpleCharacters, Set.image_image]
  rfl

/-- Pulling back along `g` carries the restricted roots for `f'` exactly onto those for
`g ≫ f'`. -/
theorem image_restrictedSimpleRoots {f : A ⟶ T} (g : A ⟶ A') {f' : A' ⟶ T}
    (hg : g ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) '' restrictedSimpleRoots i ν J f' =
      restrictedSimpleRoots i ν J f := by
  rw [restrictedSimpleRoots, restrictedSimpleRoots, Set.image_image]
  exact Set.image_congr fun α _ => rationalCharacterRestrictReal_restrictedRootVector g hg α

/-! ### The root-positive cones -/

/-- The strictly positive root cone `+[𝔞*]_P^G`: sums over all restricted simple roots
with strictly positive real coefficients. -/
def restrictedRootPositiveCone (hfin : (simpleRelativeRoots i ν).Finite) : Set (Vstar A) :=
  RootCombination.positive (restrictedSimpleRoots i ν J f)
    (finite_restrictedSimpleRoots i ν J f hfin)

/-- The nonnegative root cone, the closure-type cone of V.3.15: sums over all restricted
simple roots with nonnegative real coefficients. -/
def restrictedRootNonnegCone (hfin : (simpleRelativeRoots i ν).Finite) : Set (Vstar A) :=
  RootCombination.nonneg (restrictedSimpleRoots i ν J f)
    (finite_restrictedSimpleRoots i ν J f hfin)

variable (hfin : (simpleRelativeRoots i ν).Finite) {x y : Vstar A}

theorem mem_restrictedRootPositiveCone :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ z ∈ restrictedSimpleRoots i ν J f, 0 < c z) ∧
        ∑ᶠ z ∈ restrictedSimpleRoots i ν J f, c z • z = x :=
  RootCombination.mem_positive_iff_finsum _

theorem mem_restrictedRootNonnegCone :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ z ∈ restrictedSimpleRoots i ν J f, 0 ≤ c z) ∧
        ∑ᶠ z ∈ restrictedSimpleRoots i ν J f, c z • z = x :=
  RootCombination.mem_nonneg_iff_finsum _

/-- Membership through any finset listing the distinct restricted roots. -/
theorem mem_restrictedRootPositiveCone_iff_finset (t : Finset (Vstar A))
    (ht : ↑t = restrictedSimpleRoots i ν J f) :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ z ∈ t, 0 < c z) ∧ ∑ z ∈ t, c z • z = x :=
  RootCombination.mem_positive_iff_finset _ t ht

/-- Membership through any finset listing the distinct restricted roots. -/
theorem mem_restrictedRootNonnegCone_iff_finset (t : Finset (Vstar A))
    (ht : ↑t = restrictedSimpleRoots i ν J f) :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ z ∈ t, 0 ≤ c z) ∧ ∑ z ∈ t, c z • z = x :=
  RootCombination.mem_nonneg_iff_finset _ t ht

/-- Equivalently, index by the actual simple roots outside `J`, with one strictly positive
coefficient for each root even when two roots have the same restriction. -/
theorem mem_restrictedRootPositiveCone_iff_roots (s : Finset (characterLattice T))
    (hs : ↑s = simpleRelativeRoots i ν \ J) :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : characterLattice T → ℝ, (∀ α ∈ s, 0 < c α) ∧
        ∑ α ∈ s, c α • restrictedRootVector f α = x :=
  RootCombination.mem_positive_iff_family _ s (restrictedRootVector f) (by rw [hs]; rfl)

/-- Equivalently, index by the actual simple roots outside `J`, with one nonnegative
coefficient for each root. -/
theorem mem_restrictedRootNonnegCone_iff_roots (s : Finset (characterLattice T))
    (hs : ↑s = simpleRelativeRoots i ν \ J) :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : characterLattice T → ℝ, (∀ α ∈ s, 0 ≤ c α) ∧
        ∑ α ∈ s, c α • restrictedRootVector f α = x :=
  RootCombination.mem_nonneg_iff_family _ s (restrictedRootVector f) (by rw [hs]; rfl)

theorem restrictedRootPositiveCone_subset_nonnegCone :
    restrictedRootPositiveCone i ν J f hfin ⊆ restrictedRootNonnegCone i ν J f hfin :=
  RootCombination.positive_subset_nonneg _

theorem zero_mem_restrictedRootNonnegCone :
    (0 : Vstar A) ∈ restrictedRootNonnegCone i ν J f hfin :=
  RootCombination.zero_mem_nonneg _

theorem add_mem_restrictedRootNonnegCone (hx : x ∈ restrictedRootNonnegCone i ν J f hfin)
    (hy : y ∈ restrictedRootNonnegCone i ν J f hfin) :
    x + y ∈ restrictedRootNonnegCone i ν J f hfin :=
  RootCombination.add_mem_nonneg _ hx hy

theorem smul_mem_restrictedRootNonnegCone {r : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ restrictedRootNonnegCone i ν J f hfin) :
    r • x ∈ restrictedRootNonnegCone i ν J f hfin :=
  RootCombination.smul_mem_nonneg _ hr hx

theorem add_mem_restrictedRootPositiveCone (hx : x ∈ restrictedRootPositiveCone i ν J f hfin)
    (hy : y ∈ restrictedRootPositiveCone i ν J f hfin) :
    x + y ∈ restrictedRootPositiveCone i ν J f hfin :=
  RootCombination.add_mem_positive _ hx hy

theorem smul_mem_restrictedRootPositiveCone {r : ℝ} (hr : 0 < r)
    (hx : x ∈ restrictedRootPositiveCone i ν J f hfin) :
    r • x ∈ restrictedRootPositiveCone i ν J f hfin :=
  RootCombination.smul_mem_positive _ hr hx

theorem restrictedSimpleRoots_subset_nonnegCone :
    restrictedSimpleRoots i ν J f ⊆ restrictedRootNonnegCone i ν J f hfin :=
  RootCombination.subset_nonneg _

/-- The nonnegative root cone is the cone hull of the restricted simple roots. -/
theorem restrictedRootNonnegCone_eq_hull :
    restrictedRootNonnegCone i ν J f hfin =
      (PointedCone.hull ℝ (restrictedSimpleRoots i ν J f) : Set (Vstar A)) := by
  rw [← RootCombination.nonnegCone_eq_hull (finite_restrictedSimpleRoots i ν J f hfin)]
  rfl

/-- If `J` contains every actual simple root, the strictly positive root cone is `{0}`. -/
theorem restrictedRootPositiveCone_of_subset (hJ : simpleRelativeRoots i ν ⊆ J) :
    restrictedRootPositiveCone i ν J f hfin = {0} := by
  have h := (restrictedSimpleRoots_eq_empty_iff i ν J f).mpr hJ
  unfold restrictedRootPositiveCone
  generalize finite_restrictedSimpleRoots i ν J f hfin = hS
  revert hS
  rw [h]
  exact RootCombination.positive_empty

/-- If `J` contains every actual simple root, the nonnegative root cone is `{0}`. -/
theorem restrictedRootNonnegCone_of_subset (hJ : simpleRelativeRoots i ν ⊆ J) :
    restrictedRootNonnegCone i ν J f hfin = {0} := by
  have h := (restrictedSimpleRoots_eq_empty_iff i ν J f).mpr hJ
  unfold restrictedRootNonnegCone
  generalize finite_restrictedSimpleRoots i ν J f hfin = hS
  revert hS
  rw [h]
  exact RootCombination.nonneg_empty

/-! ### Naturality under change of the split-component presentation -/

/-- Pulling back along `g` carries the strictly positive root cone for `f'` exactly onto
the strictly positive root cone for `g ≫ f'`. -/
theorem image_restrictedRootPositiveCone {f : A ⟶ T} (g : A ⟶ A') {f' : A' ⟶ T}
    (hg : g ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) ''
        restrictedRootPositiveCone i ν J f' hfin =
      restrictedRootPositiveCone i ν J f hfin := by
  unfold restrictedRootPositiveCone
  rw [RootCombination.image_positive]
  congr 1
  exact image_restrictedSimpleRoots i ν J g hg

/-- Pulling back along `g` carries the nonnegative root cone for `f'` exactly onto the
nonnegative root cone for `g ≫ f'`. -/
theorem image_restrictedRootNonnegCone {f : A ⟶ T} (g : A ⟶ A') {f' : A' ⟶ T}
    (hg : g ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) ''
        restrictedRootNonnegCone i ν J f' hfin =
      restrictedRootNonnegCone i ν J f hfin := by
  unfold restrictedRootNonnegCone
  rw [RootCombination.image_nonneg]
  congr 1
  exact image_restrictedSimpleRoots i ν J g hg

section Iso

variable {f : A ⟶ T} (e : A ≅ A') {f' : A' ⟶ T} (he : e.hom ≫ f' = f)
include he

theorem iso_inv_comp_eq : e.inv ≫ f = f' := by
  rw [← he, Iso.inv_hom_id_assoc]

/-- For a torus isomorphism `e`, the restricted roots for `f'` pull back exactly to those
for `f = e.hom ≫ f'`, and those for `f` pull back along `e.inv` to those for `f'`. -/
theorem image_restrictedSimpleRoots_iso :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedSimpleRoots i ν J f' = restrictedSimpleRoots i ν J f ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        restrictedSimpleRoots i ν J f = restrictedSimpleRoots i ν J f' :=
  ⟨image_restrictedSimpleRoots i ν J e.hom he,
    image_restrictedSimpleRoots i ν J e.inv (iso_inv_comp_eq e he)⟩

/-- The strictly positive root cones for `f'` and `f = e.hom ≫ f'` correspond exactly
under the two real character pullbacks of the torus isomorphism `e`. -/
theorem image_restrictedRootPositiveCone_iso :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootPositiveCone i ν J f' hfin = restrictedRootPositiveCone i ν J f hfin ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        restrictedRootPositiveCone i ν J f hfin = restrictedRootPositiveCone i ν J f' hfin :=
  ⟨image_restrictedRootPositiveCone i ν J hfin e.hom he,
    image_restrictedRootPositiveCone i ν J hfin e.inv (iso_inv_comp_eq e he)⟩

/-- The nonnegative root cones for `f'` and `f = e.hom ≫ f'` correspond exactly under the
two real character pullbacks of the torus isomorphism `e`. -/
theorem image_restrictedRootNonnegCone_iso :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootNonnegCone i ν J f' hfin = restrictedRootNonnegCone i ν J f hfin ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        restrictedRootNonnegCone i ν J f hfin = restrictedRootNonnegCone i ν J f' hfin :=
  ⟨image_restrictedRootNonnegCone i ν J hfin e.hom he,
    image_restrictedRootNonnegCone i ν J hfin e.inv (iso_inv_comp_eq e he)⟩

end Iso

/-! ### Standard-Levi split components -/

section StandardLevi

variable [Mono i.hom.hom.left] {L : GroupScheme (Spec (CommRingCat.of k))} (j : L ⟶ G)

omit [IsAffineHom G.X.hom] in
/-- For a monomorphic torus inclusion, the factorization `f ≫ i = a ≫ j` of a split
component `a` through the Levi representative `j` determines `f`. -/
theorem eq_of_groupHom_comp_eq {a : A.toGrp ⟶ L} {f₁ f₂ : A ⟶ T}
    (h₁ : CommGroupScheme.groupHom f₁ ≫ i = a ≫ j)
    (h₂ : CommGroupScheme.groupHom f₂ ≫ i = a ≫ j) : f₁ = f₂ := by
  apply Additive.toMul.injective
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact (cancel_mono i.hom.hom.left).mp
    (congrArg (fun z : A.toGrp ⟶ G => z.hom.hom.left) (h₁.trans h₂.symm))

/-- Changing the split-component presentation `a = e.hom ≫ a'` by a torus isomorphism
`e`: the strictly positive root cones attached to the factorizations of `a` and `a'`
correspond under the real character pullbacks along `e.hom` and `e.inv`. -/
theorem image_restrictedRootPositiveCone_splitComponentIso {a : A.toGrp ⟶ L}
    {a' : A'.toGrp ⟶ L} (e : A ≅ A') (hea : CommGroupScheme.groupHom e.hom ≫ a' = a)
    {f : A ⟶ T} {f' : A' ⟶ T} (hf : CommGroupScheme.groupHom f ≫ i = a ≫ j)
    (hf' : CommGroupScheme.groupHom f' ≫ i = a' ≫ j) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootPositiveCone i ν J f' hfin = restrictedRootPositiveCone i ν J f hfin ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        restrictedRootPositiveCone i ν J f hfin = restrictedRootPositiveCone i ν J f' hfin := by
  have he : e.hom ≫ f' = f := by
    refine eq_of_groupHom_comp_eq i j (a := a) ?_ hf
    change (CommGroupScheme.groupHom e.hom ≫ CommGroupScheme.groupHom f') ≫ i = a ≫ j
    rw [Category.assoc, hf', ← Category.assoc, hea]
  exact image_restrictedRootPositiveCone_iso i ν J hfin e he

/-- The nonnegative version of `image_restrictedRootPositiveCone_splitComponentIso`. -/
theorem image_restrictedRootNonnegCone_splitComponentIso {a : A.toGrp ⟶ L}
    {a' : A'.toGrp ⟶ L} (e : A ≅ A') (hea : CommGroupScheme.groupHom e.hom ≫ a' = a)
    {f : A ⟶ T} {f' : A' ⟶ T} (hf : CommGroupScheme.groupHom f ≫ i = a ≫ j)
    (hf' : CommGroupScheme.groupHom f' ≫ i = a' ≫ j) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootNonnegCone i ν J f' hfin = restrictedRootNonnegCone i ν J f hfin ∧
      rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv) ''
        restrictedRootNonnegCone i ν J f hfin = restrictedRootNonnegCone i ν J f' hfin := by
  have he : e.hom ≫ f' = f := by
    refine eq_of_groupHom_comp_eq i j (a := a) ?_ hf
    change (CommGroupScheme.groupHom e.hom ≫ CommGroupScheme.groupHom f') ≫ i = a ≫ j
    rw [Category.assoc, hf', ← Category.assoc, hea]
  exact image_restrictedRootNonnegCone_iso i ν J hfin e he

end StandardLevi

/-! ### Finiteness from the proved split-torus theorem -/

/-- With `T` split and `G` locally of finite type, the existing theorem
`IsSplitTorus.finite_simpleRelativeRoots` supplies the finiteness input. -/
theorem finite_restrictedSimpleRoots_of_isSplitTorus [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) : (restrictedSimpleRoots i ν J f).Finite :=
  finite_restrictedSimpleRoots i ν J f (hT.finite_simpleRelativeRoots i ν)

end Langlands.GroupScheme

namespace Langlands.GroupScheme

open RealTorusSpace

set_option backward.isDefEq.respectTransparency false

/-! ### Linear combinations over a finite set of vectors -/

section Combinations

variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]

theorem mem_positiveCombinations {S : Set M} {hS : S.Finite} {x : M} :
    x ∈ RootCombination.positive S hS ↔
      ∃ c : M → ℝ, (∀ s ∈ S, 0 < c s) ∧ ∑ s ∈ hS.toFinset, c s • s = x :=
  Iff.rfl

theorem mem_nonnegCombinations {S : Set M} {hS : S.Finite} {x : M} :
    x ∈ RootCombination.nonneg S hS ↔
      ∃ c : M → ℝ, (∀ s ∈ S, 0 ≤ c s) ∧ ∑ s ∈ hS.toFinset, c s • s = x :=
  Iff.rfl

omit [AddCommGroup M] [Module ℝ M] in
private theorem toFinset_eq_of_coe {S : Set M} (hS : S.Finite) {s : Finset M}
    (hs : (s : Set M) = S) : hS.toFinset = s :=
  Finset.coe_injective (by rw [Set.Finite.coe_toFinset, hs])

/-- The positive combinations computed with any repetition-free finite enumeration `s`
of `S`. -/
theorem mem_positiveCombinations_iff_finset {S : Set M} {hS : S.Finite} (s : Finset M)
    (hs : (s : Set M) = S) {x : M} :
    x ∈ RootCombination.positive S hS ↔
      ∃ c : M → ℝ, (∀ v ∈ S, 0 < c v) ∧ ∑ v ∈ s, c v • v = x := by
  rw [mem_positiveCombinations, toFinset_eq_of_coe hS hs]

/-- The nonnegative combinations computed with any repetition-free finite enumeration `s`
of `S`. -/
theorem mem_nonnegCombinations_iff_finset {S : Set M} {hS : S.Finite} (s : Finset M)
    (hs : (s : Set M) = S) {x : M} :
    x ∈ RootCombination.nonneg S hS ↔
      ∃ c : M → ℝ, (∀ v ∈ S, 0 ≤ c v) ∧ ∑ v ∈ s, c v • v = x := by
  rw [mem_nonnegCombinations, toFinset_eq_of_coe hS hs]

omit [Module ℝ M] in
private theorem sum_toFinset_eq_sum_equiv {S : Set M} (hS : S.Finite) {ι : Type*}
    [Fintype ι] (e : ι ≃ S) (g : M → M) :
    ∑ v ∈ hS.toFinset, g v = ∑ i, g (e i) := by
  let := hS.fintype
  rw [Finset.sum_subtype hS.toFinset (fun _ => hS.mem_toFinset) g]
  exact (Fintype.sum_equiv e (fun i => g (e i)) (fun v : S => g v) (fun _ => rfl)).symm

private theorem exists_coeff_iff_equiv (p : ℝ → Prop) {S : Set M} (hS : S.Finite)
    {ι : Type*} [Fintype ι] (e : ι ≃ S) (x : M) :
    (∃ c : M → ℝ, (∀ s ∈ S, p (c s)) ∧ ∑ s ∈ hS.toFinset, c s • s = x) ↔
      ∃ c : ι → ℝ, (∀ i, p (c i)) ∧ ∑ i, c i • (e i : M) = x := by
  classical
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨fun i => c (e i), fun i => hc _ (e i).2,
      (sum_toFinset_eq_sum_equiv hS e (fun v => c v • v)).symm⟩
  · rintro ⟨c, hc, rfl⟩
    let d : M → ℝ := fun v => if h : v ∈ S then c (e.symm ⟨v, h⟩) else 0
    have hd : ∀ i, d (e i) = c i := by
      intro i
      simp only [d, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply]
    refine ⟨d, fun s hs => ?_, ?_⟩
    · simp only [d, hs, ↓reduceDIte]
      exact hc _
    · rw [sum_toFinset_eq_sum_equiv hS e (fun v => d v • v)]
      simp only [hd]

/-- The positive combinations computed with an arbitrary enumeration `e : ι ≃ S` of the
distinct vectors of `S`. -/
theorem mem_positiveCombinations_iff_equiv {S : Set M} {hS : S.Finite} {ι : Type*}
    [Fintype ι] (e : ι ≃ S) {x : M} :
    x ∈ RootCombination.positive S hS ↔
      ∃ c : ι → ℝ, (∀ i, 0 < c i) ∧ ∑ i, c i • (e i : M) = x :=
  exists_coeff_iff_equiv (fun r => 0 < r) hS e x

/-- The nonnegative combinations computed with an arbitrary enumeration `e : ι ≃ S` of the
distinct vectors of `S`. -/
theorem mem_nonnegCombinations_iff_equiv {S : Set M} {hS : S.Finite} {ι : Type*}
    [Fintype ι] (e : ι ≃ S) {x : M} :
    x ∈ RootCombination.nonneg S hS ↔
      ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • (e i : M) = x :=
  exists_coeff_iff_equiv (fun r => 0 ≤ r) hS e x

theorem positiveCombinations_congr {S S' : Set M} (h : S = S') (hS : S.Finite)
    (hS' : S'.Finite) : RootCombination.positive S hS = RootCombination.positive S' hS' := by
  subst h
  rfl

theorem nonnegCombinations_congr {S S' : Set M} (h : S = S') (hS : S.Finite)
    (hS' : S'.Finite) : RootCombination.nonneg S hS = RootCombination.nonneg S' hS' := by
  subst h
  rfl

theorem positiveCombinations_subset_nonnegCombinations (S : Set M) (hS : S.Finite) :
    RootCombination.positive S hS ⊆ RootCombination.nonneg S hS :=
  fun _ ⟨c, hc, hx⟩ => ⟨c, fun s hs => (hc s hs).le, hx⟩

theorem zero_mem_nonnegCombinations (S : Set M) (hS : S.Finite) :
    (0 : M) ∈ RootCombination.nonneg S hS :=
  ⟨0, fun _ _ => le_rfl, by simp⟩

private theorem sum_add_coeff (s : Finset M) (c d : M → ℝ) :
    ∑ v ∈ s, (c + d) v • v = ∑ v ∈ s, c v • v + ∑ v ∈ s, d v • v := by
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]

private theorem sum_smul_coeff (s : Finset M) (t : ℝ) (c : M → ℝ) :
    ∑ v ∈ s, (t • c) v • v = t • ∑ v ∈ s, c v • v := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem add_mem_nonnegCombinations {S : Set M} {hS : S.Finite} {x y : M}
    (hx : x ∈ RootCombination.nonneg S hS) (hy : y ∈ RootCombination.nonneg S hS) :
    x + y ∈ RootCombination.nonneg S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  exact ⟨c + d, fun s hs => add_nonneg (hc s hs) (hd s hs), sum_add_coeff _ c d⟩

theorem smul_mem_nonnegCombinations {S : Set M} {hS : S.Finite} {t : ℝ} (ht : 0 ≤ t)
    {x : M} (hx : x ∈ RootCombination.nonneg S hS) : t • x ∈ RootCombination.nonneg S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨t • c, fun s hs => mul_nonneg ht (hc s hs), sum_smul_coeff _ t c⟩

theorem add_mem_positiveCombinations {S : Set M} {hS : S.Finite} {x y : M}
    (hx : x ∈ RootCombination.positive S hS) (hy : y ∈ RootCombination.positive S hS) :
    x + y ∈ RootCombination.positive S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨d, hd, rfl⟩ := hy
  exact ⟨c + d, fun s hs => add_pos (hc s hs) (hd s hs), sum_add_coeff _ c d⟩

theorem smul_mem_positiveCombinations {S : Set M} {hS : S.Finite} {t : ℝ} (ht : 0 < t)
    {x : M} (hx : x ∈ RootCombination.positive S hS) : t • x ∈ RootCombination.positive S hS := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨t • c, fun s hs => mul_pos ht (hc s hs), sum_smul_coeff _ t c⟩

/-- Over the empty index set the only positive combination is the empty sum `0`. -/
theorem positiveCombinations_of_eq_empty {S : Set M} (h : S = ∅) (hS : S.Finite) :
    RootCombination.positive S hS = {0} := by
  subst h
  ext x
  rw [mem_positiveCombinations, Set.Finite.toFinset_empty, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, -, rfl⟩
    rw [Finset.sum_empty]
  · rintro rfl
    exact ⟨0, fun _ h => h.elim, Finset.sum_empty⟩

/-- Over the empty index set the only nonnegative combination is the empty sum `0`. -/
theorem nonnegCombinations_of_eq_empty {S : Set M} (h : S = ∅) (hS : S.Finite) :
    RootCombination.nonneg S hS = {0} := by
  subst h
  ext x
  rw [mem_nonnegCombinations, Set.Finite.toFinset_empty, Set.mem_singleton_iff]
  constructor
  · rintro ⟨c, -, rfl⟩
    rw [Finset.sum_empty]
  · rintro rfl
    exact ⟨0, fun _ h => h.elim, Finset.sum_empty⟩

private theorem image_combinations (p : ℝ → Prop) (L : M →ₗ[ℝ] N)
    (hL : Function.Injective L) {S : Set M} (hS : S.Finite) (y : N) :
    (∃ x, (∃ c : M → ℝ, (∀ s ∈ S, p (c s)) ∧ ∑ s ∈ hS.toFinset, c s • s = x) ∧ L x = y) ↔
      ∃ d : N → ℝ, (∀ t ∈ L '' S, p (d t)) ∧
        ∑ t ∈ (hS.image L).toFinset, d t • t = y := by
  classical
  have himage : (hS.image L).toFinset = hS.toFinset.image L :=
    toFinset_eq_of_coe _ (by rw [Finset.coe_image, Set.Finite.coe_toFinset])
  have hsum : ∀ d : N → ℝ, ∑ t ∈ (hS.image L).toFinset, d t • t =
      L (∑ s ∈ hS.toFinset, d (L s) • s) := by
    intro d
    rw [himage, Finset.sum_image (fun a _ b _ h => hL h), map_sum]
    simp only [map_smul]
  have hinv : ∀ s, Function.invFun L (L s) = s := Function.leftInverse_invFun hL
  constructor
  · rintro ⟨x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨fun t => c (Function.invFun L t), ?_, ?_⟩
    · rintro _ ⟨s, hs, rfl⟩
      simpa only [hinv] using hc s hs
    · rw [hsum]
      simp only [hinv]
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, ⟨fun s => d (L s), fun s hs => hd _ ⟨s, hs, rfl⟩, rfl⟩, (hsum d).symm⟩

/-- An injective linear map carries the positive combinations of `S` exactly onto the
positive combinations of the image of `S`. -/
theorem image_positiveCombinations (L : M →ₗ[ℝ] N) (hL : Function.Injective L)
    (S : Set M) (hS : S.Finite) :
    L '' RootCombination.positive S hS = RootCombination.positive (L '' S) (hS.image L) := by
  ext y
  exact image_combinations (fun r => 0 < r) L hL hS y

/-- An injective linear map carries the nonnegative combinations of `S` exactly onto the
nonnegative combinations of the image of `S`. -/
theorem image_nonnegCombinations (L : M →ₗ[ℝ] N) (hL : Function.Injective L)
    (S : Set M) (hS : S.Finite) :
    L '' RootCombination.nonneg S hS = RootCombination.nonneg (L '' S) (hS.image L) := by
  ext y
  exact image_combinations (fun r => 0 ≤ r) L hL hS y

end Combinations

/-! ### Restricted roots along an actual morphism -/

section RestrictedRoots

variable {k : Type u} [Field k]
  {A A' T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Pulling back a restricted root along `g` restricts along the composite. -/
theorem restrictReal_restrictedRootVector (g : A ⟶ A') (f' : A' ⟶ T) {f : A ⟶ T}
    (h : g ≫ f' = f) (α : characterLattice T) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) (restrictedRootVector f' α) =
      restrictedRootVector f α := by
  subst h
  change (1 : ℝ) ⊗ₜ[ℤ] (g ≫ f' ≫ α) = (1 : ℝ) ⊗ₜ[ℤ] ((g ≫ f') ≫ α)
  rw [Category.assoc]

/-- The real character pullback along an isomorphism is injective. -/
theorem restrictReal_hom_injective (e : A ≅ A') :
    Function.Injective (rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom)) := by
  have hleft : ∀ x : Vstar A', rationalCharacterRestrictReal (CommGroupScheme.groupHom e.inv)
      (rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul r χ =>
      change r ⊗ₜ[ℤ] (e.inv ≫ e.hom ≫ χ) = r ⊗ₜ[ℤ] χ
      rw [Iso.inv_hom_id_assoc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact Function.LeftInverse.injective hleft

/-- If the real cocharacter image of `f` annihilates every character in `J`, the restriction
of each character in `J` pairs to zero with all of `V A`. -/
theorem pair_restrictedRootVector_eq_zero (f : A ⟶ T) {J : Set (characterLattice T)}
    (hf : LinearMap.range (cocharacterMapReal f) ≤ rootAnnihilator T J)
    {α : characterLattice T} (hα : α ∈ J) (v : V A) :
    pair A (restrictedRootVector f α) v = 0 := by
  rw [pair_restrictedRootVector]
  exact (mem_rootAnnihilator J _).mp (hf ⟨v, rfl⟩) α hα

/-- For an actual split torus `A`, if the real cocharacter image of `f` annihilates every
character in `J`, the restriction of each character in `J` is zero. -/
theorem restrictedRootVector_eq_zero (hA : IsSplitTorus A.toGrp) (f : A ⟶ T)
    {J : Set (characterLattice T)}
    (hf : LinearMap.range (cocharacterMapReal f) ≤ rootAnnihilator T J)
    {α : characterLattice T} (hα : α ∈ J) :
    restrictedRootVector f α = 0 := by
  have hp := isPerfPair_of_isSplitTorus hA
  apply hp.bijective_left.injective
  apply LinearMap.ext
  intro v
  rw [map_zero, LinearMap.zero_apply]
  exact pair_restrictedRootVector_eq_zero f hf hα v

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T))

theorem restrictedSimpleRoots_eq_image (f : A ⟶ T) :
    restrictedSimpleRoots i ν J f =
      (fun α : characterLattice T =>
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) ((1 : ℝ) ⊗ₜ[ℤ] α)) ''
        (simpleRelativeRoots i ν \ J) :=
  rfl

/-- The restricted simple roots are the images `1 ⊗ χ` of the integral restricted simple
characters. -/
theorem restrictedSimpleRoots_eq_image_characters (f : A ⟶ T) :
    restrictedSimpleRoots i ν J f =
      (fun χ : characterLattice A => (1 : ℝ) ⊗ₜ[ℤ] χ) '' restrictedSimpleCharacters i ν J f := by
  rw [restrictedSimpleCharacters, Set.image_image]
  rfl

/-- Finitely many simple relative roots give finitely many restricted simple roots. -/
theorem restrictedSimpleRoots_finite (f : A ⟶ T) (hfin : (simpleRelativeRoots i ν).Finite) :
    (restrictedSimpleRoots i ν J f).Finite :=
  (hfin.subset Set.sdiff_subset).image _

theorem restrictedSimpleRoots_eq_empty_iff_sdiff (f : A ⟶ T) :
    restrictedSimpleRoots i ν J f = ∅ ↔ simpleRelativeRoots i ν \ J = ∅ :=
  Set.image_eq_empty

/-- Pulling back along `g` carries the restricted simple roots for `f'` onto those for the
composite `f = g ≫ f'`. -/
theorem restrictReal_image_restrictedSimpleRoots (g : A ⟶ A') (f' : A' ⟶ T) {f : A ⟶ T}
    (h : g ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom g) ''
        restrictedSimpleRoots i ν J f' = restrictedSimpleRoots i ν J f := by
  rw [restrictedSimpleRoots, restrictedSimpleRoots, Set.image_image]
  simp only [restrictReal_restrictedRootVector g f' h]

/-! ### The two root-combination cones -/

variable (f : A ⟶ T) (hfin : (simpleRelativeRoots i ν).Finite)

theorem mem_restrictedPositiveCone {x : Vstar A} :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ restrictedSimpleRoots i ν J f, 0 < c β) ∧
        ∑ β ∈ (restrictedSimpleRoots_finite i ν J f hfin).toFinset, c β • β = x :=
  Iff.rfl

theorem mem_restrictedNonnegCone {x : Vstar A} :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ restrictedSimpleRoots i ν J f, 0 ≤ c β) ∧
        ∑ β ∈ (restrictedSimpleRoots_finite i ν J f hfin).toFinset, c β • β = x :=
  Iff.rfl

/-- Membership in the positive cone with any repetition-free finite enumeration `s` of the
restricted simple roots. -/
theorem mem_restrictedPositiveCone_iff_finset (s : Finset (Vstar A))
    (hs : (s : Set (Vstar A)) = restrictedSimpleRoots i ν J f) {x : Vstar A} :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ restrictedSimpleRoots i ν J f, 0 < c β) ∧
        ∑ β ∈ s, c β • β = x :=
  mem_positiveCombinations_iff_finset s hs

/-- Membership in the nonnegative cone with any repetition-free finite enumeration `s` of
the restricted simple roots. -/
theorem mem_restrictedNonnegCone_iff_finset (s : Finset (Vstar A))
    (hs : (s : Set (Vstar A)) = restrictedSimpleRoots i ν J f) {x : Vstar A} :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : Vstar A → ℝ, (∀ β ∈ restrictedSimpleRoots i ν J f, 0 ≤ c β) ∧
        ∑ β ∈ s, c β • β = x :=
  mem_nonnegCombinations_iff_finset s hs

/-- Membership in the positive cone with an arbitrary enumeration `e` of the distinct
restricted simple roots. -/
theorem mem_restrictedPositiveCone_iff_equiv {ι : Type*} [Fintype ι]
    (e : ι ≃ restrictedSimpleRoots i ν J f) {x : Vstar A} :
    x ∈ restrictedRootPositiveCone i ν J f hfin ↔
      ∃ c : ι → ℝ, (∀ j, 0 < c j) ∧ ∑ j, c j • (e j : Vstar A) = x :=
  mem_positiveCombinations_iff_equiv e

/-- Membership in the nonnegative cone with an arbitrary enumeration `e` of the distinct
restricted simple roots. -/
theorem mem_restrictedNonnegCone_iff_equiv {ι : Type*} [Fintype ι]
    (e : ι ≃ restrictedSimpleRoots i ν J f) {x : Vstar A} :
    x ∈ restrictedRootNonnegCone i ν J f hfin ↔
      ∃ c : ι → ℝ, (∀ j, 0 ≤ c j) ∧ ∑ j, c j • (e j : Vstar A) = x :=
  mem_nonnegCombinations_iff_equiv e

theorem restrictedPositiveCone_subset_restrictedNonnegCone :
    restrictedRootPositiveCone i ν J f hfin ⊆ restrictedRootNonnegCone i ν J f hfin :=
  positiveCombinations_subset_nonnegCombinations _ _

theorem zero_mem_restrictedNonnegCone : (0 : Vstar A) ∈ restrictedRootNonnegCone i ν J f hfin :=
  zero_mem_nonnegCombinations _ _

variable {i ν J f hfin}

theorem add_mem_restrictedNonnegCone {x y : Vstar A}
    (hx : x ∈ restrictedRootNonnegCone i ν J f hfin) (hy : y ∈ restrictedRootNonnegCone i ν J f hfin) :
    x + y ∈ restrictedRootNonnegCone i ν J f hfin :=
  add_mem_nonnegCombinations hx hy

theorem smul_mem_restrictedNonnegCone {t : ℝ} (ht : 0 ≤ t) {x : Vstar A}
    (hx : x ∈ restrictedRootNonnegCone i ν J f hfin) : t • x ∈ restrictedRootNonnegCone i ν J f hfin :=
  smul_mem_nonnegCombinations ht hx

theorem add_mem_restrictedPositiveCone {x y : Vstar A}
    (hx : x ∈ restrictedRootPositiveCone i ν J f hfin)
    (hy : y ∈ restrictedRootPositiveCone i ν J f hfin) :
    x + y ∈ restrictedRootPositiveCone i ν J f hfin :=
  add_mem_positiveCombinations hx hy

theorem smul_mem_restrictedPositiveCone {t : ℝ} (ht : 0 < t) {x : Vstar A}
    (hx : x ∈ restrictedRootPositiveCone i ν J f hfin) :
    t • x ∈ restrictedRootPositiveCone i ν J f hfin :=
  smul_mem_positiveCombinations ht hx

variable (i ν J f hfin)

/-- With no simple roots outside `J`, the positive cone is `{0}`. -/
theorem restrictedPositiveCone_of_eq_empty (h : simpleRelativeRoots i ν \ J = ∅) :
    restrictedRootPositiveCone i ν J f hfin = {0} :=
  positiveCombinations_of_eq_empty ((restrictedSimpleRoots_eq_empty_iff_sdiff i ν J f).2 h) _

/-- With no simple roots outside `J`, the nonnegative cone is `{0}`. -/
theorem restrictedNonnegCone_of_eq_empty (h : simpleRelativeRoots i ν \ J = ∅) :
    restrictedRootNonnegCone i ν J f hfin = {0} :=
  nonnegCombinations_of_eq_empty ((restrictedSimpleRoots_eq_empty_iff_sdiff i ν J f).2 h) _

/-! ### Change of split-component presentation -/

/-- Pulling back along `e.hom` carries the positive cone for `f'` exactly onto the positive
cone for `f = e.hom ≫ f'`. -/
theorem restrictReal_image_restrictedPositiveCone (e : A ≅ A') (f' : A' ⟶ T)
    (he : e.hom ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootPositiveCone i ν J f' hfin = restrictedRootPositiveCone i ν J f hfin := by
  rw [restrictedRootPositiveCone, image_positiveCombinations _ (restrictReal_hom_injective e)]
  exact positiveCombinations_congr
    (restrictReal_image_restrictedSimpleRoots i ν J e.hom f' he) _ _

/-- Pulling back along `e.hom` carries the nonnegative cone for `f'` exactly onto the
nonnegative cone for `f = e.hom ≫ f'`. -/
theorem restrictReal_image_restrictedNonnegCone (e : A ≅ A') (f' : A' ⟶ T)
    (he : e.hom ≫ f' = f) :
    rationalCharacterRestrictReal (CommGroupScheme.groupHom e.hom) ''
        restrictedRootNonnegCone i ν J f' hfin = restrictedRootNonnegCone i ν J f hfin := by
  rw [restrictedRootNonnegCone, image_nonnegCombinations _ (restrictReal_hom_injective e)]
  exact nonnegCombinations_congr
    (restrictReal_image_restrictedSimpleRoots i ν J e.hom f' he) _ _

end RestrictedRoots

end Langlands.GroupScheme
