import Langlands.Global.AdelicFunctoriality.IdeleClassNorm
import Langlands.Global.AdelicFunctoriality.LocalNormNeighborhood
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Global.Arithmetic.SUnitIdeleTopology

/-! # The idele norm and the idele-class norm are open maps -/

noncomputable section

namespace Langlands.Global.AdelicFunctoriality

open Filter Topology NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField NumberField.LiesOver FiniteExtension InfiniteExtension

universe u v

section FiberProduct

variable {ι κ : Type*} {G : ι → Type*} {H : κ → Type*}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]
  [∀ k, CommGroup (H k)] [∀ k, TopologicalSpace (H k)]
  (P : κ → ι → Prop) [∀ k, Fintype {i // P k i}]
  (N : ∀ k (i : {i // P k i}), G i →* H k)

/-- The product over fibres: the `k`-coordinate is the product of the maps `N k i` over the
indices `i` lying over `k`. -/
def fiberProd : (∀ i, G i) →* ∀ k, H k where
  toFun x k := ∏ i : {i // P k i}, N k i (x i)
  map_one' := by
    funext k
    simp
  map_mul' x y := by
    funext k
    simp [Finset.prod_mul_distrib]

omit [∀ i, TopologicalSpace (G i)] [∀ k, TopologicalSpace (H k)] in
theorem fiberProd_apply (x : ∀ i, G i) (k : κ) :
    fiberProd P N x k = ∏ i : {i // P k i}, N k i (x i) := rfl

/-- Openness at `1` of a product over fibres. Every index lies over at most one `k`, each `k`
has a chosen index `s k` over it, the map at `s k` sends neighbourhoods of `1` to
neighbourhoods of `1`, and for all but finitely many `k` the map at `s k` is surjective. -/
theorem nhds_one_le_map_fiberProd
    (huniq : ∀ i k k', P k i → P k' i → k = k')
    (s : ∀ k, {i // P k i})
    (hloc : ∀ k, ∀ t ∈ 𝓝 (1 : G (s k)), N k (s k) '' t ∈ 𝓝 (1 : H k))
    (hsurj : ∀ᶠ k in cofinite, Function.Surjective (N k (s k))) :
    𝓝 (1 : ∀ k, H k) ≤ map (fiberProd P N) (𝓝 1) := by
  classical
  rw [le_map_iff]
  intro V hV
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, hI, t, ht, hIt⟩ := hV
  let R : Set κ := {k | ¬ Function.Surjective (N k (s k))}
  have hR : R.Finite := Filter.eventually_cofinite.mp hsurj
  let J : Set κ := {k | ∃ i ∈ I, P k i} ∪ R
  have hJ : J.Finite := by
    refine Set.Finite.union ?_ hR
    refine (hI.biUnion fun i _ => Set.Subsingleton.finite
      (s := {k | P k i}) fun a ha b hb => huniq i a b ha hb).subset ?_
    rintro k ⟨i, hi, hk⟩
    exact Set.mem_biUnion hi hk
  refine mem_of_superset (set_pi_mem_nhds hJ fun k _ => hloc k _ (ht _)) ?_
  intro y hy
  have hc : ∀ k, ∃ c : G (s k), N k (s k) c = y k ∧ (k ∈ J → c ∈ t (s k)) := by
    intro k
    by_cases hk : k ∈ J
    · obtain ⟨c, hc, hcy⟩ := hy k hk
      exact ⟨c, hcy, fun _ => hc⟩
    · have hs : Function.Surjective (N k (s k)) := by
        by_contra h
        exact hk (Or.inr h)
      obtain ⟨c, hc⟩ := hs (y k)
      exact ⟨c, hc, fun h => absurd h hk⟩
  choose c hcy hct using hc
  have hex : ∀ i, (∃ k, (s k).1 = i) → ∃ g : G i, ∀ k (hk : P k i), (s k).1 = i →
      N k ⟨i, hk⟩ g = y k ∧ (k ∈ J → g ∈ t i) := by
    rintro i ⟨k, rfl⟩
    refine ⟨c k, fun k' hk' _ => ?_⟩
    obtain rfl : k' = k := huniq _ k' k hk' (s k).2
    exact ⟨hcy k', hct k'⟩
  let x : ∀ i, G i := fun i =>
    if h : ∃ k, (s k).1 = i then Classical.choose (hex i h) else 1
  refine ⟨x, hIt ?_, ?_⟩
  · intro i hi
    by_cases h : ∃ k, (s k).1 = i
    · obtain ⟨k, hk⟩ := h
      have hP : P k i := hk ▸ (s k).2
      have hxi : x i = Classical.choose (hex i ⟨k, hk⟩) := dite_eq_left ⟨k, hk⟩
      rw [hxi]
      exact ((Classical.choose_spec (hex i ⟨k, hk⟩)) k hP hk).2 (Or.inl ⟨i, hi, hP⟩)
    · have hxi : x i = 1 := dite_eq_right h
      rw [hxi]
      exact mem_of_mem_nhds (ht i)
  · funext k
    rw [fiberProd_apply, Finset.prod_eq_single (s k)]
    · have h : ∃ k', (s k').1 = (s k).1 := ⟨k, rfl⟩
      have hxi : x (s k).1 = Classical.choose (hex _ h) := dite_eq_left h
      rw [hxi]
      exact ((Classical.choose_spec (hex _ h)) k (s k).2 rfl).1
    · intro i _ hi
      have h : ¬ ∃ k', (s k').1 = i.1 := by
        rintro ⟨k', hk'⟩
        obtain rfl : k' = k := huniq i.1 k' k (hk' ▸ (s k').2) i.2
        exact hi (Subtype.ext hk'.symm)
      have hxi : x i.1 = 1 := dite_eq_right h
      rw [hxi, map_one]
    · intro h
      exact absurd (Finset.mem_univ _) h

end FiberProduct

section LocalNeighbourhoods

/-- Over a complete nontrivially normed field of characteristic zero, the `n`-th power map on
units sends neighbourhoods of `1` to neighbourhoods of `1`. -/
theorem image_pow_mem_nhds_one {F : Type*} [NontriviallyNormedField F] [CompleteSpace F]
    [CharZero F] {n : ℕ} (hn : n ≠ 0) {W : Set Fˣ} (hW : W ∈ 𝓝 (1 : Fˣ)) :
    (fun x : Fˣ => x ^ n) '' W ∈ 𝓝 (1 : Fˣ) := by
  have hderiv : HasStrictDerivAt (fun x : F => x ^ n) ((n : F) * 1 ^ (n - 1)) 1 :=
    hasStrictDerivAt_pow n 1
  have hne : (n : F) * 1 ^ (n - 1) ≠ 0 := by simpa using hn
  have hmap : map (fun x : F => x ^ n) (𝓝 1) = 𝓝 1 := by
    simpa using hderiv.map_nhds_eq hne
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Units.val_one] at hW
  obtain ⟨W', hW', hW'W⟩ := hW
  have himage : (fun x : F => x ^ n) '' (W' ∩ {x | x ≠ 0}) ∈ 𝓝 (1 : F) := by
    rw [← hmap]
    exact image_mem_map (inter_mem hW' (isOpen_ne.mem_nhds one_ne_zero))
  have hpre : (Units.val : Fˣ → F) ⁻¹' ((fun x : F => x ^ n) '' (W' ∩ {x | x ≠ 0})) ∈
      𝓝 (1 : Fˣ) :=
    Units.continuous_val.continuousAt.preimage_mem_nhds (by rw [Units.val_one]; exact himage)
  refine mem_of_superset hpre ?_
  rintro u ⟨x, ⟨hxW, hx⟩, hxu⟩
  exact ⟨Units.mk0 x hx, hW'W hxW, Units.ext (by simpa using hxu)⟩

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

/-- At a finite place, the local norm on units sends neighbourhoods of `1` to neighbourhoods
of `1`. -/
theorem image_finiteLocalNorm_mem_nhds (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal]
    {t : Set (q.adicCompletion L)ˣ} (ht : t ∈ 𝓝 (1 : (q.adicCompletion L)ˣ)) :
    Units.map (FiniteExtension.localNorm p q) '' t ∈ 𝓝 (1 : (p.adicCompletion K)ˣ) := by
  let _ : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField (p.adicCompletion K) (WithZero (Multiplicative ℤ))
  have : CharZero (p.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (p.adicCompletion K)).injective
  have hd : Module.finrank (p.adicCompletion K) (q.adicCompletion L) ≠ 0 :=
    Module.finrank_pos.ne'
  have hW : Units.map (FiniteExtension.completionMap p q).toMonoidHom ⁻¹' t ∈
      𝓝 (1 : (p.adicCompletion K)ˣ) :=
    ((FiniteExtension.continuous_completionMap p q).units_map _).continuousAt.preimage_mem_nhds
      (by rw [map_one]; exact ht)
  refine mem_of_superset (image_pow_mem_nhds_one hd hW) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, hx, Units.ext ?_⟩
  simp

omit [NumberField L] in
/-- At an infinite place, the local norm on units sends neighbourhoods of `1` to
neighbourhoods of `1`. -/
theorem image_infiniteLocalNorm_mem_nhds (p : InfinitePlace K) (q : InfinitePlace L)
    [q.LiesOver p] {t : Set q.Completionˣ} (ht : t ∈ 𝓝 (1 : q.Completionˣ)) :
    Units.map (InfiniteExtension.localNorm p q) '' t ∈ 𝓝 (1 : p.Completionˣ) := by
  let _ : NontriviallyNormedField p.Completion :=
    { (inferInstance : NormedField p.Completion) with
      non_trivial := by
        refine ⟨2, ?_⟩
        have h := (InfinitePlace.Completion.isometry_extensionEmbedding p).norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.extensionEmbedding p)) (2 : p.Completion)
        rw [← h]
        norm_num only [map_ofNat, Complex.norm_ofNat] }
  have : CharZero p.Completion :=
    charZero_of_injective_algebraMap (algebraMap K p.Completion).injective
  have hd : Module.finrank p.Completion q.Completion ≠ 0 :=
    Module.finrank_pos.ne'
  have hW : Units.map (NumberField.LiesOver.completionMap (v := p) (w := q)).toMonoidHom ⁻¹' t ∈
      𝓝 (1 : p.Completionˣ) :=
    ((NumberField.LiesOver.continuous_completionMap (v := p) (w := q)).units_map
      _).continuousAt.preimage_mem_nhds (by rw [map_one]; exact ht)
  refine mem_of_superset (image_pow_mem_nhds_one hd hW) ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨_, hx, Units.ext ?_⟩
  simp

end LocalNeighbourhoods
section Transport

/-- Openness at `1` transported along isomorphisms of topological groups: if `e' ∘ f = f' ∘ e`
and `f'` maps neighbourhoods of `1` onto neighbourhoods of `1`, so does `f`. -/
theorem nhds_one_le_map_of_comm {G G' H H' : Type*} [Group G] [Group G'] [Group H] [Group H']
    [TopologicalSpace G] [TopologicalSpace G'] [TopologicalSpace H] [TopologicalSpace H']
    (e : G ≃ₜ* G') (e' : H ≃ₜ* H') (f : G →* H) (f' : G' →* H')
    (hcomm : ∀ x, e' (f x) = f' (e x)) (h : 𝓝 (1 : H') ≤ map f' (𝓝 1)) :
    𝓝 (1 : H) ≤ map f (𝓝 1) := by
  have hf : (f : G → H) = e'.symm ∘ f' ∘ e := by
    funext x
    simp [← hcomm x]
  have he : map e (𝓝 (1 : G)) = 𝓝 1 :=
    (e.toHomeomorph.map_nhds_eq 1).trans (congrArg 𝓝 (map_one e))
  have he' : map e'.symm (𝓝 (1 : H')) = 𝓝 1 :=
    (e'.symm.toHomeomorph.map_nhds_eq 1).trans (congrArg 𝓝 (map_one e'.symm))
  calc 𝓝 (1 : H) = map e'.symm (𝓝 1) := he'.symm
    _ ≤ map e'.symm (map f' (map e (𝓝 1))) := map_mono (by rw [he]; exact h)
    _ = map f (𝓝 1) := by rw [map_map, map_map, hf]; rfl

end Transport

variable {K : Type u} {L : Type v} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

section Infinite

/-- The local norms on units at the infinite places above `p`. -/
def infiniteLocalUnitNorm (p : InfinitePlace K) (q : InfinitePlacesAbove L p) :
    q.1.Completionˣ →* p.Completionˣ :=
  Units.map (InfiniteExtension.localNorm p q.1)

variable (K L) in
/-- The norm on the product of the local unit groups at the infinite places: at each infinite
place `p` of `K`, the product of the local norms over the places above `p`. -/
def infiniteUnitNorm :
    (∀ q : InfinitePlace L, q.Completionˣ) →* ∀ p : InfinitePlace K, p.Completionˣ :=
  fiberProd (G := fun q : InfinitePlace L => q.Completionˣ)
    (H := fun p : InfinitePlace K => p.Completionˣ)
    (fun p q => q.LiesOver p) infiniteLocalUnitNorm

/-- The norm on the infinite local unit groups maps neighbourhoods of `1` onto neighbourhoods
of `1`. -/
theorem nhds_one_le_map_infiniteUnitNorm :
    𝓝 (1 : ∀ p : InfinitePlace K, p.Completionˣ) ≤ map (infiniteUnitNorm K L) (𝓝 1) := by
  refine nhds_one_le_map_fiberProd _ _ ?_ ?_ ?_ ?_
  · intro q p p' hp hp'
    exact (@InfinitePlace.LiesOver.comap_eq _ _ _ _ _ q p hp).symm.trans
      (@InfinitePlace.LiesOver.comap_eq _ _ _ _ _ q p' hp')
  · intro p
    refine Classical.choice ?_
    obtain ⟨q, hq⟩ := InfinitePlace.comap_surjective (K := L) p
    subst hq
    exact ⟨⟨q, ⟨rfl⟩⟩⟩
  · intro p t ht
    exact image_infiniteLocalNorm_mem_nhds p _ ht
  · exact Filter.eventually_cofinite.2 (Set.toFinite _)

/-- The infinite-adele norm on units maps neighbourhoods of `1` onto neighbourhoods of `1`. -/
theorem nhds_one_le_map_infiniteAdeleNorm :
    𝓝 (1 : (InfiniteAdeleRing K)ˣ) ≤
      map (Units.map (infiniteAdeleNorm (K := K) (L := L))) (𝓝 1) := by
  refine nhds_one_le_map_of_comm ContinuousMulEquiv.piUnits ContinuousMulEquiv.piUnits _
    (infiniteUnitNorm K L) ?_ nhds_one_le_map_infiniteUnitNorm
  intro x
  funext p
  apply Units.ext
  rw [infiniteUnitNorm, fiberProd_apply, Units.coe_prod]
  rfl

end Infinite

section Finite

open Langlands.Global Langlands.ClassField.Global
open Langlands.Global.Arithmetic.SUnitIdeleTopology

omit [NumberField K] in
/-- A unit of a finite completion has valuation one exactly when it is a unit of the valuation
ring. -/
theorem valued_eq_one_iff_mem_units {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    Valued.v (x : w.adicCompletion F) = 1 ↔ x ∈ (w.adicCompletionIntegers F).units := by
  rw [Submonoid.mem_units_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change Valued.v (x : w.adicCompletion F) ≤ 1
      exact h.le
    · change Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]
  · rintro ⟨ha, hb⟩
    change Valued.v (x : w.adicCompletion F) ≤ 1 at ha
    change Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≤ 1 at hb
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hb
    exact le_antisymm ha ((inv_le_one₀ (pos_iff_ne_zero.2
      ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))).1 hb)

/-- The local factor with `S = ∅`, the valuation units, is a neighbourhood of `1`. -/
theorem localFactor_empty_mem_nhds {F : Type*} [Field F] [NumberField F]
    (w : HeightOneSpectrum (𝓞 F)) :
    (localFactor F ∅ w : Set (w.adicCompletion F)ˣ) ∈ 𝓝 (1 : (w.adicCompletion F)ˣ) := by
  refine mem_of_superset ((Submonoid.isOpen_units
    (U := (w.adicCompletionIntegers F).toSubmonoid)
    (Valued.isOpen_valuationSubring _)).mem_nhds (one_mem _)) ?_
  intro x hx
  exact (mem_localFactor_iff F ∅ w x).2 fun _ => (valued_eq_one_iff_mem_units w x).2 hx

/-- The local norm sends valuation units to valuation units. -/
theorem localNorm_mem_localFactor_empty (p : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 L)) [q.asIdeal.LiesOver p.asIdeal] (x : localFactor L ∅ q) :
    Units.map (FiniteExtension.localNorm p q) (x : (q.adicCompletion L)ˣ) ∈
      localFactor K ∅ p := by
  have hx : (x : (q.adicCompletion L)ˣ) ∈ (q.adicCompletionIntegers L).units :=
    (valued_eq_one_iff_mem_units q _).1
      ((mem_localFactor_iff L ∅ q _).1 x.2 (Finset.notMem_empty q))
  exact (mem_localFactor_iff K ∅ p _).2 fun _ =>
    (valued_eq_one_iff_mem_units p _).2 (FiniteExtension.localUnitNorm_integral p q hx)

/-- The local norm between the valuation-unit factors of the `S = ∅` product models. -/
def localFactorNorm (p : HeightOneSpectrum (𝓞 K)) (q : FinitePlacesAbove L p) :
    localFactor L ∅ q.1 →* localFactor K ∅ p :=
  ((Units.map (FiniteExtension.localNorm p q.1)).comp (localFactor L ∅ q.1).subtype).codRestrict
    _ (localNorm_mem_localFactor_empty p q.1)

/-- The local norm on valuation units maps neighbourhoods of `1` onto neighbourhoods of `1`. -/
theorem image_localFactorNorm_mem_nhds (p : HeightOneSpectrum (𝓞 K))
    (q : FinitePlacesAbove L p) {t : Set (localFactor L ∅ q.1)} (ht : t ∈ 𝓝 1) :
    localFactorNorm p q '' t ∈ 𝓝 (1 : localFactor K ∅ p) := by
  obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 ht
  have himg := image_finiteLocalNorm_mem_nhds p q.1
    (inter_mem hu (localFactor_empty_mem_nhds q.1))
  refine mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds himg) ?_
  rintro y ⟨x, ⟨hxu, hxU⟩, hxy⟩
  exact ⟨⟨x, hxU⟩, hut hxu, Subtype.ext hxy⟩

/-- For all but finitely many finite places `p` of `K`, the local norm on valuation units at the
chosen place above `p` is surjective. -/
theorem eventually_localFactorNorm_surjective :
    ∀ᶠ p : HeightOneSpectrum (𝓞 K) in cofinite,
      Function.Surjective (localFactorNorm p (placeAbove L p)) := by
  filter_upwards [eventually_ramificationIdx_eq_one K L] with p hp
  intro y
  have hy : Valued.v ((y : (p.adicCompletion K)ˣ) : p.adicCompletion K) = 1 :=
    (mem_localFactor_iff K ∅ p _).1 y.2 (Finset.notMem_empty p)
  obtain ⟨c, hc, hcy⟩ := FiniteExtension.exists_localNorm_eq_of_ramificationIdx_eq_one p
    (placeAbove L p).1 (hp _ (placeAbove L p).2) _ hy
  exact ⟨⟨c, (mem_localFactor_iff L ∅ _ c).2 fun _ => hc⟩, Subtype.ext (Units.ext hcy)⟩

variable (K L) in
/-- The norm on the finite factors of the `S = ∅` product models: at each finite place `p` of
`K`, the product of the local norms over the places above `p`. -/
def finiteModelNorm : finiteModel L ∅ →* finiteModel K ∅ :=
  fiberProd (G := fun q : HeightOneSpectrum (𝓞 L) => localFactor L ∅ q)
    (H := fun p : HeightOneSpectrum (𝓞 K) => localFactor K ∅ p)
    (fun p q => q.asIdeal.LiesOver p.asIdeal) localFactorNorm

variable (K L) in
/-- The norm on the `S = ∅` product models: the infinite-adele norm on the infinite factor and
`finiteModelNorm` on the finite factors. -/
def modelNorm : model L ∅ →* model K ∅ :=
  (Units.map (infiniteAdeleNorm (K := K) (L := L))).prodMap (finiteModelNorm K L)

/-- The idele norm commutes with the assembly maps of the `S = ∅` product models. -/
theorem ideleNorm_assemble (x : model L ∅) :
    ideleNorm (K := K) (assemble L ∅ x) = assemble K ∅ (modelNorm K L x) := by
  apply Units.ext
  apply Prod.ext
  · rfl
  · apply FiniteAdeleRing.ext
    intro p
    change (∏ q : FinitePlacesAbove L p, FiniteExtension.localNorm p q.1
        (((x.2 q.1 : (q.1.adicCompletion L)ˣ)) : q.1.adicCompletion L)) =
      (((∏ q : FinitePlacesAbove L p, localFactorNorm p q (x.2 q.1) : localFactor K ∅ p) :
        (p.adicCompletion K)ˣ) : p.adicCompletion K)
    rw [SubmonoidClass.coe_finsetProd, Units.coe_prod]
    rfl

/-- The norm on the `S = ∅` product models maps neighbourhoods of `1` onto neighbourhoods
of `1`. -/
theorem nhds_one_le_map_modelNorm :
    𝓝 (1 : model K ∅) ≤ map (modelNorm K L) (𝓝 1) := by
  have hK : 𝓝 (1 : model K ∅) = 𝓝 (1 : (InfiniteAdeles K)ˣ) ×ˢ 𝓝 (1 : finiteModel K ∅) :=
    nhds_prod_eq
  have hL : 𝓝 (1 : model L ∅) = 𝓝 (1 : (InfiniteAdeles L)ˣ) ×ˢ 𝓝 (1 : finiteModel L ∅) :=
    nhds_prod_eq
  have hmap : map (modelNorm K L) (𝓝 (1 : (InfiniteAdeles L)ˣ) ×ˢ 𝓝 (1 : finiteModel L ∅)) =
      map (Units.map (infiniteAdeleNorm (K := K) (L := L))) (𝓝 1) ×ˢ
        map (finiteModelNorm K L) (𝓝 1) := by
    rw [Filter.prod_map_map_eq']
    rfl
  rw [hK, hL, hmap]
  refine Filter.prod_mono nhds_one_le_map_infiniteAdeleNorm ?_
  exact nhds_one_le_map_fiberProd _ _
    (fun q p p' hp hp' => (finitePlacesAbove_under p ⟨q, hp⟩).symm.trans
      (finitePlacesAbove_under p' ⟨q, hp'⟩))
    (placeAbove L) (fun p t ht => image_localFactorNorm_mem_nhds p _ ht)
    eventually_localFactorNorm_surjective

/-- The assembly map of the `S = ∅` product model is an open embedding into the ideles. -/
theorem isOpenEmbedding_assemble (F : Type*) [Field F] [NumberField F] :
    IsOpenEmbedding (assemble F ∅) :=
  (isOpen_sUnitIdeles F ∅).isOpenEmbedding_subtypeVal.comp
    (productEquiv F ∅).toHomeomorph.isOpenEmbedding

end Finite

open Langlands.Global.Arithmetic.SUnitIdeleTopology in
/-- The idele norm `𝕀_L → 𝕀_K` is an open map. -/
theorem isOpenMap_ideleNorm : IsOpenMap (ideleNorm (K := K) (L := L)) := by
  rw [IsTopologicalGroup.isOpenMap_iff_nhds_one]
  have hK := (isOpenEmbedding_assemble K).map_nhds_eq 1
  have hL := (isOpenEmbedding_assemble L).map_nhds_eq 1
  rw [map_one] at hK hL
  calc 𝓝 (1 : IdeleGroup (𝓞 K) K) = map (assemble K ∅) (𝓝 1) := hK.symm
    _ ≤ map (assemble K ∅) (map (modelNorm K L) (𝓝 1)) := map_mono nhds_one_le_map_modelNorm
    _ = map ideleNorm (map (assemble L ∅) (𝓝 1)) := by
      rw [map_map, map_map]
      congr 1
      funext x
      exact (ideleNorm_assemble x).symm
    _ = map ideleNorm (𝓝 1) := by rw [hL]

/-- The idele-class norm `C_L → C_K` is an open map. -/
theorem isOpenMap_ideleClassNorm : IsOpenMap (ideleClassNorm (K := K) (L := L)) := by
  intro U hU
  have h : ideleClassNorm (K := K) '' U =
      (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) ''
        (ideleNorm (K := K) '' ((QuotientGroup.mk : IdeleGroup (𝓞 L) L →
          IdeleClassGroup (𝓞 L) L) ⁻¹' U)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨ideleNorm a, ⟨a, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk a, ha, rfl⟩
  rw [h]
  exact QuotientGroup.isOpenMap_coe _ (isOpenMap_ideleNorm _
    (hU.preimage QuotientGroup.continuous_mk))

end Langlands.Global.AdelicFunctoriality
