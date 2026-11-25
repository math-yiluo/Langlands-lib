import Langlands.Galois.RestrictedRamification.Unramified
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# The maximal extension unramified outside `S` and its Galois group `G_S`

For a number field `K`, a field `Ω` over `K` and a set `S` of finite places of `K`, the maximal
extension of `K` in `Ω` unramified outside `S` is the compositum `K_S` of the finite subextensions
of `Ω / K` that are unramified outside `S` (the real places may ramify). When `Ω / K` is Galois,
`K_S / K` is Galois, and its Galois group `G_S = Gal(K_S / K)` is profinite. For `T ⊆ S` restriction
is a continuous surjection `G_S → G_T`, and `G_S` is a quotient of `Gal(Ω / K)`. When `Ω` is moreover
separably closed, every finite extension of `K` unramified outside `S` embeds over `K` into `K_S`
(`nonempty_algHom_maximalUnramifiedOutside`).
-/

namespace Langlands.Galois

open NumberField IsDedekindDomain

universe u v

section Definitions

variable (K : Type u) [Field K] (Ω : Type v) [Field Ω] [Algebra K Ω]

/-- The maximal extension of `K` in `Ω` unramified outside the set `S` of finite places: the
compositum of the finite subextensions unramified outside `S`. -/
noncomputable def maximalUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K))) :
    IntermediateField K Ω :=
  ⨆ (E : IntermediateField K Ω) (_ : FiniteDimensional K E) (_ : IsUnramifiedOutside S E), E

/-- The Galois group `G_S = Gal(K_S / K)` of the maximal extension unramified outside `S`. -/
abbrev GaloisGroupUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 K))) : Type v :=
  Gal(maximalUnramifiedOutside K Ω S / K)

end Definitions

section Basic

variable {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

theorem le_maximalUnramifiedOutside {E : IntermediateField K Ω} [FiniteDimensional K E]
    (hE : IsUnramifiedOutside S E) : E ≤ maximalUnramifiedOutside K Ω S :=
  le_iSup_of_le E (le_iSup_of_le ‹_› (le_iSup_of_le hE le_rfl))

variable (K Ω) in
theorem maximalUnramifiedOutside_mono {S T : Set (HeightOneSpectrum (𝓞 K))} (h : S ⊆ T) :
    maximalUnramifiedOutside K Ω S ≤ maximalUnramifiedOutside K Ω T :=
  iSup_mono fun _ => iSup_mono fun _ => iSup_le fun hE =>
    le_iSup_of_le (fun v hv => hE v fun hs => hv (h hs)) le_rfl

theorem maximalUnramifiedOutside_eq_iSup :
    maximalUnramifiedOutside K Ω S =
      ⨆ E : {E : IntermediateField K Ω // FiniteDimensional K E ∧ IsUnramifiedOutside S E}, E.1 := by
  apply le_antisymm
  · exact iSup_le fun E => iSup_le fun hf => iSup_le fun hu => le_iSup_of_le ⟨E, hf, hu⟩ le_rfl
  · exact iSup_le fun E => have := E.2.1; le_maximalUnramifiedOutside S E.2.2

variable [NumberField K] [IsGalois K Ω]

theorem mem_maximalUnramifiedOutside_iff {x : Ω} :
    x ∈ maximalUnramifiedOutside K Ω S ↔
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsUnramifiedOutside S E ∧ x ∈ E := by
  constructor
  · intro hx
    have hne : Nonempty {E : IntermediateField K Ω // FiniteDimensional K E ∧
        IsUnramifiedOutside S E} := ⟨⟨⊥, inferInstance, isUnramifiedOutside_bot S⟩⟩
    have hdir : Directed (· ≤ ·) (fun E : {E : IntermediateField K Ω // FiniteDimensional K E ∧
        IsUnramifiedOutside S E} => E.1) := by
      intro E₁ E₂
      have := E₁.2.1
      have := E₂.2.1
      exact ⟨⟨E₁.1 ⊔ E₂.1, inferInstance, E₁.2.2.sup E₂.2.2⟩, le_sup_left, le_sup_right⟩
    rw [maximalUnramifiedOutside_eq_iSup, ← SetLike.mem_coe,
      IntermediateField.coe_iSup_of_directed hdir, Set.mem_iUnion] at hx
    obtain ⟨E, hE⟩ := hx
    exact ⟨E.1, E.2.1, E.2.2, hE⟩
  · rintro ⟨E, hf, hu, hx⟩
    exact le_maximalUnramifiedOutside S hu hx

theorem exists_subset_of_subset_maximalUnramifiedOutside (s : Finset Ω)
    (hs : ∀ x ∈ s, x ∈ maximalUnramifiedOutside K Ω S) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsUnramifiedOutside S E ∧
      ∀ x ∈ s, x ∈ E := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊥, inferInstance, isUnramifiedOutside_bot S, by simp⟩
  | insert a s _ ih =>
    obtain ⟨E₁, hf₁, hu₁, ha⟩ :=
      (mem_maximalUnramifiedOutside_iff S).1 (hs a (Finset.mem_insert_self a s))
    obtain ⟨E₂, hf₂, hu₂, hs₂⟩ := ih fun x hx => hs x (Finset.mem_insert_of_mem hx)
    refine ⟨E₁ ⊔ E₂, inferInstance, hu₁.sup hu₂, fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact le_sup_left (α := IntermediateField K Ω) ha
    · exact le_sup_right (α := IntermediateField K Ω) (hs₂ x hx)

/-- A finite subextension is unramified outside `S` if and only if it lies in `K_S`. -/
theorem isUnramifiedOutside_iff_le {E : IntermediateField K Ω} [FiniteDimensional K E] :
    IsUnramifiedOutside S E ↔ E ≤ maximalUnramifiedOutside K Ω S := by
  refine ⟨le_maximalUnramifiedOutside S, fun h => ?_⟩
  classical
  let b := Module.finBasis K E
  obtain ⟨E', hf, hu, hE'⟩ := exists_subset_of_subset_maximalUnramifiedOutside S
    (Finset.univ.image fun i => (b i : Ω)) fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact h (b i).2
  have hle : E ≤ E' := by
    intro x hx
    have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : Ω) := by
      have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
      rw [map_sum] at this
      simp only [map_smul] at this
      exact this.symm
    rw [hx']
    exact sum_mem fun i _ => E'.smul_mem (hE' _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  exact hu.of_le hle

/-- `K_S / K` is Galois. -/
instance isGalois_maximalUnramifiedOutside : IsGalois K (maximalUnramifiedOutside K Ω S) := by
  have hN : Normal K (maximalUnramifiedOutside K Ω S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro τ x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    obtain ⟨E, hf, hu, hyE⟩ := (mem_maximalUnramifiedOutside_iff S).1 hy
    have : FiniteDimensional K (E.map (τ : Ω →ₐ[K] Ω)) :=
      LinearEquiv.finiteDimensional (IntermediateField.equivMap E (τ : Ω →ₐ[K] Ω)).toLinearEquiv
    exact le_maximalUnramifiedOutside S (hu.map τ) ((IntermediateField.mem_map _).2 ⟨y, hyE, rfl⟩)
  exact ⟨⟩

end Basic

namespace GaloisGroupUnramifiedOutside

variable (K : Type u) [Field K] [NumberField K] (Ω : Type v) [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- `G_S` is compact. -/
instance compactSpace : CompactSpace (GaloisGroupUnramifiedOutside K Ω S) := inferInstance

/-- `G_S` is Hausdorff. -/
instance t2Space : T2Space (GaloisGroupUnramifiedOutside K Ω S) := krullTopology_t2

/-- `G_S` is totally disconnected. -/
instance totallyDisconnectedSpace : TotallyDisconnectedSpace (GaloisGroupUnramifiedOutside K Ω S) :=
  inferInstance

/-- `G_S` as a profinite group. -/
noncomputable abbrev profiniteGrp : ProfiniteGrp.{v} :=
  ProfiniteGrp.of (GaloisGroupUnramifiedOutside K Ω S)

/-! ### `G_S` as a quotient of `Gal(Ω / K)` -/

/-- Restriction `Gal(Ω / K) → G_S`; it is surjective (`quotientMap_surjective`). -/
noncomputable def quotientMap : Gal(Ω/K) →ₜ* GaloisGroupUnramifiedOutside K Ω S :=
  ⟨AlgEquiv.restrictNormalHom (maximalUnramifiedOutside K Ω S),
    InfiniteGalois.restrictNormalHom_continuous _⟩

variable {K Ω S}

theorem quotientMap_apply (σ : Gal(Ω/K)) (x : maximalUnramifiedOutside K Ω S) :
    ((quotientMap K Ω S σ x : maximalUnramifiedOutside K Ω S) : Ω) = σ x :=
  AlgEquiv.restrictNormal_commutes σ (maximalUnramifiedOutside K Ω S) x

variable (K Ω S) in
theorem quotientMap_surjective : Function.Surjective (quotientMap K Ω S) :=
  AlgEquiv.restrictNormalHom_surjective Ω

variable (K Ω S) in
theorem isQuotientMap_quotientMap : Topology.IsQuotientMap (quotientMap K Ω S) :=
  (quotientMap K Ω S).continuous.isClosedMap.isQuotientMap (quotientMap K Ω S).continuous
    (quotientMap_surjective K Ω S)

/-! ### Restriction `G_S → G_T` for `T ⊆ S` -/

variable {T U : Set (HeightOneSpectrum (𝓞 K))}

/-- An extension of an element of `G_S` to `Ω` (a choice). -/
noncomputable def lift (σ : GaloisGroupUnramifiedOutside K Ω S) : Gal(Ω/K) :=
  (quotientMap_surjective K Ω S σ).choose

@[simp]
theorem quotientMap_lift (σ : GaloisGroupUnramifiedOutside K Ω S) :
    quotientMap K Ω S (lift σ) = σ :=
  (quotientMap_surjective K Ω S σ).choose_spec

theorem lift_apply (σ : GaloisGroupUnramifiedOutside K Ω S) (y : maximalUnramifiedOutside K Ω S) :
    lift σ (y : Ω) = ((σ y : maximalUnramifiedOutside K Ω S) : Ω) := by
  conv_rhs => rw [← quotientMap_lift σ]
  exact (quotientMap_apply (lift σ) y).symm

theorem lift_inv_apply (σ : GaloisGroupUnramifiedOutside K Ω S)
    (y : maximalUnramifiedOutside K Ω S) :
    (lift σ)⁻¹ (y : Ω) = ((σ⁻¹ y : maximalUnramifiedOutside K Ω S) : Ω) := by
  rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, lift_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
    AlgEquiv.one_apply]

variable (Ω) in
/-- The underlying map of the restriction `G_S → G_T`. -/
noncomputable def restrictFun (T : Set (HeightOneSpectrum (𝓞 K)))
    (σ : GaloisGroupUnramifiedOutside K Ω S) : GaloisGroupUnramifiedOutside K Ω T :=
  quotientMap K Ω T (lift σ)

theorem restrictFun_apply (h : T ⊆ S) (σ : GaloisGroupUnramifiedOutside K Ω S)
    (x : maximalUnramifiedOutside K Ω T) :
    ((restrictFun Ω T σ x : maximalUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ : maximalUnramifiedOutside K Ω S) : Ω) := by
  rw [restrictFun, quotientMap_apply]
  exact lift_apply σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩

variable (Ω) in
/-- Restriction `G_S → G_T` for `T ⊆ S`, as a homomorphism of groups. -/
noncomputable def restrictHom (h : T ⊆ S) :
    GaloisGroupUnramifiedOutside K Ω S →* GaloisGroupUnramifiedOutside K Ω T where
  toFun := restrictFun Ω T
  map_one' := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [restrictFun_apply h, AlgEquiv.one_apply, AlgEquiv.one_apply]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    have e : (⟨((restrictFun Ω T τ x : maximalUnramifiedOutside K Ω T) : Ω),
        maximalUnramifiedOutside_mono K Ω h (restrictFun Ω T τ x).2⟩ :
          maximalUnramifiedOutside K Ω S) = τ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ :=
      Subtype.val_injective (restrictFun_apply h τ x)
    rw [AlgEquiv.mul_apply (restrictFun Ω T σ), restrictFun_apply h (σ * τ) x,
      restrictFun_apply h σ (restrictFun Ω T τ x), e, AlgEquiv.mul_apply]

theorem restrictHom_apply (h : T ⊆ S) (σ : GaloisGroupUnramifiedOutside K Ω S)
    (x : maximalUnramifiedOutside K Ω T) :
    ((restrictHom Ω h σ x : maximalUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ : maximalUnramifiedOutside K Ω S) : Ω) :=
  restrictFun_apply h σ x

theorem restrictHom_quotientMap (h : T ⊆ S) (σ : Gal(Ω/K)) :
    restrictHom Ω h (quotientMap K Ω S σ) = quotientMap K Ω T σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [restrictHom_apply, quotientMap_apply, quotientMap_apply]

theorem continuous_restrictHom (h : T ⊆ S) : Continuous (restrictHom Ω h) := by
  rw [(isQuotientMap_quotientMap K Ω S).continuous_iff]
  have e : ⇑(restrictHom Ω h) ∘ ⇑(quotientMap K Ω S) = ⇑(quotientMap K Ω T) :=
    funext (restrictHom_quotientMap h)
  rw [e]
  exact (quotientMap K Ω T).continuous

variable (Ω) in
/-- Restriction `G_S → G_T` for `T ⊆ S`: the restriction of automorphisms of `K_S` to `K_T`. -/
noncomputable def restrict (h : T ⊆ S) :
    GaloisGroupUnramifiedOutside K Ω S →ₜ* GaloisGroupUnramifiedOutside K Ω T :=
  ⟨restrictHom Ω h, continuous_restrictHom h⟩

theorem restrict_apply (h : T ⊆ S) (σ : GaloisGroupUnramifiedOutside K Ω S)
    (x : maximalUnramifiedOutside K Ω T) :
    ((restrict Ω h σ x : maximalUnramifiedOutside K Ω T) : Ω) =
      ((σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ : maximalUnramifiedOutside K Ω S) : Ω) :=
  restrictFun_apply h σ x

theorem restrict_toMonoidHom (h : T ⊆ S) : (restrict Ω h).toMonoidHom = restrictHom Ω h :=
  rfl

@[simp]
theorem restrict_quotientMap (h : T ⊆ S) (σ : Gal(Ω/K)) :
    restrict Ω h (quotientMap K Ω S σ) = quotientMap K Ω T σ :=
  restrictHom_quotientMap h σ

theorem restrict_surjective (h : T ⊆ S) : Function.Surjective (restrict Ω h) := fun τ =>
  ⟨quotientMap K Ω S (lift τ), by rw [restrict_quotientMap, quotientMap_lift]⟩

theorem restrict_restrict (hTS : T ⊆ S) (hUT : U ⊆ T) (σ : GaloisGroupUnramifiedOutside K Ω S) :
    restrict Ω hUT (restrict Ω hTS σ) = restrict Ω (hUT.trans hTS) σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [restrict_apply hUT, restrict_apply hTS, restrict_apply]

@[simp]
theorem restrict_refl (σ : GaloisGroupUnramifiedOutside K Ω S) :
    restrict Ω (subset_refl S) σ = σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [restrict_apply]

theorem mem_ker_restrict (h : T ⊆ S) (σ : GaloisGroupUnramifiedOutside K Ω S) :
    σ ∈ (restrictHom Ω h).ker ↔
      ∀ x : maximalUnramifiedOutside K Ω T, σ ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ =
        ⟨x, maximalUnramifiedOutside_mono K Ω h x.2⟩ := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hσ x
    apply Subtype.val_injective
    have := restrictHom_apply h σ x
    rw [hσ] at this
    exact this.symm
  · intro hσ
    apply AlgEquiv.ext
    intro x
    apply Subtype.val_injective
    rw [restrictHom_apply, hσ x, AlgEquiv.one_apply]

theorem isQuotientMap_restrict (h : T ⊆ S) : Topology.IsQuotientMap (restrict Ω h) :=
  (restrict Ω h).continuous.isClosedMap.isQuotientMap (restrict Ω h).continuous
    (restrict_surjective h)

omit [IsGalois K Ω] in
/-- Only finitely many places of `K` are ramified in a finite subextension `E`. -/
theorem finite_setOf_ramified_below (E : IntermediateField K Ω) [FiniteDimensional K E] :
    {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 E), w.asIdeal.LiesOver v.asIdeal ∧
      w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}.Finite := by
  have := NumberField.of_module_finite K E
  refine ((finite_setOf_ramificationIdx_ne_one K E).image
    (HeightOneSpectrum.under (𝓞 K))).subset ?_
  rintro v ⟨w, hw, he⟩
  exact ⟨w, he, (liesOver_iff_eq_under.1 hw).symm⟩

/-- An open subgroup of `G_S` contains the kernel of `G_S → G_T` for some finite `T ⊆ S`
containing a given finite `T₁ ⊆ S`. -/
theorem exists_finite_ker_restrict_le (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S))
    (hU : IsOpen (U : Set (GaloisGroupUnramifiedOutside K Ω S)))
    {T₁ : Set (HeightOneSpectrum (𝓞 K))} (hT₁ : T₁.Finite) (hT₁S : T₁ ⊆ S) :
    ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ T₁ ⊆ T ∧
      ∃ hTS : T ⊆ S, (restrictHom Ω hTS).ker ≤ U := by
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K (maximalUnramifiedOutside K Ω S)
    (U : Set (GaloisGroupUnramifiedOutside K Ω S))).1 (hU.mem_nhds U.one_mem)
  let E' : IntermediateField K Ω := E.map (maximalUnramifiedOutside K Ω S).val
  have hE' : FiniteDimensional K E' :=
    LinearEquiv.finiteDimensional (E.equivMap (maximalUnramifiedOutside K Ω S).val).toLinearEquiv
  set R := {v : HeightOneSpectrum (𝓞 K) | ∃ w : HeightOneSpectrum (𝓞 E'),
    w.asIdeal.LiesOver v.asIdeal ∧ w.asIdeal.ramificationIdx (𝓞 K) ≠ 1}
  have hR : R.Finite := finite_setOf_ramified_below E'
  have hE'S : E' ≤ maximalUnramifiedOutside K Ω S := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE'Sun : IsUnramifiedOutside S E' := (isUnramifiedOutside_iff_le S).2 hE'S
  refine ⟨T₁ ∪ (R ∩ S), hT₁.union (hR.inter_of_left S), Set.subset_union_left,
    Set.union_subset hT₁S Set.inter_subset_right, ?_⟩
  have hE'T : IsUnramifiedOutside (T₁ ∪ (R ∩ S)) E' := by
    refine isUnramifiedOutside_of_ramificationIdx_eq_one fun v hv w hw => ?_
    by_cases hvS : v ∈ S
    · by_contra he
      exact hv (Or.inr ⟨⟨w, hw, he⟩, hvS⟩)
    · exact hE'Sun.ramificationIdx_eq_one hvS w
  have hE'le : E' ≤ maximalUnramifiedOutside K Ω (T₁ ∪ (R ∩ S)) := le_maximalUnramifiedOutside _ hE'T
  intro σ hσ
  apply hEU
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hy : (x : Ω) ∈ maximalUnramifiedOutside K Ω (T₁ ∪ (R ∩ S)) := hE'le ⟨x, hx, rfl⟩
  have h := (mem_ker_restrict _ σ).1 hσ ⟨x, hy⟩
  have hx' : (⟨((⟨(x : Ω), hy⟩ : maximalUnramifiedOutside K Ω (T₁ ∪ (R ∩ S))) : Ω),
      maximalUnramifiedOutside_mono K Ω (Set.union_subset hT₁S Set.inter_subset_right) hy⟩ :
      maximalUnramifiedOutside K Ω S) = x :=
    Subtype.ext rfl
  rw [hx'] at h
  exact h

end GaloisGroupUnramifiedOutside

section Embedding

variable {F Ω : Type u} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
variable (S : Set (HeightOneSpectrum (𝓞 F))) [IsSepClosed Ω]

/-- A finite extension of `F` in which every place outside `S` is unramified embeds over `F`
into `K_S`. -/
theorem nonempty_algHom_maximalUnramifiedOutside (H : Type*) [Field H] [NumberField H]
    [Algebra F H] [FiniteDimensional F H]
    (hH : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 H) v.asIdeal) :
    Nonempty (H →ₐ[F] maximalUnramifiedOutside F Ω S) := by
  let φ : H →ₐ[F] Ω := IsSepClosed.lift
  let : Algebra H Ω := φ.toRingHom.toAlgebra
  have : IsScalarTower F H Ω := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have : IsGalois H Ω := IsGalois.tower_top_of_isGalois F H Ω
  have : FiniteDimensional F ((⊥ : IntermediateField H Ω).restrictScalars F) :=
    FiniteDimensional.trans F H (⊥ : IntermediateField H Ω)
  have hE : IsUnramifiedOutside S ((⊥ : IntermediateField H Ω).restrictScalars F) :=
    (isUnramifiedOutside_restrictScalars_iff S hH ⊥).2 (isUnramifiedOutside_bot _)
  exact ⟨φ.codRestrict (maximalUnramifiedOutside F Ω S).toSubalgebra fun z =>
    le_maximalUnramifiedOutside S hE (IntermediateField.algebraMap_mem _ z)⟩

end Embedding

end Langlands.Galois
