import Langlands.Galois.RestrictedRamification.MaximalExtension

/-!
# Open subgroups of `G_S` and finite subextensions of `K_S`

Let `K` be a number field, `Ω / K` a Galois extension, `S` a set of finite places of `K`, and `L`
a number field with `K → L → Ω` whose image lies in `K_S`. Then `K_S`, viewed over `L`, is the
maximal extension of `L` in `Ω` unramified outside the places `S_L` of `L` above `S`, and the open
subgroup of `G_S(K)` fixing `L` is isomorphic, as a topological group, to `G_{S_L}(L)`. Every open
subgroup of `G_S(K)` is of this form.

The first section is field theory for an arbitrary tower `F → L → Ω`: two intermediate fields
`E` of `Ω / F` and `E'` of `Ω / L` with `E'.restrictScalars F = E` have the same elements, and the
subgroup of `Gal(E / F)` fixing `L` is `Gal(E' / L)`.
-/

namespace Langlands.Galois

open NumberField IsDedekindDomain

noncomputable section

section Abstract

variable {F L Ω : Type*} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
  [IsScalarTower F L Ω] {E : IntermediateField F Ω} {E' : IntermediateField L Ω}
  (h : E'.restrictScalars F = E)

include h in
theorem mem_of_restrictScalars_eq {x : Ω} (hx : x ∈ E') : x ∈ E := by
  rw [← h]
  exact hx

include h in
theorem mem_of_restrictScalars_eq' {x : Ω} (hx : x ∈ E) : x ∈ E' := by
  rw [← h] at hx
  exact hx

/-- The identity of the common underlying set of `E` and `E'`, as an `F`-algebra isomorphism. -/
def fieldEquivOfRestrictScalarsEq : E ≃ₐ[F] E' where
  toFun x := ⟨x.1, mem_of_restrictScalars_eq' h x.2⟩
  invFun y := ⟨y.1, mem_of_restrictScalars_eq h y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp]
theorem coe_fieldEquivOfRestrictScalarsEq (x : E) :
    ((fieldEquivOfRestrictScalarsEq h x : E') : Ω) = x :=
  rfl

@[simp]
theorem coe_fieldEquivOfRestrictScalarsEq_symm (y : E') :
    (((fieldEquivOfRestrictScalarsEq h).symm y : E) : Ω) = y :=
  rfl

/-- The embedding of `L` into `E`. -/
def embeddingOfRestrictScalarsEq : L →ₐ[F] E :=
  (IsScalarTower.toAlgHom F L Ω).codRestrict E.toSubalgebra fun x =>
    mem_of_restrictScalars_eq h (E'.algebraMap_mem x)

@[simp]
theorem coe_embeddingOfRestrictScalarsEq (x : L) :
    ((embeddingOfRestrictScalarsEq h x : E) : Ω) = algebraMap L Ω x :=
  rfl

theorem fieldEquivOfRestrictScalarsEq_embedding (x : L) :
    fieldEquivOfRestrictScalarsEq h (embeddingOfRestrictScalarsEq h x) = algebraMap L E' x :=
  rfl

/-- The subgroup of `Gal(E / F)` fixing the image of `L`. -/
def fixingOfRestrictScalarsEq : Subgroup Gal(E/F) :=
  (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup

theorem mem_fixingOfRestrictScalarsEq_iff (σ : Gal(E/F)) :
    σ ∈ fixingOfRestrictScalarsEq h ↔
      ∀ x : L, σ (embeddingOfRestrictScalarsEq h x) = embeddingOfRestrictScalarsEq h x := by
  change σ ∈ (embeddingOfRestrictScalarsEq h).fieldRange.fixingSubgroup ↔ _
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hσ x
    exact hσ _ ⟨x, rfl⟩
  · rintro hσ _ ⟨x, rfl⟩
    exact hσ x

/-- An element of `Gal(E / F)` fixing `L`, as an element of `Gal(E' / L)`. -/
def autOfRestrictScalarsEq (σ : Gal(E/F)) (hσ : σ ∈ fixingOfRestrictScalarsEq h) : Gal(E'/L) :=
  AlgEquiv.ofRingEquiv (f := ((fieldEquivOfRestrictScalarsEq h).symm.toRingEquiv.trans
      σ.toRingEquiv).trans (fieldEquivOfRestrictScalarsEq h).toRingEquiv) fun x => by
    change fieldEquivOfRestrictScalarsEq h (σ (embeddingOfRestrictScalarsEq h x)) = _
    rw [(mem_fixingOfRestrictScalarsEq_iff h σ).1 hσ x]
    rfl

/-- An element of `Gal(E' / L)` as an element of `Gal(E / F)`. -/
def autOfRestrictScalarsEqInv (τ : Gal(E'/L)) : Gal(E/F) :=
  (fieldEquivOfRestrictScalarsEq h).trans ((τ.restrictScalars F).trans
    (fieldEquivOfRestrictScalarsEq h).symm)

theorem autOfRestrictScalarsEqInv_mem (τ : Gal(E'/L)) :
    autOfRestrictScalarsEqInv h τ ∈ fixingOfRestrictScalarsEq h := by
  rw [mem_fixingOfRestrictScalarsEq_iff]
  intro x
  apply Subtype.ext
  change ((τ (algebraMap L E' x) : E') : Ω) = algebraMap L Ω x
  rw [τ.commutes]
  rfl

/-- The subgroup of `Gal(E / F)` fixing `L` is `Gal(E' / L)`. -/
def fixingMulEquivOfRestrictScalarsEq : fixingOfRestrictScalarsEq h ≃* Gal(E'/L) where
  toFun σ := autOfRestrictScalarsEq h σ.1 σ.2
  invFun τ := ⟨autOfRestrictScalarsEqInv h τ, autOfRestrictScalarsEqInv_mem h τ⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coe_fixingMulEquivOfRestrictScalarsEq_apply (σ : fixingOfRestrictScalarsEq h) (x : E') :
    ((fixingMulEquivOfRestrictScalarsEq h σ x : E') : Ω) =
      ((σ : Gal(E/F)) ((fieldEquivOfRestrictScalarsEq h).symm x) : Ω) :=
  rfl

theorem fieldEquivOfRestrictScalarsEq_apply_apply (σ : fixingOfRestrictScalarsEq h) (x : E) :
    fieldEquivOfRestrictScalarsEq h ((σ : Gal(E/F)) x) =
      fixingMulEquivOfRestrictScalarsEq h σ (fieldEquivOfRestrictScalarsEq h x) :=
  rfl

theorem coe_fixingMulEquivOfRestrictScalarsEq_symm_apply (τ : Gal(E'/L)) (x : E) :
    (((((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) x :
      E) : Ω) = (τ (fieldEquivOfRestrictScalarsEq h x) : Ω) :=
  rfl

theorem continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm [Algebra.IsIntegral L E'] :
    Continuous fun τ : Gal(E'/L) =>
      (((fixingMulEquivOfRestrictScalarsEq h).symm τ : fixingOfRestrictScalarsEq h) : Gal(E/F)) := by
  let f : Gal(E'/L) →* Gal(E/F) :=
    (fixingOfRestrictScalarsEq h).subtype.comp (fixingMulEquivOfRestrictScalarsEq h).symm.toMonoidHom
  change Continuous f
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨K, hK, hKs⟩ := (krullTopology_mem_nhds_one_iff F E s).1 hs
  classical
  let b := Module.finBasis F K
  let K' : IntermediateField L E' :=
    IntermediateField.adjoin L (Set.range fun i => fieldEquivOfRestrictScalarsEq h (b i : E))
  have hK' : FiniteDimensional L K' :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  rw [Filter.mem_map]
  refine Filter.mem_of_superset
    ((krullTopology_mem_nhds_one_iff L E' _).2 ⟨K', hK', le_rfl⟩) fun τ hτ => hKs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
  have hb : ∀ i, f τ (b i : E) = b i := fun i => by
    apply Subtype.ext
    change ((τ (fieldEquivOfRestrictScalarsEq h (b i : E)) : E') : Ω) = _
    rw [hτ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)]
    rfl
  intro y hy
  have hy' : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i : E) := by
    have := congrArg K.val (b.sum_repr ⟨y, hy⟩)
    rw [map_sum] at this
    simp only [map_smul] at this
    exact this.symm
  rw [hy', map_sum]
  simp only [map_smul, hb]

end Abstract

section Fields

variable {K L Ω : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]
variable (S : Set (HeightOneSpectrum (𝓞 K)))

theorem exists_le_of_algebraMap_mem (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsUnramifiedOutside S E ∧
      ∀ x : L, algebraMap L Ω x ∈ E := by
  classical
  let b := Module.finBasis K L
  obtain ⟨E, hf, hu, hE⟩ := exists_subset_of_subset_maximalUnramifiedOutside S
    (Finset.univ.image fun i => algebraMap L Ω (b i)) fun x hx => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      exact hL (b i)
  refine ⟨E, hf, hu, fun x => ?_⟩
  have hx : algebraMap L Ω x = ∑ i, b.repr x i • algebraMap L Ω (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    change IsScalarTower.toAlgHom K L Ω _ = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [hx]
  exact sum_mem fun i _ => E.smul_mem (hE _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

/-- A number field `L` inside `K_S` is unramified over `K` outside `S`. -/
theorem isUnramifiedIn_of_algebraMap_mem
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) :
    ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  obtain ⟨E, hf, hu, hE⟩ := exists_le_of_algebraMap_mem S hL
  let j : L →ₐ[K] E := (IsScalarTower.toAlgHom K L Ω).codRestrict E.toSubalgebra hE
  let _ : Algebra L E := j.toRingHom.toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have := NumberField.of_module_finite K E
  intro v hv P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 E)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have h := ((isUnramifiedAt_tower_iff (F := K) (L := L) Q).1 (hu v hv Q hQ this)).1
  have e : P = Q.under (𝓞 L) := Ideal.over_def Q P
  subst e
  exact h

/-- For a number field `L` inside `K_S`, the maximal extension of `L` in `Ω` unramified outside the
places above `S` is `K_S`. -/
theorem restrictScalars_maximalUnramifiedOutside
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) :
    (maximalUnramifiedOutside L Ω (finitePlacesAbove L S)).restrictScalars K =
      maximalUnramifiedOutside K Ω S := by
  have hLu := isUnramifiedIn_of_algebraMap_mem S hL
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  ext x
  rw [IntermediateField.mem_restrictScalars]
  constructor
  · intro hx
    obtain ⟨M, hf, hu, hxM⟩ := (mem_maximalUnramifiedOutside_iff (finitePlacesAbove L S)).1 hx
    have : FiniteDimensional K (M.restrictScalars K) := FiniteDimensional.trans K L M
    exact le_maximalUnramifiedOutside S
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).2 hu) hxM
  · intro hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maximalUnramifiedOutside_iff S).1 hx
    obtain ⟨E₀, hf₀, hu₀, hE₀⟩ := exists_le_of_algebraMap_mem S hL
    let E' : IntermediateField K Ω := E₀ ⊔ E
    have hE' : ∀ y : L, algebraMap L Ω y ∈ E'.toSubfield := fun y =>
      le_sup_left (α := IntermediateField K Ω) (hE₀ y)
    let M : IntermediateField L Ω := E'.toSubfield.toIntermediateField hE'
    have hMF : M.restrictScalars K = E' := by
      ext y
      exact Iff.rfl
    have : FiniteDimensional K M := (inferInstance : FiniteDimensional K E')
    have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
    have hMu : IsUnramifiedOutside S (M.restrictScalars K) := by
      rw [hMF]
      exact hu₀.sup hu
    exact le_maximalUnramifiedOutside (finitePlacesAbove L S)
      ((isUnramifiedOutside_restrictScalars_iff S hLu M).1 hMu)
      (le_sup_right (α := IntermediateField K Ω) hxE)

variable {S} (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- `K_S`, viewed as the maximal extension of `L` unramified outside the places above `S`. -/
abbrev maximalUnramifiedOutsideEquiv :
    maximalUnramifiedOutside K Ω S ≃ₐ[K] maximalUnramifiedOutside L Ω (finitePlacesAbove L S) :=
  fieldEquivOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL)

/-- The embedding of `L` into `K_S`. -/
abbrev embeddingMaximalUnramifiedOutside : L →ₐ[K] maximalUnramifiedOutside K Ω S :=
  embeddingOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL)

instance finiteDimensional_fieldRange_embeddingMaximalUnramifiedOutside :
    FiniteDimensional K (embeddingMaximalUnramifiedOutside hL).fieldRange :=
  LinearEquiv.finiteDimensional (embeddingMaximalUnramifiedOutside hL).equivFieldRange.toLinearEquiv

end Fields

namespace GaloisGroupUnramifiedOutside

variable {K L Ω : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
  [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsGalois K Ω]

variable (S : Set (HeightOneSpectrum (𝓞 K)))
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

/-- The open subgroup of `G_S` fixing a number field `L` with `K → L → Ω` that lies in `K_S`. -/
def fixingOpenSubgroup : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S) :=
  ⟨fixingOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL),
    (embeddingMaximalUnramifiedOutside hL).fieldRange.fixingSubgroup_isOpen⟩

theorem coe_fixingOpenSubgroup :
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) =
      fixingOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL) :=
  rfl

theorem mem_fixingOpenSubgroup_iff (σ : GaloisGroupUnramifiedOutside K Ω S) :
    σ ∈ fixingOpenSubgroup S hL ↔
      ∀ x : L, σ (embeddingMaximalUnramifiedOutside hL x) = embeddingMaximalUnramifiedOutside hL x :=
  mem_fixingOfRestrictScalarsEq_iff _ σ

/-- The open subgroup of `G_S(K)` fixing `L` is `G_{S_L}(L)`, for `S_L` the places of `L` above
`S`. -/
def fixingOpenSubgroupEquiv :
    (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≃ₜ*
      GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S) :=
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  have hc : Continuous (fixingMulEquivOfRestrictScalarsEq
      (restrictScalars_maximalUnramifiedOutside S hL)).symm :=
    (continuous_coe_fixingMulEquivOfRestrictScalarsEq_symm _).subtype_mk _
  let e := hc.homeoOfEquivCompactToT2
    (f := (fixingMulEquivOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL)).symm.toEquiv)
  { fixingMulEquivOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL) with
    continuous_toFun := e.symm.continuous
    continuous_invFun := hc }

theorem fixingOpenSubgroupEquiv_toMulEquiv : (fixingOpenSubgroupEquiv S hL).toMulEquiv =
    fixingMulEquivOfRestrictScalarsEq (restrictScalars_maximalUnramifiedOutside S hL) :=
  rfl

variable {S}

theorem coe_fixingOpenSubgroupEquiv_apply
    (σ : (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    (x : maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) :
    ((fixingOpenSubgroupEquiv S hL σ x : maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) : Ω) =
      ((σ : GaloisGroupUnramifiedOutside K Ω S) ((maximalUnramifiedOutsideEquiv hL).symm x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_apply _ σ x

theorem maximalUnramifiedOutsideEquiv_apply_apply
    (σ : (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    (x : maximalUnramifiedOutside K Ω S) :
    maximalUnramifiedOutsideEquiv hL ((σ : GaloisGroupUnramifiedOutside K Ω S) x) =
      fixingOpenSubgroupEquiv S hL σ (maximalUnramifiedOutsideEquiv hL x) :=
  fieldEquivOfRestrictScalarsEq_apply_apply _ σ x

theorem coe_fixingOpenSubgroupEquiv_symm_apply
    (τ : GaloisGroupUnramifiedOutside L Ω (finitePlacesAbove L S))
    (x : maximalUnramifiedOutside K Ω S) :
    (((((fixingOpenSubgroupEquiv S hL).symm τ :
        (fixingOpenSubgroup S hL : Subgroup (GaloisGroupUnramifiedOutside K Ω S))) :
          GaloisGroupUnramifiedOutside K Ω S) x : maximalUnramifiedOutside K Ω S) : Ω) =
      (τ (maximalUnramifiedOutsideEquiv hL x) : Ω) :=
  coe_fixingMulEquivOfRestrictScalarsEq_symm_apply _ τ x

end GaloisGroupUnramifiedOutside

namespace GaloisGroupUnramifiedOutside

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))}

theorem mem_fixingOpenSubgroup_iff_of_image {L : Type*} [Field L] [NumberField L] [Algebra K L]
    [Algebra L Ω] [IsScalarTower K L Ω]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (T : Set (maximalUnramifiedOutside K Ω S))
    (hT : ∀ x : L, embeddingMaximalUnramifiedOutside hL x ∈ T)
    (hT' : ∀ y ∈ T, ∃ x : L, embeddingMaximalUnramifiedOutside hL x = y)
    (σ : GaloisGroupUnramifiedOutside K Ω S) :
    σ ∈ fixingOpenSubgroup S hL ↔ ∀ y ∈ T, σ y = y := by
  rw [mem_fixingOpenSubgroup_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hT' y hy
    exact h x
  · intro h x
    exact h _ (hT x)

/-- Every open subgroup of `G_S` is the subgroup fixing a finite extension of `K` inside `K_S`. -/
theorem exists_fixingOpenSubgroup_eq (U : OpenSubgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField L)
      (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S),
      fixingOpenSubgroup S hL = U := by
  let KS := maximalUnramifiedOutside K Ω S
  let H : ClosedSubgroup Gal(KS/K) := ⟨(U : Subgroup Gal(KS/K)), U.isClosed⟩
  let E : IntermediateField K KS := IntermediateField.fixedField (H : Subgroup Gal(KS/K))
  have hEV : E.fixingSubgroup = (U : Subgroup Gal(KS/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField H
  have hEfin : FiniteDimensional K E := by
    rw [← InfiniteGalois.isOpen_iff_finite E, hEV]
    exact U.isOpen
  let E' : IntermediateField K Ω := E.map KS.val
  have hE'fin : FiniteDimensional K E' :=
    LinearEquiv.finiteDimensional (E.equivMap KS.val).toLinearEquiv
  have : NumberField E' := NumberField.of_module_finite K E'
  have hKS : ∀ x : E', algebraMap E' Ω x ∈ KS := by
    intro x
    obtain ⟨y, -, hy⟩ := (x.2 : (x : Ω) ∈ E')
    change (x : Ω) ∈ KS
    rw [← hy]
    exact y.2
  refine ⟨E', inferInstance, hKS, ?_⟩
  ext σ
  rw [mem_fixingOpenSubgroup_iff_of_image hKS (E : Set KS)]
  · change _ ↔ σ ∈ (U : Subgroup Gal(KS/K))
    rw [← hEV, IntermediateField.mem_fixingSubgroup_iff]
    rfl
  · intro x
    obtain ⟨y, hy, hyx⟩ := (x.2 : (x : Ω) ∈ E')
    have hy' : y ∈ (E : Set KS) := hy
    convert hy' using 1
    apply Subtype.ext
    exact hyx.symm
  · intro y hy
    exact ⟨⟨(y : Ω), ⟨y, hy, rfl⟩⟩, Subtype.ext rfl⟩

end GaloisGroupUnramifiedOutside

end

end Langlands.Galois

namespace Langlands.Galois

open NumberField IsDedekindDomain

universe u

noncomputable section

section FixedElements

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (S : Set (HeightOneSpectrum (𝓞 K)))

/-- An element of `K_S` fixed by the subgroup fixing a finite extension `L ⊆ K_S` lies in `L`. -/
theorem exists_embeddingMaximalUnramifiedOutside_eq {L : IntermediateField K Ω} [NumberField L]
    (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)
    (x : maximalUnramifiedOutside K Ω S)
    (hx : ∀ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL, σ x = x) :
    ∃ y : L, embeddingMaximalUnramifiedOutside hL y = x := by
  let E : IntermediateField K (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).fieldRange
  have hE : E.fixingSubgroup =
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) := by
    ext σ
    change _ ↔ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL
    rw [IntermediateField.mem_fixingSubgroup_iff,
      GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff]
    constructor
    · exact fun h y => h _ ⟨y, rfl⟩
    · rintro h _ ⟨y, rfl⟩
      exact h y
  have hmem : x ∈ IntermediateField.fixedField E.fixingSubgroup := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    rw [hE] at hσ
    exact hx σ hσ
  rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
  exact hmem

end FixedElements

section Quotient

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

attribute [local instance 2000] IsSepClosure.isGalois

/-- The subgroup fixing `L` is the subgroup fixing the image of `L` in `K_S`. -/
theorem coe_fixingOpenSubgroup_eq_fixingSubgroup :
    (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) =
      (embeddingMaximalUnramifiedOutside hL).fieldRange.fixingSubgroup :=
  rfl

/-- If the subgroup of `G_S` fixing `L` is normal, `L / K` is Galois. -/
theorem isGalois_of_fixingOpenSubgroup_normal
    (hN : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal) : IsGalois K L := by
  rw [coe_fixingOpenSubgroup_eq_fixingSubgroup] at hN
  have := (InfiniteGalois.normal_iff_isGalois _).1 hN
  exact IsGalois.of_algEquiv (embeddingMaximalUnramifiedOutside hL).equivFieldRange.symm

variable [IsGalois K L]

/-- Restriction `G_S → Gal(L/K)`. -/
def galRestrict : GaloisGroupUnramifiedOutside K Ω S →* (L ≃ₐ[K] L) :=
  letI : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  haveI : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  AlgEquiv.restrictNormalHom L

theorem galRestrict_apply (σ : GaloisGroupUnramifiedOutside K Ω S) (x : L) :
    embeddingMaximalUnramifiedOutside hL (galRestrict hL σ x) =
      σ (embeddingMaximalUnramifiedOutside hL x) :=
  letI : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  haveI : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  AlgEquiv.restrictNormal_commutes σ L x

theorem algebraMap_galRestrict_apply (σ : GaloisGroupUnramifiedOutside K Ω S) (x : L) :
    algebraMap L Ω (galRestrict hL σ x) =
      ((σ (embeddingMaximalUnramifiedOutside hL x) : maximalUnramifiedOutside K Ω S) : Ω) := by
  rw [← galRestrict_apply hL σ x]
  rfl

theorem galRestrict_surjective : Function.Surjective (galRestrict hL) :=
  letI : Algebra L (maximalUnramifiedOutside K Ω S) :=
    (embeddingMaximalUnramifiedOutside hL).toRingHom.toAlgebra
  haveI : IsScalarTower K L (maximalUnramifiedOutside K Ω S) :=
    IsScalarTower.of_algebraMap_eq fun a => ((embeddingMaximalUnramifiedOutside hL).commutes a).symm
  AlgEquiv.restrictNormalHom_surjective (maximalUnramifiedOutside K Ω S)

theorem mem_ker_galRestrict_iff (σ : GaloisGroupUnramifiedOutside K Ω S) :
    σ ∈ (galRestrict hL).ker ↔ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL := by
  rw [MonoidHom.mem_ker, GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff, AlgEquiv.ext_iff]
  refine forall_congr' fun x => ?_
  rw [← galRestrict_apply, AlgEquiv.one_apply]
  exact ⟨fun h => by rw [h], fun h => (embeddingMaximalUnramifiedOutside hL).injective h⟩

theorem ker_galRestrict :
    (galRestrict hL).ker =
      (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :=
  Subgroup.ext (mem_ker_galRestrict_iff hL)

variable [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
  Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]

/-- `G_S / P ≅ Gal(L/K)` for the subgroup `P` fixing `L`. -/
def quotientGalEquiv :
    GaloisGroupUnramifiedOutside K Ω S ⧸ (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)) ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_galRestrict hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (galRestrict_surjective hL))

@[simp]
theorem quotientGalEquiv_mk (σ : GaloisGroupUnramifiedOutside K Ω S) :
    quotientGalEquiv hL (QuotientGroup.mk σ) = galRestrict hL σ :=
  rfl

theorem card_gal_eq_index :
    Nat.card (L ≃ₐ[K] L) = (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).index :=
  (Nat.card_congr (quotientGalEquiv hL).toEquiv).symm

end Quotient

end

end Langlands.Galois
