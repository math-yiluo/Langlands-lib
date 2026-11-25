import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Primary
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.TwistCount
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.UnitLattice
import Langlands.GaloisCohomology.Global.Units.Kummer
import Langlands.GaloisCohomology.Local.EulerCharacteristic.Kummer

/-!
# The Kummer sequence of `G_S` over a subgroup `G_S(L)`

Let `K` be a number field, `Ω` a separable closure, `S` a finite set of finite places of `K`, and
`L ⊆ K_S` finite Galois over `K`, with `P ⊆ G_S` the subgroup fixing `L`. The cohomology groups
`Aᵢ = Hⁱ(P, 𝒪_Sˣ)` of the `S`-units of `K_S` are `Gal(L/K)`-modules by conjugation. This file
identifies `A₀` with the `S`-units of `L` as a `Gal(L/K)`-module (`sUnitsOfEquivCohomologyZero`,
`sUnitsOfEquivCohomologyZero_smul`), shows that `A₁` is finite (it embeds into the `S_L`-class group
of `L`, `finite_cohomology_one_res_maximalSUnits`), and records the properties of `μ_ℓ` needed for the
coprime twist: `P` acts trivially on it when `μ_ℓ ⊆ L` (`rootsOfUnity_res_trivial`), and it has
dimension one over `𝔽_ℓ` (`finrank_zmodRepOfTorsion_rootsOfUnity`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory Langlands.ProfiniteCohomology Langlands.Galois NumberField IsDedekindDomain
  Langlands.GaloisCohomology.Local

universe u

noncomputable section

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S)

attribute [local instance 2000] IsSepClosure.isGalois

section Zero

/-- A unit of `L` is an `S`-unit of `K_S` exactly when it is an `S`-unit of `L`. -/
theorem map_mem_maximalSUnits_iff {x : Lˣ} :
    Units.map (embeddingMaximalUnramifiedOutside hL : L →* maximalUnramifiedOutside K Ω S) x ∈
      maximalSUnits K Ω S ↔ x ∈ sUnitsOf S L := by
  let f := (embeddingMaximalUnramifiedOutside hL).restrictScalars (S.integer K)
  have hf : Function.Injective f := (embeddingMaximalUnramifiedOutside hL).toRingHom.injective
  constructor
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).1 h.1, (isIntegral_algHom_iff f hf).1 ?_⟩
    have := h.2
    rwa [← map_inv] at this
  · intro h
    refine ⟨(isIntegral_algHom_iff f hf).2 h.1, ?_⟩
    rw [← map_inv]
    exact (isIntegral_algHom_iff f hf).2 h.2

/-- The unit of `K_S` underlying an element of the module of `S`-units of `K_S`. -/
abbrev maximalSUnitsVal (z : Additive (maximalSUnits K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ :=
  ((Additive.toMul z : maximalSUnits K Ω S) : (maximalUnramifiedOutside K Ω S)ˣ)

/-- Smoothness of the restriction of the `S`-units of `K_S` to a subgroup. -/
instance isSmoothRep_res_maximalSUnitsModule (U : Subgroup (GaloisGroupUnramifiedOutside K Ω S)) :
    IsSmoothRep (Rep.res U.subtype (maximalSUnitsModule K Ω S)) :=
  isSmoothRep_res_subtype (maximalSUnitsModule K Ω S) U

/-- The `S`-units of `L` as `P`-invariants of the `S`-units of `K_S`. -/
def sUnitsOfToInvariants :
    Additive (sUnitsOf S L) →+ (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)).ρ.invariants where
  toFun x := ⟨Additive.ofMul ⟨Units.map (embeddingMaximalUnramifiedOutside hL :
      L →* maximalUnramifiedOutside K Ω S) (x.toMul : Lˣ), (map_mem_maximalSUnits_iff hL).2 x.toMul.2⟩,
    fun σ => by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      exact ((GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hL σ.1).1 σ.2 _)⟩
  map_zero' := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_one _
  map_add' x y := by
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact map_mul _ _ _

theorem coe_sUnitsOfToInvariants_apply (x : Additive (sUnitsOf S L)) :
    ((maximalSUnitsVal (sUnitsOfToInvariants hL x).1 : (maximalUnramifiedOutside K Ω S)ˣ) :
        maximalUnramifiedOutside K Ω S) = embeddingMaximalUnramifiedOutside hL ((x.toMul : Lˣ) : L) :=
  rfl

theorem sUnitsOfToInvariants_bijective : Function.Bijective (sUnitsOfToInvariants hL) := by
  constructor
  · intro x y h
    have h' := congrArg (fun z : (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)).ρ.invariants =>
        ((maximalSUnitsVal z.1 : (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S)) h
    simp only at h'
    rw [coe_sUnitsOfToInvariants_apply, coe_sUnitsOfToInvariants_apply] at h'
    exact Additive.toMul.injective (Subtype.ext (Units.ext
      ((embeddingMaximalUnramifiedOutside hL).toRingHom.injective h')))
  · intro y
    let u : (maximalUnramifiedOutside K Ω S)ˣ := maximalSUnitsVal y.1
    have hfix : ∀ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL,
        σ (u : maximalUnramifiedOutside K Ω S) = u := fun σ hσ =>
      congrArg (fun z : Additive (maximalSUnits K Ω S) =>
        ((maximalSUnitsVal z : (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S))
        (y.2 ⟨σ, hσ⟩)
    have hfix' : ∀ σ ∈ GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL,
        σ ((u⁻¹ : (maximalUnramifiedOutside K Ω S)ˣ) : maximalUnramifiedOutside K Ω S) = (u⁻¹ : _) :=
      fun σ hσ => by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hfix σ hσ]
    obtain ⟨a, ha⟩ := exists_eq_embedding_of_forall_fixingOpenSubgroup hL _ hfix
    obtain ⟨b, hb⟩ := exists_eq_embedding_of_forall_fixingOpenSubgroup hL _ hfix'
    have hab : a * b = 1 := (embeddingMaximalUnramifiedOutside hL).toRingHom.injective (by
      rw [map_mul, map_one]
      change embeddingMaximalUnramifiedOutside hL a * embeddingMaximalUnramifiedOutside hL b = 1
      rw [ha, hb, Units.mul_inv])
    let x : Lˣ := ⟨a, b, hab, by rw [mul_comm, hab]⟩
    have hx : Units.map (embeddingMaximalUnramifiedOutside hL : L →* maximalUnramifiedOutside K Ω S) x =
        u := Units.ext ha
    have hmem : x ∈ sUnitsOf S L := by
      rw [← map_mem_maximalSUnits_iff hL, hx]
      exact (Additive.toMul (α := maximalSUnits K Ω S) y.1).2
    refine ⟨Additive.ofMul ⟨x, hmem⟩, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hx

/-- `H⁰(P, 𝒪_Sˣ)` is the group of `S`-units of `L`. -/
def sUnitsOfEquivCohomologyZero :
    Additive (sUnitsOf S L) ≃+ cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 0 :=
  (AddEquiv.ofBijective _ (sUnitsOfToInvariants_bijective hL)).trans
    (zeroIso (Rep.res _ (maximalSUnitsModule K Ω S))).toLinearEquiv.toAddEquiv.symm

variable [IsGalois K L]

include hL in
omit [IsGalois K L] in
theorem embedding_galRestrict_smul [IsGalois K L] (σ : GaloisGroupUnramifiedOutside K Ω S)
    (x : Additive (sUnitsOf S L)) :
    (letI := sUnitsOfAction (K := K) (L := L) S;
      embeddingMaximalUnramifiedOutside hL (((Galois.galRestrict hL σ • x).toMul : Lˣ) : L)) =
      σ (embeddingMaximalUnramifiedOutside hL ((x.toMul : Lˣ) : L)) :=
  Galois.galRestrict_apply hL σ _

/-- The identification of `H⁰(P, 𝒪_Sˣ)` with the `S`-units of `L` is `Gal(L/K)`-equivariant. -/
theorem sUnitsOfEquivCohomologyZero_smul [(GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).Normal]
    (σ : GaloisGroupUnramifiedOutside K Ω S) (x : Additive (sUnitsOf S L)) :
    (letI := sUnitsOfAction (K := K) (L := L) S;
      sUnitsOfEquivCohomologyZero hL (Galois.galRestrict hL σ • x)) =
      (cohomologyConj (maximalSUnitsModule K Ω S) (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)) 0 σ).hom (sUnitsOfEquivCohomologyZero hL x) := by
  let := sUnitsOfAction (K := K) (L := L) S
  change (zeroIso _).inv.hom (sUnitsOfToInvariants hL _) =
    (cohomologyConj _ _ 0 σ).hom ((zeroIso _).inv.hom (sUnitsOfToInvariants hL x))
  rw [cohomologyConj_zeroIso_inv]
  congr 1
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact embedding_galRestrict_smul hL σ x

end Zero

section One

/-- The `S`-units of `K_S` restricted to `P ≅ G_{S_L}(L)` are the `S_L`-units of `L_{S_L} = K_S`. -/
def resMaximalSUnitsHom :
    Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL).symm.toMulEquiv.toMonoidHom
      (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
        Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) ⟶
      maximalSUnitsModule L Ω (finitePlacesAbove L S) :=
  Rep.ofHom ⟨(uliftIntLinearEquivAddHom _ _).symm
    { toFun := fun x => Additive.ofMul ⟨Units.map (maximalUnramifiedOutsideEquiv hL :
          maximalUnramifiedOutside K Ω S →* maximalUnramifiedOutside L Ω (finitePlacesAbove L S))
          (maximalSUnitsVal x), by
        rw [sUnitsOf_finitePlacesAbove_eq (L := L) S]
        have hx := (Additive.toMul (α := maximalSUnits K Ω S) x).2
        let f := ((maximalUnramifiedOutsideEquiv hL).toAlgHom).restrictScalars (S.integer K)
        have hf : Function.Injective f := (maximalUnramifiedOutsideEquiv hL).injective
        refine ⟨(isIntegral_algHom_iff f hf).2 hx.1, ?_⟩
        rw [← map_inv]
        exact (isIntegral_algHom_iff f hf).2 hx.2⟩
      map_zero' := Additive.toMul.injective (Subtype.ext (map_one _))
      map_add' := fun _ _ => Additive.toMul.injective (Subtype.ext (map_mul _ _ _)) },
    fun τ => LinearMap.ext fun x => by
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      apply Subtype.ext
      exact (GaloisGroupUnramifiedOutside.coe_fixingOpenSubgroupEquiv_symm_apply hL τ _)⟩

theorem resMaximalSUnitsHom_bijective : Function.Bijective (resMaximalSUnitsHom hL).hom := by
  constructor
  · intro x y h
    have h' := congrArg (fun z : Additive (sUnitsOf (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L)))
      (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) =>
        (((Additive.toMul z : sUnitsOf _ _) : (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))ˣ) :
          maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) h
    exact Additive.toMul.injective (Subtype.ext (Units.ext
      ((maximalUnramifiedOutsideEquiv hL).injective h')))
  · intro y
    let u : (maximalUnramifiedOutside K Ω S)ˣ := Units.map
      ((maximalUnramifiedOutsideEquiv hL).symm : maximalUnramifiedOutside L Ω (finitePlacesAbove L S) →*
        maximalUnramifiedOutside K Ω S)
        ((Additive.toMul (α := sUnitsOf (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L)))
          (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) y : _) : _ˣ)
    have hu : u ∈ maximalSUnits K Ω S := by
      have hy := (Additive.toMul (α := sUnitsOf (finitePlacesAbove L S : Set (HeightOneSpectrum (𝓞 L)))
          (maximalUnramifiedOutside L Ω (finitePlacesAbove L S))) y).2
      replace hy := (SetLike.ext_iff.1 (sUnitsOf_finitePlacesAbove_eq (L := L)
        (E := maximalUnramifiedOutside L Ω (finitePlacesAbove L S)) S) _).1 hy
      let f := ((maximalUnramifiedOutsideEquiv hL).symm.toAlgHom).restrictScalars (S.integer K)
      have hf : Function.Injective f := (maximalUnramifiedOutsideEquiv hL).symm.injective
      refine ⟨(isIntegral_algHom_iff f hf).2 hy.1, ?_⟩
      rw [← map_inv]
      exact (isIntegral_algHom_iff f hf).2 hy.2
    refine ⟨Additive.ofMul ⟨u, hu⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact (maximalUnramifiedOutsideEquiv hL).apply_symm_apply _

/-- `H¹(P, 𝒪_Sˣ)` is finite: it is `H¹(G_{S_L}(L), 𝒪_{S_L}ˣ)`, which embeds into the
`S_L`-class group of `L`. -/
theorem finite_cohomology_one_res_maximalSUnits :
    Finite (cohomology (Rep.res (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)).subtype (maximalSUnitsModule K Ω S)) 1) := by
  let e := GaloisGroupUnramifiedOutside.fixingOpenSubgroupEquiv S hL
  have : IsGalois L Ω := IsGalois.tower_top_of_isGalois K L Ω
  have : IsSmoothRep (maximalSUnitsModule L Ω (finitePlacesAbove L S)) := inferInstance
  have hiso := isIso_map_of_mulEquiv e.symm.toMulEquiv e.symm.continuous e.continuous
    (resMaximalSUnitsHom hL) (resMaximalSUnitsHom_bijective hL) 1
  have hinj : Function.Injective
      (map ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous⟩ (resMaximalSUnitsHom hL) 1).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : Finite (cohomology (maximalSUnitsModule L Ω (finitePlacesAbove L S)) 1) :=
    Finite.of_injective _ (cohomologyOneSUnitsToSPicard_injective (Ω := Ω) (finitePlacesAbove L S))
  exact Finite.of_injective _ hinj

end One

section Roots

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The `ℓ`-th roots of unity of `K_S` are fixed by the subgroup fixing `L` when `μ_ℓ ⊆ L`. -/
theorem rootsOfUnity_res_trivial (hζ : ∃ ζ : L, IsPrimitiveRoot ζ ℓ)
    (g : (GaloisGroupUnramifiedOutside.fixingOpenSubgroup S hL :
      Subgroup (GaloisGroupUnramifiedOutside K Ω S)))
    (t : rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ) :
    (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ).ρ g t = t := by
  obtain ⟨ζ, hζ⟩ := hζ
  have hℓ : ℓ.Prime := Fact.out
  have hζ' : IsPrimitiveRoot (embeddingMaximalUnramifiedOutside hL ζ) ℓ :=
    hζ.map_of_injective (embeddingMaximalUnramifiedOutside hL).injective
  let s' : (maximalUnramifiedOutside K Ω S)ˣ :=
    ((Additive.toMul (α := rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) t :
      rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) : (maximalUnramifiedOutside K Ω S)ˣ)
  let s : maximalUnramifiedOutside K Ω S := s'
  have hs : s ^ ℓ = 1 := by
    have h1 : s' ^ ℓ = 1 :=
      (mem_rootsOfUnity ℓ _).1 (Additive.toMul (α := rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)) t).2
    change (s' : maximalUnramifiedOutside K Ω S) ^ ℓ = 1
    rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hs
  rw [rootsOfUnityModule_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  rw [toMul_ofMul, coe_galRootsOfUnityHom_apply]
  change (g : GaloisGroupUnramifiedOutside K Ω S) s = s
  rw [← hi, map_pow, (GaloisGroupUnramifiedOutside.mem_fixingOpenSubgroup_iff S hL _).1 g.2 ζ]

/-- `μ_ℓ(K_S)` has `ℓ` elements, so dimension one over `𝔽_ℓ`. -/
theorem finrank_zmodRepOfTorsion_rootsOfUnity
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((ℓ : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    Module.finrank (ULift.{u} (ZMod ℓ)) (zmodRepOfTorsion ℓ
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) = 1 := by
  have hℓ : ℓ.Prime := Fact.out
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hK : ((ℓ : ℕ) : K) ≠ 0 := by
    have : CharZero K := inferInstance
    exact_mod_cast hℓ.ne_zero
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hΩ : NeZero ((ℓ : ℕ) : Ω) := ⟨by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero _).mpr hK⟩
  -- the roots of unity of `Ω` lie in `K_S`
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω ℓ
  have hmem : ζ ∈ maximalUnramifiedOutside K Ω S :=
    mem_maximalUnramifiedOutside_of_pow_eq_one S hℓ.ne_zero
      (fun v hv h => hv (hS v h)) hζ.pow_eq_one
  have hζS : IsPrimitiveRoot (⟨ζ, hmem⟩ : maximalUnramifiedOutside K Ω S) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := (maximalUnramifiedOutside K Ω S).val) hζ
      (maximalUnramifiedOutside K Ω S).val.injective
  have hcard : Nat.card (zmodRepOfTorsion ℓ
      (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) = ℓ ^ 1 := by
    rw [pow_one]
    exact (Nat.card_congr (Additive.toMul (α := rootsOfUnity ℓ (maximalUnramifiedOutside K Ω S)))).trans
      hζS.card_rootsOfUnity
  have : Finite (zmodRepOfTorsion ℓ (rootsOfUnityModule K (maximalUnramifiedOutside K Ω S) ℓ)
      (nsmul_galRootsOfUnity_eq_zero ℓ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  exact finrank_eq_of_natCard_zmod ℓ hcard

end Roots

end

end Langlands.GaloisCohomology
