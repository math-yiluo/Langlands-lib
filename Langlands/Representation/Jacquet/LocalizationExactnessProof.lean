import Langlands.Representation.Jacquet.LocalizationExactnessStatement
import Langlands.Representation.Jacquet.ExactProof

namespace Langlands.Jacquet.Localization

universe uG uV uW uX

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V]
variable [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

omit [TopologicalSpace G] in
/-- Restricting the subgroup only removes character relations. -/
theorem relations_comp_subgroup_le (ρ : Representation ℂ G V)
    (U : Subgroup G) (θ : U →* ℂˣ) (K : Subgroup U) :
    relations (ρ.comp U.subtype) K (θ.comp K.subtype) ≤ relations ρ U θ := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact sub_mem_relations ρ U θ u.val v

/-- Finite span membership is detected in one compact subgroup. -/
theorem mem_relations_iff_compact
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (ρ : Representation ℂ G V) (v : V) :
    v ∈ relations ρ U θ ↔ ∃ K : Subgroup U, IsCompact (K : Set U) ∧
      v ∈ relations (ρ.comp U.subtype) K (θ.comp K.subtype) := by
  classical
  constructor
  · intro hv
    obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
    choose uv huv using hT
    let s : Finset U := T.attach.image (fun x => (uv x.property).1)
    obtain ⟨K, hK, hsK⟩ := hU s (Set.Finite.isCompact (Finset.finite_toSet s))
    refine ⟨K, hK, ?_⟩
    apply (Submodule.span_le.mpr ?_) hvT
    intro x hx
    have hu : (uv hx).1 ∈ K :=
      hsK (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
    rw [← huv hx]
    exact sub_mem_relations (ρ.comp U.subtype) K (θ.comp K.subtype)
      ⟨(uv hx).1, hu⟩ (uv hx).2
  · rintro ⟨K, _, hv⟩
    exact relations_comp_subgroup_le ρ U θ K hv

omit [TopologicalSpace G] in
/-- Inverse-character twisting converts the actual character span to coinvariant relations. -/
theorem relations_eq_twisted_ker (ρ : Representation ℂ G V)
    (U : Subgroup G) (θ : U →* ℂˣ) :
    relations ρ U θ = Representation.Coinvariants.ker (twist θ⁻¹ (ρ.comp U.subtype)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have h := (Representation.Coinvariants.ker (twist θ⁻¹ (ρ.comp U.subtype))).smul_mem
      (θ u : ℂ) (Representation.Coinvariants.sub_mem_ker
        (ρ := twist θ⁻¹ (ρ.comp U.subtype)) u v)
    simpa [twist, smul_sub, smul_smul] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    have h := (relations ρ U θ).smul_mem (((θ u)⁻¹ : ℂˣ) : ℂ)
      (sub_mem_relations ρ U θ u v)
    simpa [twist, smul_sub, smul_smul] using h

omit [TopologicalSpace G] in
/-- A surjection maps the character relation submodule onto the target relation submodule. -/
theorem relations_map_of_surjective {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (U : Subgroup G) (θ : U →* ℂˣ)
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) :
    (relations ρ U θ).map p.toLinearMap = relations σ U θ := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change p (ρ u v - (θ u : ℂ) • v) ∈ relations σ U θ
    rw [map_sub, map_smul, p.isIntertwining]
    exact sub_mem_relations σ U θ u (p v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨ρ u v - (θ u : ℂ) • v, sub_mem_relations ρ U θ u v, ?_⟩
    change p (ρ u v - (θ u : ℂ) • v) = _
    rw [map_sub, map_smul, p.isIntertwining]

omit [TopologicalSpace G] in
/-- The actual localization map preserves surjectivity without topology. -/
theorem map_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (U : Subgroup G) (θ : U →* ℂˣ) (M : Subgroup G)
    (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) :
    Function.Surjective (map U θ M hMU hθ p) := by
  intro x
  obtain ⟨w, rfl⟩ := mk_surjective σ U θ x
  obtain ⟨v, rfl⟩ := hp w
  exact ⟨mk ρ U θ v, rfl⟩

omit [TopologicalSpace G] in
/-- Middle exactness is an algebraic property of the actual quotient maps. -/
theorem map_range_eq_ker {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    {τ : Representation ℂ G X} (U : Subgroup G) (θ : U →* ℂˣ)
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    (i : ρ.IntertwiningMap σ) (p : σ.IntertwiningMap τ) (hp : Function.Surjective p)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    LinearMap.range (map U θ M hMU hθ i).toLinearMap =
      LinearMap.ker (map U θ M hMU hθ p).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨v, rfl⟩ := mk_surjective ρ U θ x
    have hpiv : p (i v) = 0 := by
      change i v ∈ LinearMap.ker p.toLinearMap
      rw [← hex]
      exact ⟨v, rfl⟩
    change mk τ U θ (p (i v)) = 0
    rw [hpiv, map_zero]
  · intro x hx
    obtain ⟨w, rfl⟩ := mk_surjective σ U θ x
    have hpw : p w ∈ relations τ U θ := (mk_eq_zero τ U θ _).mp hx
    rw [← relations_map_of_surjective U θ p hp] at hpw
    obtain ⟨z, hz, hpz⟩ := hpw
    change p z = p w at hpz
    have hwz : w - z ∈ LinearMap.range i.toLinearMap := by
      rw [hex]
      change p (w - z) = 0
      rw [map_sub, hpz, sub_self]
    obtain ⟨v, hv⟩ := hwz
    refine ⟨mk ρ U θ v, ?_⟩
    change mk σ U θ (i v) = mk σ U θ w
    change i v = w - z at hv
    rw [hv, map_sub, (mk_eq_zero σ U θ z).mpr hz, sub_zero]

/-- Compact detection and finite averaging give injectivity for character localization. -/
theorem map_injective_of_smooth [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U)
    (θ : U →* ℂˣ) (hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)))
    (M : Subgroup G) (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (i : ρ.IntertwiningMap σ) (hi : Function.Injective i) (hσ : IsSmooth σ) :
    Function.Injective (map U θ M hMU hθ i) := by
  suffices hz : ∀ x, map U θ M hMU hθ i x = 0 → x = 0 from
    fun x y h => sub_eq_zero.mp (hz (x - y) (by simp [map_sub, h]))
  intro x
  obtain ⟨v, rfl⟩ := mk_surjective ρ U θ x
  intro hv
  have hiv : i v ∈ relations σ U θ := (mk_eq_zero σ U θ _).mp hv
  obtain ⟨K, hK, hivK⟩ := (mem_relations_iff_compact U hU θ σ (i v)).mp hiv
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let χ : K →* ℂˣ := (θ.comp K.subtype)⁻¹
  have hχ : IsOpen (χ.ker : Set K) := by
    convert (hθloc.isOpen_fiber 1).preimage continuous_subtype_val using 1
    ext k
    change (θ k.val)⁻¹ = 1 ↔ (θ k.val : ℂ) = 1
    rw [inv_eq_one]
    exact Units.ext_iff
  let ρK := twist χ ((ρ.comp U.subtype).comp K.subtype)
  let σK := twist χ ((σ.comp U.subtype).comp K.subtype)
  let iK : ρK.IntertwiningMap σK :=
    twistIntertwining χ (Jacquet.restrictMap (Jacquet.restrictMap i U) K)
  have hσK : IsSmooth σK := (isSmooth_twist_iff χ _ hχ).mpr
    (isSmooth_comp K.subtype continuous_subtype_val
      (isSmooth_comp U.subtype continuous_subtype_val hσ))
  have hinj : Function.Injective (Representation.Coinvariants.map ρK σK iK) :=
    coinvariants_map_injective_of_smooth
      (fun _ => ⟨⊤, isCompact_univ, fun _ _ => Subgroup.mem_top _⟩) iK hi hσK
  have hivK' : i v ∈ Representation.Coinvariants.ker σK := by
    rw [relations_eq_twisted_ker] at hivK
    exact hivK
  have hvK : v ∈ Representation.Coinvariants.ker ρK := by
    apply (Representation.Coinvariants.mk_eq_zero ρK).mp
    apply hinj
    rw [map_zero]
    exact (Representation.Coinvariants.mk_eq_zero σK).mpr hivK'
  apply (mk_eq_zero ρ U θ v).mpr
  apply relations_comp_subgroup_le ρ U θ K
  rw [relations_eq_twisted_ker]
  exact hvK

/-- Both published clauses, with the complete independent-universe target. -/
theorem characterLocalizationExactness :
    CharacterLocalizationExactnessStatement (G := G) (V := V) (W := W) (X := X) := by
  constructor
  · exact fun U hU θ ρ v => mem_relations_iff_compact U hU θ ρ v
  · intro _ U hU θ hθloc M hMU hθ ρ σ τ i p hi hp hex hσ
    exact ⟨map_injective_of_smooth U hU θ hθloc M hMU hθ i hi hσ,
      map_range_eq_ker U θ M hMU hθ i p hp hex,
      map_surjective U θ M hMU hθ p hp⟩

end Langlands.Jacquet.Localization
