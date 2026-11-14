import Langlands.Group.GL.LowerTriangularQuotientCell
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
/-!
# The open lower-triangular cell of the left-unipotent quotient

The coset map `B⁻_m → N_m \ GL_m`, `b ↦ [b]`, is an open embedding. Injectivity
is `N_m ∩ B⁻_m = 1`; openness comes from the singleton-shape Iwahori
factorization, which places every small compact open subgroup `K` inside
`N_m · (K ∩ B⁻_m)`.
-/

noncomputable section

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear hiding exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular isOpenEmbedding_lowerTriangularQuotientMap isOpen_upperUnipotent_mul_lowerTriangular_inter
open Langlands.AllField.GeneralLinear

open _root_.Topology
open Langlands.QuotientIntegration

universe u uF

section Algebra


end Algebra

section Padic

variable {F : Type uF} [Field F]

/-- Arbitrarily small compact open subgroups `K` satisfy `K ⊆ N_m · (K ∩ B⁻_m)`. -/
theorem exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular
    (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    ∀ {U : Set (GeneralLinear m F)}, U ∈ 𝓝 (1 : GeneralLinear m F) →
      ∃ K : OpenSubgroup (GeneralLinear m F),
        IsCompact (K : Set (GeneralLinear m F)) ∧
        (K : Set (GeneralLinear m F)) ⊆ U ∧
        ∀ k ∈ K, ∃ u ∈ upperUnipotent m F, ∃ c ∈ lowerTriangularSubgroup m F,
          c ∈ K ∧ u * c = k := by
  let := T.topology
  intro U hU
  obtain ⟨K, hKc, hKU, hK⟩ :=
    Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      (BlockShape.singletons m) T hU
  refine ⟨K, hKc, hKU, fun k hk => ?_⟩
  obtain ⟨⟨l, t, v⟩, hx⟩ := hK.bijective.2 ⟨k⁻¹, K.inv_mem hk⟩
  have hx' : l.val * t.val * v.val = k⁻¹ := congrArg Subtype.val hx
  have hv : v.val ∈ upperUnipotent m F := by
    have := v.property.2
    rwa [BlockShape.singletons_unipotentSubgroup] at this
  refine ⟨v.val⁻¹, inv_mem hv, t.val⁻¹ * l.val⁻¹, ?_, ?_, ?_⟩
  · exact mul_mem (inv_mem (singletons_leviSubgroup_le_lowerTriangular t.property.2))
      (inv_mem (singletons_oppositeUnipotentSubgroup_le_lowerTriangular l.property.2))
  · exact K.mul_mem (K.inv_mem t.property.1) (K.inv_mem l.property.1)
  · have hk' : k = (l.val * t.val * v.val)⁻¹ := by rw [hx', inv_inv]
    rw [hk']
    group

/-- For every open set `O`, the set `N_m · (B⁻_m ∩ O)` is open. -/
theorem isOpen_upperUnipotent_mul_lowerTriangular_inter (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    ∀ {O : Set (GeneralLinear m F)}, IsOpen O →
      IsOpen {g : GeneralLinear m F | ∃ u ∈ upperUnipotent m F,
        ∃ b ∈ lowerTriangularSubgroup m F, b ∈ O ∧ u * b = g} := by
  let := T.topology
  have := T.generalLinearTopologicalGroup m
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, b, hb, hbO, rfl⟩
  have hU : (fun c => c * b) ⁻¹' O ∈ 𝓝 (1 : GeneralLinear m F) :=
    (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hbO)
  obtain ⟨K, -, hKU, hK⟩ :=
    exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular T m hU
  have hcont : Continuous fun g : GeneralLinear m F => u⁻¹ * g * b⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem : (fun g : GeneralLinear m F => u⁻¹ * g * b⁻¹) ⁻¹' (K : Set _) ∈
      𝓝 (u * b) :=
    hcont.continuousAt.preimage_mem_nhds (by
      simpa using K.isOpen.mem_nhds K.one_mem)
  filter_upwards [hmem] with g hg
  obtain ⟨u', hu', c, hc, hcK, hk⟩ := hK _ hg
  refine ⟨u * u', mul_mem hu hu', c * b, mul_mem hc hb, hKU hcK, ?_⟩
  calc u * u' * (c * b) = u * (u' * c) * b := by group
    _ = g := by rw [hk]; group

/-- The coset map `B⁻_m → N_m \ GL_m` is an open embedding. -/
theorem isOpenEmbedding_lowerTriangularQuotientMap (T : LocalFieldData F) (m : ℕ) :
    letI := T.topology
    IsOpenEmbedding (lowerTriangularQuotientMap m F) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup m
  refine .of_continuous_injective_isOpenMap ?_ lowerTriangularQuotientMap_injective ?_
  · exact (leftQuotient_isOpenQuotientMap _).continuous.comp continuous_subtype_val
  · intro V hV
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hV
    have himage : lowerTriangularQuotientMap m F '' (Subtype.val ⁻¹' O) =
        leftQuotientMap (upperUnipotent m F) ''
          {g : GeneralLinear m F | ∃ u ∈ upperUnipotent m F,
            ∃ b ∈ lowerTriangularSubgroup m F, b ∈ O ∧ u * b = g} := by
      ext q
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨b.val, ⟨1, one_mem _, b.val, b.property, hb, one_mul _⟩, rfl⟩
      · rintro ⟨_, ⟨u, hu, b, hb, hbO, rfl⟩, rfl⟩
        refine ⟨⟨b, hb⟩, hbO, ?_⟩
        refine (leftQuotient_mk_eq_iff _ _ _).mpr ?_
        simpa using hu
    rw [himage]
    exact (leftQuotient_isOpenQuotientMap _).isOpenMap _
      (isOpen_upperUnipotent_mul_lowerTriangular_inter T m hO)

end Padic

end Langlands.AllField.GeneralLinear
