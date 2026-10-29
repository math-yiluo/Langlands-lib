import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Group.GL.SingletonBlocks

/-!
# The open lower-triangular cell of the left-unipotent quotient

The coset map `B⁻_m → N_m \ GL_m`, `b ↦ [b]`, is an open embedding. Injectivity
is `N_m ∩ B⁻_m = 1`; openness comes from the singleton-shape Iwahori
factorization, which places every small compact open subgroup `K` inside
`N_m · (K ∩ B⁻_m)`.
-/

noncomputable section

namespace Langlands.GeneralLinear

open Topology Langlands.QuotientIntegration

universe u uF

section Algebra

variable {R : Type u} [CommRing R] {m : ℕ}

/-- An upper unipotent lower triangular matrix is the identity. -/
theorem eq_one_of_mem_upperUnipotent_of_mem_lowerTriangular {g : GeneralLinear m R}
    (hN : g ∈ upperUnipotent m R) (hB : g ∈ lowerTriangularSubgroup m R) : g = 1 :=
  Units.ext (matrix_eq_one_of_triangular hN.1 hB hN.2)

/-- The opposite radical of the singleton shape consists of lower triangular matrices. -/
theorem singletons_oppositeUnipotentSubgroup_le_lowerTriangular :
    (BlockShape.singletons m).oppositeUnipotentSubgroup R ≤ lowerTriangularSubgroup m R := by
  intro g hg
  rw [mem_lowerTriangularSubgroup_iff]
  intro i j hij
  have hP := (((BlockShape.singletons m).mem_oppositeUnipotentSubgroup_iff R g).mp hg).1
  have h := ((BlockShape.singletons m).mem_oppositeParabolic_iff R g).mp hP i j 0 0 hij
  rwa [BlockShape.singletons_index, BlockShape.singletons_index] at h

/-- The Levi subgroup of the singleton shape consists of diagonal, hence lower
triangular, matrices. -/
theorem singletons_leviSubgroup_le_lowerTriangular :
    (BlockShape.singletons m).leviSubgroup R ≤ lowerTriangularSubgroup m R := by
  rintro _ ⟨t, rfl⟩
  rw [mem_lowerTriangularSubgroup_iff]
  intro i j hij
  have h := (BlockShape.singletons m).leviEmbedding_apply_ne R t (i := i) (j := j) 0 0
    (ne_of_lt hij)
  rwa [BlockShape.singletons_index, BlockShape.singletons_index] at h

/-- The coset map from the lower triangular group to `N_m \ GL_m`. -/
def lowerTriangularQuotientMap (m : ℕ) (R : Type u) [CommRing R]
    (b : lowerTriangularSubgroup m R) : LeftQuotient (upperUnipotent m R) :=
  Quotient.mk _ b.val

@[simp] theorem lowerTriangularQuotientMap_apply (b : lowerTriangularSubgroup m R) :
    lowerTriangularQuotientMap m R b = Quotient.mk _ b.val :=
  rfl

/-- Distinct lower triangular matrices have distinct `N_m` cosets. -/
theorem lowerTriangularQuotientMap_injective :
    Function.Injective (lowerTriangularQuotientMap m R) := by
  intro b b' h
  have hN := (leftQuotient_mk_eq_iff _ _ _).mp h
  have hB : b'.val * b.val⁻¹ ∈ lowerTriangularSubgroup m R :=
    mul_mem b'.property (inv_mem b.property)
  exact Subtype.ext (mul_inv_eq_one.mp
    (eq_one_of_mem_upperUnipotent_of_mem_lowerTriangular hN hB)).symm

end Algebra

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Arbitrarily small compact open subgroups `K` satisfy `K ⊆ N_m · (K ∩ B⁻_m)`. -/
theorem exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular
    (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ {U : Set (GeneralLinear m F.Carrier)}, U ∈ 𝓝 (1 : GeneralLinear m F.Carrier) →
      ∃ K : OpenSubgroup (GeneralLinear m F.Carrier),
        IsCompact (K : Set (GeneralLinear m F.Carrier)) ∧
        (K : Set (GeneralLinear m F.Carrier)) ⊆ U ∧
        ∀ k ∈ K, ∃ u ∈ upperUnipotent m F.Carrier, ∃ c ∈ lowerTriangularSubgroup m F.Carrier,
          c ∈ K ∧ u * c = k := by
  let := T.topology
  intro U hU
  obtain ⟨K, hKc, hKU, hK⟩ :=
    BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      (BlockShape.singletons m) T hU
  refine ⟨K, hKc, hKU, fun k hk => ?_⟩
  obtain ⟨⟨l, t, v⟩, hx⟩ := hK.bijective.2 ⟨k⁻¹, K.inv_mem hk⟩
  have hx' : l.val * t.val * v.val = k⁻¹ := congrArg Subtype.val hx
  have hv : v.val ∈ upperUnipotent m F.Carrier := by
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
theorem isOpen_upperUnipotent_mul_lowerTriangular_inter (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ {O : Set (GeneralLinear m F.Carrier)}, IsOpen O →
      IsOpen {g : GeneralLinear m F.Carrier | ∃ u ∈ upperUnipotent m F.Carrier,
        ∃ b ∈ lowerTriangularSubgroup m F.Carrier, b ∈ O ∧ u * b = g} := by
  let := T.topology
  have := T.generalLinearTopologicalGroup m
  intro O hO
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨u, hu, b, hb, hbO, rfl⟩
  have hU : (fun c => c * b) ⁻¹' O ∈ 𝓝 (1 : GeneralLinear m F.Carrier) :=
    (continuous_id.mul continuous_const).continuousAt.preimage_mem_nhds (by simpa using hO.mem_nhds hbO)
  obtain ⟨K, -, hKU, hK⟩ :=
    exists_compactOpenSubgroup_subset_upperUnipotent_mul_lowerTriangular T m hU
  have hcont : Continuous fun g : GeneralLinear m F.Carrier => u⁻¹ * g * b⁻¹ :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hmem : (fun g : GeneralLinear m F.Carrier => u⁻¹ * g * b⁻¹) ⁻¹' (K : Set _) ∈
      𝓝 (u * b) :=
    hcont.continuousAt.preimage_mem_nhds (by
      simpa using K.isOpen.mem_nhds K.one_mem)
  filter_upwards [hmem] with g hg
  obtain ⟨u', hu', c, hc, hcK, hk⟩ := hK _ hg
  refine ⟨u * u', mul_mem hu hu', c * b, mul_mem hc hb, hKU hcK, ?_⟩
  calc u * u' * (c * b) = u * (u' * c) * b := by group
    _ = g := by rw [hk]; group

/-- The coset map `B⁻_m → N_m \ GL_m` is an open embedding. -/
theorem isOpenEmbedding_lowerTriangularQuotientMap (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    IsOpenEmbedding (lowerTriangularQuotientMap m F.Carrier) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup m
  refine .of_continuous_injective_isOpenMap ?_ lowerTriangularQuotientMap_injective ?_
  · exact (leftQuotient_isOpenQuotientMap _).continuous.comp continuous_subtype_val
  · intro V hV
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.mp hV
    have himage : lowerTriangularQuotientMap m F.Carrier '' (Subtype.val ⁻¹' O) =
        leftQuotientMap (upperUnipotent m F.Carrier) ''
          {g : GeneralLinear m F.Carrier | ∃ u ∈ upperUnipotent m F.Carrier,
            ∃ b ∈ lowerTriangularSubgroup m F.Carrier, b ∈ O ∧ u * b = g} := by
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

end Langlands.GeneralLinear
