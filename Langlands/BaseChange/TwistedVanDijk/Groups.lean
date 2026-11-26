import Langlands.Group.GL.ParabolicQuotient
import Langlands.BaseChange.SigmaInducedIntertwiner
import Langlands.Group.GL.IntegralSubgroup
import Langlands.Group.GL.LocalFieldTopology
import Langlands.Group.GL.TriangularParabolic
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.LocalField.ContinuousIntegerTransport

/-! # Integral points, the Iwasawa factorization and the entrywise automorphism

For a nonarchimedean local field `E`, this module collects the group-theoretic facts about
`K = GL_n(𝒪_E)`, a standard block parabolic `P = M U` and the entrywise action of an
automorphism `σ` of `E` that the twisted van Dijk formula uses. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open GeneralLinear

universe u v

section Integral

variable {E : Type v} [Field E] [ValuativeRel E]

/-- The integral points `GL_r(𝒪_E)`. -/
abbrev integralGL (E : Type v) [Field E] [ValuativeRel E] (r : ℕ) :
    Subgroup (GeneralLinear r E) :=
  GeneralLinearGroup.integralSubgroup (Fin r) (ValuativeRel.valuation E).integer

theorem mem_integralGL_of_mem_integralRange {r : ℕ} {k : GeneralLinear r E}
    (hk : k ∈ Iwasawa.integralRange (ValuativeRel.valuation E) r) : k ∈ integralGL E r := by
  obtain ⟨h, rfl⟩ := hk
  rw [GeneralLinearGroup.mem_integralSubgroup]
  refine ⟨fun i j => (h i j).property, fun i j => ?_⟩
  rw [← map_inv]
  exact (h⁻¹ i j).property

/-- Iwasawa factorization `G = P K` for every standard block parabolic. -/
theorem exists_parabolic_mul_integralGL {n : ℕ} (B : BlockShape n) (g : GeneralLinear n E) :
    ∃ p ∈ B.parabolic E, ∃ k ∈ integralGL E n, g = p * k := by
  obtain ⟨k, hk, hb⟩ := Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation E) n g
  exact ⟨g * k, B.mem_parabolic_of_isUpperTriangular _ hb, k⁻¹,
    inv_mem (mem_integralGL_of_mem_integralRange hk), by rw [mul_inv_cancel_right]⟩

variable {n : ℕ} (B : BlockShape n)

/-- The Levi part of an integral parabolic element is integral. -/
theorem leviProjection_mem_integralGL (p : B.parabolic E)
    (hp : (p : GeneralLinear n E) ∈ integralGL E n) (i : Fin B.length) :
    B.leviProjection E p i ∈ integralGL E (B.size i) := by
  rw [GeneralLinearGroup.mem_integralSubgroup] at hp ⊢
  refine ⟨fun a b => ?_, fun a b => ?_⟩
  · rw [BlockShape.leviProjection_apply]
    exact hp.1 _ _
  · rw [← Pi.inv_apply, ← map_inv, BlockShape.leviProjection_apply]
    exact hp.2 _ _

/-- A block diagonal element is integral exactly when its blocks are. -/
theorem leviEmbedding_mem_integralGL_iff (m : B.Levi E) :
    B.leviEmbedding E m ∈ integralGL E n ↔ ∀ i, m i ∈ integralGL E (B.size i) := by
  constructor
  · intro h i
    have := leviProjection_mem_integralGL B (B.leviInParabolic E m) h i
    rwa [BlockShape.leviProjection_section] at this
  · intro h
    have hentries : ∀ x : B.Levi E, (∀ i, ∀ a b, x i a b ∈ (ValuativeRel.valuation E).integer) →
        ∀ a b, B.leviEmbedding E x a b ∈ (ValuativeRel.valuation E).integer := by
      intro x hx a b
      obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
      obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
      by_cases hij : i = j
      · subst hij
        change B.leviEmbedding E x (B.index i a) (B.index i b) ∈ _
        rw [BlockShape.leviEmbedding_apply_same]
        exact hx i a b
      · change B.leviEmbedding E x (B.index i a) (B.index j b) ∈ _
        rw [B.leviEmbedding_apply_ne E x a b hij]
        exact Subring.zero_mem _
    have h' := fun i => (GeneralLinearGroup.mem_integralSubgroup _ _ _).1 (h i)
    rw [GeneralLinearGroup.mem_integralSubgroup]
    refine ⟨hentries m fun i => (h' i).1, ?_⟩
    rw [← map_inv]
    exact hentries m⁻¹ fun i => (h' i).2

/-- A product `m u` of a block diagonal element and an element of the unipotent radical is
integral exactly when both factors are. -/
theorem leviEmbedding_mul_mem_integralGL_iff (m : B.Levi E) (y : B.unipotentSubgroup E) :
    B.leviEmbedding E m * (y : GeneralLinear n E) ∈ integralGL E n ↔
      (∀ i, m i ∈ integralGL E (B.size i)) ∧ (y : GeneralLinear n E) ∈ integralGL E n := by
  obtain ⟨⟨yv, hyP⟩, hyU, hyv⟩ := y.property
  have hyP' : (y : GeneralLinear n E) ∈ B.parabolic E := by
    rw [← hyv]
    exact hyP
  constructor
  · intro h
    let p : B.parabolic E := ⟨B.leviEmbedding E m * y, (B.parabolic E).mul_mem
      (B.leviInParabolic E m).property hyP'⟩
    have hproj : B.leviProjection E p = m := by
      have hp : p = B.leviInParabolic E m * ⟨y, hyP'⟩ := rfl
      have hy1 : B.leviProjection E ⟨y, hyP'⟩ = 1 := by
        have : (⟨y, hyP'⟩ : B.parabolic E) = ⟨yv, hyP⟩ := Subtype.ext hyv.symm
        rw [this]
        exact hyU
      rw [hp, map_mul, hy1, mul_one, BlockShape.leviProjection_section]
    have hm : ∀ i, m i ∈ integralGL E (B.size i) := fun i => by
      have := leviProjection_mem_integralGL B p h i
      rwa [hproj] at this
    refine ⟨hm, ?_⟩
    have hy : (y : GeneralLinear n E) = (B.leviEmbedding E m)⁻¹ *
        (B.leviEmbedding E m * y) := by group
    rw [hy]
    exact (integralGL E n).mul_mem
      ((integralGL E n).inv_mem ((leviEmbedding_mem_integralGL_iff B m).mpr hm)) h
  · rintro ⟨hm, hy⟩
    exact (integralGL E n).mul_mem ((leviEmbedding_mem_integralGL_iff B m).mpr hm) hy

end Integral

section Parabolic

variable {R : Type v} [CommRing R] {n : ℕ} (B : BlockShape n)

/-- Conjugation by a block diagonal element preserves the unipotent radical. -/
theorem leviEmbedding_conj_mem_unipotentSubgroup (m : B.Levi R)
    {y : GeneralLinear n R} (hy : y ∈ B.unipotentSubgroup R) :
    (B.leviEmbedding R m)⁻¹ * y * B.leviEmbedding R m ∈ B.unipotentSubgroup R := by
  obtain ⟨h, hh, rfl⟩ := hy
  refine ⟨(B.leviInParabolic R m)⁻¹ * h * B.leviInParabolic R m, ?_, rfl⟩
  have := (B.unipotentRadicalNormal R).conj_mem h hh (B.leviInParabolic R m)⁻¹
  exact SetLike.mem_coe.mpr (by simpa only [inv_inv] using this)

/-- The element `m u` of the parabolic, for `m` in the Levi and `u` in the unipotent radical. -/
def parabolicProduct (x : B.Levi R × B.unipotentSubgroup R) : B.parabolic R :=
  ⟨B.leviEmbedding R x.1 * (x.2 : GeneralLinear n R),
    (B.parabolic R).mul_mem (B.leviInParabolic R x.1).property
      (B.unipotentSubgroup_le_parabolic R x.2.property)⟩

@[simp]
theorem coe_parabolicProduct (x : B.Levi R × B.unipotentSubgroup R) :
    (parabolicProduct B x : GeneralLinear n R) =
      B.leviEmbedding R x.1 * (x.2 : GeneralLinear n R) := rfl

theorem leviProjection_parabolicProduct (x : B.Levi R × B.unipotentSubgroup R) :
    B.leviProjection R (parabolicProduct B x) = x.1 := by
  obtain ⟨h, hh, hv⟩ := x.2.property
  have hx : parabolicProduct B x = B.leviInParabolic R x.1 * h := by
    apply Subtype.ext
    simp only [coe_parabolicProduct, Subgroup.coe_mul, BlockShape.leviInParabolic_val]
    rw [← hv]
    rfl
  rw [hx, map_mul, BlockShape.leviProjection_section]
  change x.1 * B.leviProjection R h = x.1
  rw [show B.leviProjection R h = 1 from hh, mul_one]

/-- The unipotent part `m⁻¹ p` of a parabolic element `p` with Levi part `m`. -/
def parabolicUnipotentPart (p : B.parabolic R) : B.unipotentSubgroup R :=
  ⟨(B.leviEmbedding R (B.leviProjection R p))⁻¹ * p, by
    refine ⟨(B.leviInParabolic R (B.leviProjection R p))⁻¹ * p, ?_, rfl⟩
    change B.leviProjection R ((B.leviInParabolic R (B.leviProjection R p))⁻¹ * p) = 1
    rw [map_mul, map_inv, BlockShape.leviProjection_section, inv_mul_cancel]⟩

/-- `p ↦ (m, m⁻¹ p)` inverts `parabolicProduct`. -/
def parabolicProductEquiv : B.Levi R × B.unipotentSubgroup R ≃ B.parabolic R where
  toFun := parabolicProduct B
  invFun p := (B.leviProjection R p, parabolicUnipotentPart B p)
  left_inv x := by
    have h1 := leviProjection_parabolicProduct B x
    apply Prod.ext
    · exact h1
    · apply Subtype.ext
      change (B.leviEmbedding R (B.leviProjection R (parabolicProduct B x)))⁻¹ *
        (B.leviEmbedding R x.1 * (x.2 : GeneralLinear n R)) = x.2
      rw [h1, inv_mul_cancel_left]
  right_inv p := by
    apply Subtype.ext
    change B.leviEmbedding R (B.leviProjection R p) *
      ((B.leviEmbedding R (B.leviProjection R p))⁻¹ * p) = p
    rw [mul_inv_cancel_left]

/-- Left multiplication by `m₀ u₀` in the coordinates `(m, u)`:
`m₀ u₀ m u = (m₀ m) (m⁻¹ u₀ m u)`. -/
theorem parabolicProduct_mul (x₀ x : B.Levi R × B.unipotentSubgroup R) :
    parabolicProduct B x₀ * parabolicProduct B x =
      parabolicProduct B (x₀.1 * x.1,
        ⟨(B.leviEmbedding R x.1)⁻¹ * x₀.2 * B.leviEmbedding R x.1,
          leviEmbedding_conj_mem_unipotentSubgroup B x.1 x₀.2.property⟩ * x.2) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, coe_parabolicProduct, map_mul]
  group

section Topology

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_parabolicProduct : Continuous (parabolicProduct (R := R) B) :=
  (((B.leviEmbeddingContinuous R).continuous.comp continuous_fst).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

theorem continuous_parabolicUnipotentPart : Continuous (parabolicUnipotentPart (R := R) B) :=
  ((((B.leviEmbeddingContinuous R).continuous.comp
    (B.leviProjectionContinuous R).continuous).inv).mul continuous_subtype_val).subtype_mk _

/-- `(m, u) ↦ m u` as a homeomorphism onto the parabolic. -/
def parabolicProductHomeomorph : B.Levi R × B.unipotentSubgroup R ≃ₜ B.parabolic R where
  toEquiv := parabolicProductEquiv B
  continuous_toFun := continuous_parabolicProduct (R := R) B
  continuous_invFun :=
    (B.leviProjectionContinuous R).continuous.prodMk (continuous_parabolicUnipotentPart (R := R) B)

@[simp]
theorem parabolicProductHomeomorph_apply (x : B.Levi R × B.unipotentSubgroup R) :
    parabolicProductHomeomorph B x = parabolicProduct B x := rfl

end Topology

end Parabolic

section Topology

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

theorem isCompact_integralGL (r : ℕ) : IsCompact (integralGL E r : Set (GeneralLinear r E)) :=
  GeneralLinearGroup.isCompact_integralSubgroup (Fin r) _
    (LocalFieldData.ofInstances E).isCompact_integers

theorem isOpen_integralGL (r : ℕ) : IsOpen (integralGL E r : Set (GeneralLinear r E)) :=
  GeneralLinearGroup.isOpen_integralSubgroup (Fin r) _
    (LocalFieldData.ofInstances E).isOpen_integers

end Topology

section Sigma

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

/-- An `F`-automorphism of `E` preserves and reflects integrality. -/
theorem algEquiv_mem_integer_iff (σ : E ≃ₐ[F] E) (a : E) :
    σ a ∈ (ValuativeRel.valuation E).integer ↔ a ∈ (ValuativeRel.valuation E).integer :=
  ((LocalFieldData.ofInstances E).mem_integers_iff_of_continuous_ringEquiv
    (LocalFieldData.ofInstances E) σ.toRingEquiv (continuous_algEquiv σ)
    (continuous_algEquiv σ.symm) a).symm

/-- The entrywise action of `σ` preserves `GL_r(𝒪_E)`. -/
theorem entrywiseAut_mem_integralGL_iff (σ : E ≃ₐ[F] E) {r : ℕ} (g : GeneralLinear r E) :
    entrywiseAut σ r g ∈ integralGL E r ↔ g ∈ integralGL E r := by
  simp only [GeneralLinearGroup.mem_integralSubgroup, ← map_inv, entrywiseAut_apply_apply,
    algEquiv_mem_integer_iff]

omit [TopologicalSpace F] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [IsModuleTopology F E] in
/-- The entrywise action of `σ` preserves the unipotent radical of a standard parabolic. -/
theorem entrywiseAut_mem_unipotentSubgroup_iff (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (g : GeneralLinear n E) :
    entrywiseAut σ n g ∈ B.unipotentSubgroup E ↔ g ∈ B.unipotentSubgroup E := by
  rw [BlockShape.mem_unipotentSubgroup_iff, BlockShape.mem_unipotentSubgroup_iff,
    entrywiseAut_mem_parabolic_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro a
  apply forall_congr'
  intro b
  rw [entrywiseAut_apply_apply]
  constructor
  · intro h
    split_ifs at h ⊢ with hab
    · exact σ.injective (h.trans (map_one σ).symm)
    · exact σ.injective (h.trans (map_zero σ).symm)
  · intro h
    rw [h]
    split_ifs <;> simp

/-- The entrywise action of `σ` as a topological group automorphism of `GL_r(E)`. -/
def entrywiseContinuousAut (σ : E ≃ₐ[F] E) (r : ℕ) : GeneralLinear r E ≃ₜ* GeneralLinear r E where
  toMulEquiv := entrywiseAut σ r
  continuous_toFun := continuous_entrywiseAut σ r
  continuous_invFun := continuous_entrywiseAut_symm σ r

@[simp]
theorem entrywiseContinuousAut_apply (σ : E ≃ₐ[F] E) (r : ℕ) (g : GeneralLinear r E) :
    entrywiseContinuousAut σ r g = entrywiseAut σ r g := rfl

end Sigma

end Langlands.BaseChange.TwistedVanDijk
