import Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof
import Langlands.LocalFactor.CommonClosure
import Langlands.Galois.Local.UnramifiedCriterionProof
import Langlands.Weil.Local.AssemblyProof

/-!
# The slope of the relative inverse Herbrand function past the last break

For a finite Galois field `L` over `K` and a subfield `E`, once the lower groups of `L/K`
lie in `Gal(L/E)`, the Herbrand functions of `L/E` and `L/K` have proportional increments.
Hence the relative index `ψ_{E/K} = φ_{L/E} ∘ ψ_{L/K}` has constant slope
`[G_0 : G_0 ∩ Gal(L/E)]` past any upper index whose group lies in `Gal(L/E)`.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Herbrand

universe u uK uE uL

section Increments

/-- Weighted ramp sums whose weights agree past `x` have equal increments on `[x, y]`. -/
theorem rampSum_sub_eq (c d : ℕ → ℝ) (N : ℕ) {x y : ℝ} (hxy : x ≤ y)
    (hcd : ∀ j : ℕ, x < j → c j = d j) :
    rampSum c N y - rampSum c N x = rampSum d N y - rampSum d N x := by
  unfold rampSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x < ((i + 1 : ℕ) : ℝ)
  · rw [hcd (i + 1) hi]
  · rw [not_lt] at hi
    push_cast at hi
    rw [ramp_eq_one hi, ramp_eq_one (hi.trans hxy)]
    ring

end Increments

section GroupIndex

variable {G : Type*} [Group G]

/-- For a normal subgroup `N`, the cosets of `S` in `S ⊔ N` are those of `S ∩ N` in `N`. -/
theorem relIndex_sup_of_normal (S N : Subgroup G) [N.Normal] :
    S.relIndex (S ⊔ N) = S.relIndex N := by
  let q : N ⧸ S.subgroupOf N → ↥(S ⊔ N) ⧸ S.subgroupOf (S ⊔ N) :=
    Quotient.map' (Subgroup.inclusion le_sup_right) (fun a b hab => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
      exact hab)
  have hq : Function.Bijective q := by
    constructor
    · rintro ⟨a⟩ ⟨b⟩ hab
      apply Quotient.sound'
      have hab' := Quotient.exact' hab
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab' ⊢
      exact hab'
    · rintro ⟨x⟩
      have hx : (x : G) ∈ ((N ⊔ S : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact x.2
      rw [Subgroup.normal_mul] at hx
      obtain ⟨n, hn, t, ht, hnt⟩ := hx
      refine ⟨Quotient.mk'' ⟨n, hn⟩, ?_⟩
      apply Quotient.sound'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      change n⁻¹ * (x : G) ∈ S
      rw [← hnt, inv_mul_cancel_left]
      exact ht
  exact (Nat.card_congr (Equiv.ofBijective q hq)).symm

end GroupIndex

section Orders

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (K : Type uK) [Field K] [Algebra (Padic p) K]
  (E : Type uE) [Field E] [Algebra (Padic p) E] {L : PadicField.{uL} p}
  [Algebra K E] [Algebra E L.Carrier] [Algebra K L.Carrier]
  [IsScalarTower K E L.Carrier]
  [IsScalarTower (Padic p) K L.Carrier] [IsScalarTower (Padic p) E L.Carrier]
  (T : L.TopologicalData)

/-- Past a real lower index whose group fixes `E`, the Herbrand functions over `E` and `K`
have increments in the ratio `[G_0 : G_0 ∩ Gal(L/E)]`. -/
theorem herbrandPhi_sub_eq {u₀ : ℝ} (hu₀ : 0 ≤ u₀)
    (hH : Padic.lowerRamificationGroupReal T K u₀ ≤
      (AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range)
    {x y : ℝ} (hx : u₀ ≤ x) (hxy : x ≤ y) :
    Padic.herbrandPhi T E y - Padic.herbrandPhi T E x =
      ((AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.relIndex
          (Padic.lowerRamificationGroup T K 0) : ℝ) *
        (Padic.herbrandPhi T K y - Padic.herbrandPhi T K x) := by
  set H := (AlgEquiv.restrictScalarsHom K :
    (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range
  set B := max (ramificationCutoff T K) (max (ramificationCutoff T E) ⌈y⌉₊)
  have hBK : ramificationCutoff T K ≤ B := le_max_left _ _
  have hBE : ramificationCutoff T E ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hyB : y ≤ B := (Nat.le_ceil y).trans (by exact_mod_cast
    (le_max_right _ _ : ⌈y⌉₊ ≤ max (ramificationCutoff T E) ⌈y⌉₊).trans (le_max_right _ _))
  have hxB : x ≤ B := hxy.trans hyB
  have hx0 : 0 ≤ x := hu₀.trans hx
  have hAx := herbrandPhi_eq_sum T K hBK hx0 hxB
  have hAy := herbrandPhi_eq_sum T K hBK (hx0.trans hxy) hyB
  have hBx := herbrandPhi_eq_sum T E hBE hx0 hxB
  have hBy := herbrandPhi_eq_sum T E hBE (hx0.trans hxy) hyB
  have hj : ∀ j : ℕ, x < j →
      (Padic.lowerGroupOrder T E j : ℝ) = Padic.lowerGroupOrder T K j := by
    intro j hj
    have hle : Padic.lowerRamificationGroup T K j ≤ H := by
      rw [← Padic.lowerRamificationGroupReal_nat]
      exact (Padic.lowerRamificationGroupReal_antitone T K (hx.trans hj.le)).trans hH
    have h1 := lowerGroupOrder_subfield_mul_relIndex K E T j
    rw [Subgroup.relIndex_eq_one.mpr hle, mul_one] at h1
    exact_mod_cast h1
  have hinc := rampSum_sub_eq (fun i => (Padic.lowerGroupOrder T E i : ℝ))
    (fun i => (Padic.lowerGroupOrder T K i : ℝ)) B hxy hj
  have h0 : (Padic.lowerGroupOrder T K 0 : ℝ) =
      Padic.lowerGroupOrder T E 0 * H.relIndex (Padic.lowerRamificationGroup T K 0) := by
    exact_mod_cast (lowerGroupOrder_subfield_mul_relIndex K E T 0).symm
  have hh0 : (0 : ℝ) < Padic.lowerGroupOrder T E 0 := by
    exact_mod_cast lowerGroupOrder_pos T E 0
  have hr : (0 : ℝ) < H.relIndex (Padic.lowerRamificationGroup T K 0) := by
    have hg0 : (0 : ℝ) < Padic.lowerGroupOrder T K 0 := by
      exact_mod_cast lowerGroupOrder_pos T K 0
    rw [h0] at hg0
    exact pos_of_mul_pos_right hg0 hh0.le
  rw [hAx, hAy, hBx, hBy, div_sub_div_same, div_sub_div_same, hinc, h0]
  field_simp

/-- Past an upper index whose group fixes `E`, the relative index
`φ_{L/E} ∘ ψ_{L/K}` has slope `[G_0 : G_0 ∩ Gal(L/E)]`. -/
theorem herbrandPhi_herbrandPsi_sub_eq {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hH : Padic.upperRamificationGroup T K v₀ ≤
      (AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    Padic.herbrandPhi T E (Padic.herbrandPsi T K t) -
        Padic.herbrandPhi T E (Padic.herbrandPsi T K s) =
      ((AlgEquiv.restrictScalarsHom K :
        (L.Carrier ≃ₐ[E] L.Carrier) →* (L.Carrier ≃ₐ[K] L.Carrier)).range.relIndex
          (Padic.lowerRamificationGroup T K 0) : ℝ) * (t - s) := by
  have hu₀ : 0 ≤ Padic.herbrandPsi T K v₀ := by
    have h := (Padic.herbrandPsi_strictMono T K).monotone hv₀
    rwa [Padic.herbrandPsi_zero] at h
  rw [herbrandPhi_sub_eq K E T hu₀ hH ((Padic.herbrandPsi_strictMono T K).monotone hs)
    ((Padic.herbrandPsi_strictMono T K).monotone hst), Padic.herbrandPhi_herbrandPsi,
    Padic.herbrandPhi_herbrandPsi]

end Orders

section Relative

open _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p) {K : PadicField.{uE} p}
  {Ω : Type uL} [Field Ω] [Algebra F.Carrier Ω] [Algebra K.Carrier Ω] [Algebra (Padic p) Ω]
  [Algebra F.Carrier K.Carrier] [IsScalarTower F.Carrier K.Carrier Ω]
  [IsScalarTower (Padic p) F.Carrier Ω] [IsScalarTower (Padic p) K.Carrier Ω]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier Ω}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier Ω x ∈ M.toIntermediateField)

/-- The image of `Gal(M/K)` in `Gal(M/F)`, for the finite Galois field viewed over `K`. -/
abbrev relativeSubgroup :
    Subgroup ((finiteGaloisPadicField K (extendFiniteGalois h)).Carrier ≃ₐ[F.Carrier]
      (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier) :=
  (AlgEquiv.restrictScalarsHom F.Carrier :
    ((finiteGaloisPadicField K (extendFiniteGalois h)).Carrier ≃ₐ[K.Carrier]
      (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier) →*
    ((finiteGaloisPadicField K (extendFiniteGalois h)).Carrier ≃ₐ[F.Carrier]
      (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier)).range

/-- The slope of the relative index past an upper index whose group fixes `K`. -/
theorem relativeIndex_sub_eq {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hH : Padic.upperRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData F.Carrier v₀ ≤
      relativeSubgroup F h)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    relativeIndex F M h t - relativeIndex F M h s =
      ((relativeSubgroup F h).relIndex (Padic.lowerRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
          F.Carrier 0) : ℝ) * (t - s) :=
  herbrandPhi_herbrandPsi_sub_eq F.Carrier K.Carrier _ hv₀ hH hs hst

/-- An element of `Gal(Ω/F)` restricts into the image of `Gal(M/K)` exactly when it fixes
the image of `K`. -/
theorem autCongr_restrictNormalHom_mem_relativeSubgroup_iff (σ : Ω ≃ₐ[F.Carrier] Ω) :
    (extendFiniteGaloisEquiv h).autCongr
        (AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := Ω) M σ) ∈ relativeSubgroup F h ↔
      ∀ k : K.Carrier, σ (algebraMap K.Carrier Ω k) = algebraMap K.Carrier Ω k := by
  set ρ := (extendFiniteGaloisEquiv h).autCongr
    (AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := Ω) M σ)
  have hρ : ∀ y : (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier,
      ((ρ y : (extendFiniteGalois h).toIntermediateField) : Ω) = σ (y : Ω) := by
    intro y
    change (AlgEquiv.restrictNormalHom M.toIntermediateField σ ⟨(y : Ω), y.2⟩ : Ω) = _
    rw [AlgEquiv.restrictNormalHom_apply]
  constructor
  · rintro ⟨τ, hτ⟩ k
    have h1 := congrArg (fun π : _ ≃ₐ[F.Carrier] _ =>
      ((π (algebraMap K.Carrier (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier k) :
        (extendFiniteGalois h).toIntermediateField) : Ω)) hτ
    simp only at h1
    rw [hρ] at h1
    refine h1.symm.trans ?_
    change ((τ (algebraMap K.Carrier _ k) : (extendFiniteGalois h).toIntermediateField) : Ω) = _
    rw [τ.commutes]
    rfl
  · intro hk
    refine ⟨{ ρ.toRingEquiv with
      commutes' := fun k => Subtype.ext ?_ }, ?_⟩
    · change ((ρ (algebraMap K.Carrier _ k) : (extendFiniteGalois h).toIntermediateField) : Ω) =
        algebraMap K.Carrier Ω k
      rw [hρ]
      exact hk k
    · apply AlgEquiv.ext
      intro y
      rfl

end Relative

section AbsoluteSlope

open LocalClassField _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {K : PadicField.{uE} p}
  [Algebra K.Carrier (AlgebraicClosure F.Carrier)] [Algebra F.Carrier K.Carrier]
  [IsScalarTower F.Carrier K.Carrier (AlgebraicClosure F.Carrier)]
  [IsScalarTower (Padic p) K.Carrier (AlgebraicClosure F.Carrier)]

attribute [local instance] extension_padicScalarTower

variable {M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier)}
  (h : ∀ x : K.Carrier, algebraMap K.Carrier (AlgebraicClosure F.Carrier) x ∈
    M.toIntermediateField)

/-- Restriction from the absolute Galois group of `F` to `Gal(M/F)`, for the finite Galois
field `M ⊇ K` viewed as a field over `K`. -/
def absoluteRelativeRestriction :
    Field.absoluteGaloisGroup F.Carrier →*
      ((finiteGaloisPadicField K (extendFiniteGalois h)).Carrier ≃ₐ[F.Carrier]
        (finiteGaloisPadicField K (extendFiniteGalois h)).Carrier) :=
  ((extendFiniteGaloisEquiv h).autCongr : _ →* _).comp
    (absoluteFiniteRestriction F M).toMonoidHom

/-- An absolute Galois element restricts into `Gal(M/K)` exactly when it fixes `K`. -/
theorem mem_comap_absoluteRelativeRestriction_iff (τ : Field.absoluteGaloisGroup F.Carrier) :
    τ ∈ (relativeSubgroup F h).comap (absoluteRelativeRestriction F h) ↔
      ∀ k : K.Carrier, AlgEquiv.toAlgHom τ (algebraMap K.Carrier _ k) =
        algebraMap K.Carrier (AlgebraicClosure F.Carrier) k :=
  autCongr_restrictNormalHom_mem_relativeSubgroup_iff F h τ

/-- Absolute upper groups restrict onto the upper groups of `M/F`. -/
theorem map_absoluteRelativeRestriction_upper {v : ℝ} (hv : -1 ≤ v) :
    (absoluteUpperRamificationGroup F v).map (absoluteRelativeRestriction F h) =
      Padic.upperRamificationGroup
        (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData F.Carrier v := by
  rw [absoluteRelativeRestriction, ← Subgroup.map_map, absoluteUpperFiniteImage F M v hv]
  exact map_autCongr_upperRamificationGroup _ _ F.Carrier (extendFiniteGaloisEquiv h) v

/-- If `G_F^{v₀}` fixes `K`, the relative index has slope `[I_F : I_F ∩ G_K]` past `v₀`, where
`G_K` is the subgroup of the absolute Galois group fixing `K`. -/
theorem relativeIndex_sub_eq_relIndex {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hG : absoluteUpperRamificationGroup F v₀ ≤
      (relativeSubgroup F h).comap (absoluteRelativeRestriction F h))
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    relativeIndex F M h t - relativeIndex F M h s =
      (((relativeSubgroup F h).comap (absoluteRelativeRestriction F h)).relIndex
        (F.absoluteInertia F.canonicalTopologicalData) : ℝ) * (t - s) := by
  set T := (finiteGaloisPadicField K (extendFiniteGalois h)).canonicalTopologicalData
  have hH : Padic.upperRamificationGroup T F.Carrier v₀ ≤ relativeSubgroup F h := by
    rw [← map_absoluteRelativeRestriction_upper F h (by linarith)]
    exact (Subgroup.map_mono hG).trans (Subgroup.map_comap_le _ _)
  have hlow0 : Padic.lowerRamificationGroup T F.Carrier 0 =
      Padic.upperRamificationGroup T F.Carrier 0 := by
    rw [Padic.upperRamificationGroup_zero, ← Padic.lowerRamificationGroupReal_nat, Nat.cast_zero,
      Padic.lowerRamificationGroupReal_zero]
  have key := relativeIndex_sub_eq F h hv₀ hH hs hst
  rw [hlow0, ← map_absoluteRelativeRestriction_upper F h (by norm_num),
    ← Subgroup.relIndex_comap, absoluteUpperCanonicalInertia F] at key
  exact key

end AbsoluteSlope

section Intermediate

open LocalClassField Weil.Local _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

attribute [local instance] asPadicField_isScalarTower

/-- For the Galois closure of `E`, the absolute Galois elements restricting into
`Gal(M/E)` form the fixing subgroup of `E`. -/
theorem comap_absoluteRelativeRestriction_galoisClosure :
    (relativeSubgroup F (algebraMap_mem_galoisClosure E)).comap
        (absoluteRelativeRestriction F (algebraMap_mem_galoisClosure E)) =
      E.field.fixingSubgroup := by
  ext τ
  refine (mem_comap_absoluteRelativeRestriction_iff F (algebraMap_mem_galoisClosure E) τ).trans
    (Iff.trans ⟨fun hk x hx => hk ⟨x, hx⟩, fun hk k => hk k.1 k.2⟩
      (IntermediateField.mem_fixingSubgroup_iff E.field τ).symm)

/-- If `G_F^{v₀}` fixes `E`, then past `v₀` the relative inverse Herbrand function has slope
`[I_F : I_F ∩ G_E]`. -/
theorem relativeHerbrandPsi_sub_eq_relIndex {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hG : absoluteUpperRamificationGroup F v₀ ≤ E.field.fixingSubgroup)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    relativeHerbrandPsi E t - relativeHerbrandPsi E s =
      (E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) : ℝ) *
        (t - s) := by
  have hcomap := comap_absoluteRelativeRestriction_galoisClosure E
  have key := relativeIndex_sub_eq_relIndex F (algebraMap_mem_galoisClosure E) hv₀
    (hcomap ▸ hG) hs hst
  rw [hcomap] at key
  exact key

end Intermediate

section RamificationIndex

open LocalClassField Weil.Local PadicField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

local instance slopeProofAlgebra : Algebra (Padic p) E.field := (EP).algebra

/-- A subgroup of the absolute Galois group with the elements of the fixing subgroup of `E`
has index `e_E / e_F` over its intersection with absolute inertia. -/
theorem relIndex_absoluteInertia_mul_of_mem_iff (S : Subgroup (Field.absoluteGaloisGroup F.Carrier))
    (hS : ∀ τ, τ ∈ S ↔ τ ∈ E.field.fixingSubgroup) :
    S.relIndex (F.absoluteInertia F.canonicalTopologicalData) *
        F.canonicalTopologicalData.ramificationIndex =
      (EP).canonicalTopologicalData.ramificationIndex := by
  have hN : (F.absoluteInertia F.canonicalTopologicalData).Normal := inferInstance
  have hrange : (extensionGaloisMap F EP (intermediateEmbedding F E)).toMonoidHom.range =
      S.comap (MulAut.conj (intermediateClosureCorrection F E)).toMonoidHom := by
    ext τ
    rw [Subgroup.mem_comap, extensionGaloisMap_range, hS]
    exact (intermediateClosureCorrection_conj_mem F E τ).symm
  have hI : (F.absoluteInertia F.canonicalTopologicalData).map
      (MulAut.conj (intermediateClosureCorrection F E)).toMonoidHom =
        F.absoluteInertia F.canonicalTopologicalData := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hN.conj_mem y hy _
    · intro hx
      refine ⟨(intermediateClosureCorrection F E)⁻¹ * x * (intermediateClosureCorrection F E)⁻¹⁻¹,
        hN.conj_mem x hx _, ?_⟩
      change intermediateClosureCorrection F E * ((intermediateClosureCorrection F E)⁻¹ * x *
        (intermediateClosureCorrection F E)⁻¹⁻¹) * (intermediateClosureCorrection F E)⁻¹ = x
      group
  have hrel : S.relIndex (F.absoluteInertia F.canonicalTopologicalData) =
      (extensionGaloisMap F EP (intermediateEmbedding F E)).toMonoidHom.range.relIndex
        (F.absoluteInertia F.canonicalTopologicalData) := by
    rw [hrange, Subgroup.relIndex_comap, hI]
  have hmul := Subgroup.relIndex_mul_index
    (le_sup_left : (extensionGaloisMap F EP (intermediateEmbedding F E)).toMonoidHom.range ≤
      (extensionGaloisMap F EP (intermediateEmbedding F E)).toMonoidHom.range ⊔
        F.absoluteInertia F.canonicalTopologicalData)
  rw [relIndex_sup_of_normal, extensionGaloisMap_range_sup_absoluteInertia_index,
    extensionGaloisMap_range_index] at hmul
  have hram := ramificationIndex_mul_extensionResidueDegree F EP (intermediateEmbedding F E)
  have hf := extensionResidueDegree_pos F EP (intermediateEmbedding F E)
  rw [hrel]
  apply Nat.eq_of_mul_eq_mul_right hf
  rw [hram, ← hmul]
  ring

/-- The index of `I_F ∩ G_E` in the absolute inertia group is the relative ramification index:
`[I_F : I_F ∩ G_E] · e_F = e_E`. -/
theorem fixingSubgroup_relIndex_absoluteInertia_mul :
    E.field.fixingSubgroup.relIndex (F.absoluteInertia F.canonicalTopologicalData) *
        F.canonicalTopologicalData.ramificationIndex =
      (EP).canonicalTopologicalData.ramificationIndex :=
  relIndex_absoluteInertia_mul_of_mem_iff F E _ fun _ => Iff.rfl

end RamificationIndex

section Slope

open LocalClassField Weil.Local _root_.Langlands.Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

/-- Deligne–Henniart 3.2(iii), first assertion: if `G_F^{v₀}` fixes `E` for some `v₀ ≥ 0`,
then for `v₀ ≤ s ≤ t`, `ψ_{E/F}(t) - ψ_{E/F}(s) = e(E/F) (t - s)`, with
`e(E/F) = e_E / e_F` the quotient of the canonical ramification indices. -/
theorem relativeHerbrandPsi_sub_eq {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hG : absoluteUpperRamificationGroup F v₀ ≤ E.field.fixingSubgroup)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    relativeHerbrandPsi E t - relativeHerbrandPsi E s =
      ((LocalClassField.CommonClosure.canonicalData F E).ramificationIndex /
        F.canonicalTopologicalData.ramificationIndex : ℝ) * (t - s) := by
  rw [relativeHerbrandPsi_sub_eq_relIndex E hv₀ hG hs hst]
  congr 1
  have h := fixingSubgroup_relIndex_absoluteInertia_mul F E
  have hF : (0 : ℝ) < F.canonicalTopologicalData.ramificationIndex := by
    exact_mod_cast F.canonicalTopologicalData.ramificationIndex_pos
  rw [show LocalClassField.CommonClosure.canonicalData F E =
    (E.asPadicField (p := p)).canonicalTopologicalData from rfl, eq_div_iff hF.ne']
  exact_mod_cast h

/-- The same slope, with the hypothesis on the actual upper groups of the local Weil group:
`W_F^{v₀} ≤ W_E` for some `v₀ ≥ 0`. -/
theorem relativeHerbrandPsi_sub_eq_of_upperGroup_le {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    (hW : VirtualRepresentation.LocalWeil.Ramification.upperGroup F v₀ ≤
      LocalFactor.CommonClosure.weilSubgroup F E)
    {s t : ℝ} (hs : v₀ ≤ s) (hst : s ≤ t) :
    relativeHerbrandPsi E t - relativeHerbrandPsi E s =
      ((LocalFactor.CommonClosure.fieldData F E).ramificationIndex /
        F.canonicalTopologicalData.ramificationIndex : ℝ) * (t - s) := by
  refine relativeHerbrandPsi_sub_eq E hv₀ ?_ hs hst
  intro τ hτ
  have hτ0 : τ ∈ F.absoluteInertia F.canonicalTopologicalData := by
    rw [← absoluteUpperCanonicalInertia F]
    exact absoluteUpperRamificationGroup_antitone F hv₀ hτ
  set w : localInertia F := (localInertiaEquiv F).symm ⟨τ, hτ0⟩
  have hwτ : localProjection F (w : localWeilGroup F) = τ :=
    congrArg Subtype.val ((localInertiaEquiv F).apply_symm_apply ⟨τ, hτ0⟩)
  have hw : (w : localWeilGroup F) ∈ VirtualRepresentation.LocalWeil.Ramification.upperGroup F v₀ := by
    change localProjection F (w : localWeilGroup F) ∈ absoluteUpperRamificationGroup F v₀
    rw [hwτ]
    exact hτ
  have hmem := hW hw
  rw [← hwτ]
  exact hmem

end Slope

end Langlands.Ramification.HerbrandBridge
