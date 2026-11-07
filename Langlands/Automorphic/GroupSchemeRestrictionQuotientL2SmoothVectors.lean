import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2InfiniteAction
import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Representation.Smooth.Definitions

/-! # Smooth vectors in `L²([G])` and their transport along `quotientL2Equiv` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

section Intertwining

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ChartedSpace H Γ]
  {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- A bounded intertwiner carries real smooth vectors to real smooth vectors. -/
theorem isSmoothVector_of_intertwining (π : Γ →* (E →L[ℂ] E)) (π' : Γ →* (E' →L[ℂ] E'))
    (L : E →L[ℂ] E') (hL : ∀ g v, L (π g v) = π' g (L v)) {v : E}
    (hv : Langlands.Archimedean.IsSmoothVector I π v) :
    Langlands.Archimedean.IsSmoothVector I π' (L v) := by
  have he : Langlands.Archimedean.orbitMap π' (L v) = L ∘ Langlands.Archimedean.orbitMap π v := by
    funext g
    simp [Langlands.Archimedean.orbitMap, hL]
  change ContMDiff I 𝓘(ℝ, E') ∞ (Langlands.Archimedean.orbitMap π' (L v))
  rw [he]
  exact (L.restrictScalars ℝ).contDiff.contMDiff.comp hv

/-- An isometric intertwining equivalence identifies real smooth vectors. -/
theorem isSmoothVector_linearIsometryEquiv_iff (π : Γ →* (E →L[ℂ] E))
    (π' : Γ →* (E' →L[ℂ] E')) (L : E ≃ₗᵢ[ℂ] E') (hL : ∀ g v, L (π g v) = π' g (L v)) (v : E) :
    Langlands.Archimedean.IsSmoothVector I π' (L v) ↔
      Langlands.Archimedean.IsSmoothVector I π v := by
  refine ⟨fun hv => ?_, isSmoothVector_of_intertwining I π π'
    (L : E →L[ℂ] E') hL⟩
  have hL' : ∀ g w, L.symm (π' g w) = π g (L.symm w) := by
    intro g w
    apply L.injective
    rw [LinearIsometryEquiv.apply_symm_apply, hL, LinearIsometryEquiv.apply_symm_apply]
  simpa using isSmoothVector_of_intertwining I π' π (L.symm : E' →L[ℂ] E) hL' hv

end Intertwining

section FiniteIntertwining

variable {R Γ V V' : Type*} [CommRing R] [Group Γ] [TopologicalSpace Γ]
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']

/-- An intertwiner carries vectors fixed by an open subgroup to vectors fixed by it. -/
theorem isSmoothVector_of_finiteIntertwining (ρ : Representation R Γ V)
    (ρ' : Representation R Γ V') (L : V →ₗ[R] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v))
    {v : V} (hv : Langlands.IsSmoothVector ρ v) : Langlands.IsSmoothVector ρ' (L v) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨K, ?_⟩
  rw [Langlands.fixedVectors, Representation.mem_invariants] at hK ⊢
  intro k
  change ρ' (k : Γ) (L v) = L v
  rw [← hL]
  exact congrArg L (hK k)

/-- A linear intertwining equivalence identifies vectors fixed by open subgroups. -/
theorem isSmoothVector_linearEquiv_iff (ρ : Representation R Γ V)
    (ρ' : Representation R Γ V') (L : V ≃ₗ[R] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v))
    (v : V) : Langlands.IsSmoothVector ρ' (L v) ↔ Langlands.IsSmoothVector ρ v := by
  refine ⟨fun hv => ?_, isSmoothVector_of_finiteIntertwining ρ ρ' (L : V →ₗ[R] V') hL⟩
  have hL' : ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
    intro g w
    apply L.injective
    rw [LinearEquiv.apply_symm_apply, hL, LinearEquiv.apply_symm_apply]
  simpa using isSmoothVector_of_finiteIntertwining ρ' ρ (L.symm : V' →ₗ[R] V) hL' hv

end FiniteIntertwining

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}

section Submodules

variable (measureQ : Measure (Quotient F G S j))
variable (hInv : QuotientRightInvariant F G measureQ)

/-- The classes in `L²([G])` fixed by some open subgroup of the finite adelic points. -/
def rationalQuotientL2FiniteSmoothVectors : Submodule ℂ (Lp ℂ 2 measureQ) where
  carrier := {φ | Langlands.IsSmoothVector (rationalQuotientL2FiniteRightAction F G measureQ hInv) φ}
  zero_mem' := ⟨⊤, by
    rw [Langlands.fixedVectors, Representation.mem_invariants]
    intro k
    exact map_zero _⟩
  add_mem' {φ ψ} hφ hψ := by
    obtain ⟨K, hK⟩ := hφ
    obtain ⟨K', hK'⟩ := hψ
    refine ⟨K ⊓ K', ?_⟩
    rw [Langlands.fixedVectors, Representation.mem_invariants] at hK hK' ⊢
    intro k
    change rationalQuotientL2FiniteRightAction F G measureQ hInv (k : _) (φ + ψ) = φ + ψ
    rw [map_add]
    exact congrArg₂ (· + ·) (hK ⟨k, k.property.1⟩) (hK' ⟨k, k.property.2⟩)
  smul_mem' c φ hφ := by
    obtain ⟨K, hK⟩ := hφ
    refine ⟨K, ?_⟩
    rw [Langlands.fixedVectors, Representation.mem_invariants] at hK ⊢
    intro k
    change rationalQuotientL2FiniteRightAction F G measureQ hInv (k : _) (c • φ) = c • φ
    rw [map_smul]
    exact congrArg (c • ·) (hK k)

theorem mem_rationalQuotientL2FiniteSmoothVectors (φ : Lp ℂ 2 measureQ) :
    φ ∈ rationalQuotientL2FiniteSmoothVectors F G measureQ hInv ↔
      Langlands.IsSmoothVector (rationalQuotientL2FiniteRightAction F G measureQ hInv) φ :=
  Iff.rfl

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  [ChartedSpace H (InfiniteAdelicGroupPoints F G)]

/-- The classes in `L²([G])` that are real smooth for the infinite adelic action and fixed by
some open subgroup of the finite adelic points. -/
def rationalQuotientL2BiSmoothVectors : Submodule ℂ (Lp ℂ 2 measureQ) :=
  Langlands.Archimedean.smoothVectors I (rationalQuotientL2InfiniteRightAction F G measureQ hInv) ⊓
    rationalQuotientL2FiniteSmoothVectors F G measureQ hInv

theorem mem_rationalQuotientL2BiSmoothVectors (φ : Lp ℂ 2 measureQ) :
    φ ∈ rationalQuotientL2BiSmoothVectors F G measureQ hInv I ↔
      φ ∈ Langlands.Archimedean.smoothVectors I
          (rationalQuotientL2InfiniteRightAction F G measureQ hInv) ∧
        Langlands.IsSmoothVector (rationalQuotientL2FiniteRightAction F G measureQ hInv) φ :=
  Iff.rfl

end Submodules

variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hc : IsCentral i)
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))
variable (Iₛ : Type) [Fintype Iₛ] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) Iₛ)

local notation "μ" => quotientHaarMeasure F G S j
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "π∞G" => rationalQuotientL2InfiniteRightAction F G μ hInv'
local notation "π∞P" => haarQuotientL2InfiniteRightAction F G T i hi Iₛ e hc
local notation "ρG" => rationalQuotientL2FiniteRightAction F G μ hInv'
local notation "ρP" => haarQuotientL2FiniteRightAction F G T i hi Iₛ e hc

/-- `quotientL2Equiv` carries the published positive-torus finite action to the finite action
on `[G]`. -/
theorem quotientL2Equiv_finiteRightAction (b : FiniteAdelicGroupPoints F G)
    (φ : QuotientL2 F G T i μQ) :
    quotientL2Equiv F G h (ρP b φ) = ρG b (quotientL2Equiv F G h φ) :=
  quotientL2Equiv_rightAction F G h (haarQuotientMeasureRightInvariant F G T i hi Iₛ e hc) hInv'
    _ φ

variable {𝔤 : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ 𝔤 H)
  [ChartedSpace H (InfiniteAdelicGroupPoints F G)]

/-- A positive-torus class is real smooth for the infinite action exactly when its image in
`L²([G])` is. -/
theorem isSmoothVector_quotientL2Equiv_iff (φ : QuotientL2 F G T i μQ) :
    Langlands.Archimedean.IsSmoothVector I π∞G (quotientL2Equiv F G h φ) ↔
      Langlands.Archimedean.IsSmoothVector I π∞P φ :=
  isSmoothVector_linearIsometryEquiv_iff I π∞P π∞G (quotientL2Equiv F G h)
    (quotientL2Equiv_infiniteRightAction F G h hi hc hInv' Iₛ e) φ

/-- A positive-torus class is fixed by an open subgroup of the finite adelic points exactly
when its image in `L²([G])` is. -/
theorem isFiniteSmoothVector_quotientL2Equiv_iff (φ : QuotientL2 F G T i μQ) :
    Langlands.IsSmoothVector ρG (quotientL2Equiv F G h φ) ↔ Langlands.IsSmoothVector ρP φ :=
  isSmoothVector_linearEquiv_iff ρP ρG (quotientL2Equiv F G h).toLinearEquiv
    (quotientL2Equiv_finiteRightAction F G h hi hc hInv' Iₛ e) φ

/-- `quotientL2Equiv` maps the positive-torus real smooth vectors onto those of `L²([G])`. -/
theorem image_quotientL2Equiv_smoothVectors :
    quotientL2Equiv F G h '' (Langlands.Archimedean.smoothVectors I π∞P : Set (QuotientL2 F G T i μQ)) =
      (Langlands.Archimedean.smoothVectors I π∞G : Set (Lp ℂ 2 μ)) := by
  ext ψ
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (isSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e I φ).2 hφ
  · intro hψ
    refine ⟨(quotientL2Equiv F G h).symm ψ, ?_, LinearIsometryEquiv.apply_symm_apply _ ψ⟩
    apply (isSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e I _).1
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact hψ

/-- `quotientL2Equiv` maps the positive-torus simultaneously smooth vectors onto those of
`L²([G])`. -/
theorem image_quotientL2Equiv_biSmoothVectors :
    quotientL2Equiv F G h '' {φ : QuotientL2 F G T i μQ |
        φ ∈ Langlands.Archimedean.smoothVectors I π∞P ∧ Langlands.IsSmoothVector ρP φ} =
      (rationalQuotientL2BiSmoothVectors F G μ hInv' I : Set (Lp ℂ 2 μ)) := by
  ext ψ
  constructor
  · rintro ⟨φ, ⟨hφ, hφ'⟩, rfl⟩
    exact ⟨(isSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e I φ).2 hφ,
      (isFiniteSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e φ).2 hφ'⟩
  · rintro ⟨hψ, hψ'⟩
    refine ⟨(quotientL2Equiv F G h).symm ψ, ⟨?_, ?_⟩, LinearIsometryEquiv.apply_symm_apply _ ψ⟩
    · apply (isSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e I _).1
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hψ
    · apply (isFiniteSmoothVector_quotientL2Equiv_iff F G h hi hc hInv' Iₛ e _).1
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hψ'

include h in
/-- Density of real smooth vectors transfers between the positive-torus quotient and `[G]`. -/
theorem dense_smoothVectors_iff :
    Dense (Langlands.Archimedean.smoothVectors I π∞G : Set (Lp ℂ 2 μ)) ↔
      Dense (Langlands.Archimedean.smoothVectors I π∞P : Set (QuotientL2 F G T i μQ)) := by
  rw [← image_quotientL2Equiv_smoothVectors F G h hi hc hInv' Iₛ e I]
  exact (quotientL2Equiv F G h).toHomeomorph.isDenseEmbedding.dense_image

include h in
/-- Density of simultaneously smooth vectors transfers between the positive-torus quotient and
`[G]`. -/
theorem dense_biSmoothVectors_iff :
    Dense (rationalQuotientL2BiSmoothVectors F G μ hInv' I : Set (Lp ℂ 2 μ)) ↔
      Dense {φ : QuotientL2 F G T i μQ |
        φ ∈ Langlands.Archimedean.smoothVectors I π∞P ∧ Langlands.IsSmoothVector ρP φ} := by
  rw [← image_quotientL2Equiv_biSmoothVectors F G h hi hc hInv' Iₛ e I]
  exact (quotientL2Equiv F G h).toHomeomorph.isDenseEmbedding.dense_image

end Langlands.Global.RestrictionSplitCentre
