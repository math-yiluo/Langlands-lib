import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestrictionStatement
import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.FibreGenericNeighbourhood
import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.TranslationDensity
import Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.DvrDenseOpen

/-! # Proof that birational group laws over a DVR are strict on a dense open -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry

open StrictBirationalGroupLawRestriction

/-- Proof of `StrictBirationalGroupLawRestrictionStatement` (Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §5.2 Proposition 2, in the case of a discrete valuation ring). The open `X'`
is chosen by `exists_opens_of_forall_fibreGeneric` so that `D ∩ Φ(D) ∩ Ψ(D)` contains the generic
points of the fibres of both projections over its points, and the six density conditions follow
from `translation_density`. -/
theorem strictBirationalGroupLawRestriction :
    StrictBirationalGroupLawRestrictionStatement.{u} := by
  intro R _ _ _ X f hsm hsep hlft hqc hsurj m
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set p₁ := pullback.fst f f with hp₁
  set p₂ := pullback.snd f f with hp₂
  set D := m.domain with hD
  set Φ := leftTranslation f m.domain m.mul m.mul_comp with hΦ
  set Ψ := rightTranslation f m.domain m.mul m.mul_comp with hΨ
  have : IsOpenImmersion Φ := m.isOpenImmersion_leftTranslation
  have : IsOpenImmersion Ψ := m.isOpenImmersion_rightTranslation
  set F := fibreGenericPoints f with hF
  have hFgen (ξ : X) (hξ : ξ ∈ F) : IsFibreGeneric f ξ := (mem_fibreGenericPoints_iff f ξ).mp hξ
  -- The open set `Z = D ∩ Φ(D) ∩ Ψ(D)` contains the generic points of the fibres over `S`.
  let Z : Set ↑(pullback f f) := (D : Set _) ∩ Set.range Φ ∩ Set.range Ψ
  have hZo : IsOpen Z :=
    (D.2.inter Φ.isOpenEmbedding.isOpen_range).inter Ψ.isOpenEmbedding.isOpen_range
  have hZgen (q : ↑(pullback f f)) (hq : IsFibreGeneric (p₁ ≫ f) q) : q ∈ Z := by
    have hq' : q ∈ fibreGenericPoints (p₁ ≫ f) := (mem_fibreGenericPoints_iff _ q).mpr hq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact (fibreGenericPoints_subset_iff _ _).mpr m.domain_dense hq'
    · exact (fibreGenericPoints_subset_iff _ _).mpr m.leftTranslation_dense hq'
    · exact (fibreGenericPoints_subset_iff _ _).mpr m.rightTranslation_dense hq'
  have hcond (q : ↑(pullback f f)) : f (p₁ q) = f (p₂ q) :=
    congrArg (fun h => h.base q) (pullback.condition (f := f) (g := f))
  -- Neighbourhoods of the generic points of the fibres of `X`.
  let G : X → Prop := fun x =>
    (∀ q, p₁ q = x → IsFibreGeneric p₁ q → q ∈ Z) ∧ (∀ q, p₂ q = x → IsFibreGeneric p₂ q → q ∈ Z)
  obtain ⟨X', hFX', hX'G⟩ := exists_opens_of_forall_fibreGeneric R f G (by
    intro ξ hξ
    obtain ⟨N₁, hN₁o, hξN₁, hN₁⟩ := exists_open_forall_isFibreGeneric_mem p₁ Z hZo ξ (by
      intro q hqξ hq
      apply hZgen
      intro q' hq'q hfq'
      have h1 : p₁ q' = ξ := hFgen ξ hξ (p₁ q') (hqξ ▸ hq'q.map p₁.continuous)
        (by rw [← hqξ]; exact hfq')
      exact hq q' hq'q (h1.trans hqξ.symm))
    obtain ⟨N₂, hN₂o, hξN₂, hN₂⟩ := exists_open_forall_isFibreGeneric_mem p₂ Z hZo ξ (by
      intro q hqξ hq
      apply hZgen
      intro q' hq'q hfq'
      have hfq'' : f (p₂ q') = f (p₂ q) := by
        rw [← hcond, ← hcond]; exact hfq'
      have h1 : p₂ q' = ξ := hFgen ξ hξ (p₂ q') (hqξ ▸ hq'q.map p₂.continuous)
        (by rw [← hqξ]; exact hfq'')
      exact hq q' hq'q (h1.trans hqξ.symm))
    exact ⟨N₁ ∩ N₂, hN₁o.inter hN₂o, ⟨hξN₁, hξN₂⟩, fun x hx hξx =>
      ⟨hN₁ x hx.1 hξx, hN₂ x hx.2 hξx⟩⟩)
  refine ⟨X', (fibreGenericPoints_subset_iff f _).mp hFX', ?_⟩
  -- The open `U'` of points of the domain with both coordinates and product in `X'`.
  let U'set : Set ↑(pullback f f) :=
    {y | p₁ y ∈ X' ∧ p₂ y ∈ X' ∧ ∃ u, D.ι u = y ∧ m.mul u ∈ X'}
  have hU'o : IsOpen U'set := by
    have : U'set = p₁ ⁻¹' X' ∩ p₂ ⁻¹' X' ∩ D.ι '' (m.mul ⁻¹' X') := by
      ext y
      simp only [U'set, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨h1, h2, u, hu, hm⟩; exact ⟨⟨h1, h2⟩, u, hm, hu⟩
      · rintro ⟨⟨h1, h2⟩, u, hm, hu⟩; exact ⟨h1, h2, u, hu, hm⟩
    rw [this]
    exact ((X'.2.preimage p₁.continuous).inter (X'.2.preimage p₂.continuous)).inter
      (D.ι.isOpenEmbedding.isOpenMap _ (X'.2.preimage m.mul.continuous))
  let U' : (pullback f f).Opens := ⟨U'set, hU'o⟩
  have eΦ₁ : Φ ≫ p₁ = D.ι ≫ p₁ := pullback.lift_fst _ _ _
  have eΦ₂ : Φ ≫ p₂ = m.mul := pullback.lift_snd _ _ _
  have eΨ₁ : Ψ ≫ p₁ = m.mul := pullback.lift_fst _ _ _
  have eΨ₂ : Ψ ≫ p₂ = D.ι ≫ p₂ := pullback.lift_snd _ _ _
  have hdens := translation_density p₁ p₂ p₁.continuous p₂.continuous D.ι Φ Ψ m.mul
    D.ι.isOpenEmbedding Φ.isOpenEmbedding Ψ.isOpenEmbedding
    (funext fun u => congrArg (fun h : D.toScheme ⟶ X => h.base u) eΦ₁)
    (funext fun u => congrArg (fun h : D.toScheme ⟶ X => h.base u) eΦ₂)
    (funext fun u => congrArg (fun h : D.toScheme ⟶ X => h.base u) eΨ₁)
    (funext fun u => congrArg (fun h : D.toScheme ⟶ X => h.base u) eΨ₂)
    F X' X'.2 hFX'
    (fun y => by
      obtain ⟨y₀, hy₀, h1, h2⟩ := exists_fibreGenericPoint_specializes p₁ y
      exact ⟨y₀, (mem_fibreGenericPoints_iff _ _).mp hy₀, h1, h2⟩)
    (fun y => by
      obtain ⟨y₀, hy₀, h1, h2⟩ := exists_fibreGenericPoint_specializes p₂ y
      exact ⟨y₀, (mem_fibreGenericPoints_iff _ _).mp hy₀, h1, h2⟩)
    (fun y hy => (mem_fibreGenericPoints_iff f _).mpr (isFibreGeneric_snd f f hy))
    (fun y hy => (mem_fibreGenericPoints_iff f _).mpr (isFibreGeneric_fst f f hy))
    (fun y hy hyX' => by
      obtain ⟨⟨hD', hΦ'⟩, hΨ'⟩ := (hX'G _ hyX').1 y rfl hy
      exact ⟨by rw [Scheme.Opens.range_ι]; exact hD', hΦ', hΨ'⟩)
    (fun y hy hyX' => by
      obtain ⟨⟨hD', hΦ'⟩, hΨ'⟩ := (hX'G _ hyX').2 y rfl hy
      exact ⟨by rw [Scheme.Opens.range_ι]; exact hD', hΦ', hΨ'⟩)
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdens
  refine ⟨U', ?_, fun y hy => hy.1, fun y hy => hy.2.1, ?_, d1, d2, d3, d4, d5, d6⟩
  · intro y hy
    obtain ⟨u, rfl, -⟩ := hy.2.2
    have := Set.mem_range_self (f := D.ι) u
    rwa [Scheme.Opens.range_ι] at this
  · intro u hu
    obtain ⟨u', hu', hm⟩ := hu.2.2
    rw [D.ι.isOpenEmbedding.injective hu'] at hm
    exact hm

end Langlands.AlgebraicGeometry
