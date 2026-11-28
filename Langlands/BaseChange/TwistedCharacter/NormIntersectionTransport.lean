import Langlands.BaseChange.TwistedCharacter.CompactSemisimpleDescentPushforward
import Langlands.HarmonicAnalysis.UnitConjugation.NormOrbitIntertwining
import Langlands.Representation.Character.CompactTraceSelfIntertwining

/-! # Compact intertwining under open subgroup image charts -/

noncomputable section

namespace Langlands.BaseChange

open HarmonicAnalysis UnitConjugation Character Set Function _root_.Topology

section Intertwiner

variable {G J X Y : Type*} [Group G] [Group J]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

private theorem nonzeroIntertwiner_of_restrict (f : J →* G)
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {ρ' : Representation ℂ J X} {σ' : Representation ℂ J Y}
    (hρ : ∀ x, ρ' x = ρ (f x)) (hσ : ∀ x, σ' x = σ (f x)) :
    (∃ A : Representation.IntertwiningMap ρ σ, A ≠ 0) →
      ∃ A' : Representation.IntertwiningMap ρ' σ', A' ≠ 0 := by
  rintro ⟨A, hA⟩
  let A' : Representation.IntertwiningMap ρ' σ' :=
    ⟨A.toLinearMap, fun x => by rw [hρ, hσ]; exact A.isIntertwining' (f x)⟩
  refine ⟨A', fun h => hA (Representation.IntertwiningMap.ext ?_)⟩
  exact congrArg (fun T : Representation.IntertwiningMap ρ' σ' => T.toLinearMap) h

end Intertwiner

variable {G H X Y : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  (i : G →* H) (hi : IsOpenEmbedding i) (K : OpenSubgroup G)

section Slice

variable {M : Type*} [Group M] [TopologicalSpace M]
  (f : M →* G) (hf : Continuous f)
  (τ : Representation ℂ (openSubgroupImage K i hi) X) (σ : Representation ℂ M Y)

/-- A slice intertwiner on the ambient image pulls back to the actual unit subgroup intersection. -/
def OpenImageSliceIntertwiningStatement : Prop :=
  let ι := i.comp f
  let hι := hi.continuous.comp hf
  let K' := openSubgroupImage K i hi
  let E := openSubgroupImageEquiv K i hi
  let J := K.toSubgroup.comap f
  let J' := K'.comap ι hι
  (∃ A : Representation.IntertwiningMap (τ.comp (compactSliceRestriction K' ι hι))
    (σ.comp J'.toSubgroup.subtype), A ≠ 0) →
  ∃ A : Representation.IntertwiningMap ((τ.comp E.toMonoidHom).comp (subgroupComapHom K.toSubgroup f))
    (σ.comp J.subtype), A ≠ 0

omit [IsTopologicalGroup H] in
theorem openImageSliceIntertwining : OpenImageSliceIntertwiningStatement i hi K f hf τ σ := by
  intro hA
  let ι := i.comp f
  let hι : Continuous ι := hi.continuous.comp hf
  let K' := openSubgroupImage K i hi
  let E := openSubgroupImageEquiv K i hi
  let J := K.toSubgroup.comap f
  let J' := K'.comap ι hι
  let ψ : J →* J' := J.subtype.codRestrict J'.toSubgroup fun x => ⟨f x.val, x.property, rfl⟩
  have hK (x : J) : E (subgroupComapHom K.toSubgroup f x) = compactSliceRestriction K' ι hι (ψ x) := by
    apply Subtype.ext
    rfl
  apply nonzeroIntertwiner_of_restrict ψ (ρ := τ.comp (compactSliceRestriction K' ι hι))
    (σ := σ.comp J'.toSubgroup.subtype) _ _ hA
  · intro x
    exact congrArg τ (hK x)
  · intro x
    rfl

end Slice

section Conjugate

variable (L : OpenSubgroup G) (β : G →* G) (y : H)
  (ρ : Representation ℂ (openSubgroupImage K i hi) X)
  (σ : Representation ℂ (openSubgroupImage L i hi) Y)

/-- If the homomorphism on units implements inverse ambient conjugation, an
intertwiner on the ambient conjugate intersection restricts to the unit intersection. -/
def OpenImageConjugateIntertwiningStatement : Prop :=
  (∀ g, i (β g) = y⁻¹ * i g * y) →
  let K' := openSubgroupImage K i hi
  let L' := openSubgroupImage L i hi
  let E₁ := openSubgroupImageEquiv K i hi
  let E₂ := openSubgroupImageEquiv L i hi
  let J' := conjugateIntersection L' K' y
  let φ := β.comp K.toSubgroup.subtype
  let J := L.toSubgroup.comap φ
  (∃ A : Representation.IntertwiningMap (ρ.comp J'.toSubgroup.subtype)
    (σ.comp (conjugateIntersectionTransport L' K' y)), A ≠ 0) →
  ∃ A : Representation.IntertwiningMap ((ρ.comp E₁.toMonoidHom).comp J.subtype)
    ((σ.comp E₂.toMonoidHom).comp (subgroupComapHom L.toSubgroup φ)), A ≠ 0

theorem openImageConjugateIntertwining : OpenImageConjugateIntertwiningStatement i hi K L β y ρ σ := by
  intro hβ K' L' E₁ E₂ J' φ J hA
  let ψ : J →* J' := (E₁.toMonoidHom.comp J.subtype).codRestrict J'.toSubgroup fun x => by
    change y⁻¹ * i x.val.val * y⁻¹⁻¹ ∈ L'
    rw [inv_inv, ← hβ]
    exact ⟨β x.val.val, x.property, rfl⟩
  have hL (x : J) : E₂ (subgroupComapHom L.toSubgroup φ x) = conjugateIntersectionTransport L' K' y (ψ x) := by
    apply Subtype.ext
    change i (β x.val.val) = y⁻¹ * i x.val.val * y⁻¹⁻¹
    rw [inv_inv, hβ]
  apply nonzeroIntertwiner_of_restrict ψ (ρ := ρ.comp J'.toSubgroup.subtype)
    (σ := σ.comp (conjugateIntersectionTransport L' K' y)) _ _ hA
  · intro x
    rfl
  · intro x
    exact congrArg σ (hL x)

end Conjugate

end Langlands.BaseChange
