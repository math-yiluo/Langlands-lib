import Langlands.Representation.LanglandsClassification.OppositeIntertwiningExponentComparison
import Langlands.GroupScheme.Rational.DominantInvariantFormComparison

/-! # Equality of the parameters of two Langlands triplets from mutual cone estimates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  {J₁ J₂ : Set (characterLattice T)} {f₁ : A₁ ⟶ T} {f₂ : A₂ ⟶ T}
  {p₁ : P₁ ⟶ G} {l₁ : M₁ ⟶ P₁} {a₁ : A₁.toGrp ⟶ M₁}
  {p₂ : P₂ ⟶ G} {l₂ : M₂ ⟶ P₂} {a₂ : A₂.toGrp ⟶ M₂}

/-- The full real parameter of an unramified character whose split-component real part
lies in the open coroot chamber is dominant: it pairs nonnegatively with every simple
coroot. -/
theorem pair_leviUnramifiedFullRealPart_nonneg (hG : IsConnectedReductive G)
    (D : RelativeRootReflectionData i)
    (h : (⟨T, i, ν, J₁, f₁⟩ : ParabolicRootPresentationData A₁ G).IsCompatible p₁ l₁ a₁)
    (ψ : leviUnramifiedCharacters l₁ h.levi)
    (hψ : leviUnramifiedRealPart l₁ h.levi a₁ h.splitComponent ψ ∈
      restrictedCorootChamber i ν J₁ f₁ D)
    (α : relativeRoots i) (hα : α.val ∈ simpleRelativeRoots i ν) :
    0 ≤ pair T (leviUnramifiedFullRealPart
        (⟨⟨T, i, ν, J₁, f₁⟩, h⟩ : ParabolicRootPresentation p₁ l₁ a₁) ψ)
      ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) := by
  by_cases hαJ : α.val ∈ J₁
  · exact (pair_leviUnramifiedFullRealPart_selectedCoroot
      (⟨⟨T, i, ν, J₁, f₁⟩, h⟩ : ParabolicRootPresentation p₁ l₁ a₁) hG D ψ α hαJ).ge
  · exact (pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber
      (⟨⟨T, i, ν, J₁, f₁⟩, h⟩ : ParabolicRootPresentation p₁ l₁ a₁) hG D ψ hψ α hα hαJ).le

/-- Renard VII.4.2 (ii), comparison of the real parameters, in two-sided form. For two
standard Levis presented by the same `(T, i, ν)` with indices `J₁, J₂`, and unramified
characters `ψ₁, ψ₂` whose real parts lie in the open coroot chambers, suppose that a Weyl
translate of each full real parameter dominates the other one modulo the nonnegative
restricted root cone of the other index. Then the two full real parameters are equal and
`J₁ = J₂`. -/
theorem fullRealPart_eq_and_index_eq_of_mutual_mem_nonnegCone
    (hG : IsConnectedReductive G) (D : RelativeRootReflectionData i)
    (h₁ : (⟨T, i, ν, J₁, f₁⟩ : ParabolicRootPresentationData A₁ G).IsCompatible p₁ l₁ a₁)
    (h₂ : (⟨T, i, ν, J₂, f₂⟩ : ParabolicRootPresentationData A₂ G).IsCompatible p₂ l₂ a₂)
    (ψ₁ : leviUnramifiedCharacters l₁ h₁.levi) (ψ₂ : leviUnramifiedCharacters l₂ h₂.levi)
    (hψ₁ : leviUnramifiedRealPart l₁ h₁.levi a₁ h₁.splitComponent ψ₁ ∈
      restrictedCorootChamber i ν J₁ f₁ D)
    (hψ₂ : leviUnramifiedRealPart l₂ h₂.levi a₂ h₂.splitComponent ψ₂ ∈
      restrictedCorootChamber i ν J₂ f₂ D)
    (w₁ w₂ : relativeWeylGroup i)
    (hc₁ : rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (relativeWeylFullRealAction i w₁ (leviUnramifiedFullRealPart
          (⟨⟨T, i, ν, J₁, f₁⟩, h₁⟩ : ParabolicRootPresentation p₁ l₁ a₁) ψ₁)) -
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (leviUnramifiedFullRealPart
          (⟨⟨T, i, ν, J₂, f₂⟩, h₂⟩ : ParabolicRootPresentation p₂ l₂ a₂) ψ₂) ∈
      (⟨⟨T, i, ν, J₂, f₂⟩, h₂⟩ : ParabolicRootPresentation p₂ l₂ a₂).nonnegCone)
    (hc₂ : rationalCharacterRestrictReal (CommGroupScheme.groupHom f₁)
        (relativeWeylFullRealAction i w₂ (leviUnramifiedFullRealPart
          (⟨⟨T, i, ν, J₂, f₂⟩, h₂⟩ : ParabolicRootPresentation p₂ l₂ a₂) ψ₂)) -
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₁)
        (leviUnramifiedFullRealPart
          (⟨⟨T, i, ν, J₁, f₁⟩, h₁⟩ : ParabolicRootPresentation p₁ l₁ a₁) ψ₁) ∈
      (⟨⟨T, i, ν, J₁, f₁⟩, h₁⟩ : ParabolicRootPresentation p₁ l₁ a₁).nonnegCone) :
    leviUnramifiedFullRealPart
        (⟨⟨T, i, ν, J₁, f₁⟩, h₁⟩ : ParabolicRootPresentation p₁ l₁ a₁) ψ₁ =
      leviUnramifiedFullRealPart
        (⟨⟨T, i, ν, J₂, f₂⟩, h₂⟩ : ParabolicRootPresentation p₂ l₂ a₂) ψ₂ ∧
    J₁ = J₂ := by
  let pres₁ : ParabolicRootPresentation p₁ l₁ a₁ := ⟨⟨T, i, ν, J₁, f₁⟩, h₁⟩
  let pres₂ : ParabolicRootPresentation p₂ l₂ a₂ := ⟨⟨T, i, ν, J₂, f₂⟩, h₂⟩
  have hy₁J := pair_leviUnramifiedFullRealPart_selectedCoroot pres₁ hG D ψ₁
  have hy₂J := pair_leviUnramifiedFullRealPart_selectedCoroot pres₂ hG D ψ₂
  have hy : leviUnramifiedFullRealPart pres₁ ψ₁ = leviUnramifiedFullRealPart pres₂ ψ₂ :=
    D.eq_of_mutual_mem_restrictedRootNonnegCone ν hG h₁.maximalSplit h₁.generic
      pres₁.finite_simpleRoots f₁ f₂ h₁.subset_simpleRoots h₂.subset_simpleRoots
      (pair_leviUnramifiedFullRealPart_nonneg hG D h₁ ψ₁ hψ₁)
      (pair_leviUnramifiedFullRealPart_nonneg hG D h₂ ψ₂ hψ₂) hy₁J hy₂J
      (fun z hz => pres₁.mem_selectedRootSpan_of_restrict_eq_zero hz)
      (fun z hz => pres₂.mem_selectedRootSpan_of_restrict_eq_zero hz) w₁ w₂ hc₁ hc₂
  refine ⟨hy, ?_⟩
  apply D.selected_eq_of_pair ν h₁.subset_simpleRoots h₂.subset_simpleRoots hy₁J
  · rw [hy]
    exact hy₂J
  · exact pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber pres₁ hG D ψ₁ hψ₁
  · rw [hy]
    exact pair_leviUnramifiedFullRealPart_pos_of_mem_restrictedCorootChamber pres₂ hG D ψ₂ hψ₂

end Langlands.Aubert.General.RepresentedParabolic
