import Langlands.ClassField.Global.RelativeWeilTransferReciprocityStatement
import Langlands.ClassField.Global.RelativeWeilSplittingNorm
import Langlands.GroupTheory.CocycleSplittingAbelianization
import Langlands.GroupTheory.CocycleSplittingTransfer

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits NumberField
open scoped NumberField

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NormalizedTwoCocycle.SplittingModule

set_option backward.isDefEq.respectTransparency false

attribute [local instance] relativeIdeleClassAction

variable (c : FundamentalClass.ClassFamily.{u}) (F E : Type u)
  [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

private lemma splittingNormToBase_extensionCoinvariant :
    letI := Fintype.ofFinite (E ≃ₐ[F] E)
    ∀ t : RelativeWeilGroup c F E,
      splittingNormToBase F E c
          (extensionCoinvariant (ClassExtension.representative (c F E)) t) =
        Additive.ofMul (transfer c F E t) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  intro t
  change (splittingNormToBase F E c
    (extensionCoinvariant (ClassExtension.representative (c F E)) t)).toMul =
      transfer c F E t
  apply (ideleClassGaloisDescent F E).1
  rw [ideleClassInclusion_splittingNormToBase, ideleClassInclusion_transfer]
  exact splittingNorm_extensionCoinvariant_toMul
    (ClassExtension.representative (c F E)) t

private theorem transfer_reciprocity_of_splitting_comparison
    (hgen : FundamentalClass.Generates c) (hres : FundamentalClass.Restriction c)
    (hcompare :
      letI := Fintype.ofFinite (E ≃ₐ[F] E)
      ∀ t : RelativeWeilGroup c F E,
        splittingNormToBase F E c
            (extensionCoinvariant (ClassExtension.representative (c F E)) t) =
          Additive.ofMul (transfer c F E t)) :
    Function.Surjective (transfer c F E) ∧
      (transfer c F E).ker = commutator (RelativeWeilGroup c F E) := by
  let := Fintype.ofFinite (E ≃ₐ[F] E)
  let C := ClassExtension.representative (c F E)
  let e := coinvariantsAbelianizationEquiv C
  have hn := splittingNormToBase_bijective F E c hgen hres
  have hq : Function.Surjective (extensionCoinvariant C) := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e y).toMul
    refine ⟨x, ?_⟩
    apply e.injective
    change coinvariantsToAbelianization C (extensionCoinvariant C x) = e y
    rw [coinvariantsToAbelianization_extensionCoinvariant]
    exact congrArg Additive.ofMul hx
  constructor
  · intro a
    obtain ⟨v, hv⟩ := hn.2 (Additive.ofMul a)
    obtain ⟨x, rfl⟩ := hq v
    refine ⟨x, ?_⟩
    exact congrArg Additive.toMul ((hcompare x).symm.trans hv)
  · apply le_antisymm ?_ (commutator_le_ker_transfer c F E)
    intro x hx
    change transfer c F E x = 1 at hx
    have hzero : extensionCoinvariant C x = 0 := by
      apply hn.1
      rw [map_zero, hcompare x]
      exact congrArg Additive.ofMul hx
    have hab : Abelianization.of x = 1 := by
      have h := congrArg (coinvariantsToAbelianization C) hzero
      rw [coinvariantsToAbelianization_extensionCoinvariant, map_zero] at h
      exact congrArg Additive.toMul h
    rw [← Abelianization.ker_of (RelativeWeilGroup c F E)]
    exact hab

/-- Transfer reciprocity for the actual relative global Weil groups under
the full original arithmetic fundamental-class hypotheses. -/
theorem relativeWeilTransferReciprocity : RelativeWeilTransferReciprocityStatement.{u} := by
  intro I hI d hd K L _ _ _ _ _ _
  exact transfer_reciprocity_of_splitting_comparison d K L hd.1 hd.2.1
    (splittingNormToBase_extensionCoinvariant d K L)

end Langlands.ClassField.Global.RelativeWeilGroup
