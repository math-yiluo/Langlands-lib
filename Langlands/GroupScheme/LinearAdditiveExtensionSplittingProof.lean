import Langlands.GroupScheme.LinearAdditiveExtensionSplittingStatement
import Langlands.GroupScheme.LinearAdditiveExtension.Section

/-! # Splitting of extensions of diagonalizable groups by linear closed additive subgroups -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open LinearAdditiveExtension

/-- Milne (2022), Theorem 15.34(d), in the form of `LinearAdditiveExtensionSplittingStatement`:
an extension of a diagonalizable group by a closed subgroup of `𝔾ₐ` on which the group acts
through a character has a homomorphic section. -/
theorem linearAdditiveExtensionSplitting : LinearAdditiveExtensionSplittingStatement.{u} := by
  intro k _ _ Λ _ _ D E _ _ q hflat hsurj _ a ha χ b hconj hlin
  have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom
  have : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  have : IsAffineHom q.hom.hom.left := isAffineHom_of_isAffine _
  have : Flat q.hom.hom.left := hflat
  have : Surjective q.hom.hom.left := hsurj
  obtain ⟨fE, hfE⟩ := exists_equivariant q a χ hflat hsurj
  have hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      cd ((g * h) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (g ≫ crossedHom q a χ b fE hconj hlin hfE) +
          chi q χ g * cd (h ≫ crossedHom q a χ b fE hconj hlin hfE) := by
    intro T g h
    have := congrArg (fun m => cd (lift g h ≫ m)) (crossedHom_mul q a χ b fE hconj hlin hfE)
    rw [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, cd_mul,
      AutomorphicAction.naturality, cd_act, lift_fst_assoc, lift_fst_assoc,
      lift_snd_assoc] at this
    exact this
  have hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
      cd ((u ≫ (kernelι q).hom.hom) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (u ≫ a.hom.hom) := by
    intro T u
    rw [Category.assoc, kernel_comp_crossedHom q a χ b fE hconj hlin hfE ha]
  obtain ⟨c, h₁, h₂, h₃⟩ := exists_corrected q a χ b hlin ha _ hc₁ hc₂
  exact exists_section q a χ b hlin c h₁ h₂ ha h₃

end Langlands.GroupScheme
