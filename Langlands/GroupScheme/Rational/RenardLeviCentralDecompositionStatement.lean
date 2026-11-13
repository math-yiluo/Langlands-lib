import Langlands.Geometry.Building.RealTorusDuality

/-! # Renard V.3.6: central and relative directions for compatible Levi data

The statement uses the actual shared character and cocharacter tensor spaces
and split-component morphisms. It does not assume the decompositions or a
root-system realization, and it does not assert geometric Levi factorization.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

/-- The real character diagram and its two direct-sum decompositions from
Renard V.3.6, for actual compatible split components of connected reductive
groups. The linear-algebra assertion applies to every such morphism, including
an arbitrary Levi inclusion with its displayed split-component factorization.
The relative cocharacter space is the pairing annihilator of the central
character directions, so both decompositions use the published actual pairing. -/
def RenardLeviCentralDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
    IsConnectedReductive G → IsConnectedReductive M →
    ∀ (AG AM : CommGroupScheme (Spec (CommRingCat.of k)))
      (aG : AG.toGrp ⟶ G) (aM : AM.toGrp ⟶ M) (f : AG ⟶ AM),
      IsSplitComponent aG → IsSplitComponent aM →
      CommGroupScheme.groupHom f ≫ aM ≫ j = aG →
      Function.Bijective (rationalCharacterRestrictReal aG) ∧
      Function.Bijective (rationalCharacterRestrictReal aM) ∧
      ∃ s : Vstar AG →ₗ[ℝ] Vstar AM,
        s.comp (rationalCharacterRestrictReal aG) =
          rationalCharacterRestrictReal (aM ≫ j) ∧
        (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).comp s =
          LinearMap.id ∧
        s.range = (rationalCharacterRestrictReal (aM ≫ j)).range ∧
        IsCompl s.range
          (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker ∧
        (∃ e : (Vstar AG ×
            (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker) ≃ₗ[ℝ]
              Vstar AM,
          ∀ (x : Vstar AG)
            (y : (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker),
            e (x, y) = s x + (y : Vstar AM)) ∧
        Function.Injective (cocharacterMapReal f) ∧
        IsCompl (cocharacterMapReal f).range (cocharacterAnnihilator s.range) ∧
        (∃ e : (V AG × cocharacterAnnihilator s.range) ≃ₗ[ℝ] V AM,
          ∀ (x : V AG) (y : cocharacterAnnihilator s.range),
            e (x, y) = cocharacterMapReal f x + (y : V AM))

end Langlands.GroupScheme
