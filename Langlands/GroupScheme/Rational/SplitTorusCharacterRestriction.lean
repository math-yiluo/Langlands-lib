import Langlands.GroupScheme.Rational.SplitTorusMonomorphism
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Character restriction along monomorphisms of actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {A T : GroupScheme (Spec (CommRingCat.of k))}

/-- A scheme monomorphism between actual split tori is surjective on integral
characters. -/
theorem IsSplitTorus.characterRestrict_surjective_of_mono (hA : IsSplitTorus A)
    (hT : IsSplitTorus T) (f : A ⟶ T) [Mono f.hom.hom.left] :
    Function.Surjective (characterRestrict f) := by
  obtain ⟨I, hI, ⟨eA⟩⟩ := hA
  obtain ⟨J, hJ, ⟨eT⟩⟩ := hT
  let g := eA.inv ≫ f ≫ eT.hom
  have : IsIso eA.inv.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map eA.inv)))
  have : IsIso eT.hom.hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map ((Grp.forget _).map eT.hom)))
  have : Mono g.hom.hom.left := by
    change Mono (eA.inv.hom.hom.left ≫ f.hom.hom.left ≫ eT.hom.hom.hom.left)
    infer_instance
  have : Mono g.hom.hom := Over.mono_of_mono_left _
  intro χ
  obtain ⟨m, hm⟩ := splitTorus.characterMap_surjective I J g
    (splitTorus.characterLatticeEquiv k I (characterRestrict eA.inv χ))
  let ψ := (splitTorus.characterLatticeEquiv k J).symm m
  have hψ : characterRestrict g ψ = characterRestrict eA.inv χ := by
    apply (splitTorus.characterLatticeEquiv k I).injective
    change (splitTorus.characterLatticeEquiv k I)
      ((Additive.ofMul g : splitTorus.commGroupScheme _ I ⟶
        splitTorus.commGroupScheme _ J) ≫ ψ) = _
    rw [← splitTorus.characterMap_equiv I J g ψ]
    simpa only [ψ, AddEquiv.apply_symm_apply] using hm
  refine ⟨characterRestrict eT.hom ψ, ?_⟩
  have h := congrArg (characterRestrict eA.hom) hψ
  simpa only [g, ← AddMonoidHom.comp_apply, ← characterRestrict_comp,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, characterRestrict_id,
    AddMonoidHom.id_apply] using h

/-- Rationalized restriction along a scheme monomorphism of split tori is
surjective. -/
theorem IsSplitTorus.rationalCharacterRestrictRat_surjective_of_mono
    (hA : IsSplitTorus A) (hT : IsSplitTorus T) (f : A ⟶ T)
    [Mono f.hom.hom.left] :
    Function.Surjective (rationalCharacterRestrictRat f) :=
  LinearMap.baseChange_surjective ℚ
    (hA.characterRestrict_surjective_of_mono hT f)

/-- Real restriction along a scheme monomorphism of split tori is surjective. -/
theorem IsSplitTorus.rationalCharacterRestrictReal_surjective_of_mono
    (hA : IsSplitTorus A) (hT : IsSplitTorus T) (f : A ⟶ T)
    [Mono f.hom.hom.left] :
    Function.Surjective (rationalCharacterRestrictReal f) :=
  LinearMap.baseChange_surjective ℝ
    (hA.characterRestrict_surjective_of_mono hT f)

/-- A chosen extension of an actual character along a scheme monomorphism
between split tori. -/
def IsSplitTorus.characterLift (hA : IsSplitTorus A) (hT : IsSplitTorus T)
    (f : A ⟶ T) [Mono f.hom.hom.left] (χ : rationalCharacters A) :
    rationalCharacters T :=
  Classical.choose (hA.characterRestrict_surjective_of_mono hT f χ)

@[simp] theorem IsSplitTorus.characterRestrict_characterLift
    (hA : IsSplitTorus A) (hT : IsSplitTorus T)
    (f : A ⟶ T) [Mono f.hom.hom.left] (χ : rationalCharacters A) :
    characterRestrict f (hA.characterLift hT f χ) = χ :=
  Classical.choose_spec (hA.characterRestrict_surjective_of_mono hT f χ)

end Langlands.GroupScheme
