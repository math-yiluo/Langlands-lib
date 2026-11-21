import Langlands.Global.AdelicEisensteinAmbientParametersProof
import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # The ambient linear part of a Bruhat exponent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints RealTorusSpace

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)
  (I I₁ J : StandardIndex F G fam.i fam.ν)
  (f : fam.P I₁ ⟶ fam.P I)

omit [NumberField F] in
private theorem standardParabolic_mono (T : StandardIndex F G fam.i fam.ν) : Mono (fam.p T) := by
  have h : Mono (fam.p T).hom.hom := by
    let := (fam.isCompatible T).parabolic.isClosedSubgroup.mono
    exact Over.mono_of_mono_left _
  exact (Grp.forget _).mono_of_mono_map (f := fam.p T) h

omit [NumberField F] in
/-- Restriction along an inclusion of the supplied standard parabolics
does not change the ambient real parameter. -/
theorem chamberEmbedding_parameterRestrict (hf : f ≫ fam.p I = fam.p I₁)
    (lam : ComplexCharacterParameter F (fam.P I)) :
    fam.chamberEmbedding I₁ (parameterRealPart F (fam.P I₁) (parameterRestrict f lam)) =
      fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam) := by
  let : Mono (fam.p I) := standardParabolic_mono fam I
  have hT : (fam.torus I₁ ≫ fam.l I₁) ≫ f = fam.torus I ≫ fam.l I := by
    apply (cancel_mono (fam.p I)).mp
    simp only [Category.assoc, hf, fam.torus_comp]
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    change realParameterRestriction (fam.torus I₁ ≫ fam.l I₁)
        (parameterRealPart F (fam.P I₁) (s ⊗ₜ[ℤ] characterRestrict f χ)) =
      realParameterRestriction (fam.torus I ≫ fam.l I) (parameterRealPart F (fam.P I) (s ⊗ₜ[ℤ] χ))
    simp only [parameterRealPart_tmul]
    change s.re ⊗ₜ[ℤ] characterRestrict (fam.torus I₁ ≫ fam.l I₁) (characterRestrict f χ) =
      s.re ⊗ₜ[ℤ] characterRestrict (fam.torus I ≫ fam.l I) χ
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hT]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (n : normalizerPoints fam.i) (c : fam.M J ⟶ fam.M I₁) (π : fam.P J ⟶ fam.M J)

/-- The affine exponent of a surviving Bruhat term has linear part given
by the actual Weyl transport of restriction of the original parameter. -/
def StandardBruhatParameterStatement : Prop :=
  f ≫ fam.p I = fam.p I₁ → fam.l J ≫ π = 𝟙 (fam.M J) →
  IsWeylConjugation (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J) n.val c →
  ∀ lam : ComplexCharacterParameter F (fam.P I),
    fam.chamberEmbedding J
        (parameterRealPart F (fam.P J) (weylParameter (fam.l I₁) c π (parameterRestrict f lam))) =
      relativeWeylRealCharacterAction fam.i (QuotientGroup.mk n)
        (fam.chamberEmbedding I (parameterRealPart F (fam.P I) lam))

set_option maxHeartbeats 1600000 in
theorem standardBruhatParameter : StandardBruhatParameterStatement fam I I₁ J f n c π := by
  intro hf hπ hw lam
  let : Mono (fam.p I₁) := standardParabolic_mono fam I₁
  have h := eisensteinAmbientWeylParameter F G (fam.P I₁) (fam.M I₁) (fam.P J) (fam.M J)
    fam.T fam.i (fam.p I₁) (fam.l I₁) (fam.p J) (fam.l J)
    (fam.torus I₁) (fam.torus J) π n c (fam.torus_comp I₁) (fam.torus_comp J) hπ hw
    (parameterRestrict f lam)
  change fam.chamberEmbedding J
      (parameterRealPart F (fam.P J) (weylParameter (fam.l I₁) c π (parameterRestrict f lam))) =
    relativeWeylRealCharacterAction fam.i (QuotientGroup.mk n)
      (fam.chamberEmbedding I₁ (parameterRealPart F (fam.P I₁) (parameterRestrict f lam))) at h
  rwa [fam.chamberEmbedding_parameterRestrict I I₁ f hf lam] at h

end Langlands.Global.StandardParabolicFamily
