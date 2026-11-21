import Langlands.Global.AdelicIntertwiningOperator
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Torus.UnipotentHom

/-! # Linear equivalence of Weyl parameters -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {P Q M M' : GroupScheme (Spec (CommRingCat.of F))}

private theorem characterRestrict_injective_of_levi {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) : Function.Injective (characterRestrict l) := by
  obtain ⟨U, i, hi, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l i) := hmul
  intro χ ψ h
  apply Additive.toMul.injective
  apply hom_ext_points
  intro T x
  have hfactor (θ : rationalCharacters P) :
      x ≫ θ.toMul.hom.hom = leviComponent l i x ≫ (characterRestrict l θ).toMul.hom.hom := by
    have htriv := hi.1.isUnipotent.comp_eq_one_of_isSplitTorus isSplitTorus_gm
      (i ≫ θ.toMul) T (radicalComponent l i x)
    simp only [Grp.comp_hom_hom] at htriv
    calc
      _ = ((leviComponent l i x ≫ l.hom.hom) *
          (radicalComponent l i x ≫ i.hom.hom)) ≫ θ.toMul.hom.hom :=
        congrArg (fun y : T ⟶ P.X => y ≫ θ.toMul.hom.hom)
          (leviComponent_mul_radicalComponent l i x).symm
      _ = _ := by
        simp only [MonObj.mul_comp, Category.assoc, htriv, mul_one,
          characterRestrict_apply, Grp.comp_hom_hom]
  rw [hfactor χ, hfactor ψ, h]

private theorem characterRestrict_rightInverse {L H : GroupScheme (Spec (CommRingCat.of F))}
    (j : L ⟶ H) (q : H ⟶ L) (hq : j ≫ q = 𝟙 L) :
    Function.RightInverse (characterRestrict q) (characterRestrict j) := by
  intro χ
  change ((characterRestrict j).comp (characterRestrict q)) χ = χ
  rw [← characterRestrict_comp, hq, characterRestrict_id]
  rfl

/-- Restriction to a rational Levi is bijective on rational characters. -/
theorem _root_.Langlands.GroupScheme.IsRationalLeviSubgroup.characterRestrict_bijective
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l) : Function.Bijective (characterRestrict l) := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  exact ⟨characterRestrict_injective_of_levi hl, (characterRestrict_rightInverse l π hπ).surjective⟩

private noncomputable def leviCharacterEquiv {L H : GroupScheme (Spec (CommRingCat.of F))}
    (j : L ⟶ H) (hj : IsRationalLeviSubgroup j) (q : H ⟶ L) (hq : j ≫ q = 𝟙 L) :
    rationalCharacters H ≃+ rationalCharacters L where
  toFun := characterRestrict j
  invFun := characterRestrict q
  left_inv χ := characterRestrict_injective_of_levi hj
    (characterRestrict_rightInverse j q hq (characterRestrict j χ))
  right_inv := characterRestrict_rightInverse j q hq
  map_add' := (characterRestrict j).map_add

private noncomputable def isoCharacterEquiv (c : M' ⟶ M) [IsIso c] :
    rationalCharacters M ≃+ rationalCharacters M' where
  toFun := characterRestrict c
  invFun := characterRestrict (inv c)
  left_inv := characterRestrict_rightInverse (inv c) c (IsIso.inv_hom_id c)
  right_inv := characterRestrict_rightInverse c (inv c) (IsIso.hom_inv_id c)
  map_add' := (characterRestrict c).map_add

/-- The Weyl parameter map is a complex linear equivalence. Its forward map
uses the indicated retraction of the target Levi. -/
theorem exists_weylParameter_linearEquiv [NumberField F] (l : M ⟶ P) (l' : M' ⟶ Q)
    (hl : IsRationalLeviSubgroup l) (hl' : IsRationalLeviSubgroup l')
    (c : M' ⟶ M) [IsIso c] (π' : Q ⟶ M') (hπ' : l' ≫ π' = 𝟙 M') :
    ∃ e : ComplexCharacterParameter F P ≃ₗ[ℂ] ComplexCharacterParameter F Q,
      e.toLinearMap = weylParameter l c π' := by
  obtain ⟨_, _, π, _, _, hπ, _⟩ := hl.exists_unipotentRadical_retraction
  let e := ((leviCharacterEquiv l hl π hπ).trans (isoCharacterEquiv c)).trans
    (leviCharacterEquiv l' hl' π' hπ').symm
  refine ⟨AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ) e.toIntLinearEquiv, ?_⟩
  apply AlgebraTensorModule.ext
  intro s χ
  change s ⊗ₜ[ℤ] characterRestrict π' (characterRestrict c (characterRestrict l χ)) =
    weylParameter l c π' (s ⊗ₜ[ℤ] χ)
  simp only [weylParameter_tmul, characterRestrict_comp, AddMonoidHom.comp_apply]

end Langlands.Global.AdelicGroupPoints
