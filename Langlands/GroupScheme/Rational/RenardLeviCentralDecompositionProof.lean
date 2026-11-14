import Langlands.GroupScheme.Rational.RenardLeviCentralDecompositionStatement
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeCharacterComplementReduction

/-! # Compatible Levi central decompositions on the actual real torus spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace Langlands.LinearAlgebra

variable {k : Type u} [Field k]

private theorem restrictReal_bijective
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (a : A.toGrp ⟶ G) (ha : IsSplitComponent a) :
    Function.Bijective (rationalCharacterRestrictReal a) := by
  obtain ⟨hinj, hindex⟩ := characterRestriction k G hG A a ha
  let eQ := rationalCharacterRestrictRatEquiv a hinj hindex
  let eR := (rationalRealTensorEquiv (rationalCharacters G)).symm.trans
    ((LinearEquiv.baseChange ℚ ℝ _ _ eQ).trans
      (rationalRealTensorEquiv (characterLattice A)))
  have he : eR.toLinearMap = rationalCharacterRestrictReal a := by
    apply AlgebraTensorModule.ext
    intro r χ
    change ((1 : ℚ) • r) ⊗ₜ[ℤ] characterRestrict a χ =
      r ⊗ₜ[ℤ] characterRestrict a χ
    rw [one_smul]
  rw [← he]
  exact eR.bijective

private theorem restrictReal_comp
    {G H K : GroupScheme (Spec (CommRingCat.of k))} (g : K ⟶ H) (f : H ⟶ G) :
    rationalCharacterRestrictReal (g ≫ f) =
      (rationalCharacterRestrictReal g).comp (rationalCharacterRestrictReal f) := by
  apply AlgebraTensorModule.ext
  intro r χ
  change r ⊗ₜ[ℤ] characterRestrict (g ≫ f) χ =
    r ⊗ₜ[ℤ] characterRestrict g (characterRestrict f χ)
  rw [characterRestrict_comp, AddMonoidHom.comp_apply]

private def transposeSection
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) (s : Vstar A →ₗ[ℝ] Vstar T) : V T →ₗ[ℝ] V A :=
  (LinearEquiv.ofBijective (pair A).flip
    (isPerfPair_of_isSplitTorus hA).bijective_right).symm.toLinearMap.comp
      (s.dualMap.comp (pair T).flip)

private theorem pair_transposeSection
    {A T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) (s : Vstar A →ₗ[ℝ] Vstar T)
    (x : Vstar A) (v : V T) :
    pair A x (transposeSection hA s v) = pair T (s x) v := by
  let e := LinearEquiv.ofBijective (pair A).flip
    (isPerfPair_of_isSplitTorus hA).bijective_right
  exact congrArg (fun φ : Module.Dual ℝ (Vstar A) => φ x)
    (e.apply_symm_apply (s.dualMap ((pair T).flip v)))

/-- The real restriction square of compatible split components yields both
central/relative decompositions, with the literal kernel and pairing annihilator. -/
theorem renardLeviCentralDecomposition : RenardLeviCentralDecompositionStatement.{u} := by
  intro k _ G M j hG hM AG AM aG aM f haG haM hf
  have hGbij := restrictReal_bijective hG aG haG
  have hMbij := restrictReal_bijective hM aM haM
  let eG := LinearEquiv.ofBijective (rationalCharacterRestrictReal aG) hGbij
  let g := rationalCharacterRestrictReal (aM ≫ j)
  let r := rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
  let s := g.comp eG.symm.toLinearMap
  have hs : s.comp (rationalCharacterRestrictReal aG) = g := by
    apply LinearMap.ext
    intro x
    change g (eG.symm (eG x)) = g x
    rw [eG.symm_apply_apply]
  have hrg : r.comp g = rationalCharacterRestrictReal aG := by
    dsimp only [r, g]
    rw [← restrictReal_comp, hf]
  have hrs : r.comp s = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (r.comp g) (eG.symm x) = x
    rw [hrg]
    exact eG.apply_symm_apply x
  have hrange : s.range = g.range :=
    LinearMap.range_comp_of_range_eq_top g
      (LinearMap.range_eq_top_of_surjective _ eG.symm.surjective)
  have hbij : Function.Bijective (r.comp s) := by
    rw [hrs]
    exact Function.bijective_id
  have hAG : IsSplitTorus AG.toGrp := haG.1.1.1
  let q := transposeSection hAG s
  have hqf : q.comp (cocharacterMapReal f) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply (isPerfPair_of_isSplitTorus hAG).bijective_right.injective
    apply LinearMap.ext
    intro x
    change pair AG x (transposeSection hAG s (cocharacterMapReal f v)) = pair AG x v
    rw [pair_transposeSection, pair_cocharacterMapReal]
    have hx := LinearMap.congr_fun hrs x
    change r (s x) = x at hx
    rw [hx]
  have hqker : q.ker = cocharacterAnnihilator s.range := by
    ext v
    rw [LinearMap.mem_ker, mem_cocharacterAnnihilator]
    constructor
    · intro hv x hx
      obtain ⟨x₀, rfl⟩ := hx
      rw [← pair_transposeSection hAG s x₀ v]
      change pair AG x₀ (q v) = 0
      rw [hv, map_zero]
    · intro hv
      apply (isPerfPair_of_isSplitTorus hAG).bijective_right.injective
      apply LinearMap.ext
      intro x
      change pair AG x (transposeSection hAG s v) = pair AG x 0
      rw [pair_transposeSection, map_zero]
      exact hv (s x) ⟨x, rfl⟩
  have hqbij : Function.Bijective (q.comp (cocharacterMapReal f)) := by
    rw [hqf]
    exact Function.bijective_id
  refine ⟨hGbij, hMbij, s, hs, hrs, hrange,
    (isCompl_ker_range_of_bijective_comp r s hbij).symm, ?_, ?_, ?_, ?_⟩
  · refine ⟨(LinearEquiv.prodComm ℝ _ _).trans
      (kerProdEquivOfBijectiveComp r s hbij), ?_⟩
    intro x y
    change (y : Vstar AM) + s x = s x + (y : Vstar AM)
    exact add_comm _ _
  · intro v w hvw
    exact hqbij.injective (congrArg q hvw)
  · rw [← hqker]
    exact (isCompl_ker_range_of_bijective_comp q (cocharacterMapReal f) hqbij).symm
  · rw [← hqker]
    refine ⟨(LinearEquiv.prodComm ℝ _ _).trans
      (kerProdEquivOfBijectiveComp q (cocharacterMapReal f) hqbij), ?_⟩
    intro x y
    change (y : V AM) + cocharacterMapReal f x = cocharacterMapReal f x + (y : V AM)
    exact add_comm _ _

end Langlands.GroupScheme
