import Langlands.GroupScheme.Rational.BruhatCellStatement
import Langlands.GroupScheme.Rational.BruhatOpenCellProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.ImageGenerationSubgroup

/-! # Rational Bruhat cells as locally closed multiplication maps -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatCell

variable {k : Type u} [Field k]
  {G U V P : GroupScheme (Spec (CommRingCat.of k))}
  (u : U ⟶ G) (v : V ⟶ G) (p : P ⟶ G)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

/-- The cell parametrization is the displayed multiplication on every test scheme. -/
theorem lift_parametrization {X : Over (Spec (CommRingCat.of k))}
    (a : X ⟶ (factor u v n).X) (b : X ⟶ P.X) :
    lift a b ≫ parametrization u v p n =
      (a ≫ (subgroupIntersectionHom (v ≫ (G.innerIso n).hom) u).hom.hom) *
        G.constantPoint n X * (b ≫ p.hom.hom) := by
  let j := subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u
  rw [parametrization, lift_map_assoc, Category.comp_id, ← Category.assoc,
    SubgroupFunctor.lift_cellMultiplication,
    Dynamic.comp_rationalLeftTranslation]
  have ha : a ≫ (subgroupIntersectionHom (v ≫ (G.innerIso n).hom) u).hom.hom =
      ((a ≫ j.hom.hom) ≫ v.hom.hom) ≫ (G.innerIso n).hom.hom.hom := by
    simp only [j, subgroupIntersectionHom, Grp.comp_hom_hom, Category.assoc]
  rw [ha, comp_innerIso_hom]
  change G.constantPoint n X * _ = _
  dsimp only [j]
  group

private theorem parametrization_isImmersion
    (hu : IsClosedSubgroup u)
    (hcell : IsOpenImmersion (SubgroupFunctor.cellMultiplication v p).left) :
    IsImmersion (parametrization u v p n).left := by
  let j := subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u
  have : IsClosedImmersion j.hom.hom.left :=
    isClosedSubgroup_subgroupIntersectionFst _ hu
  have : IsClosedImmersion (j.hom.hom ⊗ₘ 𝟙 P.X).left :=
    ImageGeneration.isClosedImmersion_tensorHom_left _ _
  have : IsIso (Dynamic.rationalLeftTranslation k G n).hom.left :=
    inferInstanceAs (IsIso ((Over.forget _).map (Dynamic.rationalLeftTranslation k G n).hom))
  change IsImmersion
    ((j.hom.hom ⊗ₘ 𝟙 P.X).left ≫ (SubgroupFunctor.cellMultiplication v p).left ≫
      (Dynamic.rationalLeftTranslation k G n).hom.left)
  infer_instance

end BruhatCell

/-- The actual rational Bruhat multiplication parametrizes the double coset
and is a locally closed immersion. -/
theorem rationalBruhatCell : RationalBruhatCellStatement.{u} := by
  intro k _ G hG T i hi ν
  let := hG.isAffineHom
  let := hG.smooth
  dsimp only
  intro hν P U V p u v hp hu huc hv n
  let χ := CommGroupScheme.groupHom ν ≫ i
  let S₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let aG : S₀ ⟶ G.X := n.val
  let j := subgroupIntersectionHom (v ≫ (G.innerIso aG).hom) u
  have hZ : Dynamic.centralizer χ = torusCentralizer i :=
    genericCentralizer k G hG T i hi ν hν
  have hfac := hasUnipotentWeylFactorization_of_oppositeCell i ν oppositeCellStatement hZ
  have hcell : IsOpenImmersion (SubgroupFunctor.cellMultiplication v p).left :=
    oppositeCellStatement k G χ V P v p hv hp
  refine ⟨BruhatCell.parametrization_isImmersion u v p aG huc hcell, ?_⟩
  intro g
  constructor
  · rintro ⟨x, hx⟩
    let a := x ≫ fst (BruhatCell.factor u v aG).X P.X
    let b := x ≫ snd (BruhatCell.factor u v aG).X P.X
    have hjU : a ≫ j.hom.hom ∈ (Dynamic.unipotent χ).carrier S₀ := by
      have hm : a ≫ j.hom.hom ∈ (SubgroupFunctor.range j).carrier S₀ :=
        SubgroupFunctor.mem_range.mpr ⟨a, rfl⟩
      dsimp only [j] at hm
      rw [range_subgroupIntersectionHom, hu.2] at hm
      exact hm.2
    let aP := (hp.pointsEquiv S₀).symm
      ⟨a ≫ j.hom.hom, Dynamic.unipotent_le_parabolic χ _ hjU⟩
    have haP : aP ≫ p.hom.hom = a ≫ j.hom.hom := hp.pointsEquiv_symm_comp _
    refine ⟨aP, b, ?_⟩
    rw [← hx, ← lift_comp_fst_snd x, BruhatCell.lift_parametrization, haP,
      constantPoint_self]
  · rintro ⟨a, b, rfl⟩
    have ha : a ≫ p.hom.hom ∈ RationalPoint.parabolic χ := (hp.pointsEquiv S₀ a).2
    obtain ⟨⟨x, z⟩, ⟨hx, hz, haxz⟩, _⟩ :=
      RationalPoint.existsUnique_unipotent_mul_levi χ ha
    obtain ⟨x₁, x₂, hx₁₂, hx₁, hx₂⟩ := hfac n ⟨x, hx⟩
    change x = x₁.val * x₂.val at hx₁₂
    change a ≫ p.hom.hom = x * z at haxz
    have hz' : aG⁻¹ * z * aG ∈ RationalPoint.levi χ := by
      have hz₀ : z ∈ (torusCentralizer i).carrier S₀ := by
        rwa [← hZ]
      have h := torusCentralizer_isNormalizedBy_torusNormalizer i S₀ aG⁻¹ z
        ((normalizerPointsRestrict i S₀ n⁻¹).property) hz₀
      simpa only [RationalPoint.levi, hZ, inv_inv] using h
    let aV := (hv.pointsEquiv S₀).symm ⟨aG⁻¹ * x₁ * aG, hx₁⟩
    have haV : aV ≫ v.hom.hom = aG⁻¹ * x₁ * aG := hv.pointsEquiv_symm_comp _
    have hx₁V : x₁.val ∈ (SubgroupFunctor.range (v ≫ (G.innerIso aG).hom)).carrier S₀ := by
      refine SubgroupFunctor.mem_range.mpr ⟨aV, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, haV, constantPoint_self]
      group
    have hx₁U : x₁.val ∈ (SubgroupFunctor.range u).carrier S₀ := by
      rw [hu.2]
      exact x₁.property
    obtain ⟨c, hc⟩ : ∃ c : S₀ ⟶ (BruhatCell.factor u v aG).X,
        c ≫ j.hom.hom = x₁.val := by
      apply SubgroupFunctor.mem_range.mp
      dsimp only [j]
      rw [range_subgroupIntersectionHom]
      exact ⟨hx₁V, hx₁U⟩
    let d : S₀ ⟶ G.X := (aG⁻¹ * x₂ * aG) * (aG⁻¹ * z * aG) * (b ≫ p.hom.hom)
    have hd : d ∈ RationalPoint.parabolic χ :=
      mul_mem (mul_mem (RationalPoint.unipotent_le_parabolic χ hx₂)
        (RationalPoint.levi_le_parabolic χ hz')) (hp.pointsEquiv S₀ b).2
    let dP := (hp.pointsEquiv S₀).symm ⟨d, hd⟩
    have hdP : dP ≫ p.hom.hom = d := hp.pointsEquiv_symm_comp _
    refine ⟨lift c dP, ?_⟩
    rw [BruhatCell.lift_parametrization, hc, hdP, constantPoint_self, haxz, hx₁₂]
    dsimp only [d, aG]
    group

end Langlands.GroupScheme
