import Langlands.GroupScheme.HomScheme.MultiplicativeTargetClassifying
import Langlands.GroupScheme.Torus.MultiplicativeTypeAffineChart
import Langlands.GroupScheme.Torus.MultiplicativeTypeSplitCriterion
import Langlands.GroupScheme.Torus.RelativeLargestSubtorusProof

/-! # Groups of multiplicative type split on an étale neighbourhood of each point -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open HomScheme

/-- The diagonalizable group with character group `I → ℤ` is the split torus `𝔾_m^I`. -/
def diagonalizableSplitTorusIso (S : Scheme.{u}) (I : Type u) [Fintype I] [DecidableEq I] :
    diagonalizable S (I → ℤ) ≅ splitTorus S I :=
  (GroupScheme.baseChange (Gm.toSpecZ S)).mapIso
      (Diagonalizable.splitIso (CommRingCat.of (ULift.{u} ℤ)) (AddEquiv.refl (I → ℤ))) ≪≫
    splitTorus.baseChangeIso (Gm.toSpecZ S) I

open Diagonalizable in
/-- **Groups of multiplicative type split étale-locally, pointwise.** For every point `s` of
the base there is an étale morphism `U ⟶ S` whose image contains `s`, over which `H` becomes
diagonalizable. -/
theorem IsMultiplicativeType.exists_etale_diagonalizable {S : Scheme.{u}} {H : GroupScheme S}
    (hH : IsMultiplicativeType H) (s : S) :
    ∃ (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧ s ∈ Set.range f ∧
      IsDiagonalizable ((GroupScheme.baseChange f).obj H) := by
  classical
  obtain ⟨T, j, hj⟩ := hH.exists_universalSubtorus
  obtain ⟨𝒰, h𝒰⟩ := hj.2.1
  obtain ⟨v, hv⟩ := 𝒰.covers s
  let p := 𝒰.f (𝒰.idx s)
  have hp : Etale p := 𝒰.map_prop _
  obtain ⟨I', _, ⟨eT⟩⟩ := h𝒰 (𝒰.idx s)
  have := Fintype.ofFinite I'
  obtain ⟨R, iR, hiR, hviR, hGaff, hGlfp, R', φ, hφff, hφfp, hdiag⟩ :=
    (hH.baseChange p).exists_affine_chart v
  let : Algebra R R' := φ.hom.toAlgebra
  have : Module.FaithfullyFlat R R' := hφff
  have : Algebra.FinitePresentation R R' := hφfp
  let G : GroupScheme (Spec (CommRingCat.of R)) :=
    (GroupScheme.baseChange iR).obj ((GroupScheme.baseChange p).obj H)
  have : IsAffine G.X.left := hGaff
  have : LocallyOfFinitePresentation G.X.hom := hGlfp
  obtain ⟨Λ, _, _, ⟨ψ₀⟩⟩ := hdiag
  let ψ : (GroupScheme.baseChange (specBase R R')).obj G ≅
      diagonalizable (Spec (CommRingCat.of R')) Λ :=
    Descent.pullbackComparison iR (Spec.map φ) (Spec.map φ ≫ iR) rfl _ ≪≫ ψ₀
  obtain ⟨I, A, _, _, _, ⟨e⟩⟩ := exists_freeFiniteEquiv Λ
  have := Fintype.ofFinite A
  obtain ⟨X, f, q, hq, hf, hqs, hqf, hql, σ, hσ⟩ :=
    exists_etale_classifying G ψ A (finiteInclusionOverScheme _ e ≫ ψ.inv)
  let eTR : (GroupScheme.baseChange iR).obj ((GroupScheme.baseChange p).obj T) ≅
      diagonalizable (Spec (CommRingCat.of R)) (I' → ℤ) :=
    (GroupScheme.baseChange iR).mapIso eT ≪≫ splitTorus.baseChangeIso iR I' ≪≫
      (diagonalizableSplitTorusIso _ I').symm
  let τ : diagonalizable (Spec (CommRingCat.of R)) (I' → ℤ) ⟶ G :=
    eTR.inv ≫ (GroupScheme.baseChange iR).map ((GroupScheme.baseChange p).map j)
  have hτ : IsUniversalSubtorus τ := ((hj.baseChange p).baseChange iR).iso_comp eTR.symm
  let τX := (diagonalizableBaseChangeIso f (I' → ℤ)).inv ≫ (GroupScheme.baseChange f).map τ
  have hτX : IsUniversalSubtorus τX :=
    (hτ.baseChange f).iso_comp (diagonalizableBaseChangeIso f (I' → ℤ)).symm
  have hσ' : (diagonalizableBaseChangeIso q A).inv ≫ (GroupScheme.baseChange q).map σ ≫
      (Descent.pullbackComparison f q (specBase R R') hq G ≪≫ ψ).hom =
        finiteInclusionOverScheme _ e := by
    have h := congrArg (· ≫ ψ.hom) hσ
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
    simpa only [Iso.trans_hom, Category.assoc] using h
  have hdX : IsDiagonalizable ((GroupScheme.baseChange f).obj G) :=
    isDiagonalizable_of_split_parts q e τX hτX σ _ hσ'
  have : IsOpenImmersion iR := hiR
  refine ⟨X, f ≫ iR ≫ p, inferInstance, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hviR
    have hfs : Surjective f := by
      have : Surjective (q ≫ f) := by rw [hq]; exact surjective_specBase
      exact Surjective.of_comp q f
    obtain ⟨y, hy⟩ := hfs.surj x
    refine ⟨y, ?_⟩
    change p (iR (f y)) = s
    rw [hy, hx, hv]
  · exact hdX.of_iso
      ((Descent.pullbackComparison (iR ≫ p) f (f ≫ iR ≫ p) rfl H).symm ≪≫
        (GroupScheme.baseChange f).mapIso (Descent.pullbackComparison p iR (iR ≫ p) rfl H).symm)

end Langlands.GroupScheme.RelativeMultiplicativeType
