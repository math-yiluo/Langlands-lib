import Langlands.GroupScheme.Reductive.IsogenyAdjointTorusDescent
import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityStatement
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.Reductive.RelativeDerivedInputs

/-! # Descent and uniqueness for relative torus conjugators -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G' G : GroupScheme S} {T' T : CommGroupScheme S}
  {i' : T'.toGrp ⟶ G'} {i : T.toGrp ⟶ G} {f F : G' ⟶ G}

/-- The all-test torus conjugacy identity has solutions on an fppf cover of the base. -/
def FppfLocallyTorusConjugate (i : T.toGrp ⟶ G) (f F : G' ⟶ G) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S,
    ∀ k : 𝒰.I₀, ∃ t : Over.mk (𝒰.f k) ⟶ T.X, TorusConjugates i f F t

/-- Two torus conjugators differ by a point of the full scheme-theoretic centre,
provided the second homomorphism is finite, flat and surjective. -/
theorem TorusConjugates.difference_mem_center_of_isogeny
    (hF : IsIsogeny F) {V : Over S} {t₁ t₂ : V ⟶ T.X}
    (ht₁ : TorusConjugates i f F t₁) (ht₂ : TorusConjugates i f F t₂) :
    (t₁ ≫ i.hom.hom)⁻¹ * (t₂ ≫ i.hom.hom) ∈ (center G).carrier V := by
  let := hF.1
  let := hF.2.1
  let := hF.2.2
  rw [mem_center]
  intro U a h
  apply AutomorphicAction.hom_ext_of_local_quotient_lift F h
  intro W b g hg
  simp only [MonObj.comp_mul, GrpObj.comp_inv]
  rw [hg]
  have he := (ht₁ W (b ≫ a) g).symm.trans (ht₂ W (b ≫ a) g)
  simp only [Category.assoc] at he
  have he' := congrArg (fun z =>
    (b ≫ a ≫ t₁ ≫ i.hom.hom)⁻¹ * z * (b ≫ a ≫ t₂ ≫ i.hom.hom)) he
  convert he'.symm using 1 <;> group

/-- Local torus conjugators force equality on any commutative source subgroup
whose image under the second homomorphism factors through the conjugating torus. -/
theorem torusRestriction_eq_of_fppf_local_conjugates
    (hFT : ∃ τ : T'.toGrp ⟶ T.toGrp, i' ≫ F = τ ≫ i)
    (𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) S)
    (t : ∀ k : 𝒰.I₀, Over.mk (𝒰.f k) ⟶ T.X)
    (ht : ∀ k, TorusConjugates i f F (t k)) :
    i' ≫ f = i' ≫ F := by
  obtain ⟨τ, hτ⟩ := hFT
  have hτ' := congrArg (fun z : T'.toGrp ⟶ G => z.hom.hom) hτ
  change i'.hom.hom ≫ F.hom.hom = τ.hom.hom ≫ i.hom.hom at hτ'
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  let 𝒱 := 𝒰.pullback₁ T'.X.hom
  let := RelativeDerived.effectiveEpiFamily_fppfCover 𝒱
  apply EffectiveEpiFamily.hom_ext 𝒱.X 𝒱.f
  intro k
  let W : Over S := Over.mk (𝒱.f k ≫ T'.X.hom)
  let b : W ⟶ T'.X := Over.homMk (𝒱.f k) rfl
  let c : W ⟶ Over.mk (𝒰.f k) :=
    Over.homMk (𝒰.pullbackHom T'.X.hom k) (𝒰.pullbackHom_map T'.X.hom k)
  have he := ht k W c (b ≫ i'.hom.hom)
  simp only [Category.assoc] at he
  rw [hτ', ← Category.assoc b τ.hom.hom] at he
  have hc : (c ≫ t k ≫ i.hom.hom) * ((b ≫ τ.hom.hom) ≫ i.hom.hom) *
      (c ≫ t k ≫ i.hom.hom)⁻¹ = (b ≫ τ.hom.hom) ≫ i.hom.hom := by
    rw [← Category.assoc c, ← GrpObj.inv_comp, ← MonObj.mul_comp,
      ← MonObj.mul_comp]
    congr 1
    simp [mul_comm]
  rw [hc] at he
  have he' : b ≫ (i' ≫ f).hom.hom = b ≫ (i' ≫ F).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc, hτ'] using he
  exact congrArg (fun z => z.left) he'

/-- The existence of local conjugators implies equality on the source torus. -/
theorem FppfLocallyTorusConjugate.torusRestriction_eq
    (h : FppfLocallyTorusConjugate i f F)
    (hFT : ∃ τ : T'.toGrp ⟶ T.toGrp, i' ≫ F = τ ≫ i) :
    i' ≫ f = i' ≫ F := by
  obtain ⟨𝒰, h𝒰⟩ := h
  choose t ht using h𝒰
  exact torusRestriction_eq_of_fppf_local_conjugates hFT 𝒰 t ht

end Langlands.GroupScheme
