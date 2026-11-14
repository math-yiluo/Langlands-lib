import Langlands.GroupScheme.CocycleRestriction
import Langlands.GroupScheme.AffineVectorSeries

/-! # Local cocycle triviality for extensions of split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Cocycle

/-- A cocycle admits an all-test coboundary expression near every base point. -/
def IsZariskiLocallyTrivial {S : Scheme.{u}} {G : GroupScheme S} {U : Over S}
    (ξ : Cocycle G U) : Prop :=
  ∀ y : S, Nonempty (ξ.LocalTrivialization y)

end Cocycle

namespace SplitSolvableLocalCocycle

open SplitUnipotentAffineTorsor

variable {R : CommRingCat.{u}} {K H T : GroupScheme (Spec R)}
  (j : K ⟶ H) (q : H ⟶ T) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

include hjq in
/-- An extension with cocycle-acyclic kernel and split-torus quotient has locally
trivial cocycles when its quotient map has a scheme section. -/
theorem isZariskiLocallyTrivial_of_section
    (σ : T.X ⟶ H.X) (hσ : σ ≫ q.hom.hom = 𝟙 T.X)
    (hK : CocyclesVanish K) (hT : IsSplitTorus T)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsZariskiLocallyTrivial := by
  intro y
  let L := Classical.choice
    (Cocycle.nonempty_localTrivialization_of_isSplitTorus hT (ξ.map q) y)
  obtain ⟨W, hW, hyW, hWL⟩ := exists_isAffineOpen_mem_and_subset L.mem_openSet
  have hWL' : W ≤ L.openSet := hWL
  let V : U.left.Opens := U.hom ⁻¹ᵁ W
  let UW : Over W.toScheme := Over.mk (U.hom ∣_ W)
  have : IsAffine W.toScheme := hW
  have : IsAffine UW.left := hW.preimage U.hom
  have : Flat UW.hom := inferInstanceAs (Flat (U.hom ∣_ W))
  have : Surjective UW.hom := inferInstanceAs (Surjective (U.hom ∣_ W))
  let QW := (Over.map W.ι).obj UW
  let r : QW ⟶ U := Over.homMk V.ι (morphismRestrict_ι U.hom W).symm
  let UL : Over (Spec R) := Over.mk ((U.hom ⁻¹ᵁ L.openSet).ι ≫ U.hom)
  let rL : QW ⟶ UL := Over.homMk (U.left.homOfLE (U.hom.preimage_mono hWL')) (by
    change U.left.homOfLE (U.hom.preimage_mono hWL') ≫
        (U.hom ⁻¹ᵁ L.openSet).ι ≫ U.hom = (U.hom ∣_ W) ≫ W.ι
    rw [← Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι])
  have hrL : rL ≫ Over.homMk (U.hom ⁻¹ᵁ L.openSet).ι = r := by
    apply Over.OverMorphism.ext
    exact U.left.homOfLE_ι (U.hom.preimage_mono hWL')
  let ξR := ξ.comap r
  let f₀ : QW ⟶ T.X := rL ≫ L.cochain
  have hf₀ : ∀ {Z : Over (Spec R)} (a b : Z ⟶ QW),
      ξR.toFun a b ≫ q.hom.hom = (a ≫ f₀) * (b ≫ f₀)⁻¹ := by
    intro Z a b
    have h := L.coboundary (a ≫ rL) (b ≫ rL)
    simpa only [Cocycle.map, Category.assoc, hrL, f₀, ξR, Cocycle.comap] using h
  let f₁ : QW ⟶ H.X := f₀ ≫ σ
  have hf₁ : f₁ ≫ q.hom.hom = f₀ := by
    rw [Category.assoc, hσ, Category.comp_id]
  have hval : ∀ {Z : Over (Spec R)} (a b : Z ⟶ QW),
      ∃ k : Z ⟶ K.X, k ≫ j.hom.hom = (ξR.twist f₁).toFun a b := by
    intro Z a b
    refine exists_comp_eq_of_comp_eq_one hjq _ ?_
    change ((a ≫ f₁)⁻¹ * ξR.toFun a b * (b ≫ f₁)) ≫ q.hom.hom = 1
    simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, f₁, hσ,
      Category.comp_id, hf₀]
    group
  let ζ := (ξR.twist f₁).lift j hval
  have : IsAffine (Over.mk W.ι).left := hW
  have hζ : ζ.IsTrivial :=
    Cocycle.IsTrivial.of_baseChangeAlong W.ι
      (hK (Over.mk W.ι) UW (ζ.baseChangeAlong W.ι UW (𝟙 _)))
  obtain ⟨f, hf⟩ := Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift hζ)
  let UC : Over (Spec R) := Over.mk (V.ι ≫ U.hom)
  let e : UC ⟶ QW := Over.homMk (𝟙 V.toScheme) (by
    change 𝟙 V.toScheme ≫ (U.hom ∣_ W) ≫ W.ι = V.ι ≫ U.hom
    rw [Category.id_comp, morphismRestrict_ι])
  have her : e ≫ r = Over.homMk V.ι := by
    apply Over.OverMorphism.ext
    exact Category.id_comp _
  refine ⟨⟨W, hyW, e ≫ f, fun {Z} a b => ?_⟩⟩
  have h := hf (a ≫ e) (b ≫ e)
  simpa only [ξR, Cocycle.comap, Category.assoc, her] using h

include hjq in
/-- For an affine extension, a flat, surjective, locally finitely presented quotient
has a scheme section once the kernel's affine cocycles vanish. -/
theorem isZariskiLocallyTrivial
    [IsAffine H.X.left] [IsAffine T.X.left]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    (hK : CocyclesVanish K) (hT : IsSplitTorus T)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsZariskiLocallyTrivial := by
  obtain ⟨σ, hσ⟩ := exists_section j q hjq hK
  exact isZariskiLocallyTrivial_of_section j q hjq σ hσ hK hT U ξ

include hjq in
/-- The kernel's finite vector-quotient series supplies the required cocycle
vanishing over every commutative ring. -/
theorem isZariskiLocallyTrivial_of_vectorSeries
    [IsAffine H.X.left] [IsAffine T.X.left] [IsAffineHom K.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [LocallyOfFinitePresentation q.hom.hom.left]
    {n : ℕ} (hK : HasAffineVectorSeries n K) (hT : IsSplitTorus T)
    (U : Over (Spec R)) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle H U) : ξ.IsZariskiLocallyTrivial :=
  isZariskiLocallyTrivial j q hjq
    (HasAffineVectorSeries.cocyclesVanish n K hK inferInstance) hT U ξ

end SplitSolvableLocalCocycle

end Langlands.GroupScheme
