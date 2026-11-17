import Langlands.GroupScheme.Torus.LocalDiagonalizableHom
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable

/-! # Base-change comparison for diagonalizable groups over local rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.CompleteLocalDeformation

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
  (b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
  {H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Base change between local rings induces a bijection on actual Hom sets
between any two diagonalizable groups. -/
theorem diagonalizable_baseChange_hom_bijective
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable G) :
    Function.Bijective (fun f : H ⟶ G => (GroupScheme.baseChange b).map f) := by
  obtain ⟨M, _, _, ⟨eH⟩⟩ := hH
  obtain ⟨N, _, _, ⟨eG⟩⟩ := hG
  let eH' := eH ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of A) M).symm
  let eG' := eG ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of A) N).symm
  let e := Iso.homCongr eH' eG'
  let e' := Iso.homCongr ((GroupScheme.baseChange b).mapIso eH')
    ((GroupScheme.baseChange b).mapIso eG')
  have hcomp :
      (fun f : H ⟶ G => e' ((GroupScheme.baseChange b).map f)) =
        (fun f : H ⟶ G => (GroupScheme.baseChange b).map (e f)) := by
    funext f
    simp only [e', e, Iso.homCongr_apply, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp]
  have hc : Function.Bijective (fun f : H ⟶ G => e' ((GroupScheme.baseChange b).map f)) := by
    rw [hcomp]
    exact (baseChange_hom_bijective b M N).comp e.bijective
  exact (Function.Bijective.of_comp_iff' e'.bijective _).mp hc

/-- The actual Hom-set comparison for chosen diagonalizable groups. -/
def diagonalizableHomBaseChangeEquiv
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable G) :
    (H ⟶ G) ≃ ((GroupScheme.baseChange b).obj H ⟶ (GroupScheme.baseChange b).obj G) :=
  Equiv.ofBijective _ (diagonalizable_baseChange_hom_bijective b hH hG)

/-- Each homomorphism after local base change has a unique lift. -/
theorem diagonalizable_existsUnique_lift
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable G)
    (f₀ : (GroupScheme.baseChange b).obj H ⟶ (GroupScheme.baseChange b).obj G) :
    ∃! f : H ⟶ G, (GroupScheme.baseChange b).map f = f₀ := by
  have hb := diagonalizable_baseChange_hom_bijective b hH hG
  obtain ⟨f, hf⟩ := hb.surjective f₀
  exact ⟨f, hf, fun f' hf' => hb.injective (hf'.trans hf.symm)⟩

/-- A homomorphism between diagonalizable groups is an isomorphism whenever
its local base change is an isomorphism. -/
theorem diagonalizable_isIso_of_baseChange
    (hH : RelativeMultiplicativeType.IsDiagonalizable H)
    (hG : RelativeMultiplicativeType.IsDiagonalizable G)
    (f : H ⟶ G) [IsIso ((GroupScheme.baseChange b).map f)] : IsIso f := by
  obtain ⟨g, hg⟩ := (diagonalizable_baseChange_hom_bijective b hG hH).surjective
    (inv ((GroupScheme.baseChange b).map f))
  have hfg : f ≫ g = 𝟙 H := by
    apply (diagonalizable_baseChange_hom_bijective b hH hH).injective
    simp only [Functor.map_comp, hg, IsIso.hom_inv_id]
    exact ((GroupScheme.baseChange b).map_id H).symm
  have hgf : g ≫ f = 𝟙 G := by
    apply (diagonalizable_baseChange_hom_bijective b hG hG).injective
    simp only [Functor.map_comp, hg, IsIso.inv_hom_id]
    exact ((GroupScheme.baseChange b).map_id G).symm
  exact ⟨⟨g, hfg, hgf⟩⟩

end Langlands.GroupScheme.CompleteLocalDeformation
