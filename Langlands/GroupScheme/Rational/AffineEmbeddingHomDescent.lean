import Langlands.AlgebraicGeometry.AffineEmbeddingDescent
import Langlands.GroupScheme.Absolute.CocharacterDescentGroup

/-! # Group homomorphism descent detected by a dominant parametrization -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.AffineEmbeddingHomDescent

open Langlands.AlgebraicGeometry.AffineEmbeddingDescent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {H Y : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine H.X.left] [IsAffine Y.X.left]
    {T : Over (Spec (CommRingCat.of k))} [IsAffine T.left]
    (p : T ⟶ H.X)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left]
    (g : (baseChange (algebraBaseMap k K)).obj H ⟶
      (baseChange (algebraBaseMap k K)).obj Y)
    (h : T ⟶ Y.X)
    (hgh : (scalarExtension k K).map p ≫
        (Over.map (algebraBaseMap k K)).map g.hom.hom ≫ projection Y.X =
      projection T ≫ h)

/-- Descend the underlying morphism using its supplied composite on the
dominant affine parametrizing scheme. -/
def overHom : H.X ⟶ Y.X :=
  descendHom p
    ((Over.map (algebraBaseMap k K)).map g.hom.hom ≫ projection Y.X) h hgh

/-- Pullback recovers the actual extension-field underlying morphism. -/
theorem pullback_overHom :
    (Over.pullback (algebraBaseMap k K)).map (overHom p g h hgh) =
      g.hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have he := congrArg (fun q => q.left)
      (projection_comp_descendHom p
        ((Over.map (algebraBaseMap k K)).map g.hom.hom ≫ projection Y.X) h hgh)
    exact (pullback.lift_fst _ _ _).trans he
  · exact (pullback.lift_snd _ _ _).trans (Over.w g.hom.hom).symm

/-- Faithful pullback along the field extension reflects the group laws. -/
theorem overHom_isMonHom : IsMonHom (overHom p g h hgh) := by
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  have : IsMonHom
      ((Over.pullback (algebraBaseMap k K)).map (overHom p g h hgh)) := by
    rw [pullback_overHom]
    infer_instance
  exact GaloisCocharacterDescent.isMonHom_of_faithfulMap
    (Over.pullback (algebraBaseMap k K)) _

/-- The actual ground-field group homomorphism detected by the supplied
dominant affine parametrization. -/
def descend : H ⟶ Y :=
  letI := overHom_isMonHom p g h hgh
  Grp.homMk (overHom p g h hgh)

/-- Base change of the descended group homomorphism recovers the given map. -/
theorem baseChange_descend :
    (baseChange (algebraBaseMap k K)).map (descend p g h hgh) = g := by
  apply Grp.hom_ext
  exact pullback_overHom p g h hgh

/-- Recovery by base change uniquely determines the ground-field
group homomorphism. -/
theorem descend_unique (g₀ : H ⟶ Y)
    (hg₀ : (baseChange (algebraBaseMap k K)).map g₀ = g) :
    g₀ = descend p g h hgh := by
  let := GaloisCocharacterDescent.faithful_algebraPullback k K
  apply Grp.hom_ext
  apply (Over.pullback (algebraBaseMap k K)).map_injective
  change ((baseChange (algebraBaseMap k K)).map g₀).hom.hom =
    ((baseChange (algebraBaseMap k K)).map (descend p g h hgh)).hom.hom
  rw [hg₀, baseChange_descend]

include p h hgh in
/-- A group homomorphism over the extension field descends uniquely whenever
its composite with the supplied dominant affine parametrization descends. -/
theorem existsUnique_hom :
    ∃! g₀ : H ⟶ Y, (baseChange (algebraBaseMap k K)).map g₀ = g :=
  ⟨descend p g h hgh, baseChange_descend p g h hgh,
    fun g₀ hg₀ => descend_unique p g h hgh g₀ hg₀⟩

end Langlands.GroupScheme.AffineEmbeddingHomDescent
