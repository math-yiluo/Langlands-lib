import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplittingAssembly
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Geometry of finite-type groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The affine finite-type commutative geometry needed for structural constructions. -/
def MultiplicativeTypeGeometry (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  IsAffine G.X.left ∧ LocallyOfFiniteType G.X.hom ∧ IsCommMonObj G.X

/-- Affineness descends from the full diagonalizable splitting model. -/
theorem IsMultiplicativeType.isAffine (hG : IsMultiplicativeType G) :
    IsAffine G.X.left := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  have : IsAffineHom ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom :=
    isAffineHom_of_over_iso ((Grp.forget _).mapIso e)
      (inferInstanceAs
        (IsAffineHom (Diagonalizable.groupScheme (CommRingCat.of K) Λ).X.hom))
  have hbcaff : IsAffine ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G).X.hom
  exact Langlands.AlgebraicGeometry.fieldExtensionAffineDescent k K G.X.left G.X.hom
    hbcaff

/-- Every finite-type multiplicative-type group is affine over its field. -/
theorem IsMultiplicativeType.isAffineHom (hG : IsMultiplicativeType G) :
    IsAffineHom G.X.hom := by
  have : IsAffine G.X.left := hG.isAffine
  infer_instance

/-- Finite generation of the full character group descends finite type. -/
theorem IsMultiplicativeType.locallyOfFiniteType (hG : IsMultiplicativeType G) :
    LocallyOfFiniteType G.X.hom := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have he : e.hom.hom.hom.left ≫
      (Diagonalizable.groupScheme (CommRingCat.of K) Λ).X.hom =
      ((GroupScheme.baseChange b).obj G).X.hom := Over.w e.hom.hom.hom
  have : IsIso e.hom.hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso e.hom
  have hbc : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    rw [← he]
    infer_instance
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @LocallyOfFiniteType) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := G.X.hom) (g := b) ⟨⟨hsurj, hflat⟩, hqc⟩ hbc

/-- Commutativity descends from the diagonalizable splitting model. -/
theorem IsMultiplicativeType.isCommMonObj (hG : IsMultiplicativeType G) :
    IsCommMonObj G.X := by
  obtain ⟨K, hK, aK, Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k K
  let := hsurj
  let := hflat
  let := hqc
  apply isCommMonObj_of_baseChange b G
  apply (isCommMonObj_iff_isMulCommutative _).2
  intro U
  refine ⟨⟨fun x y => ?_⟩⟩
  apply (isoPointsEquiv e U).injective
  rw [map_mul, map_mul, mul_comm]

/-- An actual diagonalizable splitting model supplies all three geometric properties. -/
theorem IsMultiplicativeType.geometry (hG : IsMultiplicativeType G) :
    MultiplicativeTypeGeometry G :=
  ⟨hG.isAffine, hG.locallyOfFiniteType, hG.isCommMonObj⟩

end Langlands.GroupScheme
