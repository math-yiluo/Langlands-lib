import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionStatement
import Langlands.AlgebraicGeometry.Picard.AmpleSectionOpenBasisProof
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Topological prerequisites for field base change ampleness reflection -/

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Langlands.AlgebraicGeometry.Picard

namespace FieldAmpleReflection

/-- A quasi-compact surjection reflects quasi-separatedness of the underlying scheme. -/
theorem quasiSeparatedSpace_of_surjective {X Y : Scheme.{u}} (g : Y ⟶ X)
    [QuasiCompact g] [Surjective g] [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have hU : IsCompact (g ⁻¹ᵁ U.1 : Set Y) := g.isCompact_preimage U.2.isCompact
  have hV : IsCompact (g ⁻¹ᵁ V.1 : Set Y) := g.isCompact_preimage V.2.isCompact
  have hUV := hU.inter_of_isOpen hV (g ⁻¹ᵁ U.1).isOpen (g ⁻¹ᵁ V.1).isOpen
  have hImage := hUV.image g.continuous
  change IsCompact (g '' (g ⁻¹' (U : Set X) ∩ g ⁻¹' (V : Set X))) at hImage
  rwa [← Set.preimage_inter, Set.image_preimage_eq _ g.surjective] at hImage

/-- The projection associated to a morphism of field spectra is surjective. -/
theorem surjective_projection (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) :
    Surjective (CategoryTheory.Limits.pullback.fst p b) := by
  let : Surjective b := inferInstance
  infer_instance

/-- Ampleness after field base change supplies compactness and quasi-separatedness below. -/
theorem compactSpace_and_quasiSeparatedSpace (k K : Type u) [Field k] [Field K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k)) (L : LineBundle X)
    (hL : ((LineBundle.pullback (CategoryTheory.Limits.pullback.fst p b)).obj L).IsAmple) :
    CompactSpace X ∧ QuasiSeparatedSpace X := by
  let q := CategoryTheory.Limits.pullback.fst p b
  let : Surjective q := surjective_projection k K b X p
  let : CompactSpace (CategoryTheory.Limits.pullback p b : Scheme.{u}) := hL.compactSpace
  let : QuasiSeparatedSpace (CategoryTheory.Limits.pullback p b : Scheme.{u}) :=
    hL.quasiSeparatedSpace
  let : IsAffineHom b := inferInstance
  let : IsAffineHom q := MorphismProperty.pullback_fst p b (inferInstance : IsAffineHom b)
  exact ⟨q.surjective.compactSpace q.continuous, quasiSeparatedSpace_of_surjective q⟩

end FieldAmpleReflection

end Langlands.AlgebraicGeometry.Picard
