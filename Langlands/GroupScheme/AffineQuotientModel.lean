import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.DominantHomFlatProof
import Langlands.GroupScheme.HomDescent
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # An affine model of an actual quotient with a faithful representation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GeneratedImage

variable {S : Scheme.{u}} {G H : GroupScheme S} {f : G ⟶ H}
    (D : GeneratedImage f.hom.hom)

private theorem factorIsMonHom : IsMonHom D.factor := by
  have : Mono D.inclusion.hom.hom := D.represents.1
  constructor
  · apply (cancel_mono D.inclusion.hom.hom).mp
    simp only [Category.assoc, D.factor_comp, IsMonHom.one_hom]
  · apply (cancel_mono D.inclusion.hom.hom).mp
    rw [Category.assoc, D.factor_comp, IsMonHom.mul_hom,
      Category.assoc, IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc,
      D.factor_comp]

/-- The factor of an actual group homomorphism through its generated image
preserves the actual group laws. -/
def factorHom : G ⟶ D.group :=
  letI := factorIsMonHom D
  Grp.homMk D.factor

@[reassoc]
theorem factorHom_comp : D.factorHom ≫ D.inclusion = f :=
  Grp.hom_ext _ _ D.factor_comp

/-- Dominance of a product of images implies dominance of the original
homomorphism, since its image is already closed under multiplication. -/
theorem isDominant_factorHom
    (hD : ∃ n : ℕ, 0 < n ∧ IsDominant (D.powerMap n).left) :
    IsDominant D.factorHom.hom.hom.left := by
  obtain ⟨n, _, hn⟩ := hD
  have he : orderedPowerMap (𝟙 G.X) n ≫ D.factorHom.hom.hom = D.powerMap n := by
    have h := orderedPowerMap_comp (𝟙 G.X) D.factorHom n
    change orderedPowerMap (𝟙 G.X) n ≫ D.factor = D.powerMap n
    change orderedPowerMap (𝟙 G.X) n ≫ D.factor =
      orderedPowerMap (𝟙 G.X ≫ D.factor) n at h
    simpa only [Category.id_comp, powerMap] using h
  have : IsDominant ((orderedPowerMap (𝟙 G.X) n).left ≫ D.factorHom.hom.hom.left) := by
    rw [← Over.comp_left, he]
    exact hn
  exact IsDominant.of_comp (orderedPowerMap (𝟙 G.X) n).left D.factorHom.hom.hom.left

end GeneratedImage

variable {k : Type u} [Field k]
    {G Q : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]

/-- An actual affine group with a closed linear embedding, identified with the
given quotient by an inclusion-compatible group-scheme isomorphism. -/
structure AffineQuotientModel (ρ : MatrixRepresentation Q n) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : MatrixRepresentation group n
  closed : IsClosedSubgroup inclusion
  affine : IsAffineHom group.X.hom
  comparison : Q ≅ group
  comparison_fac : comparison.hom ≫ inclusion = ρ

namespace AffineQuotientModel

/-- Construct an actual affine model using the smooth generated image of the
original connected affine source and faithful flat descent. -/
def ofFaithfulRepresentation
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [LocallyOfFiniteType Q.X.hom] [QuasiCompact Q.X.hom]
    (q : G ⟶ Q) [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (ρ : MatrixRepresentation Q n) [Mono ρ.hom.hom] : AffineQuotientModel ρ :=
  Classical.choice (by
    have : GeometricallyIntegral G.X.hom :=
      smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
    let L := GeneralLinear.groupScheme n (CommRingCat.of k)
    have : Smooth L.X.hom := GeneralLinear.smoothStatement n (CommRingCat.of k)
    have : IsAffineHom L.X.hom :=
      GeneralLinear.isAffineHom_groupScheme (n := n) (R := CommRingCat.of k)
    let f : G ⟶ L := q ≫ ρ
    obtain ⟨D, hD⟩ := ImageGeneration.pointedImageGeneration k L inferInstance inferInstance
      G.X inferInstance inferInstance inferInstance η[G.X] f.hom.hom
      (IsMonHom.one_hom f.hom.hom)
    have : Mono D.inclusion.hom.hom := D.represents.1
    have hk : kernelι q ≫ D.factorHom = 0 := by
      apply Grp.hom_ext
      apply (cancel_mono D.inclusion.hom.hom).mp
      change ((kernelι q).hom.hom ≫ D.factor) ≫ D.inclusion.hom.hom =
        (1 : (kernel q).X ⟶ D.group.X) ≫ D.inclusion.hom.hom
      have hq : (kernelι q).hom.hom ≫ q.hom.hom = 1 := (kernel_isPullback q).w
      rw [Category.assoc, D.factor_comp]
      change (kernelι q).hom.hom ≫ (q.hom.hom ≫ ρ.hom.hom) =
        (1 : (kernel q).X ⟶ D.group.X) ≫ D.inclusion.hom.hom
      rw [← Category.assoc, hq, MonObj.one_comp, MonObj.one_comp]
    let t : Q ⟶ D.group := FpqcHomDescent.hom q D.factorHom hk
    have ht : q ≫ t = D.factorHom := FpqcHomDescent.fac q D.factorHom hk
    have hti : t ≫ D.inclusion = ρ := by
      have : Epi q.hom.hom.left := Flat.epi_of_flat_of_surjective _
      have : Epi q.hom.hom := Over.epi_of_epi_left _
      apply Grp.hom_ext
      apply (cancel_epi q.hom.hom).mp
      change (q ≫ t ≫ D.inclusion).hom.hom = (q ≫ ρ).hom.hom
      rw [← Category.assoc, ht, D.factorHom_comp]
    have : Mono t.hom.hom :=
      mono_of_mono_fac (congrArg (fun a => a.hom.hom) hti)
    have : Smooth D.group.X.hom := hD.1
    have : IsAffineHom D.group.X.hom := hD.2.1
    have : IsReduced D.group.X.left :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
        k D.group.X.left D.group.X.hom
    have : GeometricallyReduced D.group.X.hom :=
      Langlands.AlgebraicGeometry.SmoothReducedProof.geometricallyReduced_of_smooth _
    have hDom : IsDominant D.factorHom.hom.hom.left := D.isDominant_factorHom hD.2.2.2
    have : IsDominant (q.hom.hom.left ≫ t.hom.hom.left) := by
      change IsDominant (q ≫ t).hom.hom.left
      rw [ht]
      exact hDom
    have : IsDominant t.hom.hom.left := IsDominant.of_comp q.hom.hom.left t.hom.hom.left
    have : IsSchemeTheoreticallyDominant t.hom.hom.left :=
      IsSchemeTheoreticallyDominant.of_isDominant _
    have : IsIso t := DominantHomFlat.isIso_of_schematicallyDominant t
    exact ⟨{
      group := D.group
      inclusion := D.inclusion
      closed := D.closed
      affine := hD.2.1
      comparison := asIso t
      comparison_fac := hti
    }⟩)

/-- The given quotient itself is affine by the actual comparison isomorphism. -/
theorem isAffineHom {ρ : MatrixRepresentation Q n} (D : AffineQuotientModel ρ) :
    IsAffineHom Q.X.hom := by
  have : IsAffineHom D.group.X.hom := D.affine
  let e : Q.X ≅ D.group.X :=
    (Grp.forget (Over (Spec (CommRingCat.of k)))).mapIso D.comparison
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

end AffineQuotientModel

end Langlands.GroupScheme
