import Langlands.GroupScheme.SchematicImage
import Langlands.GroupScheme.SchematicImageComparison
import Langlands.GroupScheme.Descent.GaloisInvariantParabolics

/-! # Actual schematic images commute with flat field base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchematicImage

variable {k L : Type u} [Field k] [Field L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (f : G ⟶ H)
  (b : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of k)) [Flat b]

local instance original_isAffine (D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom D.X.hom] : IsAffine D.X.left :=
  isAffine_of_isAffineHom D.X.hom

local instance pulled_affine (D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom D.X.hom] :
    IsAffineHom ((GroupScheme.baseChange b).obj D).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd D.X.hom b)
  infer_instance

local instance pulled_isAffine (D : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom D.X.hom] :
    IsAffine ((GroupScheme.baseChange b).obj D).X.left :=
  isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj D).X.hom

local instance pulled_projection_dominant :
    IsSchemeTheoreticallyDominant
      ((GroupScheme.baseChange b).map (projection f)).hom.hom.left :=
  isSchemeTheoreticallyDominant_baseChange b (projection f)

omit [Flat b] in
private theorem pulled_inclusion_closed :
    IsClosedSubgroup ((GroupScheme.baseChange b).map (inclusion f)) :=
  IsClosedSubgroup.baseChange b
    (inferInstanceAs (IsClosedImmersion (inclusion f).hom.hom.left))

omit [Flat b] in
private theorem pulled_factorization :
    (GroupScheme.baseChange b).map (projection f) ≫
        (GroupScheme.baseChange b).map (inclusion f) =
      projection ((GroupScheme.baseChange b).map f) ≫
        inclusion ((GroupScheme.baseChange b).map f) := by
  rw [← Functor.map_comp, projection_inclusion, projection_inclusion]

/-- The actual base change of the original schematic image is canonically
isomorphic to the schematic image of the actual base-changed homomorphism. -/
def baseChangeIso :
    (GroupScheme.baseChange b).obj (image f) ≅
      image ((GroupScheme.baseChange b).map f) :=
  isoOfDominantFactorizations
    ((GroupScheme.baseChange b).map (projection f))
    (projection ((GroupScheme.baseChange b).map f))
    ((GroupScheme.baseChange b).map (inclusion f))
    (inclusion ((GroupScheme.baseChange b).map f))
    (pulled_inclusion_closed f b)
    (inferInstanceAs
      (IsClosedImmersion (inclusion ((GroupScheme.baseChange b).map f)).hom.hom.left))
    (pulled_factorization f b)

/-- The comparison preserves the inclusions into the original pulled-back target. -/
@[reassoc]
theorem baseChangeIso_hom_comp :
    (baseChangeIso f b).hom ≫ inclusion ((GroupScheme.baseChange b).map f) =
      (GroupScheme.baseChange b).map (inclusion f) :=
  isoOfDominantFactorizations_hom_comp _ _ _ _ _ _ _

/-- The comparison also preserves the original projections onto the two images. -/
@[reassoc]
theorem projection_baseChangeIso_hom :
    (GroupScheme.baseChange b).map (projection f) ≫ (baseChangeIso f b).hom =
      projection ((GroupScheme.baseChange b).map f) := by
  have : Mono (inclusion ((GroupScheme.baseChange b).map f)).hom.hom :=
    Over.mono_of_mono_left _
  apply Grp.hom_ext
  apply (cancel_mono (inclusion ((GroupScheme.baseChange b).map f)).hom.hom).mp
  change
    (((GroupScheme.baseChange b).map (projection f) ≫ (baseChangeIso f b).hom) ≫
      inclusion ((GroupScheme.baseChange b).map f)).hom.hom =
    (projection ((GroupScheme.baseChange b).map f) ≫
      inclusion ((GroupScheme.baseChange b).map f)).hom.hom
  rw [Category.assoc, baseChangeIso_hom_comp, ← Functor.map_comp,
    projection_inclusion, projection_inclusion]

/-- The full all-test subgroup functors agree after base change. -/
theorem baseChange_range_inclusion :
    (SubgroupFunctor.range (inclusion f)).baseChange b =
      SubgroupFunctor.range (inclusion ((GroupScheme.baseChange b).map f)) := by
  rw [SubgroupFunctor.range_baseChange]
  exact range_eq_of_dominantFactorizations
    ((GroupScheme.baseChange b).map (projection f))
    (projection ((GroupScheme.baseChange b).map f))
    ((GroupScheme.baseChange b).map (inclusion f))
    (inclusion ((GroupScheme.baseChange b).map f))
    (pulled_inclusion_closed f b)
    (inferInstanceAs
      (IsClosedImmersion (inclusion ((GroupScheme.baseChange b).map f)).hom.hom.left))
    (pulled_factorization f b)

end Langlands.GroupScheme.SchematicImage

namespace Langlands.GroupScheme.SchematicImage

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (f : G ⟶ H)

/-- Parabolicity of the actual image after an algebraic field extension implies
parabolicity of the actual original image. -/
theorem isParabolic_inclusion_of_baseChange
    (hp : IsParabolicSubgroup
      (inclusion ((GroupScheme.baseChange (algebraBaseMap k L)).map f))) :
    IsParabolicSubgroup (inclusion f) := by
  let b := algebraBaseMap k L
  have : Flat b := (fieldExtension_fpqc k L).2.1
  have hbc : IsParabolicSubgroup ((GroupScheme.baseChange b).map (inclusion f)) := by
    rw [← baseChangeIso_hom_comp f b]
    exact hp.iso_comp (baseChangeIso f b)
  exact hbc.of_baseChange_of_algebraicExtension
    (inferInstanceAs (IsClosedImmersion (inclusion f).hom.hom.left))

end Langlands.GroupScheme.SchematicImage
