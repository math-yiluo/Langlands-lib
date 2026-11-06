import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.LocalRing.Pullback
import Langlands.AlgebraicGeometry.AffineSchemePushoutStatement

open CategoryTheory Limits Opposite
open AlgebraicGeometry

universe u v w

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

variable {A B C D : CommRingCat.{u}} {f : B ⟶ D} {g : C ⟶ D}
  {i : A ⟶ B} {j : A ⟶ C}

/-- The comparison isomorphism from a supplied pullback to the compatible-pair ring. -/
noncomputable def canonicalPullbackIso (h : IsPullback i j f g) :
    A ≅ CommRingCat.of (f.hom.pullback g.hom) :=
  IsLimit.conePointUniqueUpToIso h.isLimit (CommRingCat.pullbackConeIsLimit f g)

@[reassoc (attr := simp)]
theorem canonicalPullbackIso_hom_fst (h : IsPullback i j f g) :
    (canonicalPullbackIso h).hom ≫ CommRingCat.ofHom (f.hom.pullbackFst g.hom) = i :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit
    (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.left

@[reassoc (attr := simp)]
theorem canonicalPullbackIso_hom_snd (h : IsPullback i j f g) :
    (canonicalPullbackIso h).hom ≫ CommRingCat.ofHom (f.hom.pullbackSnd g.hom) = j :=
  IsLimit.conePointUniqueUpToIso_hom_comp h.isLimit
    (CommRingCat.pullbackConeIsLimit f g) WalkingCospan.right

/-- A contravariant functor's pushout on the compatible-pair cone transports
along the comparison with any supplied ring pullback. -/
theorem isPushout_map_of_canonical {E : Type v} [Category.{w} E]
    (F : CommRingCat.{u}ᵒᵖ ⥤ E) (h : IsPullback i j f g)
    (hc : IsPushout (F.map f.op) (F.map g.op)
      (F.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)).op)
      (F.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)).op)) :
    IsPushout (F.map f.op) (F.map g.op) (F.map i.op) (F.map j.op) := by
  apply hc.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (F.mapIso (canonicalPullbackIso h).op)
  · simp
  · simp
  · change F.map _ ≫ F.map (canonicalPullbackIso h).hom.op = 𝟙 _ ≫ F.map i.op
    rw [Category.id_comp, ← F.map_comp, ← op_comp, canonicalPullbackIso_hom_fst]
  · change F.map _ ≫ F.map (canonicalPullbackIso h).hom.op = 𝟙 _ ≫ F.map j.op
    rw [Category.id_comp, ← F.map_comp, ← op_comp, canonicalPullbackIso_hom_snd]

/-- The canonical scheme pushout suffices for an arbitrary displayed ring pullback. -/
theorem isPushout_specMap_of_canonical (h : IsPullback i j f g)
    (hc : IsPushout (Spec.map f) (Spec.map g)
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.map (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)))) :
    IsPushout (Spec.map f) (Spec.map g) (Spec.map i) (Spec.map j) :=
  isPushout_map_of_canonical Scheme.Spec h hc

/-- The same transport applies to the underlying topological spectrum maps. -/
theorem isPushout_specTopMap_of_canonical (h : IsPullback i j f g)
    (hc : IsPushout (Spec.topMap f) (Spec.topMap g)
      (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackFst g.hom)))
      (Spec.topMap (CommRingCat.ofHom (f.hom.pullbackSnd g.hom)))) :
    IsPushout (Spec.topMap f) (Spec.topMap g) (Spec.topMap i) (Spec.topMap j) :=
  isPushout_map_of_canonical Spec.toTop h hc

end Langlands.AlgebraicGeometry.AffineSchemePushout
