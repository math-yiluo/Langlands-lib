import Langlands.AlgebraicGeometry.Picard.AffineFamilyDescent
import Langlands.AlgebraicGeometry.Picard.ProperLineBundleIsomOfHom
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType

/-! # Eventual equality of actual presheaf sections over affine bases -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard

/-- The structure arrow from an affine algebra test to the identity base. -/
def affineBaseProjection (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    affineBase R A ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R))) :=
  Over.homMk (affineBase R A).hom (by simp)

/-- Equality of two sections after an arbitrary affine algebra extension is
already visible over a finitely generated subalgebra containing any prescribed
finite set. -/
def HasAffineSubalgebraEqualityDescent
    {R : Type u} [CommRing R]
    (F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of R))) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra R A]
    (x y : F.obj (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))))
    (_ : F.map (affineBaseProjection R A).op x =
      F.map (affineBaseProjection R A).op y) (s : Finset A),
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      F.map (affineBaseProjection R B).op x = F.map (affineBaseProjection R B).op y

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Equality of two scheme points descends to a finite algebra stage. -/
theorem exists_affinePoint_equality_subalgebra
    (I : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType I.hom]
    (p q : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ I)
    (hpq : affineBaseProjection R A ≫ p = affineBaseProjection R A ≫ q)
    (s : Finset A) :
    ∃ B : Subalgebra R A, B.FG ∧ (↑s : Set A) ⊆ B ∧
      affineBaseProjection R B ≫ p = affineBaseProjection R B ≫ q := by
  let S := Spec (CommRingCat.of R)
  let a := (affineBase R A).hom
  have hab : a ≫ p.left = a ≫ q.left :=
    congrArg CommaMorphism.left hpq
  have hfst : pullback.fst (𝟙 S) a = pullback.snd (𝟙 S) a ≫ a := by
    simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := a))
  have hpb : pullback.fst (𝟙 S) a ≫ p.left =
      pullback.fst (𝟙 S) a ≫ q.left := by
    simpa only [← Category.assoc, ← hfst] using
      congrArg (fun k ↦ pullback.snd (𝟙 S) a ≫ k) hab
  obtain ⟨B, hB, hs, h⟩ :=
    exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (𝟙 S) I.hom p.left q.left (Over.w p) (Over.w q) hpb s
  let b := (affineBase R B).hom
  let i : (affineBase R B).left ⟶ pullback (𝟙 S) b :=
    pullback.lift b (𝟙 _) (by simp)
  refine ⟨B, hB, hs, ?_⟩
  apply Over.OverMorphism.ext
  change b ≫ p.left = b ≫ q.left
  change pullback.fst (𝟙 S) b ≫ p.left = pullback.fst (𝟙 S) b ≫ q.left at h
  simpa only [Category.assoc, i, pullback.lift_fst_assoc] using
    congrArg (fun k ↦ i ≫ k) h

/-- Affine finite-presentation representability detects equality at a finite
algebra stage, with the actual restriction maps. -/
theorem hasAffineSubalgebraEqualityDescent_of_representable
    {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of R))}
    (hF : AlgebraicSpace.IsAffineFinitePresentationRepresentable F) :
    HasAffineSubalgebraEqualityDescent F := by
  obtain ⟨I, ⟨e⟩, _, hI⟩ := hF
  intro A _ _ x y hxy s
  let T := Over.mk (𝟙 (Spec (CommRingCat.of R)))
  let p : T ⟶ I := (e.inv.app (op T) x).down
  let q : T ⟶ I := (e.inv.app (op T) y).down
  have hx : (e.inv.app _ (F.map (affineBaseProjection R A).op x)).down =
      affineBaseProjection R A ≫ p :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineBaseProjection R A).op) x)
  have hy : (e.inv.app _ (F.map (affineBaseProjection R A).op y)).down =
      affineBaseProjection R A ≫ q :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineBaseProjection R A).op) y)
  have hpq : affineBaseProjection R A ≫ p = affineBaseProjection R A ≫ q :=
    hx.symm.trans ((congrArg (fun z ↦ (e.inv.app _ z).down) hxy).trans hy)
  obtain ⟨B, hB, hs, hBpq⟩ := exists_affinePoint_equality_subalgebra I p q hpq s
  refine ⟨B, hB, hs, ?_⟩
  have hxB : (e.inv.app _ (F.map (affineBaseProjection R B).op x)).down =
      affineBaseProjection R B ≫ p :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineBaseProjection R B).op) x)
  have hyB : (e.inv.app _ (F.map (affineBaseProjection R B).op y)).down =
      affineBaseProjection R B ≫ q :=
    congrArg ULift.down (types_congr_hom (e.inv.naturality
      (affineBaseProjection R B).op) y)
  apply ((e.app (op (affineBase R B))).toEquiv).symm.injective
  apply ULift.ext
  exact hxB.trans (hBpq.trans hyB.symm)

namespace PicardGroupoid

/-- Under focused Isom representability, equality of actual Picard arrows is
detected at a finite algebra stage. -/
theorem affineIsomEqualityDescent_of_isomRepresentability
    (h : ProperLineBundleIsomRepresentabilityStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S) (hf : IsProper f) (hflat : Flat f)
    (hfp : LocallyOfFinitePresentation f) (t : Spec (CommRingCat.of R) ⟶ S)
    (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t))) :
    HasAffineSubalgebraEqualityDescent (relativeIsomPresheaf f L M) :=
  hasAffineSubalgebraEqualityDescent_of_representable
    (h S X f hf hflat hfp (Over.mk t) L M)

/-- The focused Hom premise suffices for eventual equality of actual Picard
isomorphisms. -/
theorem affineIsomEqualityDescent_of_homRepresentability
    (h : ProperLineBundleHomRepresentabilityStatement.{u})
    {S X : Scheme.{u}} (f : X ⟶ S) (hf : IsProper f) (hflat : Flat f)
    (hfp : LocallyOfFinitePresentation f) (t : Spec (CommRingCat.of R) ⟶ S)
    (L M : PicardGroupoid ((relativeSpace f).obj (Over.mk t))) :
    HasAffineSubalgebraEqualityDescent (relativeIsomPresheaf f L M) :=
  affineIsomEqualityDescent_of_isomRepresentability
    (properLineBundleIsomRepresentability_of_hom h) f hf hflat hfp t L M

end PicardGroupoid

end Langlands.AlgebraicGeometry.Picard
