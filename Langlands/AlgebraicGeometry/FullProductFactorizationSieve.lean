import Langlands.AlgebraicGeometry.Descent.FppfClosedLocusDescentProof
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # The sieve of full-product factorizations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FullProductFactorization

variable {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- The morphism from the entire base-changed source to the ambient product. -/
def productMap {T : Scheme.{u}} (t : T ⟶ Y) :
    pullback f (t ≫ g) ⟶ pullback f g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ t) (by
    rw [Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma productMap_fst {T : Scheme.{u}} (t : T ⟶ Y) :
    productMap f g t ≫ pullback.fst f g = pullback.fst f (t ≫ g) := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma productMap_snd {T : Scheme.{u}} (t : T ⟶ Y) :
    productMap f g t ≫ pullback.snd f g = pullback.snd f (t ≫ g) ≫ t := by
  exact pullback.lift_snd _ _ _

variable (d : D ⟶ pullback f g)

/-- Maps into `Y` whose whole product with `X` factors through `d`. -/
def sieve : Sieve Y where
  arrows T t := ∃ q : pullback f (t ≫ g) ⟶ D, q ≫ d = productMap f g t
  downward_closed := by
    intro T V t ht v
    obtain ⟨q, hq⟩ := ht
    let a : pullback f ((v ≫ t) ≫ g) ⟶ pullback f (t ≫ g) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ v) (by
        simpa only [Category.assoc] using (pullback.condition (f := f) (g := (v ≫ t) ≫ g)))
    refine ⟨a ≫ q, ?_⟩
    rw [Category.assoc a q d, hq]
    apply pullback.hom_ext <;>
      simp [a, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc]

/-- Full-product factorization through a monomorphism descends along covering
sieves in every subcanonical topology on schemes. -/
theorem isClosed (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] [Mono d] :
    J.IsClosed (sieve f g d) := by
  intro T t ht
  let p : pullback f (t ≫ g) ⟶ T := pullback.snd _ _
  refine FppfClosedLocusDescent.exists_lift_of_covering J d (productMap f g t)
    (((sieve f g d).pullback t).pullback p) (J.pullback_stable p ht) ?_
  intro V h hh
  obtain ⟨q, hq⟩ := hh
  let a : V ⟶ pullback f (((h ≫ p) ≫ t) ≫ g) :=
    pullback.lift (h ≫ pullback.fst f (t ≫ g)) (𝟙 V) (by
      simpa only [Category.assoc, Category.id_comp, p] using
        congrArg (h ≫ ·) (pullback.condition (f := f) (g := t ≫ g)))
  refine ⟨a ≫ q, ?_⟩
  rw [Category.assoc a q d, hq]
  apply pullback.hom_ext <;>
    simp [a, p, Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc]

/-- In particular, full-product factorization is fpqc local on every test
scheme, without any finite presentation assumption. -/
theorem fpqc_isClosed [Mono d] : Scheme.fpqcTopology.IsClosed (sieve f g d) :=
  isClosed f g d Scheme.fpqcTopology

end Langlands.AlgebraicGeometry.FullProductFactorization
