import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Compatible actual line bundles on adic thickenings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

namespace FormalLineBundle

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The affine thickening with coordinate ring `R / I^(n+1)`. -/
abbrev adicBase (I : Ideal R) (n : ℕ) : Scheme.{u} :=
  Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))

/-- The quotient map defining an adic base thickening. -/
def adicBaseProjection (I : Ideal R) (n : ℕ) :
    adicBase I n ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))

/-- The canonical arrow from one adic base thickening to the next. -/
def adicBaseTransition (I : Ideal R) (n : ℕ) :
    adicBase I n ⟶ adicBase I (n + 1) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + 1 + 1))))

@[reassoc (attr := simp)]
lemma adicBaseTransition_projection (I : Ideal R) (n : ℕ) :
    adicBaseTransition I n ≫ adicBaseProjection I (n + 1) =
      adicBaseProjection I n := by
  dsimp only [adicBaseTransition, adicBaseProjection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

/-- The actual scheme obtained by base change to `R / I^(n+1)`. -/
abbrev adicSpace (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (n : ℕ) :
    Scheme.{u} :=
  pullback f (adicBaseProjection I n)

/-- Projection from the adic thickening to the original scheme. -/
def adicProjection (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (n : ℕ) :
    adicSpace f I n ⟶ X :=
  pullback.fst f (adicBaseProjection I n)

/-- The canonical arrow between consecutive actual scheme thickenings. -/
def adicTransition (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (n : ℕ) :
    adicSpace f I n ⟶ adicSpace f I (n + 1) :=
  pullback.lift (adicProjection f I n)
    (pullback.snd f (adicBaseProjection I n) ≫ adicBaseTransition I n) (by
      rw [Category.assoc, adicBaseTransition_projection]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma adicTransition_projection (f : X ⟶ Spec (CommRingCat.of R))
    (I : Ideal R) (n : ℕ) :
    adicTransition f I n ≫ adicProjection f I (n + 1) = adicProjection f I n :=
  pullback.lift_fst _ _ _

end FormalLineBundle

open FormalLineBundle

/-- A compatible system of actual locally free rank-one sheaves on the adic
thickenings, with actual isomorphisms for ordinary pullback. -/
structure FormalLineBundleSystem {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R) where
  obj (n : ℕ) : LineBundle (adicSpace f I n)
  transition (n : ℕ) :
    (LineBundle.pullback (adicTransition f I n)).obj (obj (n + 1)) ≅ obj n

namespace FormalLineBundleSystem

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {I : Ideal R}

/-- The system of ordinary restrictions of an actual line bundle. -/
def ofLineBundle (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
    (L : LineBundle X) : FormalLineBundleSystem f I where
  obj n := (LineBundle.pullback (adicProjection f I n)).obj L
  transition n :=
    (LineBundle.pullbackComp (adicTransition f I n) (adicProjection f I (n + 1))).app L ≪≫
      ObjectProperty.isoMk _
        ((Scheme.Modules.pullbackCongr (adicTransition_projection f I n)).app L.obj)

/-- A system comparison consists of component isomorphisms commuting with every
ordinary-pullback transition. -/
structure Comparison (F G : FormalLineBundleSystem f I) where
  component (n : ℕ) : F.obj n ≅ G.obj n
  commutes (n : ℕ) :
    (LineBundle.pullback (adicTransition f I n)).map (component (n + 1)).hom ≫
        (G.transition n).hom =
      (F.transition n).hom ≫ (component n).hom

/-- The identity comparison respects all transition isomorphisms. -/
def Comparison.refl (F : FormalLineBundleSystem f I) : Comparison F F where
  component n := Iso.refl (F.obj n)
  commutes n := by simp

/-- Consecutive compatible comparisons compose componentwise. -/
def Comparison.trans {F G H : FormalLineBundleSystem f I}
    (e : Comparison F G) (d : Comparison G H) : Comparison F H where
  component n := e.component n ≪≫ d.component n
  commutes n := by
    simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]
    rw [d.commutes, ← Category.assoc, e.commutes, Category.assoc]

/-- An algebraization is an actual line bundle together with a compatible
comparison of its entire restriction system with the given system. -/
def IsAlgebraization (L : LineBundle X) (F : FormalLineBundleSystem f I) : Prop :=
  Nonempty (Comparison (ofLineBundle f I L) F)

/-- An actual line bundle algebraizes its own restriction system. -/
lemma isAlgebraization_ofLineBundle (L : LineBundle X) :
    IsAlgebraization L (ofLineBundle f I L) :=
  ⟨Comparison.refl _⟩

end FormalLineBundleSystem

end Langlands.AlgebraicGeometry.Picard
