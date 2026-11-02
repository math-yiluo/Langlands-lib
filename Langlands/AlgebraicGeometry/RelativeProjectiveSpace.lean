import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Relative finite projective space over a scheme -/

noncomputable section

open CategoryTheory Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

/-- Relative projective `n`-space is the base change of the integral polynomial-Proj model. -/
def RelativeProjectiveSpace (S : Scheme.{u}) (n : ℕ) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (ProjectiveSpace (ULift.{u} ℤ) n))

namespace RelativeProjectiveSpace

/-- The structure morphism to the base scheme. -/
def toBase (S : Scheme.{u}) (n : ℕ) : RelativeProjectiveSpace S n ⟶ S :=
  pullback.fst _ _

/-- The projection to the integral polynomial-Proj model. -/
def toIntegral (S : Scheme.{u}) (n : ℕ) :
    RelativeProjectiveSpace S n ⟶ ProjectiveSpace (ULift.{u} ℤ) n :=
  pullback.snd _ _

/-- A map to relative projective space from a base map and a map to the integral model. -/
def lift {X S : Scheme.{u}} (n : ℕ) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace (ULift.{u} ℤ) n) :
    X ⟶ RelativeProjectiveSpace S n :=
  pullback.lift p q (by simp)

@[reassoc (attr := simp)]
lemma lift_toBase {X S : Scheme.{u}} (n : ℕ) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace (ULift.{u} ℤ) n) :
    lift n p q ≫ toBase S n = p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma lift_toIntegral {X S : Scheme.{u}} (n : ℕ) (p : X ⟶ S)
    (q : X ⟶ ProjectiveSpace (ULift.{u} ℤ) n) :
    lift n p q ≫ toIntegral S n = q :=
  pullback.lift_snd _ _ _

@[ext]
lemma hom_ext {X S : Scheme.{u}} {n : ℕ} {f g : X ⟶ RelativeProjectiveSpace S n}
    (h₁ : f ≫ toBase S n = g ≫ toBase S n)
    (h₂ : f ≫ toIntegral S n = g ≫ toIntegral S n) : f = g :=
  pullback.hom_ext h₁ h₂

@[simp]
lemma lift_projections {X S : Scheme.{u}} {n : ℕ}
    (f : X ⟶ RelativeProjectiveSpace S n) :
    lift n (f ≫ toBase S n) (f ≫ toIntegral S n) = f := by
  apply hom_ext <;> simp

/-- The universal property, expressed as an equivalence of actual scheme Hom types. -/
def homEquiv (X S : Scheme.{u}) (n : ℕ) :
    (X ⟶ RelativeProjectiveSpace S n) ≃
      (X ⟶ S) × (X ⟶ ProjectiveSpace (ULift.{u} ℤ) n) where
  toFun f := ⟨f ≫ toBase S n, f ≫ toIntegral S n⟩
  invFun f := lift n f.1 f.2
  left_inv := lift_projections
  right_inv f := by simp

/-- The induced morphism for a change of base. -/
def map (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    RelativeProjectiveSpace S n ⟶ RelativeProjectiveSpace T n :=
  lift n (toBase S n ≫ f) (toIntegral S n)

@[reassoc (attr := simp)]
lemma map_toBase (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toBase T n = toBase S n ≫ f :=
  lift_toBase _ _ _

@[reassoc (attr := simp)]
lemma map_toIntegral (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    map n f ≫ toIntegral T n = toIntegral S n :=
  lift_toIntegral _ _ _

@[simp]
lemma map_id (n : ℕ) (S : Scheme.{u}) : map n (𝟙 S) = 𝟙 _ := by
  apply hom_ext <;> simp

@[simp]
lemma map_comp (n : ℕ) {S T U : Scheme.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    map n (f ≫ g) = map n f ≫ map n g := by
  apply hom_ext <;> simp

/-- Relative projective `n`-space as a functor of its scheme base. -/
def functor (n : ℕ) : Scheme.{u} ⥤ Scheme.{u} where
  obj S := RelativeProjectiveSpace S n
  map f := map n f
  map_id S := map_id n S
  map_comp f g := map_comp n f g

/-- The canonical Cartesian base-change isomorphism. -/
def baseChangeIso (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    RelativeProjectiveSpace S n ≅ pullback f (toBase T n) where
  hom := pullback.lift (toBase S n) (map n f) (by simp)
  inv := lift n (pullback.fst f (toBase T n))
    (pullback.snd f (toBase T n) ≫ toIntegral T n)
  hom_inv_id := by
    apply hom_ext <;> simp [Category.assoc, pullback.lift_fst, pullback.lift_snd_assoc]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [Category.assoc, pullback.lift_fst]
    · apply hom_ext
      · simp [Category.assoc, pullback.lift_snd_assoc, pullback.condition]
      · simp [Category.assoc, pullback.lift_snd_assoc]

@[reassoc (attr := simp)]
lemma baseChangeIso_hom_fst (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (baseChangeIso n f).hom ≫ pullback.fst f (toBase T n) = toBase S n :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeIso_hom_snd (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (baseChangeIso n f).hom ≫ pullback.snd f (toBase T n) = map n f :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma baseChangeIso_inv_toBase (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (baseChangeIso n f).inv ≫ toBase S n = pullback.fst f (toBase T n) :=
  lift_toBase _ _ _

@[reassoc (attr := simp)]
lemma baseChangeIso_inv_toIntegral (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    (baseChangeIso n f).inv ≫ toIntegral S n =
      pullback.snd f (toBase T n) ≫ toIntegral T n :=
  lift_toIntegral _ _ _

lemma isPullback_map (n : ℕ) {S T : Scheme.{u}} (f : S ⟶ T) :
    IsPullback (toBase S n) (map n f) f (toBase T n) :=
  IsPullback.of_iso_pullback ⟨by simp⟩ (baseChangeIso n f)
    (baseChangeIso_hom_fst n f) (baseChangeIso_hom_snd n f)

end RelativeProjectiveSpace

end Langlands.AlgebraicGeometry
