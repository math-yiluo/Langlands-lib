import Langlands.GroupScheme.HomScheme.ConjugatorLifting

/-! # Correcting multiplicativity defects and comparing homomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- The multiplicativity defect of an arbitrary map of the underlying schemes. -/
def multiplicationDefect (s : H.X ⟶ G.X) : H.X ⊗ H.X ⟶ G.X :=
  (fst H.X H.X ≫ s) * (snd H.X H.X ≫ s) *
    ((fst H.X H.X * snd H.X H.X) ≫ s)⁻¹

/-- Evaluation of the actual defect morphism on a pair of points. -/
theorem multiplicationDefect_value (s : H.X ⟶ G.X)
    (T : Over S) (h k : T ⟶ H.X) :
    lift h k ≫ multiplicationDefect s =
      (h ≫ s) * (k ≫ s) * ((h * k) ≫ s)⁻¹ := by
  simp only [multiplicationDefect, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, lift_fst, lift_snd]

/-- Associativity is the nonabelian defect identity before any identification
of the infinitesimal kernel with an additive module. -/
theorem multiplicationDefect_cocycle (s : H.X ⟶ G.X)
    (T : Over S) (h k l : T ⟶ H.X) :
    (lift h k ≫ multiplicationDefect s) *
        (lift (h * k) l ≫ multiplicationDefect s) =
      (h ≫ s) * (lift k l ≫ multiplicationDefect s) * (h ≫ s)⁻¹ *
        (lift h (k * l) ≫ multiplicationDefect s) := by
  simp only [multiplicationDefect_value, mul_assoc h k l]
  group

/-- Correct a scheme-map lift by the inverse of a supplied regular cochain. -/
def correctedSchemeMap (s b : H.X ⟶ G.X) : H.X ⟶ G.X := b⁻¹ * s

/-- The multiplicativity defect is the coboundary of the supplied correction,
as an explicit equation on all test points. -/
def IsDefectCorrection (s b : H.X ⟶ G.X) : Prop :=
  ∀ (T : Over S) (h k : T ⟶ H.X),
    (lift h k ≫ multiplicationDefect s) * ((h * k) ≫ b) =
      (h ≫ s) * (k ≫ b) * (h ≫ s)⁻¹ * (h ≫ b)

private theorem correction_group_identity {Q : Type*} [Group Q]
    (x y z a b c : Q)
    (he : x * y * z⁻¹ * c = x * b * x⁻¹ * a) :
    c⁻¹ * z = (a⁻¹ * x) * (b⁻¹ * y) := by
  calc
    c⁻¹ * z =
        a⁻¹ * x * b⁻¹ * x⁻¹ * (x * y * z⁻¹ * c) * c⁻¹ * z := by
      rw [he]
      group
    _ = (a⁻¹ * x) * (b⁻¹ * y) := by group

/-- A cochain satisfying the defect equation makes the corrected map
multiplicative on every test scheme. -/
theorem correctedSchemeMap_mul (s b : H.X ⟶ G.X) (hb : IsDefectCorrection s b)
    (T : Over S) (h k : T ⟶ H.X) :
    (h * k) ≫ correctedSchemeMap s b =
      (h ≫ correctedSchemeMap s b) * (k ≫ correctedSchemeMap s b) := by
  have he := hb T h k
  rw [multiplicationDefect_value] at he
  simp only [correctedSchemeMap, MonObj.comp_mul, GrpObj.comp_inv]
  exact correction_group_identity (h ≫ s) (k ≫ s) ((h * k) ≫ s)
    (h ≫ b) (k ≫ b) ((h * k) ≫ b) he

/-- The actual group-scheme homomorphism obtained by correcting the regular
scheme map with a cochain satisfying the defect equation. -/
def correctedHom (s b : H.X ⟶ G.X) (hb : IsDefectCorrection s b) : H ⟶ G :=
  homOfPoints
    (fun T => MonoidHom.mk' (· ≫ correctedSchemeMap s b)
      (correctedSchemeMap_mul s b hb T))
    (fun _ _ => by simp only [MonoidHom.mk'_apply, Category.assoc])

/-- The corrected homomorphism has the prescribed corrected values on every
test scheme. -/
theorem comp_correctedHom (s b : H.X ⟶ G.X) (hb : IsDefectCorrection s b)
    (T : Over S) (h : T ⟶ H.X) :
    h ≫ (correctedHom s b hb).hom.hom = h ≫ correctedSchemeMap s b := by
  rw [correctedHom, comp_homOfPoints, MonoidHom.mk'_apply]
  intro _ _ _ _
  simp only [MonoidHom.mk'_apply, Category.assoc]

/-- Difference between two actual homomorphisms, as an actual regular map of
their source scheme into the target. -/
def homomorphismDifference (f f' : H ⟶ G) : H.X ⟶ G.X :=
  f'.hom.hom * f.hom.hom⁻¹

/-- The difference of homomorphisms is a crossed one-cocycle for conjugation
through the first homomorphism. -/
theorem homomorphismDifference_cocycle (f f' : H ⟶ G)
    (T : Over S) (h k : T ⟶ H.X) :
    (h * k) ≫ homomorphismDifference f f' =
      (h ≫ homomorphismDifference f f') * (h ≫ f.hom.hom) *
        (k ≫ homomorphismDifference f f') * (h ≫ f.hom.hom)⁻¹ := by
  simp only [homomorphismDifference, MonObj.comp_mul, GrpObj.comp_inv,
    MonObj.mul_comp]
  group

/-- A base-point coboundary formula for the difference of homomorphisms gives
actual inner conjugacy. -/
theorem homomorphism_eq_conjugate_of_difference (f f' : H ⟶ G)
    (g : Over.mk (𝟙 S) ⟶ G.X)
    (hg : ∀ (T : Over S) (h : T ⟶ H.X),
      h ≫ homomorphismDifference f f' =
        G.constantPoint g T * (h ≫ f.hom.hom) * (G.constantPoint g T)⁻¹ *
          (h ≫ f.hom.hom)⁻¹) :
    f' = f ≫ (G.innerIso g).hom := by
  apply hom_ext_points
  intro T h
  change h ≫ f'.hom.hom = (h ≫ f.hom.hom) ≫ (G.innerIso g).hom.hom.hom
  rw [comp_innerIso_hom]
  have hh := hg T h
  simp only [homomorphismDifference, MonObj.comp_mul, GrpObj.comp_inv] at hh
  exact mul_right_cancel hh

end Langlands.GroupScheme.HomScheme
