import Langlands.AlgebraicGeometry.ComponentConstantRationalMaps
import Langlands.GroupScheme.Rational.Characters

/-! # Algebraizing componentwise constant homomorphisms of rational points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry
open Langlands.AlgebraicGeometry.ComponentConstant

namespace Langlands.GroupScheme.ComponentConstant

variable {k : Type u} [Field k] [IsAlgClosed k]
  (G H : GroupScheme (Spec (CommRingCat.of k)))
  [LocallyOfFiniteType G.X.hom]

local instance : IsLocallyNoetherian G.X.left :=
  LocallyOfFiniteType.isLocallyNoetherian G.X.hom

local instance : LocallyOfFiniteType (G.X ⊗ G.X).hom := by
  change LocallyOfFiniteType
    (Limits.pullback.fst G.X.hom G.X.hom ≫ G.X.hom)
  infer_instance

local instance : IsLocallyNoetherian (G.X ⊗ G.X).left :=
  LocallyOfFiniteType.isLocallyNoetherian (G.X ⊗ G.X).hom

/-- A homomorphism of rational-point groups that is constant on actual source
components extends to an actual componentwise constant group-scheme morphism. -/
def ofRationalGroupHom
    (r : rationalPoints G →* rationalPoints H)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y) :
    G ⟶ H := by
  let f := ofRationalFunction G.X r
  have hf : IsComponentConstant G.X f := ofRationalFunction_isComponentConstant G.X r
  have hpoint (x : rationalPoints G) : x ≫ f = r x :=
    section_comp_ofRationalFunction G.X r hr x
  refine Grp.homMk'' f ?_ ?_
  · change (1 : rationalPoints G) ≫ f = (1 : rationalPoints H)
    rw [hpoint, map_one]
  · have htensor : f ⊗ₘ f =
        lift (fst G.X G.X ≫ f) (snd G.X G.X ≫ f) := by
      apply hom_ext <;> simp
    refine IsComponentConstant.hom_ext (G.X ⊗ G.X)
      (hf.precomp μ[G.X]) ?_ ?_
    · rw [htensor]
      exact ((hf.precomp (fst G.X G.X)).lift (hf.precomp (snd G.X G.X))).postcomp μ[H.X]
    · intro x
      let a : rationalPoints G := x ≫ fst G.X G.X
      let b : rationalPoints G := x ≫ snd G.X G.X
      have hx : x = lift a b := by
        apply hom_ext <;> simp only [lift_fst, lift_snd] <;> rfl
      calc
        x ≫ μ[G.X] ≫ f = (a * b) ≫ f := by
          rw [hx, CategoryTheory.Hom.mul_def, Category.assoc]
        _ = r (a * b) := hpoint _
        _ = r a * r b := map_mul r a b
        _ = x ≫ (f ⊗ₘ f) ≫ μ[H.X] := by
          rw [← hpoint a, ← hpoint b, CategoryTheory.Hom.mul_def, hx,
            lift_map_assoc]

/-- The algebraized morphism has the prescribed effect on every rational point. -/
theorem comp_ofRationalGroupHom
    (r : rationalPoints G →* rationalPoints H)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y)
    (x : rationalPoints G) :
    x ≫ (ofRationalGroupHom G H r hr).hom.hom = r x := by
  exact section_comp_ofRationalFunction G.X r hr x

/-- The algebraized homomorphism is constant on actual component schemes. -/
theorem ofRationalGroupHom_isComponentConstant
    (r : rationalPoints G →* rationalPoints H)
    (hr : ∀ x y, sectionComponent G.X x = sectionComponent G.X y → r x = r y) :
    IsComponentConstant G.X (ofRationalGroupHom G H r hr).hom.hom :=
  ofRationalFunction_isComponentConstant G.X r

end Langlands.GroupScheme.ComponentConstant
