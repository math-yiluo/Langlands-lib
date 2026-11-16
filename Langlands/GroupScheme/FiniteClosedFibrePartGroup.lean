import Langlands.AbelianScheme.GroupScheme
import Langlands.AlgebraicGeometry.FiniteClosedFibrePart
import Langlands.CategoryTheory.GroupObjectDescent

/-! # Group structure on a supplied finite closed-fibre part -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FiniteClosedFibrePart

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {K : GroupScheme (Spec (CommRingCat.of R))} {U : K.X.left.Opens}
  (hU : Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart K.X.hom U)

/-- The supplied open subscheme with its original structure morphism. -/
def partOver (_hU : Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart K.X.hom U) :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (U.ι ≫ K.X.hom)

/-- The actual open inclusion over the local base. -/
abbrev inclusionOver : partOver hU ⟶ K.X := Over.homMk U.ι

instance : IsOpenImmersion (inclusionOver hU).left :=
  inferInstanceAs (IsOpenImmersion U.ι)

instance : IsClosedImmersion (inclusionOver hU).left :=
  IsClosedImmersion.of_isPreimmersion _ (by
    change IsClosed (Set.range U.ι)
    rw [Scheme.Opens.range_ι]
    exact hU.isClosed)

instance : Mono (inclusionOver hU) := Over.mono_of_mono_left _

instance : IsFinite (partOver hU).hom := hU.isFinite

instance [Flat K.X.hom] : Flat (partOver hU).hom :=
  inferInstanceAs (Flat (U.ι ≫ K.X.hom))

instance [LocallyOfFinitePresentation K.X.hom] :
    LocallyOfFinitePresentation (partOver hU).hom :=
  inferInstanceAs (LocallyOfFinitePresentation (U.ι ≫ K.X.hom))

/-- A universally closed scheme over the base maps canonically into the part. -/
def liftOver {Y : Over (Spec (CommRingCat.of R))} [UniversallyClosed Y.hom]
    (g : Y ⟶ K.X) : Y ⟶ partOver hU :=
  Over.homMk (hU.lift Y.hom g.left (Over.w g))
    (hU.lift_over Y.hom g.left (Over.w g))

@[reassoc (attr := simp)]
theorem liftOver_fac {Y : Over (Spec (CommRingCat.of R))} [UniversallyClosed Y.hom]
    (g : Y ⟶ K.X) : liftOver hU g ≫ inclusionOver hU = g :=
  Over.OverMorphism.ext (hU.lift_fac Y.hom g.left (Over.w g))

instance : IsFinite (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
  inferInstanceAs (IsFinite (𝟙 (Spec (CommRingCat.of R))))

/-- The restricted unit. -/
def one : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ partOver hU :=
  liftOver hU η[K.X]

@[reassoc (attr := simp)]
theorem one_fac : one hU ≫ inclusionOver hU = η[K.X] := liftOver_fac hU _

instance : IsFinite (partOver hU ⊗ partOver hU).hom :=
  inferInstanceAs (IsFinite
    (pullback.fst (partOver hU).hom (partOver hU).hom ≫ (partOver hU).hom))

/-- The restricted multiplication. -/
def mul : partOver hU ⊗ partOver hU ⟶ partOver hU :=
  liftOver hU ((inclusionOver hU ⊗ₘ inclusionOver hU) ≫ μ[K.X])

@[reassoc (attr := simp)]
theorem mul_fac : mul hU ≫ inclusionOver hU =
    (inclusionOver hU ⊗ₘ inclusionOver hU) ≫ μ[K.X] := liftOver_fac hU _

/-- The restricted inverse. -/
def inv : partOver hU ⟶ partOver hU :=
  liftOver hU (inclusionOver hU ≫ ι[K.X])

@[reassoc (attr := simp)]
theorem inv_fac : inv hU ≫ inclusionOver hU = inclusionOver hU ≫ ι[K.X] :=
  liftOver_fac hU _

instance grpObj : GrpObj (partOver hU) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (inclusionOver hU) (one hU) (mul hU) (inv hU)
      (one_fac hU) (mul_fac hU) (inv_fac hU)

instance : IsMonHom (inclusionOver hU) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (inclusionOver hU) (one hU) (mul hU) (inv hU)
      (one_fac hU) (mul_fac hU) (inv_fac hU)

/-- The actual finite group scheme on the supplied open subscheme. -/
abbrev group : GroupScheme (Spec (CommRingCat.of R)) := { X := partOver hU }

/-- The open and closed subgroup inclusion. -/
def inclusion : group hU ⟶ K := Grp.homMk (inclusionOver hU)

@[simp]
theorem inclusion_hom_hom : (inclusion hU).hom.hom = inclusionOver hU := rfl

instance : IsOpenImmersion (inclusion hU).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (inclusionOver hU).left)

instance : IsClosedImmersion (inclusion hU).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (inclusionOver hU).left)

instance : Mono (inclusion hU) where
  right_cancellation _ _ h := Grp.hom_ext _ _
    ((cancel_mono (inclusionOver hU)).mp (congrArg (fun f => f.hom.hom) h))

instance : IsFinite (group hU).X.hom := inferInstanceAs (IsFinite (partOver hU).hom)

instance [Flat K.X.hom] : Flat (group hU).X.hom :=
  inferInstanceAs (Flat (partOver hU).hom)

instance [LocallyOfFinitePresentation K.X.hom] :
    LocallyOfFinitePresentation (group hU).X.hom :=
  inferInstanceAs (LocallyOfFinitePresentation (partOver hU).hom)

/-- The inclusion has exactly the supplied open as its topological range. -/
theorem range_inclusion : Set.range (inclusion hU).hom.hom.left = U :=
  Scheme.Opens.range_ι U

/-- Every point of the group's closed fibre lies in the finite subgroup. -/
theorem contains_closedFibre (x : K.X.left)
    (hx : K.X.hom x = IsLocalRing.closedPoint R) :
    x ∈ Set.range (inclusion hU).hom.hom.left := by
  rw [range_inclusion]
  exact hU.contains_closedFibre x hx

end Langlands.GroupScheme.FiniteClosedFibrePart
