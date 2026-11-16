import Langlands.AlgebraicGeometry.HenselianFinitePartStatement
import Langlands.AlgebraicGeometry.ProperLocalClosedFibreCover
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Maps into a supplied finite closed-fibre part -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {U : X.Opens} (hU : IsFiniteClosedFibrePart f U)

include hU

/-- Every map over the base from a universally closed scheme lands in the part. -/
theorem range_subset {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed p] (g : Y ⟶ X) (hfac : g ≫ f = p) :
    Set.range g ⊆ U := by
  have heq : g ⁻¹ᵁ U = ⊤ := open_eq_top_of_contains_closedFibre p (g ⁻¹ᵁ U) (by
    intro y hy
    apply hU.contains_closedFibre (g y)
    change (g ≫ f) y = _
    rw [hfac]
    exact hy)
  rintro _ ⟨y, rfl⟩
  change y ∈ g ⁻¹ᵁ U
  rw [heq]
  trivial

/-- The actual factorization through the open subscheme. -/
def lift {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed p] (g : Y ⟶ X) (hfac : g ≫ f = p) : Y ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι g (by
    simpa only [Scheme.Opens.range_ι] using hU.range_subset p g hfac)

@[reassoc (attr := simp)]
theorem lift_fac {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed p] (g : Y ⟶ X) (hfac : g ≫ f = p) :
    hU.lift p g hfac ≫ U.ι = g :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
theorem lift_over {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed p] (g : Y ⟶ X) (hfac : g ≫ f = p) :
    hU.lift p g hfac ≫ (U.ι ≫ f) = p := by
  rw [← Category.assoc, lift_fac, hfac]

/-- The factorization is unique as an actual scheme morphism. -/
theorem lift_unique {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of R))
    [UniversallyClosed p] (g : Y ⟶ X) (hfac : g ≫ f = p)
    (a : Y ⟶ U.toScheme) (ha : a ≫ U.ι = g) : a = hU.lift p g hfac := by
  apply (cancel_mono U.ι).mp
  rw [ha, lift_fac]

/-- Any two finite closed-fibre parts have the same underlying open. -/
theorem eq {V : X.Opens} (hV : IsFiniteClosedFibrePart f V) : U = V := by
  have hle {A B : X.Opens} (hA : IsFiniteClosedFibrePart f A)
      (hB : IsFiniteClosedFibrePart f B) : A ≤ B := by
    have : IsFinite (A.ι ≫ f) := hA.isFinite
    change (A : Set X) ⊆ B
    simpa only [Scheme.Opens.range_ι] using
      hB.range_subset (A.ι ≫ f) A.ι rfl
  exact le_antisymm (hle hU hV) (hle hV hU)

end Langlands.AlgebraicGeometry.IsFiniteClosedFibrePart
