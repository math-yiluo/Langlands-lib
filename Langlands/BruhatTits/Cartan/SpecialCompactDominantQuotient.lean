import Langlands.BruhatTits.Cartan.DominantQuotient
import Langlands.Geometry.Building.KPBuilding

/-! # Dominant representatives for the chosen geometric compact stabilizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.Cartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) (j : Z ⟶ G) (s : S.toGrp ⟶ Z)
  (h : Function.Bijective (restrictionEvaluation s))

local notation "K₀" => D.compactStabilizer (D.apartmentMap x)
local notation "Zdom" => dominantCentralizer i ν s h
local notation "QK" => DoubleCoset.Quotient (K₀ : Set (rationalPoints G)) K₀

/-- Send an actual dominant point to its double coset for the chosen geometric
`G(F)^1`-stabilizer. The subgroup is fixed by `D` and `x`. -/
def dominantCompactRepresentative : Zdom → QK :=
  fun z => DoubleCoset.mk K₀ K₀ (rationalPoints.map j z.val)

/-- The relation actually induced on the dominant set by the chosen `K₀`
double cosets. No valuation-kernel classification is assumed. -/
def dominantCompactSetoid : Setoid Zdom :=
  Setoid.ker (dominantCompactRepresentative D x ν j s h)

theorem dominantCompactSetoid_iff (z z' : Zdom) :
    dominantCompactSetoid D x ν j s h z z' ↔
      ∃ k ∈ K₀, ∃ k' ∈ K₀,
        rationalPoints.map j z'.val = k * rationalPoints.map j z.val * k' := by
  exact DoubleCoset.eq

/-- The dominant indexing set modulo its actual induced compact-double-coset
relation. This is a set quotient, not a quotient group. -/
def DominantCompactQuotient : Type u :=
  _root_.Quotient (dominantCompactSetoid D x ν j s h)

/-- The induced compact class of a dominant point. -/
def dominantCompactClass (z : Zdom) : DominantCompactQuotient D x ν j s h :=
  _root_.Quotient.mk _ z

@[simp] theorem dominantCompactClass_eq_iff (z z' : Zdom) :
    dominantCompactClass D x ν j s h z = dominantCompactClass D x ν j s h z' ↔
      dominantCompactRepresentative D x ν j s h z =
        dominantCompactRepresentative D x ν j s h z' := by
  exact _root_.Quotient.eq

/-- The canonical map from the induced quotient to the same geometric
`K₀` double cosets; well-definedness follows from the defining relation. -/
def dominantCompactDoubleCosetMap :
    DominantCompactQuotient D x ν j s h → QK :=
  Setoid.kerLift (dominantCompactRepresentative D x ν j s h)

@[simp] theorem dominantCompactDoubleCosetMap_class (z : Zdom) :
    dominantCompactDoubleCosetMap D x ν j s h (dominantCompactClass D x ν j s h z) =
      DoubleCoset.mk K₀ K₀ (rationalPoints.map j z.val) := rfl

/-- Quotienting by the actual induced relation makes the representative map
injective, without a Cartan or valuation-classification hypothesis. -/
theorem dominantCompactDoubleCosetMap_injective :
    Function.Injective (dominantCompactDoubleCosetMap D x ν j s h) :=
  Setoid.kerLift_injective _

/-- Coverage of actual `K₀` double cosets is exactly the missing surjectivity
condition for this canonical injective map. -/
theorem dominantCompactDoubleCosetMap_surjective_iff :
    Function.Surjective (dominantCompactDoubleCosetMap D x ν j s h) ↔
      ∀ g : rationalPoints G, ∃ z : Zdom,
        dominantCompactRepresentative D x ν j s h z = DoubleCoset.mk K₀ K₀ g := by
  constructor
  · intro hsurj g
    obtain ⟨q, hq⟩ := hsurj (DoubleCoset.mk K₀ K₀ g)
    induction q using _root_.Quotient.inductionOn with
    | h z => exact ⟨z, hq⟩
  · intro hcover q
    induction q using _root_.Quotient.inductionOn with
    | h g =>
      obtain ⟨z, hz⟩ := hcover g
      exact ⟨dominantCompactClass D x ν j s h z, hz⟩

/-- A genuine equivalence after explicit coverage is supplied. This constructor
does not assert coverage for arbitrary apartment data. -/
def dominantCompactDoubleCosetEquiv
    (hcover : ∀ g : rationalPoints G, ∃ z : Zdom,
      dominantCompactRepresentative D x ν j s h z = DoubleCoset.mk K₀ K₀ g) :
    DominantCompactQuotient D x ν j s h ≃ QK :=
  Equiv.ofBijective (dominantCompactDoubleCosetMap D x ν j s h)
    ⟨dominantCompactDoubleCosetMap_injective D x ν j s h,
      (dominantCompactDoubleCosetMap_surjective_iff D x ν j s h).mpr hcover⟩

@[simp] theorem dominantCompactDoubleCosetEquiv_class
    (hcover : ∀ g : rationalPoints G, ∃ z : Zdom,
      dominantCompactRepresentative D x ν j s h z = DoubleCoset.mk K₀ K₀ g)
    (z : Zdom) :
    dominantCompactDoubleCosetEquiv D x ν j s h hcover
      (dominantCompactClass D x ν j s h z) =
        DoubleCoset.mk K₀ K₀ (rationalPoints.map j z.val) := rfl

end Langlands.BruhatTits.Cartan
