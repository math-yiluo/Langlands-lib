import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Field points of flat schemes over a local ring -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A point of `X` lying over `Spec l → Spec R`, defined over some field
extension `L` of `l`. -/
structure FieldPointLift {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (l : Type u) [Field l] [Algebra R l] where
  /-- The extension field. -/
  L : Type u
  /-- The field structure of the extension. -/
  [field : Field L]
  /-- The `l`-algebra structure of the extension. -/
  [algebra : Algebra l L]
  /-- The `L`-valued point of `X`. -/
  point : Spec (CommRingCat.of L) ⟶ X
  /-- The point lies over `Spec L → Spec l → Spec R`. -/
  comm : point ≫ f = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R l))

attribute [instance] FieldPointLift.field FieldPointLift.algebra

namespace FieldPointLift

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of R)} {l : Type u} [Field l] [Algebra R l]

/-- The field point lift given by the residue field of a point of the
fibre product `X ×_R Spec l`. -/
def ofPullbackPoint
    (w : ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R l))))) :
    FieldPointLift f l where
  L := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R l)))).residueField w
  algebra := (Spec.preimage
    ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap R l)))).fromSpecResidueField w ≫
      pullback.snd f _)).hom.toAlgebra
  point := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R l)))).fromSpecResidueField w ≫
    pullback.fst f _
  comm := by
    rw [Category.assoc, pullback.condition, RingHom.algebraMap_toAlgebra,
      CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc]

end FieldPointLift

/-- Over a local ring, a flat scheme with a point in the closed fibre has a
point in the fibre product with every field-valued point of the base. -/
theorem nonempty_pullback_of_flat_of_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (x : X) (hx : f x = IsLocalRing.closedPoint R)
    (l : Type u) [Field l] [Algebra R l] :
    Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R l)))) := by
  obtain ⟨t⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of l)))
  have hs : Spec.map (CommRingCat.ofHom (algebraMap R l)) t ⤳ f x :=
    hx ▸ IsLocalRing.specializes_closedPoint _
  obtain ⟨z, -, hz⟩ := Flat.generalizingMap f hs
  obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback z t hz
  exact ⟨w⟩

/-- A field point lift of a flat scheme over a local ring with a point in
the closed fibre, chosen from the residue field of a point of `X ×_R Spec l`. -/
def fieldPointLift
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (x : X) (hx : f x = IsLocalRing.closedPoint R)
    (l : Type u) [Field l] [Algebra R l] :
    FieldPointLift f l :=
  FieldPointLift.ofPullbackPoint (nonempty_pullback_of_flat_of_closedPoint f x hx l).some

/-- Over a local ring `R`, a flat scheme `X` with a point in the closed fibre
has, for every field `l` over `R`, a point defined over some field extension
`L` of `l` and lying over `Spec l → Spec R`. -/
theorem exists_extension_point_of_flat_of_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (x : X) (hx : f x = IsLocalRing.closedPoint R)
    (l : Type u) [Field l] [Algebra R l] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra l L) (g : Spec (CommRingCat.of L) ⟶ X),
      g ≫ f = Spec.map (CommRingCat.ofHom (algebraMap l L)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R l)) :=
  let P := fieldPointLift f x hx l
  ⟨P.L, P.field, P.algebra, P.point, P.comm⟩

end Langlands.AlgebraicGeometry
