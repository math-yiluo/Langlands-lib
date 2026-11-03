import Langlands.Geometry.Building.SpecialCompact
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.StandardLeviPointComparison
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-!
# The same torus and compact intersection in the actual standard Levi

These are definition adapters. No inherited root valuation, apartment comparison
or compactness assertion is supplied.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.GroupScheme.Standard

variable {F : Type u} [Field F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
  (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- The same ambient torus, factored through the actual standard Levi
representative using its all-test subgroup equality. -/
def leviTorusHom : S.toGrp ⟶ leviScheme i ν J :=
  (isRepresentedBy_leviHom i ν J).factorHom i
    ((range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν J))

@[simp]
theorem leviTorusHom_comp :
    leviTorusHom i ν J ≫ leviHom i ν J = i :=
  (isRepresentedBy_leviHom i ν J).factorHom_comp i _

/-- An ambient maximal split torus remains maximal split in this actual
standard Levi representative. -/
theorem isMaximalSplitTorus_leviTorusHom (hi : IsMaximalSplitTorus i) :
    IsMaximalSplitTorus (leviTorusHom i ν J) :=
  hi.isMaximalSplitTorus_factorHom (isRepresentedBy_leviHom i ν J)
    (isClosedSubgroup_leviHom i ν J) _

/-- The existing rational-point comparison, specialized to the actual
standard Levi representative. Its forward map is the actual inclusion. -/
def leviPointsEquiv : rationalPoints (leviScheme i ν J) ≃* standardLeviPoints i ν J :=
  standardLeviRationalPointsEquiv i ν J (leviHom i ν J)
    (isRepresentedBy_leviHom i ν J)

@[simp]
theorem leviPointsEquiv_val (m : rationalPoints (leviScheme i ν J)) :
    (leviPointsEquiv i ν J m : rationalPoints G) =
      rationalPoints.map (leviHom i ν J) m :=
  rfl

end Langlands.GroupScheme.Standard

namespace Langlands.Geometry.Building.KPApartmentData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F))
  (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- The preimage of the same chosen `K₀` in the rational points of the actual
standard Levi scheme. Its ambient image is exactly `K₀ ∩ M_J(F)`. -/
def specialCompactLeviSubgroup (x : D.Apartment) :
    Subgroup (rationalPoints (Standard.leviScheme i ν J)) :=
  (D.specialCompactSubgroup x).comap (rationalPoints.map (Standard.leviHom i ν J))

theorem mem_specialCompactLeviSubgroup {x : D.Apartment}
    {m : rationalPoints (Standard.leviScheme i ν J)} :
    m ∈ D.specialCompactLeviSubgroup ν J x ↔
      rationalPoints.map (Standard.leviHom i ν J) m ∈ D.specialCompactSubgroup x :=
  Iff.rfl

/-- The subgroup in the actual Levi scheme maps to the literal intersection
inside the original rational-point group. -/
theorem specialCompactLeviSubgroup_map (x : D.Apartment) :
    (D.specialCompactLeviSubgroup ν J x).map
        (rationalPoints.map (Standard.leviHom i ν J)) =
      D.specialCompactSubgroup x ⊓ standardLeviPoints i ν J := by
  ext g
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨hm, (Standard.leviPointsEquiv i ν J m).property⟩
  · intro hg
    obtain ⟨m, hm⟩ := (Standard.leviPointsEquiv i ν J).surjective ⟨g, hg.2⟩
    have hmg : rationalPoints.map (Standard.leviHom i ν J) m = g :=
      congrArg Subtype.val hm
    exact ⟨m, show rationalPoints.map (Standard.leviHom i ν J) m ∈
      D.specialCompactSubgroup x from hmg.symm ▸ hg.1, hmg⟩

end Langlands.Geometry.Building.KPApartmentData
