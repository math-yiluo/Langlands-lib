import Langlands.Representation.Jacquet.StandardNormalLevelFixedVectors
import Langlands.Representation.Category.FixedVectorConstituent
import Langlands.Representation.Jacquet.IrreducibleFixedVectorGeneration

/-! # Fixed-vector criteria for one standard cuspidal presentation -/

noncomputable section

universe uF uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact
open Langlands.Jacquet

namespace Langlands.CuspidalSupport

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardRepresentativeHelperAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardRepresentativeHelperTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Nonzero fixed vectors in one actual Bernstein induction are equivalent to
their occurrence in an irreducible constituent with this precise cuspidal support. -/
theorem nontrivial_bernsteinInduction_fixedVectors_iff_exists_cuspidalSupport
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G))) :
    Nontrivial (fixedVectors (bernsteinInduction i ν family a).representation K.toSubgroup) ↔
      ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        IsBernsteinCuspidalSupport i ν family a π ∧
          Nontrivial (fixedVectors π.representation K.toSubgroup) := by
  constructor
  · intro h
    obtain ⟨π, hπ, hsub, hfix⟩ :=
      SmoothRep.hasFixedVectorConstituent_of_nontrivial
        (bernsteinInduction i ν family a) K.toSubgroup h
    exact ⟨π, ⟨hπ, hsub⟩, hfix⟩
  · rintro ⟨π, hπ, hfix⟩
    exact SmoothRep.nontrivial_fixedVectors_of_isSubquotient K hK hπ.2 hfix

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- A chosen irreducible constituent retaining a nonzero fixed vector from the
actual Bernstein induction of the specified datum. -/
def bernsteinFixedVectorConstituent
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hfix : Nontrivial
      (fixedVectors (bernsteinInduction i ν family a).representation K.toSubgroup)) :
    SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G) :=
  Classical.choose
    ((nontrivial_bernsteinInduction_fixedVectors_iff_exists_cuspidalSupport
      i ν family a K hK).mp hfix)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The chosen constituent has the prescribed cuspidal support and a nonzero
fixed space at the original compact open level. -/
theorem bernsteinFixedVectorConstituent_spec
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (hfix : Nontrivial
      (fixedVectors (bernsteinInduction i ν family a).representation K.toSubgroup)) :
    IsBernsteinCuspidalSupport i ν family
        a (bernsteinFixedVectorConstituent i ν family a K hK hfix) ∧
      Nontrivial (fixedVectors
        (bernsteinFixedVectorConstituent i ν family a K hK hfix).representation
        K.toSubgroup) :=
  Classical.choose_spec
    ((nontrivial_bernsteinInduction_fixedVectors_iff_exists_cuspidalSupport
      i ν family a K hK).mp hfix)

omit [LocallyOfFiniteType G.X.hom] in
/-- At a normal level with the standard Iwasawa and Iwahori decompositions,
an irreducible fixed-vector constituent of this precise induction exists exactly
when the inducing representation has a nonzero literal Levi fixed vector. -/
theorem exists_bernsteinCuspidalSupport_fixedVectors_iff
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (levi i ν a.roots)
      (unipotent i ν a.roots)
      (standardOppositeUnipotentPoints i ν (rootSet i ν a.roots))) :
    (∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
        IsBernsteinCuspidalSupport i ν family a π ∧
          Nontrivial (fixedVectors π.representation K.toSubgroup)) ↔
      Nontrivial (fixedVectors
        (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
        (K.toSubgroup.comap (levi i ν a.roots).subtype)) :=
  (nontrivial_bernsteinInduction_fixedVectors_iff_exists_cuspidalSupport
    i ν family a K hK).symm.trans
      (nontrivial_standardInduction_fixedVectors_iff i ν family a.roots K hK
        K₀ hnormal hIwasawa hIwahori
        (bernsteinLiteralLeviRep i ν a.roots a.representation))

/-- The reverse implication of the standard representative criterion is
unconditional and holds for every standard Bernstein family. -/
theorem exists_bernsteinInertialSupport_fixedVectors_of_literalLevi
    (a : BernsteinCuspidalDatum.{uF, uV} i ν family)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (hIwasawa : ∀ g : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, g = m * n * k)
    (hIwahori : HasIwahoriIntersectionDecomposition K.toSubgroup (levi i ν a.roots)
      (unipotent i ν a.roots)
      (standardOppositeUnipotentPoints i ν (rootSet i ν a.roots)))
    (hfix : Nontrivial (fixedVectors
      (bernsteinLiteralLeviRep i ν a.roots a.representation).representation
      (K.toSubgroup.comap (levi i ν a.roots).subtype))) :
    ∃ π : SmoothRep.{0, uF, max uF uV} ℂ (rationalPoints G),
      IsBernsteinInertialSupport i ν family (bernsteinInertialClass i ν family a) π ∧
        Nontrivial (fixedVectors π.representation K.toSubgroup) := by
  obtain ⟨π, hπ, hπfix⟩ :=
    (exists_bernsteinCuspidalSupport_fixedVectors_iff i ν family a K hK
      K₀ hnormal hIwasawa hIwahori).mpr hfix
  exact ⟨π, hπ.inertial, hπfix⟩

end Langlands.CuspidalSupport
