import Langlands.Geometry.Building.RootFreeApartmentConstruction
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityStatement
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-! # Constructing the actual valuation-building data of a field torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.Geometry.Building

namespace CentralizerDatum

variable {k : Type u} [Field k]
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- For an actual torus, the whole group represents the centralizer of every
maximal split subtorus, and the proved torus character comparison supplies the datum. -/
def ofTorus (hT : IsTorus T.toGrp) (i : S.toGrp ⟶ T.toGrp)
    (hi : IsMaximalSplitTorus i) : CentralizerDatum i := by
  have hred := hT.isConnectedReductive_of_fieldSplitting
  have : IsAffineHom T.toGrp.X.hom := hred.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : Smooth T.toGrp.X.hom := hred.smooth
  have hc : IsCentral i := isCentral_to_commGroupScheme i
  have hcomponent : IsSplitComponent i :=
    ⟨⟨hi.1, hc⟩, fun A a ha f hf => hi.2 A a ha.1 f hf⟩
  have := hcomponent.finiteIndex_range_characterRestrict hred
  refine {
    Z := T.toGrp
    j := 𝟙 T.toGrp
    s := i
    isClosedSubgroup := ?_
    isRepresentedBy := ?_
    comp_eq := Category.comp_id i
    bijective := Cartan.restrictionEvaluation_bijective hi.1.1 i
      (hi.characterRestrict_injective_of_isTorus hT) }
  · change IsClosedImmersion (𝟙 T.X.left)
    infer_instance
  · rw [(isCentral_iff_torusCentralizer_eq_top i).mp hc]
    exact ⟨inferInstance, SubgroupFunctor.range_id _⟩

end CentralizerDatum

namespace ValuationBuildingData

section Field

variable {k : Type u} [Field k]
  {T S : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom T.toGrp.X.hom] [LocallyOfFiniteType T.toGrp.X.hom]

/-- A split subtorus of a commutative ambient group has no actual relative roots. -/
theorem relativeRoots_eq_empty_of_commutative (i : S.toGrp ⟶ T.toGrp)
    (hi : IsSplitSubtorus i) : relativeRoots i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro χ hχ
  have hc : IsCentral (CommGroupScheme.groupHom (𝟙 S) ≫ i) := by
    change IsCentral (𝟙 S.toGrp ≫ i)
    rw [Category.id_comp]
    exact isCentral_to_commGroupScheme i
  have hz := root_restrict_eq_zero_of_isCentral i (𝟙 S) hi.1 hc hχ
  exact (mem_relativeRoots.mp hχ).1 (by simpa using hz)

end Field

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (T : CommGroupScheme (Spec (CommRingCat.of F)))

/-- Choose the actual maximal split subtorus and centralizer of a torus, then construct
its actual `localFieldOrder`-normalized valuation-building data. -/
def ofTorus (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    ValuationBuildingData T.toGrp := by
  have hred := hT.isConnectedReductive_of_fieldSplitting
  have : IsAffineHom T.toGrp.X.hom := hred.isAffineHom
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : Smooth T.toGrp.X.hom := hred.smooth
  let hsplit := exists_largestSplitSubtorus T
  let S := hsplit.choose
  let i : S.toGrp ⟶ T.toGrp := hsplit.choose_spec.choose
  have hi : IsMaximalSplitTorus i := hsplit.choose_spec.choose_spec.isMaximalSplitTorus
  exact ofRelativeRootsEqEmpty hred i hi
    (relativeRoots_eq_empty_of_commutative i hi.1) (CentralizerDatum.ofTorus hT i hi)

/-- The constructed actual torus data satisfy the full existing apartment predicate. -/
theorem ofTorus_satisfiesApartmentAxioms (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    (ofTorus T hT).SatisfiesApartmentAxioms := by
  have hred := hT.isConnectedReductive_of_fieldSplitting
  have : IsAffineHom T.toGrp.X.hom := hred.isAffineHom
  have : Smooth T.toGrp.X.hom := hred.smooth
  let B := ofTorus T hT
  exact B.apartment.satisfiesApartmentAxioms_of_relativeRoots_eq_empty B.centralizer
    (relativeRoots_eq_empty_of_commutative B.i B.isMaximalSplitTorus.1)

end Local

end ValuationBuildingData

end Langlands.Geometry.Building
