import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.BruhatTits.Cartan.CentralizerRealComparison
import Langlands.Geometry.Building.KPCentralizerCompatibility

/-! # Actual centralizer data over an arbitrary field from two structural statements

For a maximal split torus `i : S → G` of a connected reductive group over an arbitrary field,
the canonical factor `s : S → Z` through a closed representative `j : Z → G` of the whole-torus
centralizer is a split component of `Z`. Given connected reductivity of dynamic centralizers and
detection of rational characters on central split tori, restriction of rational characters along
`s` is injective with finite-index range, so `Cartan.restrictionEvaluation s` is bijective. This
gives a `CentralizerDatum i` with no local-field hypothesis.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.BruhatTits

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G M : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A central maximal split torus is a split component. -/
theorem IsMaximalSplitTorus.isSplitComponent {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (hc : IsCentral i) : IsSplitComponent i :=
  ⟨⟨hi.1, hc⟩, fun A' i' hi' f hf => hi.2 A' i' hi'.1 f hf⟩

/-- The canonical factor of a maximal split torus through a closed representative of its
whole-torus centralizer is a split component of that representative. -/
theorem IsMaximalSplitTorus.isSplitComponent_torusCentralizerFactor {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {j : M ⟶ G} (hj : (torusCentralizer i).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j) : IsSplitComponent (torusCentralizerFactor i hj) :=
  (hi.isMaximalSplitTorus_torusCentralizerFactor hj hjc).isSplitComponent
    (isCentral_torusCentralizerFactor i hj)

/-- Given the two structural statements, restriction of rational characters from a closed
representative of the centralizer of a maximal split torus to the torus is injective. -/
theorem IsMaximalSplitTorus.characterRestrict_torusCentralizerFactor_injective
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {j : M ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    Function.Injective (characterRestrict (torusCentralizerFactor i hj)) :=
  characterRestrict_injective_of_centralSplitTorusCharacter hCST
    (hi.1.1.isConnectedReductive_centralizer_of_dynamic hDCR hG i j hj hjc)
    (hi.isSplitComponent_torusCentralizerFactor hj hjc)

/-- Given connected reductivity of dynamic centralizers, the same restriction has finite-index
range. -/
theorem IsMaximalSplitTorus.finiteIndex_range_characterRestrict_torusCentralizerFactor
    (hDCR : DynamicCentralizerReductiveStatement.{u}) (hG : IsConnectedReductive G)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {j : M ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    (characterRestrict (torusCentralizerFactor i hj)).range.FiniteIndex :=
  (hi.isSplitComponent_torusCentralizerFactor hj hjc).finiteIndex_range_characterRestrict
    (hi.1.1.isConnectedReductive_centralizer_of_dynamic hDCR hG i j hj hjc)

/-- Given the two structural statements, restriction followed by real evaluation along the
canonical centralizer factor of a maximal split torus is bijective. -/
theorem IsMaximalSplitTorus.restrictionEvaluation_torusCentralizerFactor_bijective
    (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) {j : M ⟶ G}
    (hj : (torusCentralizer i).IsRepresentedBy j) (hjc : IsClosedSubgroup j) :
    Function.Bijective (Cartan.restrictionEvaluation (torusCentralizerFactor i hj)) :=
  have := hi.finiteIndex_range_characterRestrict_torusCentralizerFactor hDCR hG hj hjc
  Cartan.restrictionEvaluation_bijective hi.1.1 _
    (hi.characterRestrict_torusCentralizerFactor_injective hDCR hCST hG hj hjc)

end Langlands.GroupScheme

namespace Langlands.Geometry.Building.CentralizerDatum

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual centralizer datum of a maximal split torus of a connected reductive group over an
arbitrary field: the closed all-test centralizer, the canonical factorization of the torus
through it, and bijectivity of restriction evaluation from the two structural statements. -/
def ofStructure (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) : CentralizerDatum i :=
  Classical.choice <| by
    obtain ⟨Z, j, hj, hjc⟩ :=
      fieldCentralizerRepresentability k S G hi.1.1.isAffineHom i
    exact ⟨{
      Z := Z
      j := j
      s := torusCentralizerFactor i hj
      isClosedSubgroup := hjc
      isRepresentedBy := hj
      comp_eq := torusCentralizerFactor_comp i hj
      bijective := hi.restrictionEvaluation_torusCentralizerFactor_bijective hDCR hCST hG hj hjc
    }⟩

/-- Every maximal split torus of a connected reductive group over an arbitrary field has an
actual centralizer datum, given the two structural statements. -/
theorem nonempty_of_structure (hDCR : DynamicCentralizerReductiveStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    (i : S.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) : Nonempty (CentralizerDatum i) :=
  ⟨ofStructure hDCR hCST hG i hi⟩

end Langlands.Geometry.Building.CentralizerDatum
