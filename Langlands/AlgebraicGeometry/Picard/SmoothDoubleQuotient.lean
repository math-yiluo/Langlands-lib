import Langlands.AlgebraicGeometry.Picard.ArrowClassQuotientComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothProjectionAtlas
import Langlands.AlgebraicGeometry.Picard.SmoothAutomorphismEtaleAtlasStatement

/-! # Conditional double quotient for a smooth Picard presentation -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardGroupoid

open AlgebraicSpace.SmoothRelationQuotient

variable
  (hQuot : AlgebraicSpace.SmoothRelationQuotientStatement.{u})
  (hDescent : ∀ (P W V : Scheme.{u}) (p : P ⟶ W) (g : W ⟶ V),
    Smooth p → Surjective p → Smooth (p ≫ g) → Smooth g)
  {S X : Scheme.{u}} (f : X ⟶ S) {U : Over S}
  (L : LineBundle ((relativeSpace f).obj U))
  (hL : IsSmoothSurjectivePresentation f L)
  (hU : LocallyOfFiniteType U.hom)
  (hAut : HasSmoothRelativeAutomorphismSchemes f)
  (hLocal : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
    (etaleFamilyMap f L))

include hQuot hDescent hL hU hAut hLocal

/-- Two applications of the generic quotient theorem give the geometric
properties of the actual ordinary class sheaf, retaining all three
outstanding inputs as hypotheses. -/
lemma smoothDoubleQuotient_picardProperties :
    Presheaf.IsSheaf (AlgebraicSpace.fppfTopology S)
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    AlgebraicSpace.HasRepresentableDiagonal
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    ∃ (V : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj V ⟶
        RelativePicard.etaleClassSheafPresheaf f),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType V.hom := by
  obtain ⟨A, R, a, b, r, s, eA, _eR, ha, hb, hsa, _hsurja, hsb, _hsurjb,
    _hr, _hs, _hsr, _hss, hPB, hA, hEquiv, hSmooth⟩ :=
    exists_smoothArrowRelation f L hL hU hAut
  obtain ⟨hF, hD, _hPBq, hq, hqSurj, W, c, hc, hcSurj, _hW⟩ :=
    hQuot S A ((AlgebraicSpace.schemeToSpace S).obj R)
      ((AlgebraicSpace.schemeYoneda S).map r)
      ((AlgebraicSpace.schemeYoneda S).map s) hEquiv hSmooth hA
  have hAtlas : ∃ (W : Over S)
      (c : (AlgebraicSpace.schemeYoneda S).obj W ⟶
        (arrowKernelQuotientSheaf f L r s eA hPB).obj),
      AlgebraicSpace.IsEtale c ∧ AlgebraicSpace.IsSurjective c :=
    ⟨W, c, hc, hcSurj⟩
  let B := arrowKernelQuotientSpace f L r s eA hPB hF hD hAtlas
  have hqa : arrowKernelQuotientMap f L r s eA hPB ≫
      arrowKernelQuotientFst f L r s eA hPB =
        (AlgebraicSpace.schemeYoneda S).map a :=
    (arrowKernelQuotientMap_fst f L r s eA hPB).trans ha
  have hqb : arrowKernelQuotientMap f L r s eA hPB ≫
      arrowKernelQuotientSnd f L r s eA hPB =
        (AlgebraicSpace.schemeYoneda S).map b :=
    (arrowKernelQuotientMap_snd f L r s eA hPB).trans hb
  have hSmoothB : HasSmoothProjections B
      (arrowKernelQuotientFst f L r s eA hPB)
      (arrowKernelQuotientSnd f L r s eA hPB) :=
    (smoothProjectionAtlasOfSmoothCover hDescent B
      (arrowKernelQuotientFst f L r s eA hPB)
      (arrowKernelQuotientSnd f L r s eA hPB)
      (arrowKernelQuotientMap f L r s eA hPB) hq hqSurj
      a b hqa hqb hsa hsb).hasSmoothProjections
  obtain ⟨hF₂, hD₂, _hPB₂, _hq₂, _hqSurj₂, hAtlas₂⟩ :=
    hQuot S U B (arrowKernelQuotientFst f L r s eA hPB)
      (arrowKernelQuotientSnd f L r s eA hPB)
      (arrowKernelQuotientSpace_isEquivalenceRelation f L r s eA hPB hF hD hAtlas)
      hSmoothB hU
  let e := arrowClassQuotientPicardIso f L r s eA hPB hF hD hAtlas hLocal
  exact ⟨(Presheaf.isSheaf_of_iso_iff e).mp hF₂,
    arrowClassQuotient_picardAtlas f L r s eA hPB hF hD hAtlas hLocal hD₂ hAtlas₂⟩

/-- The actual ordinary etale Picard class sheaf as an algebraic space,
conditional on the generic quotient theorem, smooth-source descent and
local surjectivity of the original family map. -/
def smoothDoubleQuotientPicardSpace : AlgebraicSpace S :=
  let h := smoothDoubleQuotient_picardProperties hQuot hDescent f L hL hU hAut hLocal
  ⟨⟨RelativePicard.etaleClassSheafPresheaf f, h.1⟩, h.2.1, by
    obtain ⟨V, a, ha, hs, _hV⟩ := h.2.2
    exact ⟨V, a, ha, hs⟩⟩

/-- The conditional construction uses the original ordinary presheaf. -/
lemma smoothDoubleQuotientPicardSpace_presheaf :
    (smoothDoubleQuotientPicardSpace hQuot hDescent f L hL hU hAut hLocal).presheaf =
      RelativePicard.etaleClassSheafPresheaf f := rfl

/-- The ordinary class sheaf has the required locally finite type etale
atlas under the explicit inputs of the double-quotient construction. -/
lemma smoothDoubleQuotient_picardAtlas :
    AlgebraicSpace.HasRepresentableDiagonal
      (RelativePicard.etaleClassSheafPresheaf f) ∧
    ∃ (V : Over S)
      (a : (AlgebraicSpace.schemeYoneda S).obj V ⟶
        RelativePicard.etaleClassSheafPresheaf f),
      AlgebraicSpace.IsEtale a ∧ AlgebraicSpace.IsSurjective a ∧
        LocallyOfFiniteType V.hom :=
  (smoothDoubleQuotient_picardProperties hQuot hDescent f L hL hU hAut hLocal).2

end Langlands.AlgebraicGeometry.Picard.PicardGroupoid
