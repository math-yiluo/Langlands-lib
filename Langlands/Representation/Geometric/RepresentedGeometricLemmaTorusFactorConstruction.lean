import Langlands.Representation.Geometric.RepresentedGeometricLemmaCommonCocharacterConstruction
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization

/-! # Actual geometric-lemma data from original common-torus factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Construction

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Choose simultaneous cocharacters in the supplied maximal split torus, then
construct the actual intersection datum. The only universal structural input
is the explicit parabolic-dynamic statement. -/
def geometricLemmaIntersectionDatumOfTorusFactors
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (z : rationalPoints G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ta : T.toGrp ⟶ M) (hta : ta ≫ l ≫ p = i)
    (tb : T.toGrp ⟶ L) (htb : tb ≫ lQ ≫ q ≫ (G.innerIso z).hom = i) :
    letI := hG.isAffineHom
    GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z := by
  have := hG.isAffineHom
  have hzz' : (G.innerIso z).hom ≫ (G.innerIso z⁻¹).hom = 𝟙 G := by
    rw [innerIso_inv_hom, Iso.hom_inv_id]
  have hta' : ta ≫ l ≫ p ≫ (G.innerIso z⁻¹).hom = i ≫ (G.innerIso z⁻¹).hom := by
    simpa only [Category.assoc] using
      congrArg (fun f : T.toGrp ⟶ G => f ≫ (G.innerIso z⁻¹).hom) hta
  have htb' : tb ≫ lQ ≫ q = i ≫ (G.innerIso z⁻¹).hom := by
    have h := congrArg (fun f : T.toGrp ⟶ G => f ≫ (G.innerIso z⁻¹).hom) htb
    simpa only [Category.assoc, hzz', Category.comp_id] using h
  have hi' : IsMaximalSplitTorus (i ≫ (G.innerIso z⁻¹).hom) :=
    hi.comp_iso _
  have hiQ : IsMaximalSplitTorus (tb ≫ lQ ≫ q) := by
    rw [htb']
    exact hi'
  have hiP : IsMaximalSplitTorus (ta ≫ l ≫ (p ≫ (G.innerIso z⁻¹).hom)) := by
    rw [hta']
    exact hi'
  have htarget := exists_cocharacter_parabolic_triple_in_torus
    hG hq hlQ hrQ hPD tb hiQ
  have hsource := exists_cocharacter_parabolic_triple_in_torus
    hG (hp.comp_iso (G.innerIso z⁻¹)) hl hr hPD ta hiP
  let α := Classical.choose htarget
  let β := Classical.choose hsource
  obtain ⟨hQ, hL, hU⟩ := Classical.choose_spec htarget
  obtain ⟨hP, hM, hN⟩ := Classical.choose_spec hsource
  apply geometricLemmaIntersectionDatumOfCommonCocharacters p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ z (i ≫ (G.innerIso z⁻¹).hom) hi' α β
  · simpa only [α, Category.assoc, htb'] using hQ
  · simpa only [α, Category.assoc, htb'] using hL
  · simpa only [α, Category.assoc, htb'] using hU
  · simpa only [β, Category.assoc, hta'] using hP
  · simpa only [β, Category.assoc, hta'] using hM
  · simpa only [β, Category.assoc, hta'] using hN

end Construction

/-- Finite rational double cosets with torus-adapted representatives and the
parabolic-dynamic statement suffice for the represented geometric prerequisites.
There is no additional universal Levi-intersection premise. -/
theorem representedGeometricLemmaGeometry_of_doubleCoset_of_parabolicDynamic
    (hD : RepresentedParabolicDoubleCosetStatement.{u})
    (hPD : ParabolicDynamicStatement.{u}) :
    RepresentedGeometricLemmaGeometryStatement.{u} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q L U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
  obtain ⟨hfin, hrep⟩ := hD k G hG P M Q L p l hp hl q lQ hq hlQ
  apply exists_enumerated_geometricLemmaIntersectionDatum p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ hfin
  intro a
  obtain ⟨z, hz, T, i, hi, ⟨ta, hta⟩, ⟨tb, htb⟩⟩ := hrep a.out
  exact ⟨z, hz.trans (DoubleCoset.out_eq' a),
    ⟨geometricLemmaIntersectionDatumOfTorusFactors hPD hG p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ z i hi ta hta tb htb⟩⟩

end Langlands.Aubert.General.RepresentedParabolic
