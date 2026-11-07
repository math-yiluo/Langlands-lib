import Langlands.Representation.Geometric.RepresentedGeometricLemmaCommonCocharacterConstruction
import Langlands.Representation.Geometric.RepresentedGeometricLemmaDynamicRealization

/-! Actual intersection data and simultaneous realizations from known cocharacters. -/

noncomputable section
set_option maxHeartbeats 20000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct NNReal

namespace Langlands.GroupScheme.Dynamic

universe u

variable {k : Type u} [Field k]
  {G G' H : GroupScheme (Spec (CommRingCat.of k))}
  {j : H ⟶ G} {χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G}

private theorem range_comp_iso_eq_parabolic
    (h : SubgroupFunctor.range j = parabolic χ) (e : G ≅ G') :
    SubgroupFunctor.range (j ≫ e.hom) = parabolic (χ ≫ e.hom) := by
  rw [SubgroupFunctor.range_comp_iso, h]
  symm
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    parabolic_eq_comap_of_iso (χ ≫ e.hom) e.symm

private theorem range_comp_iso_eq_centralizer
    (h : SubgroupFunctor.range j = centralizer χ) (e : G ≅ G') :
    SubgroupFunctor.range (j ≫ e.hom) = centralizer (χ ≫ e.hom) := by
  rw [SubgroupFunctor.range_comp_iso, h]
  symm
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    centralizer_eq_comap_of_iso (χ ≫ e.hom) e.symm

private theorem range_comp_iso_eq_unipotent
    (h : SubgroupFunctor.range j = unipotent χ) (e : G ≅ G') :
    SubgroupFunctor.range (j ≫ e.hom) = unipotent (χ ≫ e.hom) := by
  rw [SubgroupFunctor.range_comp_iso, h]
  symm
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    unipotent_eq_comap_of_iso (χ ≫ e.hom) e.symm

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {n : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hn : LeviSubgroup.IsGeometricUnipotentRadical n}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l n)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {nQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hnQ : LeviSubgroup.IsGeometricUnipotentRadical nQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ nQ)}
  (χP χQ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  (hP : SubgroupFunctor.range p = Dynamic.parabolic χP)
  (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χP)
  (hN : SubgroupFunctor.range (n ≫ p) = Dynamic.unipotent χP)
  (hQ : SubgroupFunctor.range q = Dynamic.parabolic χQ)
  (hL : SubgroupFunctor.range (lQ ≫ q) = Dynamic.centralizer χQ)
  (hU : SubgroupFunctor.range (nQ ≫ q) = Dynamic.unipotent χQ)

/-- Known source and target cocharacters construct actual intersection data
from torus-adapted representatives without the universal parabolic-dynamic
statement. -/
def geometricLemmaIntersectionDatumOfKnownCocharacters
    (z : rationalPoints G) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ta : T.toGrp ⟶ M) (hta : ta ≫ l ≫ p = i)
    (tb : T.toGrp ⟶ L) (htb : tb ≫ lQ ≫ q ≫ (G.innerIso z).hom = i) :
    GeometricLemmaIntersectionDatum p l n hp hn hl hmul
      q lQ nQ hq hnQ hlQ hmulQ z := by
  apply Classical.choice
  let iz := i ≫ (G.innerIso z⁻¹).hom
  have hi' : IsMaximalSplitTorus iz := hi.comp_iso _
  have hzz' : (G.innerIso z).hom ≫ (G.innerIso z⁻¹).hom = 𝟙 G := by
    rw [innerIso_inv_hom, Iso.hom_inv_id]
  have htb' : tb ≫ lQ ≫ q = iz := by
    have hh := congrArg (fun f : T.toGrp ⟶ G => f ≫ (G.innerIso z⁻¹).hom) htb
    simpa only [Category.assoc, hzz', Category.comp_id] using hh
  have hcQ : SubgroupFunctor.range iz ≤ Dynamic.centralizer χQ := by
    rw [← htb', ← hL]
    exact SubgroupFunctor.range_comp_le tb (lQ ≫ q)
  have hcP : SubgroupFunctor.range i ≤ Dynamic.centralizer χP := by
    rw [← hta, ← hM]
    exact SubgroupFunctor.range_comp_le ta (l ≫ p)
  obtain ⟨α, hα⟩ := hi'.exists_cocharacter_factor_of_centralizing χQ hcQ
  obtain ⟨β, hβ⟩ := hi.exists_cocharacter_factor_of_centralizing χP hcP
  have hβ' : CommGroupScheme.groupHom β ≫ iz = χP ≫ (G.innerIso z⁻¹).hom := by
    simpa only [iz, Category.assoc] using
      congrArg (fun f => f ≫ (G.innerIso z⁻¹).hom) hβ
  refine ⟨geometricLemmaIntersectionDatumOfCommonCocharacters p l n hp hn hl hmul
    q lQ nQ hq hnQ hlQ hmulQ z iz hi' α β ?_ ?_ ?_ ?_ ?_ ?_⟩
  · rwa [hα]
  · rwa [hα]
  · rwa [hα]
  · rw [hβ']
    exact Dynamic.range_comp_iso_eq_parabolic hP (G.innerIso z⁻¹)
  · rw [hβ']
    simpa only [Category.assoc] using
      Dynamic.range_comp_iso_eq_centralizer hM (G.innerIso z⁻¹)
  · rw [hβ']
    simpa only [Category.assoc] using
      Dynamic.range_comp_iso_eq_unipotent hN (G.innerIso z⁻¹)


namespace GeometricLemmaIntersectionDatum

variable {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l n hp hn hl hmul
    q lQ nQ hq hnQ hlQ hmulQ z)

/-- The same known original cocharacters give a simultaneous realization in
any actual datum's fixed common maximal split torus. -/
def dynamicRealizationOfKnownCocharacters : D.DynamicRealization := by
  apply Classical.choice
  let iP := D.t ≫ D.l' ≫ D.p' ≫ l ≫ p
  let iQ := D.targetCommonTorusHom ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q
  have hcP : SubgroupFunctor.range iP ≤ Dynamic.centralizer χP := by
    rw [← hM]
    exact SubgroupFunctor.range_comp_le (D.t ≫ D.l' ≫ D.p') (l ≫ p)
  have hcQ : SubgroupFunctor.range iQ ≤ Dynamic.centralizer χQ := by
    rw [← hL]
    exact SubgroupFunctor.range_comp_le
      (D.targetCommonTorusHom ≫ D.lQ' ≫ D.q') (lQ ≫ q)
  obtain ⟨α, hα⟩ := D.targetCommonTorus_isMaximalSplitTorus_ambient.exists_cocharacter_factor_of_centralizing χQ hcQ
  obtain ⟨β, hβ⟩ := D.isMaximalSplitTorus.exists_cocharacter_factor_of_centralizing χP hcP
  have hsame : iP ≫ (G.innerIso z⁻¹).hom = iQ := by
    dsimp only [iP, iQ]
    rw [D.targetCommonTorusHom_comp]
    simp only [innerIso_inv_hom]
  have hβ' : CommGroupScheme.groupHom β ≫ iQ = χP ≫ (G.innerIso z⁻¹).hom := by
    rw [← hsame, ← Category.assoc, hβ]
  refine ⟨⟨α, β, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rwa [hα]
  · rwa [hα]
  · rwa [hα]
  · rw [hβ']
    exact Dynamic.range_comp_iso_eq_parabolic hP (G.innerIso z⁻¹)
  · rw [hβ']
    simpa only [Category.assoc] using
      Dynamic.range_comp_iso_eq_centralizer hM (G.innerIso z⁻¹)
  · rw [hβ']
    simpa only [Category.assoc] using
      Dynamic.range_comp_iso_eq_unipotent hN (G.innerIso z⁻¹)

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
