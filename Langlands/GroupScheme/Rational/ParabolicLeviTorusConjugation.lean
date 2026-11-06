import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.ParabolicSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalReduction
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Conjugating a supplied maximal split torus into a rational Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicLeviTorus

variable {k : Type u} [Field k]
  {G P L : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Under parabolic-dynamic comparison, the supplied rational Levi contains a
torus maximal split in the ambient connected reductive group. -/
theorem exists_maximalSplitTorus_factor
    (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    {l : L ⟶ P} (hl : IsRationalLeviSubgroup l) :
    ∃ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G),
      IsMaximalSplitTorus i' ∧ ∃ a : T'.toGrp ⟶ L, a ≫ l ≫ p = i' := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨ψ, -, hψ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi
    hPD (dynamicGeometricUnipotentRadical_of_centralizer dynamicCentralizerReductive)
    hG hp hl
  obtain ⟨T', i', ν, hi', hν⟩ := cocharacterMaximalSplitTorus k G ψ
  have hlp : IsClosedSubgroup (l ≫ p) :=
    hl.isClosedSubgroup.comp hp.isClosedSubgroup
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i')).IsRepresentedBy
      (l ≫ p) := by
    let : IsClosedImmersion (l ≫ p).hom.hom.left := hlp
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    rw [hν]
    exact hψ
  exact ⟨T', i', hi', Dynamic.torusFactor i' (CommGroupScheme.groupHom ν) hrep,
    Dynamic.torusFactor_comp i' (CommGroupScheme.groupHom ν) hrep⟩

/-- Under the two explicit structure statements, a point of the supplied
parabolic moves the supplied maximal split torus into its supplied rational Levi. -/
theorem exists_point_and_factor
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    {l : L ⟶ P} (hl : IsRationalLeviSubgroup l)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (hcontained : SubgroupFunctor.range i ≤ SubgroupFunctor.range p) :
    ∃ (x : rationalPoints P) (a : T.toGrp ⟶ L),
      a ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p x)).hom := by
  obtain ⟨T', i', hi', a', ha'⟩ := exists_maximalSplitTorus_factor hPD hG hp hl
  have hpc : IsClosedSubgroup p := hp.isClosedSubgroup
  let : IsClosedImmersion p.hom.hom.left := hpc
  have hpRep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨f, -, hf⟩ := hi.exists_lift hpRep hpc hcontained
  obtain ⟨x, e, he⟩ := exists_parabolic_innerIso_comp_eq_of_structuralStatements
    hconj hPD dynamicConnected hG p hp hi hi' f (a' ≫ l) hf
      (by simpa only [Category.assoc] using ha')
  refine ⟨x, e.hom ≫ a', ?_⟩
  change (e.hom ≫ a') ≫ l ≫ p = i ≫ (G.innerIso (x ≫ p.hom.hom)).hom
  calc
    (e.hom ≫ a') ≫ l ≫ p = (e.hom ≫ (a' ≫ l)) ≫ p := by
      simp only [Category.assoc]
    _ = (f ≫ (P.innerIso x).hom) ≫ p := by rw [he]
    _ = i ≫ (G.innerIso (x ≫ p.hom.hom)).hom := by
      rw [Category.assoc, ← comp_innerIso_hom_comp, ← Category.assoc, hf]

/-- Choose an actual parabolic point and a Levi factor of the conjugated torus,
together with their group-scheme factorization equation. -/
def pointAndFactor
    (hPD : ParabolicDynamicStatement.{u})
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    {l : L ⟶ P} (hl : IsRationalLeviSubgroup l)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (hcontained : SubgroupFunctor.range i ≤ SubgroupFunctor.range p) :
    {xa : rationalPoints P × (T.toGrp ⟶ L) //
      xa.2 ≫ l ≫ p = i ≫ (G.innerIso (rationalPoints.map p xa.1)).hom} :=
  Classical.indefiniteDescription _ (by
    obtain ⟨x, a, ha⟩ := exists_point_and_factor hPD hconj hG hp hl hi hcontained
    exact ⟨(x, a), ha⟩)

end Langlands.GroupScheme.ParabolicLeviTorus
