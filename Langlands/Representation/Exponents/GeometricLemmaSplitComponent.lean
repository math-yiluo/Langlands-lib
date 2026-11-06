import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization

/-! # Split components of the Levi `L'` of a geometric-lemma intersection datum

For intersection data `D` of a double coset `P z Q`, the Levi `L' = L ∩ z⁻¹Mz` of `L`
contains the maximal split torus `φ⁻¹(torus)` of `G`. Hence every central split torus of `L`
factors through `L'` as a central split torus of `L'`, and every split component `A_L` of `L`
factors through a split component of `L'`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

namespace GeometricLemmaIntersectionDatum

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}
  (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)

/-- The torus of `D` moved into `L'` by `φ⁻¹`. -/
def leviTorus : D.torus.toGrp ⟶ D.L' :=
  D.t ≫ D.φ.inv

/-- In `G`, the torus `leviTorus` is the torus of `D` conjugated by `z⁻¹`. -/
theorem leviTorus_comp :
    D.leviTorus ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q =
      (D.t ≫ D.l' ≫ D.p' ≫ l ≫ p) ≫ (G.innerIso z).inv := by
  have h : D.φ.inv ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q =
      (D.l' ≫ D.p' ≫ l ≫ p) ≫ (G.innerIso z).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc D.φ.hom, Iso.eq_comp_inv]
    simpa only [Category.assoc] using D.φ_comp.symm
  simp only [leviTorus, Category.assoc] at h ⊢
  rw [h]

/-- The torus `leviTorus` of `L'` is a maximal split torus of `G`. -/
theorem isMaximalSplitTorus_leviTorus_comp :
    IsMaximalSplitTorus (D.leviTorus ≫ D.lQ' ≫ D.q' ≫ lQ ≫ q) := by
  have h := D.isMaximalSplitTorus.comp_iso (G.innerIso z).symm
  rw [Iso.symm_hom] at h
  rw [leviTorus_comp]
  exact h

/-- The inclusion `L' ⟶ L` is a closed subgroup. -/
theorem isClosedSubgroup_lQ'_q' : IsClosedSubgroup (D.lQ' ≫ D.q') :=
  D.hlQ'.isClosedSubgroup.comp D.hq'.isClosedSubgroup

/-- The inclusion `L' ⟶ G` is a closed subgroup. -/
theorem isClosedSubgroup_lQ'_q'_lQ_q : IsClosedSubgroup (D.lQ' ≫ D.q' ≫ lQ ≫ q) :=
  D.hlQ'.isClosedSubgroup.comp
    (D.hq'.isClosedSubgroup.comp (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup))

/-- The torus `leviTorus` is a closed subgroup of `L'`. -/
theorem isClosedSubgroup_leviTorus : IsClosedSubgroup D.leviTorus :=
  IsClosedSubgroup.of_comp D.isClosedSubgroup_lQ'_q'_lQ_q
    D.isMaximalSplitTorus_leviTorus_comp.1.2

/-- Every central split torus of `L'` factors through `leviTorus`. -/
theorem exists_factor_leviTorus {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ D.L'} (ha : IsCentralSplitTorus a) :
    ∃ g : A.toGrp ⟶ D.torus.toGrp, g ≫ D.leviTorus = a := by
  have := D.hlQ'.isConnectedReductive.isAffineHom
  exact ha.exists_factor_of_isMaximalSplitTorus D.isClosedSubgroup_lQ'_q'_lQ_q
    D.isMaximalSplitTorus_leviTorus_comp

/-- Every central split torus `a` of `L` factors through `L'`, and the factor is a central
split torus of `L'`. -/
theorem exists_isCentralSplitTorus_factor {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ L} (ha : IsCentralSplitTorus a) :
    ∃ g : A.toGrp ⟶ D.L', g ≫ D.lQ' ≫ D.q' = a ∧ IsCentralSplitTorus g := by
  have := hlQ.isConnectedReductive.isAffineHom
  have ht : IsMaximalSplitTorus ((D.leviTorus ≫ D.lQ' ≫ D.q') ≫ lQ ≫ q) := by
    simpa only [Category.assoc] using D.isMaximalSplitTorus_leviTorus_comp
  obtain ⟨g, hg⟩ := ha.exists_factor_of_isMaximalSplitTorus
    (hlQ.isClosedSubgroup.comp hq.isClosedSubgroup) ht
  have hga : (g ≫ D.leviTorus) ≫ D.lQ' ≫ D.q' = a := by
    simpa only [Category.assoc] using hg
  have : Mono (D.lQ' ≫ D.q').hom.hom.left := D.isClosedSubgroup_lQ'_q'.mono
  refine ⟨g ≫ D.leviTorus, hga, ⟨ha.1.1, ?_⟩, ?_⟩
  · exact IsClosedSubgroup.of_comp D.isClosedSubgroup_lQ'_q' (by rw [hga]; exact ha.1.2)
  · exact IsCentral.of_comp (Over.mono_of_mono_left _) (by rw [hga]; exact ha.2)

/-- Every split component `A_L` of `L` factors through a split component `A_{L'}` of `L'`:
there is `f : A_L ⟶ A_{L'}` whose composite with `A_{L'} ⟶ L' ⟶ L` is the inclusion of
`A_L`. -/
theorem exists_isSplitComponent_factor {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {a : A.toGrp ⟶ L} (ha : IsSplitComponent a) :
    ∃ (A' : CommGroupScheme (Spec (CommRingCat.of k))) (a' : A'.toGrp ⟶ D.L')
      (f : A.toGrp ⟶ A'.toGrp), IsSplitComponent a' ∧ f ≫ a' ≫ D.lQ' ≫ D.q' = a := by
  have := D.hlQ'.isConnectedReductive.isAffineHom
  obtain ⟨g, hg, hgc⟩ := D.exists_isCentralSplitTorus_factor ha.1
  obtain ⟨A', a', ha'⟩ := exists_isSplitComponent_of_factor D.isClosedSubgroup_leviTorus
    D.isMaximalSplitTorus.1.1 (fun _ _ hb => D.exists_factor_leviTorus hb) hgc
  obtain ⟨f, hf⟩ := ha'.exists_factor ha.1.1.1 hgc.2
  exact ⟨A', a', f, ha', by rw [← Category.assoc, hf, hg]⟩

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
