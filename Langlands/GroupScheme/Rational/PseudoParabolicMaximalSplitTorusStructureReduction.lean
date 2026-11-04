import Langlands.GroupScheme.Rational.PseudoParabolicMaximalSplitTorusStructureStatement
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.PseudoParabolicStructureProof

/-! # Maximal split tori of pseudo-parabolic subgroups

Conditional reduction of the first two clauses of CGP Proposition C.2.4 (with the
maximality observation preceding it): from the published statement on conjugacy of
maximal split tori, a maximal split torus `S` of a pseudo-parabolic subgroup `P` of a
smooth connected affine group `G` has its whole ambient centralizer `Z_G(S)` inside `P`
on every relative test, and is therefore maximal split in `G`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G P : GroupScheme (Spec (CommRingCat.of k))}
  {S : CommGroupScheme (Spec (CommRingCat.of k))}

namespace IsPseudoParabolicSubgroup

/-- A rationally conjugate dynamic parabolic of a cocharacter whose parabolic lies in
`P` still lies in `P`, when the conjugating point is a point of `P`. -/
theorem parabolic_comp_innerIso_le_range {i : P ⟶ G}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hχ : Dynamic.parabolic χ ≤ SubgroupFunctor.range i)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) :
    Dynamic.parabolic (χ ≫ (G.innerIso (p ≫ i.hom.hom)).hom) ≤
      SubgroupFunctor.range i := by
  intro T g hg
  set c := p ≫ i.hom.hom
  have hc : c ∈ (SubgroupFunctor.range i).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := ⟨p, rfl⟩
  have hcT : G.constantPoint c T ∈ (SubgroupFunctor.range i).carrier T :=
    (SubgroupFunctor.range i).comp_mem (Over.homMk T.hom (by simp)) hc
  set x := (G.constantPoint c T)⁻¹ * g * G.constantPoint c T
  have hgx : g = G.constantPoint c T * x * (G.constantPoint c T)⁻¹ := by
    simp only [x, mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]
  have hx : x ∈ (Dynamic.parabolic χ).carrier T := by
    rw [Dynamic.mem_parabolic_conj χ c, ← hgx]
    exact hg
  rw [hgx]
  exact (SubgroupFunctor.range i |>.carrier T).mul_mem
    ((SubgroupFunctor.range i |>.carrier T).mul_mem hcT (hχ T hx))
    ((SubgroupFunctor.range i |>.carrier T).inv_mem hcT)

/-- Conditionally on conjugacy of maximal split tori: the whole ambient centralizer of a
maximal split torus of a pseudo-parabolic subgroup lies in that subgroup on every
relative test. -/
theorem torusCentralizer_le_range
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsPseudoParabolicSubgroup i)
    {s : S.toGrp ⟶ P} (hs : IsMaximalSplitTorus s) :
    torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i := by
  obtain ⟨hPs, hPc, hPa⟩ := pseudoParabolicSubgroupStructure k G P i hi
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨χ, hχ⟩ := hi.exists_cocharacter_le
  have hχi : SubgroupFunctor.range χ ≤ SubgroupFunctor.range i :=
    (Dynamic.range_le_parabolic χ).trans hχ
  obtain ⟨p, ξ, hpξ⟩ :=
    exists_innerIso_comp_eq_cocharacter hconj hs (hrep.factorHom χ hχi)
  have hχc : χ ≫ (G.innerIso (p ≫ i.hom.hom)).hom =
      CommGroupScheme.groupHom ξ ≫ (s ≫ i) := by
    rw [← hrep.factorHom_comp χ hχi, Category.assoc, comp_innerIso_hom_comp,
      reassoc_of% hpξ]
  calc torusCentralizer (s ≫ i)
      ≤ Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ (s ≫ i)) :=
        torusCentralizer_le_dynamicCentralizer _ _
    _ ≤ Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ (s ≫ i)) :=
        Dynamic.centralizer_le_parabolic _
    _ ≤ SubgroupFunctor.range i := by
        rw [← hχc]
        exact parabolic_comp_innerIso_le_range χ hχ p

/-- Conditionally on conjugacy of maximal split tori: a maximal split torus of a
pseudo-parabolic subgroup is maximal split in the ambient group. -/
theorem isMaximalSplitTorus_comp
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : P ⟶ G} (hi : IsPseudoParabolicSubgroup i)
    {s : S.toGrp ⟶ P} (hs : IsMaximalSplitTorus s) :
    IsMaximalSplitTorus (s ≫ i) :=
  hs.comp_of_torusCentralizer_le_range hi.isClosedSubgroup
    (hi.torusCentralizer_le_range hconj hs)

end IsPseudoParabolicSubgroup

/-- The first two clauses of CGP Proposition C.2.4 together with the maximality
observation preceding it: every maximal split torus `S` of a pseudo-parabolic subgroup
`P` of a smooth connected affine group `G` is maximal split in `G`, and `Z_G(S) ⊆ P` on
every relative test. This proposition is the conclusion of the conditional reduction
`pseudoParabolicTorusCentralizerContainment_of_conjugacy`, not an assertion that it holds
unconditionally. -/
def PseudoParabolicTorusCentralizerContainment : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : P ⟶ G), IsPseudoParabolicSubgroup i →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (s : S.toGrp ⟶ P),
        IsMaximalSplitTorus s →
          IsMaximalSplitTorus (s ≫ i) ∧
          torusCentralizer (s ≫ i) ≤ SubgroupFunctor.range i

/-- Conditionally on conjugacy of maximal split tori, the first two clauses of CGP
Proposition C.2.4 hold. -/
theorem pseudoParabolicTorusCentralizerContainment_of_conjugacy
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    PseudoParabolicTorusCentralizerContainment.{u} := by
  intro k _ G P _ _ _ i hi S s hs
  exact ⟨hi.isMaximalSplitTorus_comp hconj hs, hi.torusCentralizer_le_range hconj hs⟩

end Langlands.GroupScheme
