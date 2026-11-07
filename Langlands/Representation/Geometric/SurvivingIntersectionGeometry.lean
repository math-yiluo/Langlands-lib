import Langlands.Representation.Geometric.RepresentedGeometricLemmaIntersectionPoints
import Langlands.Representation.Geometric.RepresentedGeometricLemmaLeviProjection
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.SubgroupMaximality

/-! The entire source Levi in a surviving represented intersection. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

universe u

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance survivingIntersectionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)
  (hfull : SubgroupFunctor.range D.p' = ⊤)

include D hfull

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- A full source intersection has trivial radical in the original reductive
source Levi, on every test scheme. -/
theorem sourceRadical_range_eq_bot_of_full :
    SubgroupFunctor.range (D.r' ≫ D.p') = ⊥ := by
  have hnormal := Dynamic.range_comp_isNormalizedBy_of_isNormal
    D.r' D.p' D.hr'.1.isNormal
  rw [hfull] at hnormal
  exact hl.isConnectedReductive.hasTrivialUnipotentRadical D.N' (D.r' ≫ D.p')
    (D.hr'.1.isClosedSubgroup.comp D.hp'.isClosedSubgroup)
    D.hr'.1.smooth D.hr'.1.connectedSpace D.hr'.1.isUnipotent hnormal

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Its actual intersection Levi is the entire original source Levi image.
This follows from the original multiplication isomorphism and radical triviality. -/
theorem sourceLeviPoints_eq_source_of_full :
    pointImage (D.l' ≫ D.p' ≫ l ≫ p) = pointImage (l ≫ p) := by
  apply le_antisymm
  · simpa only [Category.assoc] using pointImage_comp_le (l ≫ p) (D.l' ≫ D.p')
  · rintro _ ⟨m, rfl⟩
    have hm : m ∈ (SubgroupFunctor.range D.p').carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      rw [hfull]
      exact Subgroup.mem_top m
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hm
    obtain ⟨a, b, hab⟩ := exists_pointMultiplication D.l' D.r' D.hmul' y
    have hb : rationalPoints.map (D.r' ≫ D.p') b = 1 := by
      have hbmem : rationalPoints.map (D.r' ≫ D.p') b ∈
          (SubgroupFunctor.range (D.r' ≫ D.p')).carrier
            (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
        SubgroupFunctor.mem_range.mpr ⟨b, rfl⟩
      rw [D.sourceRadical_range_eq_bot_of_full hfull] at hbmem
      exact hbmem
    have hma : rationalPoints.map (D.l' ≫ D.p') a = m := by
      calc
        rationalPoints.map (D.l' ≫ D.p') a =
            rationalPoints.map (D.l' ≫ D.p') a *
              rationalPoints.map (D.r' ≫ D.p') b := by rw [hb, mul_one]
        _ = rationalPoints.map D.p' y := by
          rw [pointMap_comp_apply, pointMap_comp_apply, ← map_mul, hab]
        _ = m := hy
    refine ⟨a, ?_⟩
    simpa only [pointMap_comp_apply] using congrArg (rationalPoints.map (l ≫ p)) hma

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- Every original source-Levi point conjugates into the original target Levi
when the source intersection parabolic is full. -/
theorem sourceLevi_le_conjugate_targetLevi_of_full :
    pointImage (l ≫ p) ≤ (pointImage (lQ ≫ q)).map (MulAut.conj z).toMonoidHom := by
  have heq := D.sourceLeviPoints_eq
  rw [D.sourceLeviPoints_eq_source_of_full hfull] at heq
  exact (le_of_eq heq).trans inf_le_right

local notation "C" =>
  pointImage (lQ ≫ q) ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z⁻¹))
    (pointImage (l ≫ p))

omit [T2Space k] [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
/-- The surviving target intersection Levi is literally the full conjugate
of the original source Levi, with no smaller source coefficient algebra. -/
theorem targetLeviPoints_eq_conjugate_source_of_full :
    C = (pointImage (l ≫ p)).map (MulAut.conj z⁻¹).toMonoidHom := by
  apply inf_eq_right.mpr
  rintro x ⟨m, hm, rfl⟩
  have hmem := D.sourceLevi_le_conjugate_targetLevi_of_full hfull hm
  have hconj := Subgroup.mem_map_equiv.mp hmem
  simpa only [MulAut.conj_symm_apply, MulAut.conj_apply,
    MulEquiv.coe_toMonoidHom, inv_inv] using hconj

/-- Actual conjugation identifies the surviving target common Levi, in its
inherited topology, with the entire original source Levi point subgroup. -/
def survivingIntersectionConjugationEquiv :
    ↥(C) ≃ₜ* pointImage (l ≫ p) :=
  conjugationEquiv z⁻¹ (M := pointImage (l ≫ p)) (N := C) (by
    intro x
    rw [D.targetLeviPoints_eq_conjugate_source_of_full hfull]
    simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv])

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)] in
@[simp]
theorem survivingIntersectionConjugationEquiv_apply_coe (x : ↥(C)) :
    (D.survivingIntersectionConjugationEquiv hfull x : rationalPoints G) =
      z * (x : rationalPoints G) * z⁻¹ := by
  change (z⁻¹)⁻¹ * (x : rationalPoints G) * z⁻¹ = _
  rw [inv_inv]

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)] in
/-- The full-Levi isomorphism is the original geometric coefficient map. -/
theorem targetLeviPointsToSourceLevi_eq_survivingConjugation (x : ↥(C)) :
    D.targetLeviPointsToSourceLevi x = D.survivingIntersectionConjugationEquiv hfull x := by
  apply Subtype.ext
  rw [D.targetLeviPointsToSourceLevi_apply_coe,
    D.survivingIntersectionConjugationEquiv_apply_coe]

omit [T2Space k] [LocallyCompactSpace (rationalPoints G)] in
/-- The original source-projection coefficient map is surjective in a
surviving intersection, without a surjectivity premise. -/
theorem targetLeviPointsToSourceLevi_surjective_of_full :
    Function.Surjective D.targetLeviPointsToSourceLevi := by
  intro m
  obtain ⟨x, hx⟩ := (D.survivingIntersectionConjugationEquiv hfull).surjective m
  exact ⟨x, (D.targetLeviPointsToSourceLevi_eq_survivingConjugation hfull x).trans hx⟩

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
