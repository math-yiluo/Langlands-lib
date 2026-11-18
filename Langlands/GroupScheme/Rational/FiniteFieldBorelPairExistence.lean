import Langlands.GroupScheme.Rational.FiniteFieldBorelConjugacy
import Langlands.GroupScheme.Torus.FiniteFieldGeometricMaximalProof
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.MaximalBaseChangeReflection

/-! # Existence of Borel pairs over finite fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FiniteFieldBorelPair

variable (k : Type u) [Field k] [Finite k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A smooth connected affine group over a finite field has a geometric Borel
defined over the original field. -/
theorem exists_geometricBorel :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsGeometricBorelSubgroup b := by
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨H, i, hi, hF⟩ :=
    exists_frobeniusStableBorel_of_borelConjugacy k (AlgebraicClosure k) G borelConjugacy
  let D := hi.descentOfFrobeniusTransport hF
  exact ⟨D.obj, D.inclusion, D.geometricBorel⟩

/-- A maximal torus chosen geometrically inside a geometric Borel is maximal
in the ambient group. -/
theorem exists_maximalTorus_in_geometricBorel
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ G)
    (hb : IsGeometricBorelSubgroup b) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (f : T.toGrp ⟶ B),
      IsMaximalTorus (f ≫ b) := by
  let : Smooth B.X.hom := hb.1.smooth
  let : ConnectedSpace B.X.left := hb.1.connectedSpace
  let : IsClosedImmersion b.hom.hom.left := hb.1.isClosedSubgroup
  let : IsAffineHom B.X.hom := by
    rw [← Over.w b.hom.hom]
    infer_instance
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  let : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  let : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (toAlgebraicClosure k))
    infer_instance
  let : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine (toAlgebraicClosure k)
  let : Smooth (F.obj B).X.hom := by
    change Smooth (pullback.snd B.X.hom (toAlgebraicClosure k))
    infer_instance
  let : IsAffineHom (F.obj B).X.hom := by
    change IsAffineHom (pullback.snd B.X.hom (toAlgebraicClosure k))
    infer_instance
  let : ConnectedSpace (F.obj B).X.left := hb.2.connectedSpace
  obtain ⟨T, f, hf, hfK⟩ := finiteFieldGeometricMaximalTorus k B
  obtain ⟨T', j', _, hj', f', hfactor⟩ :=
    borelMaximalTorus (AlgebraicClosure k) (F.obj G) (F.obj B) (F.map b) hb.2
  have hfull : ∃ (T' : CommGroupScheme
      (Spec (CommRingCat.of (AlgebraicClosure k))))
      (f' : T'.toGrp ⟶ F.obj B), IsMaximalTorus (f' ≫ F.map b) := by
    refine ⟨T', f', ?_⟩
    rw [hfactor]
    exact hj'
  have hc : MaximalToriAreConjugate (F.obj B) :=
    solvableMaximalTorusConjugacy (AlgebraicClosure k) (F.obj B)
      hb.2.isSolvableGroupScheme
  have hmax : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T)
      (F.map (f ≫ b)) := by
    rw [F.map_comp]
    exact hc.isMaximalTorus_comp (F.map b) hb.2.isClosedSubgroup hfK hfull
  exact ⟨T, f, IsMaximalTorus.of_baseChange
    (hf.2.1.comp hb.1.isClosedSubgroup) hmax⟩

/-- Every smooth connected affine group over a finite field has a Borel pair. -/
theorem exists_borelPair :
    ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
      (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsGeometricBorelSubgroup b ∧ IsMaximalTorus j ∧
        SubgroupFunctor.range j ≤ SubgroupFunctor.range b := by
  obtain ⟨B, b, hb⟩ := exists_geometricBorel k G
  obtain ⟨T, f, hf⟩ := exists_maximalTorus_in_geometricBorel k G b hb
  exact ⟨B, b, T, f ≫ b, hb, hf, SubgroupFunctor.range_le_of_factor f rfl⟩

end Langlands.GroupScheme.FiniteFieldBorelPair
