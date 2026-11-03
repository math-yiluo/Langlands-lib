import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusStatement
import Langlands.GroupScheme.Absolute.ParabolicIntersectionGeometryStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Torus.ExistenceStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.SubgroupIntersection
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Conditional assembly of a common rational maximal torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

/-- Forget commutative homomorphism notation in an actual isomorphism. -/
def groupIso {S : Scheme.{u}} {T T' : CommGroupScheme S} (e : T ≅ T') :
    T.toGrp ≅ T'.toGrp where
  hom := groupHom e.hom
  inv := groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

end Langlands.CommGroupScheme

namespace Langlands.GroupScheme

/-- The structural conjugacy statement supplies the individual-group conjugacy
property used by maximal-torus transport. -/
theorem MaximalTorusConjugacyStatement.maximalToriAreConjugate
    (hconj : MaximalTorusConjugacyStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] :
    MaximalToriAreConjugate H := by
  intro T T' f f' hf hf'
  obtain ⟨g, e, he⟩ := hconj k H T T' f f' hf hf'
  exact ⟨g, Langlands.CommGroupScheme.groupIso e, he⟩

/-- Rational maximal-torus existence, preservation of maximality under extension,
and geometric conjugacy promote a rational maximal torus of a geometrically
connected closed subgroup to an ambient maximal torus when the subgroup has full
geometric rank. All three structural statements are explicit hypotheses. -/
theorem exists_isMaximalTorus_comp_of_geometric
    (hexist : MaximalTorusExistenceStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    (hconj : MaximalTorusConjugacyStatement.{u})
    (k : Type u) [Field k]
    (H G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (hconnected : ConnectedSpace
      ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X.left)
    (hfull : ∃ (Tbar : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (fbar : Tbar.toGrp ⟶ (GroupScheme.baseChange (toAlgebraicClosure k)).obj H),
      IsMaximalTorus (fbar ≫ (GroupScheme.baseChange (toAlgebraicClosure k)).map j)) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (f : T.toGrp ⟶ H),
      IsMaximalTorus (f ≫ j) := by
  obtain ⟨T, f, hf⟩ := hexist k H
  let bc := GroupScheme.baseChange (toAlgebraicClosure k)
  let Tbar := (CommGroupScheme.baseChange (toAlgebraicClosure k)).obj T
  have hfb : IsMaximalTorus (T := Tbar) (bc.map f) :=
    (hbase k (AlgebraicClosure k) H T f hf.1 hf.2.1).mp hf
  have : Smooth (bc.obj H).X.hom := by
    change Smooth (pullback.snd H.X.hom (toAlgebraicClosure k))
    infer_instance
  have : IsAffineHom (bc.obj H).X.hom := by
    change IsAffineHom (pullback.snd H.X.hom (toAlgebraicClosure k))
    exact isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _) inferInstance
  have : ConnectedSpace (bc.obj H).X.left := hconnected
  have hc : MaximalToriAreConjugate (bc.obj H) :=
    hconj.maximalToriAreConjugate (AlgebraicClosure k) (bc.obj H)
  have hambient : IsMaximalTorus (T := Tbar) (bc.map (f ≫ j)) := by
    rw [bc.map_comp]
    exact hc.isMaximalTorus_comp (bc.map j) (hj.baseChange _) hfb hfull
  exact ⟨T, f,
    (hbase k (AlgebraicClosure k) G T (f ≫ j) hf.1 (hf.2.1.comp hj)).mpr hambient⟩

/-- Any ambient maximal torus factoring through an intersection gives both
simultaneous group-scheme factorizations. -/
theorem exists_common_isMaximalTorus_of_intersection
    {k : Type u} [Field k]
    {P P' G : GroupScheme (Spec (CommRingCat.of k))}
    (j : P ⟶ G) (j' : P' ⟶ G)
    (h : ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (f : T.toGrp ⟶ pullback j j'),
      IsMaximalTorus (f ≫ (pullback.fst j j' ≫ j))) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (f : T.toGrp ⟶ P) (f' : T.toGrp ⟶ P'),
      IsMaximalTorus i ∧ f ≫ j = i ∧ f' ≫ j' = i := by
  obtain ⟨T, f, hf⟩ := h
  refine ⟨T, f ≫ (pullback.fst j j' ≫ j),
    f ≫ pullback.fst j j', f ≫ pullback.snd j j', hf,
    Category.assoc _ _ _, ?_⟩
  rw [Category.assoc, ← pullback.condition]

/-- The common rational maximal-torus proposition follows from the four
structural prerequisites. This theorem retains every prerequisite explicitly. -/
theorem parabolicIntersectionTorus_of_structural_inputs
    (hexist : MaximalTorusExistenceStatement.{u})
    (hbase : MaximalTorusBaseChangeStatement.{u})
    (hconj : MaximalTorusConjugacyStatement.{u})
    (hgeometry : ParabolicIntersectionGeometryStatement.{u}) :
    ParabolicIntersectionTorusStatement.{u} := by
  intro k _ G hG P P' j j' hj hj'
  obtain ⟨hsmooth, hconnected, hfull⟩ := hgeometry k G hG P P' j j' hj hj'
  let H := pullback j j'
  let c : H ⟶ G := pullback.fst j j' ≫ j
  have hc : IsClosedSubgroup c :=
    isClosedSubgroup_subgroupIntersectionHom hj.isClosedSubgroup hj'.isClosedSubgroup
  have : Smooth H.X.hom := hsmooth
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsClosedImmersion c.hom.hom.left := hc
  have : IsAffineHom H.X.hom := by
    rw [← Over.w c.hom.hom]
    infer_instance
  exact exists_common_isMaximalTorus_of_intersection j j'
    (exists_isMaximalTorus_comp_of_geometric hexist hbase hconj
      k H G c hc hconnected hfull)

end Langlands.GroupScheme
