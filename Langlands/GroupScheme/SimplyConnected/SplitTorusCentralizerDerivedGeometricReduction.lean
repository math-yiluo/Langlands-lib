import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedStatement
import Langlands.GroupScheme.SimplyConnected.GeometricReduction
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction

/-! # Reduction of the centralizer-derived theorem to algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An arbitrary representative of a split-torus centralizer in an affine
locally finite-type field group is a closed subgroup. -/
theorem IsSplitTorus.isClosedSubgroup_torusCentralizer
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    {A : CommGroupScheme (Spec (CommRingCat.of k))}
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G)
    {M : GroupScheme (Spec (CommRingCat.of k))} {j : M ⟶ G}
    (hj : (torusCentralizer a).IsRepresentedBy j) : IsClosedSubgroup j := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply Dynamic.Affine.isClosedSubgroup_of_isRepresentedBy_centralizer
    (CommGroupScheme.groupHom (centralizingCocharacter hA a) ≫ a)
  rwa [centralizingCocharacter_spec hA a]

/-- The exact centralizer-derived assertion restricted to algebraically closed
fields. The representative of the centralizer need not be supplied as closed. -/
def SplitTorusCentralizerDerivedSimplyConnectedAlgClosedStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsSimplyConnected G →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ G),
      IsSplitSubtorus a →
    ∀ (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      (torusCentralizer a).IsRepresentedBy j →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ M),
      IsDerivedSubgroup d → IsSimplyConnected D

/-- Algebraic-closure ascent and the algebraically closed case imply the full
centralizer-derived statement. All transport and reflection steps are proved. -/
theorem splitTorusCentralizerDerivedSimplyConnected_of_algebraicClosure
    (hascent : IsSimplyConnectedAlgebraicClosureAscentStatement.{u})
    (hgeo : SplitTorusCentralizerDerivedSimplyConnectedAlgClosedStatement.{u}) :
    SplitTorusCentralizerDerivedSimplyConnectedStatement.{u} := by
  intro k _ G hG A a ha M j hj D d hd
  have := hG.isSemisimple.isConnectedReductive.isAffineHom
  have := hG.isSemisimple.isConnectedReductive.smooth
  have hjclosed : IsClosedSubgroup j := ha.1.isClosedSubgroup_torusCentralizer a hj
  have : IsClosedImmersion j.hom.hom.left := hjclosed
  have : IsAffineHom M.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let b := toAlgebraicClosure k
  have ha' : IsSplitSubtorus
      (T := (CommGroupScheme.baseChange b).obj A) ((GroupScheme.baseChange b).map a) :=
    ⟨ha.1.baseChange b, ha.2.baseChange b⟩
  have hj' := hj.baseChange b
  rw [← torusCentralizer_baseChange b a] at hj'
  have hd' := hd.baseChange_of_eq b (derivedSubgroup_baseChange_eq_of_field b M)
  have hD' := hgeo (AlgebraicClosure k) ((GroupScheme.baseChange b).obj G)
    (hascent k G hG) ((CommGroupScheme.baseChange b).obj A)
    ((GroupScheme.baseChange b).map a) ha' ((GroupScheme.baseChange b).obj M)
    ((GroupScheme.baseChange b).map j) hj' ((GroupScheme.baseChange b).obj D)
    ((GroupScheme.baseChange b).map d) hd'
  exact IsSimplyConnected.of_algebraicExtension hD'

end Langlands.GroupScheme
