import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusStatement
import Langlands.GroupScheme.Absolute.BorelMaximalTorusStatement
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnectedStatement
import Langlands.GroupScheme.Torus.ExistenceStatement
import Langlands.GroupScheme.Torus.MaximalBaseChangeStatement
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Structural inputs for the singleton parabolic maximal-torus proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The still-required structural inputs to the singleton proof.
This definition does not assert that any of them holds. -/
def ParabolicMaximalTorusStructuralInputs : Prop :=
  MaximalTorusExistenceStatement.{u} ∧
  MaximalTorusBaseChangeStatement.{u} ∧
  BorelMaximalTorusStatement.{u} ∧
  BorelContainingSubgroupConnectedStatement.{u} ∧
  (∀ (k : Type u) [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
    MaximalToriAreConjugate H) ∧
  (∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ConnectedSpace ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X.left)

/-- These explicit structural inputs imply the exact singleton proposition. -/
theorem parabolicMaximalTorus_of_structuralInputs
    (h : ParabolicMaximalTorusStructuralInputs.{u}) :
    ParabolicMaximalTorusStatement.{u} := by
  obtain ⟨hExists, hBaseChange, hBorel, hConnected, hConjugate, hGeometric⟩ := h
  intro k _ G hG P i hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth P.X.hom := hi.smooth
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨T, f, hf⟩ := hExists k P
  refine ⟨T, f ≫ i, f, ?_, rfl⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  let : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  let : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  let : ConnectedSpace (F.obj G).X.left := hGeometric k G hG
  let : Smooth (F.obj P).X.hom := by
    change Smooth (pullback.snd P.X.hom b)
    infer_instance
  let : IsAffineHom (F.obj P).X.hom := by
    change IsAffineHom (pullback.snd P.X.hom b)
    infer_instance
  have hiK : IsClosedSubgroup (F.map i) := hi.isClosedSubgroup.baseChange b
  obtain ⟨B, jB, fB, hjB, hfB⟩ := hi.exists_isBorelSubgroup
  let : ConnectedSpace (F.obj P).X.left :=
    hConnected (AlgebraicClosure k) (F.obj G) (F.obj P) B
      (F.map i) jB fB hiK inferInstance hjB hfB
  have hfK : IsMaximalTorus (T := TK) (F.map f) :=
    (hBaseChange k (AlgebraicClosure k) P T f hf.1 hf.2.1).mp hf
  obtain ⟨T', j', _, hj', f', hfactor⟩ :=
    hBorel (AlgebraicClosure k) (F.obj G) B jB hjB
  have hAmbient : ∃ (T' : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))))
      (f' : T'.toGrp ⟶ F.obj P), IsMaximalTorus (f' ≫ F.map i) := by
    refine ⟨T', f' ≫ fB, ?_⟩
    rw [Category.assoc, show fB ≫ F.map i = jB from hfB, hfactor]
    exact hj'
  have hfAmbientK : IsMaximalTorus (T := TK) (F.map (f ≫ i)) := by
    rw [Functor.map_comp]
    exact (hConjugate (AlgebraicClosure k) (F.obj P)).isMaximalTorus_comp
      (F.map i) hiK hfK hAmbient
  exact (hBaseChange k (AlgebraicClosure k) G T (f ≫ i)
    hf.1 (hf.2.1.comp hi.isClosedSubgroup)).mpr hfAmbientK

end Langlands.GroupScheme
