import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.ParabolicSplitTorusConjugacyReduction

/-! # Connectedness of parabolic subgroups and split-torus conjugacy inside them -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Parabolic subgroups of smooth connected affine groups over every field are connected. -/
def ParabolicConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (P : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G),
    IsParabolicSubgroup j → ConnectedSpace P.X.left

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- Use the geometric Borel factorization to prove connectedness after algebraic closure,
then reflect connectedness along the surjective field-extension map. -/
theorem IsParabolicSubgroup.connectedSpace
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {j : P ⟶ G} (hj : IsParabolicSubgroup j) : ConnectedSpace P.X.left := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  let : Smooth P.X.hom := hj.smooth
  let : ConnectedSpace (F.obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  obtain ⟨B, i, f, hi, hf⟩ := hj.exists_isBorelSubgroup
  have hP : ConnectedSpace (F.obj P).X.left :=
    borelContainingSubgroupConnectedStatement (AlgebraicClosure k) (F.obj G)
      (F.obj P) B (F.map j) i f (hj.isClosedSubgroup.baseChange b)
      (show Smooth (pullback.snd P.X.hom b) from inferInstance) hi hf
  let : Surjective b := (fieldExtension_fpqc k (AlgebraicClosure k)).1
  exact connectedSpace_of_baseChange b P hP

/-- The unconditional connectedness statement for all rational parabolic subgroups. -/
theorem parabolicConnected : ParabolicConnectedStatement.{u} := by
  intro k _ G _ _ _ P j hj
  exact hj.connectedSpace

variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Smooth-group split-torus conjugacy alone gives conjugacy inside a rational parabolic.
The connectedness required for the application inside `P` is already proved above. -/
theorem exists_parabolic_innerIso_comp_eq_of_smoothConjugacy
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hG : IsConnectedReductive G) (j : P ⟶ G) (hj : IsParabolicSubgroup j)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (hi' : IsMaximalSplitTorus i')
    (f : T.toGrp ⟶ P) (f' : T'.toGrp ⟶ P)
    (hf : f ≫ j = i) (hf' : f' ≫ j = i') :
    ∃ (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) (e : T.toGrp ≅ T'.toGrp),
      f ≫ (P.innerIso p).hom = e.hom ≫ f' := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth P.X.hom := hj.smooth
  let : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
  let : IsAffineHom P.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : ConnectedSpace P.X.left := hj.connectedSpace
  exact exists_innerIso_comp_eq_of_smooth_connected_closed_factorizations
    hconj j hj.isClosedSubgroup hi hi' f f' hf hf'

/-- The exact minimal-parabolic target now needs only the smooth-group conjugacy input. -/
theorem minimalParabolicSplitTorusConjugacy_of_smoothConjugacy
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u}) :
    MinimalParabolicSplitTorusConjugacyStatement.{u} := by
  intro k _ G hG P j hj T T' i i' hi hi' f f' hf hf'
  exact exists_parabolic_innerIso_comp_eq_of_smoothConjugacy
    hconj hG j hj.isParabolicSubgroup hi hi' f f' hf hf'

end Langlands.GroupScheme
