import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Cartan.Basic
import Langlands.GroupScheme.Torus.CentralizerSmoothProof

/-! # Connectedness of torus centralizers and Cartan subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {C : GroupScheme (Spec (CommRingCat.of k))}

local instance torusCentralizerConnectedAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

section Split

variable [LocallyOfFiniteType G.X.hom] (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {j : C ⟶ G}
    (hrep : (torusCentralizer i).IsRepresentedBy j)

/-- Every representative of a split-torus centralizer is isomorphic to the
chosen dynamic centralizer for the centralizing cocharacter. -/
def splitTorusCentralizerDynamicIso :
    C ≅ Dynamic.Affine.centralizerScheme
      (CommGroupScheme.groupHom (centralizingCocharacter hT i) ≫ i) := by
  apply hrep.isoOfIsRepresentedBy
  rw [← centralizingCocharacter_spec hT i]
  exact Dynamic.Affine.isRepresentedBy_centralizerHom _

@[simp]
theorem splitTorusCentralizerDynamicIso_hom_comp :
    (splitTorusCentralizerDynamicIso hT i hrep).hom ≫
      Dynamic.Affine.centralizerHom
        (CommGroupScheme.groupHom (centralizingCocharacter hT i) ≫ i) = j := by
  exact hrep.isoOfIsRepresentedBy_hom_comp _

include hT i hrep in
/-- The centralizer of a split torus in a smooth connected affine group is
connected, without a reductivity or maximality assumption. -/
theorem IsSplitTorus.connectedSpace_centralizer [Smooth G.X.hom]
    [ConnectedSpace G.X.left] : ConnectedSpace C.X.left := by
  apply DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G
    (CommGroupScheme.groupHom (centralizingCocharacter hT i) ≫ i)
  rw [centralizingCocharacter_spec hT i]
  exact hrep

end Split

/-- Every representative of a torus centralizer in a smooth connected affine
group over any field is connected. The torus homomorphism need not be closed. -/
theorem IsTorus.connectedSpace_centralizer [Smooth G.X.hom]
    [ConnectedSpace G.X.left] (hT : IsTorus T.toGrp) (i : T.toGrp ⟶ G)
    {j : C ⟶ G} (hrep : (torusCentralizer i).IsRepresentedBy j) :
    ConnectedSpace C.X.left := by
  let E := hT.splittingExtension
  let b := Spec.map (CommRingCat.ofHom (algebraMap k E.carrier))
  let G' := (GroupScheme.baseChange b).obj G
  let T' := (CommGroupScheme.baseChange b).obj T
  have : IsAffineHom G'.X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : Smooth G'.X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace G'.X.left := G.connectedSpace_baseChange_of_smooth_affine b
  have hrep' := hrep.baseChange b
  rw [← torusCentralizer_baseChange b i] at hrep'
  have hT' : IsSplitTorus T'.toGrp := E.isSplitTorus
  have hconn : ConnectedSpace ((GroupScheme.baseChange b).obj C).X.left :=
    hT'.connectedSpace_centralizer ((GroupScheme.baseChange b).map i) hrep'
  have : Surjective b := (fieldExtension_fpqc k E.carrier).1
  change ConnectedSpace (pullback C.X.hom b : Scheme.{u}) at hconn
  let : ConnectedSpace (pullback C.X.hom b : Scheme.{u}) := hconn
  exact (pullback.fst C.X.hom b).surjective.connectedSpace
    (pullback.fst C.X.hom b).continuous

/-- Every actual Cartan subgroup of a smooth connected affine group is
connected over the original field. -/
theorem IsCartanSubgroup.connectedSpace [Smooth G.X.hom]
    [ConnectedSpace G.X.left] {j : C ⟶ G} (hj : IsCartanSubgroup j) :
    ConnectedSpace C.X.left := by
  obtain ⟨T, i, hi, hrep⟩ := hj.exists_centralizer_representation
  exact hi.1.connectedSpace_centralizer i hrep

/-- Every actual Cartan subgroup of a smooth connected affine group is
smooth and connected. Geometric nilpotence is a separate obligation. -/
theorem IsCartanSubgroup.smooth_connected [Smooth G.X.hom]
    [ConnectedSpace G.X.left] {j : C ⟶ G} (hj : IsCartanSubgroup j) :
    Smooth C.X.hom ∧ ConnectedSpace C.X.left := by
  obtain ⟨T, i, hi, hrep⟩ := hj.exists_centralizer_representation
  exact ⟨torusCentralizerSmooth k G T i hi.1 hi.2.1 C j hrep hj.1,
    hi.1.connectedSpace_centralizer i hrep⟩

end Langlands.GroupScheme
