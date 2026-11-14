import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.BaseConnectedStatement
import Langlands.GroupScheme.Dynamic.FieldOppositeCellProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.ReducedSubgroup
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # Connected dynamic fibres without smoothness over any base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace DynamicBaseConnected

section FieldGeometry

variable {k : Type u} [Field k]

/-- A connected group scheme over a field is geometrically connected: its unit is
a rational section of the structure morphism. -/
theorem geometricallyConnected_of_connected (G : GroupScheme (Spec (CommRingCat.of k)))
    [ConnectedSpace G.X.left] : GeometricallyConnected G.X.hom :=
  Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section G.X.hom
    (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X).left (Over.w _)

/-- Connectedness passes to the reduction, whose inclusion is a homeomorphism. -/
theorem connectedSpace_red (X : Scheme.{u}) [ConnectedSpace X] :
    ConnectedSpace (ReducedSubgroup.red X) :=
  ((ReducedSubgroup.redι X).isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective
    (ReducedSubgroup.redι_surjective X)).connectedSpace_iff.mpr inferInstance

/-- A connected group scheme locally of finite type over a perfect field is
irreducible, since its reduction is smooth and has the same underlying topology. -/
theorem irreducibleSpace_of_perfect [PerfectField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] : IrreducibleSpace G.X.left := by
  have : ConnectedSpace (ReducedSubgroup.redOver G).left := connectedSpace_red G.X.left
  have : IsLocallyNoetherian (ReducedSubgroup.redOver G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (ReducedSubgroup.redOver G).hom
  have : IsIntegral (ReducedSubgroup.redOver G).left :=
    CharacterLatticeProof.isIntegral_of_smooth k (ReducedSubgroup.redOver G).hom
  have : IrreducibleSpace (ReducedSubgroup.red G.X.left) :=
    inferInstanceAs (IrreducibleSpace (ReducedSubgroup.redOver G).left)
  exact (ReducedSubgroup.redι_surjective G.X.left).irreducibleSpace
    (ReducedSubgroup.redι G.X.left).continuous

/-- A connected group scheme locally of finite type over any field is
irreducible. The rational unit ensures connectedness after algebraic closure;
the perfect-field reduction argument then descends through the projection. -/
theorem irreducibleSpace_of_finiteType
    (G : GroupScheme (Spec (CommRingCat.of k))) [LocallyOfFiniteType G.X.hom]
    [ConnectedSpace G.X.left] : IrreducibleSpace G.X.left := by
  let K := AlgebraicClosure k
  let y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  let G' := (GroupScheme.baseChange y).obj G
  have : GeometricallyConnected G.X.hom := geometricallyConnected_of_connected G
  have : LocallyOfFiniteType G'.X.hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom y inferInstance
  have : ConnectedSpace G'.X.left :=
    (geometrically_iff_of_isClosedUnderIsomorphisms.mp
      (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) K y
  have : IrreducibleSpace G'.X.left := irreducibleSpace_of_perfect G'
  have : IrreducibleSpace ↥(pullback G.X.hom y) := ‹IrreducibleSpace G'.X.left›
  have : Surjective y := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst G.X.hom y).surjective.irreducibleSpace
    (pullback.fst G.X.hom y).continuous

end FieldGeometry

section FieldDynamics

variable {k : Type u} [Field k]

/-- Dynamic parabolic representatives in a connected affine finite-type group
over a field are connected, without smoothness. -/
theorem connectedSpace_parabolic (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (Dynamic.parabolic χ).IsRepresentedBy j) : ConnectedSpace H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IrreducibleSpace G.X.left := irreducibleSpace_of_finiteType G
  let χ' := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let U := Dynamic.Affine.unipotentScheme χ'
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hopen := dynamicFieldOppositeCell k G χ U H (Dynamic.Affine.unipotentHom χ') j hU hj
  have : IsOpenImmersion
      ((fst U.X H.X ≫ (Dynamic.Affine.unipotentHom χ').hom.hom) *
        (snd U.X H.X ≫ j.hom.hom)).left := hopen
  have hne : Nonempty (U.X ⊗ H.X).left :=
    ⟨(lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X) (1 : 𝟙_ _ ⟶ H.X)).left
      (Classical.arbitrary (Spec (CommRingCat.of k)))⟩
  have : ConnectedSpace (U.X ⊗ H.X).left :=
    DynamicConnected.connectedSpace_of_isOpenImmersion
      ((fst U.X H.X ≫ (Dynamic.Affine.unipotentHom χ').hom.hom) *
        (snd U.X H.X ≫ j.hom.hom)).left
  have hsec : (lift (toUnit H.X ≫ (1 : 𝟙_ _ ⟶ U.X)) (𝟙 H.X)).left ≫
      (snd U.X H.X).left = 𝟙 H.X.left := by
    rw [← Over.comp_left, lift_snd]
    rfl
  exact (DynamicConnected.surjective_of_section _ _ hsec).connectedSpace
    (snd U.X H.X).left.continuous

/-- The dynamic centralizer is connected as the image of the connected
parabolic under the limit homomorphism, which has a section. -/
theorem connectedSpace_centralizer (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [ConnectedSpace G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (Dynamic.centralizer χ).IsRepresentedBy j) : ConnectedSpace H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : ConnectedSpace (Dynamic.Affine.parabolicScheme χ).X.left :=
    connectedSpace_parabolic G χ hP
  exact DynamicConnected.connectedSpace_of_section (Dynamic.limitGroupHom hP hj)
    (Dynamic.centralizerToParabolic hP hj)
    (Dynamic.centralizerToParabolic_comp_limitGroupHom hP hj)

end FieldDynamics

section BaseChange

variable {S : Scheme.{u}} {G H : GroupScheme S}

theorem locallyOfFiniteType_baseChange [LocallyOfFinitePresentation G.X.hom]
    {T : Scheme.{u}} (y : T ⟶ S) :
    LocallyOfFiniteType ((GroupScheme.baseChange y).obj G).X.hom :=
  MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) G.X.hom y inferInstance

end BaseChange

end DynamicBaseConnected

open DynamicBaseConnected DynamicBaseSmoothConnected in
/-- Connected dynamic fibres over every base, without smoothness. -/
theorem dynamicBaseConnected : DynamicBaseConnectedStatement.{u} := by
  intro S G _ _ χ H j
  refine ⟨fun hj => ?_, fun hj hG => ?_, fun hj hG => ?_⟩
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := isAffineHom_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.unipotent_baseChange] at hjK
    exact DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent _
      (Dynamic.baseChangeCocharacter y χ) hjK
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := isAffineHom_baseChange (G := G) y
    let := locallyOfFiniteType_baseChange (G := G) y
    let := connectedSpace_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.parabolic_baseChange] at hjK
    exact connectedSpace_parabolic _ (Dynamic.baseChangeCocharacter y χ) hjK
  · refine geometricallyConnected_of_baseChange fun K _ y => ?_
    let := isAffineHom_baseChange (G := G) y
    let := locallyOfFiniteType_baseChange (G := G) y
    let := connectedSpace_baseChange (G := G) y
    have hjK := hj.baseChange y
    rw [← Dynamic.centralizer_baseChange] at hjK
    exact connectedSpace_centralizer _ (Dynamic.baseChangeCocharacter y χ) hjK

end Langlands.GroupScheme
