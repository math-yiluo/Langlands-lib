import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Rational.CharacterLatticeProof

/-! # Connectedness of dynamic subgroups of a smooth affine group over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace DynamicConnected

section Topology

/-- A morphism of schemes with a section is surjective on underlying points. -/
theorem surjective_of_section {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (h : s ≫ f = 𝟙 Y) :
    Function.Surjective f := fun y =>
  ⟨s y, by rw [← Scheme.Hom.comp_apply, h]; rfl⟩

/-- A nonempty scheme with an open immersion into an irreducible scheme is connected. -/
theorem connectedSpace_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IrreducibleSpace Y] [Nonempty X] : ConnectedSpace X := by
  have hirr : IsPreirreducible (Set.range f) :=
    (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset
      f.isOpenEmbedding.isOpen_range (Set.subset_univ _)
  have hpc : _root_.IsPreconnected (Set.range f) := hirr.isPreconnected
  rw [← Set.image_univ, f.isOpenEmbedding.isInducing.isPreconnected_image] at hpc
  rw [connectedSpace_iff_univ]
  exact ⟨Set.univ_nonempty, hpc⟩

/-- If `f : H ⟶ H'` has a section, connectedness passes from `H` to `H'`. -/
theorem connectedSpace_of_section {S : Scheme.{u}} {H H' : GroupScheme S} (f : H ⟶ H')
    (s : H' ⟶ H) (h : s ≫ f = 𝟙 H') [ConnectedSpace H.X.left] : ConnectedSpace H'.X.left := by
  have h' : s.hom.hom.left ≫ f.hom.hom.left = 𝟙 H'.X.left := by
    rw [← Over.comp_left, ← Dynamic.grp_comp_hom_hom, h]
    rfl
  exact (surjective_of_section _ _ h').connectedSpace f.hom.hom.left.continuous

end Topology

section OpenCell

variable {k : Type u} [Field k]

/-- A smooth group scheme over a field with connected underlying space is irreducible. -/
theorem irreducibleSpace_of_smooth (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom]
    [ConnectedSpace G.X.left] : IrreducibleSpace G.X.left := by
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsIntegral G.X.left := CharacterLatticeProof.isIntegral_of_smooth k G.X.hom
  infer_instance

/-- Every representative of `P_G(χ)` has connected underlying space when `G` does. -/
theorem connectedSpace_of_isRepresentedBy_parabolic
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (Dynamic.parabolic χ).IsRepresentedBy j) : ConnectedSpace H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IrreducibleSpace G.X.left := irreducibleSpace_of_smooth G
  let χ' := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let U := Dynamic.Affine.unipotentScheme χ'
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom χ'
  have hopen := oppositeCellStatement k G χ U H (Dynamic.Affine.unipotentHom χ') j hU hj
  have hne : Nonempty (U.X ⊗ H.X).left :=
    ⟨(lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ U.X) (1 : 𝟙_ _ ⟶ H.X)).left
      (Classical.arbitrary (Spec (CommRingCat.of k)))⟩
  have : ConnectedSpace (U.X ⊗ H.X).left := connectedSpace_of_isOpenImmersion
    ((fst U.X H.X ≫ (Dynamic.Affine.unipotentHom χ').hom.hom) * (snd U.X H.X ≫ j.hom.hom)).left
  have hsec : (lift (toUnit H.X ≫ (1 : 𝟙_ _ ⟶ U.X)) (𝟙 H.X)).left ≫ (snd U.X H.X).left =
      𝟙 H.X.left := by
    rw [← Over.comp_left, lift_snd]
    rfl
  exact (surjective_of_section _ _ hsec).connectedSpace (snd U.X H.X).left.continuous

/-- Every representative of `Z_G(χ)` has connected underlying space when `G` does: it is the
image of the explicit representative of `P_G(χ)` under the limit homomorphism, which has a
section. -/
theorem connectedSpace_of_isRepresentedBy_centralizer
    (G : GroupScheme (Spec (CommRingCat.of k))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : (Dynamic.centralizer χ).IsRepresentedBy j) : ConnectedSpace H.X.left := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have : ConnectedSpace (Dynamic.Affine.parabolicScheme χ).X.left :=
    connectedSpace_of_isRepresentedBy_parabolic G χ hP
  exact connectedSpace_of_section (Dynamic.limitGroupHom hP hj)
    (Dynamic.centralizerToParabolic hP hj) (Dynamic.centralizerToParabolic_comp_limitGroupHom hP hj)

end OpenCell

end DynamicConnected

open DynamicConnected in
/-- **Connectedness of dynamic subgroups** (Conrad–Gabber–Prasad, Proposition 2.1.8(4)). For a
smooth affine group scheme `G` over a field and a cocharacter `χ`, every representative of
`U_G(χ)` is connected, and if `G` is connected so is every representative of `P_G(χ)` and of
`Z_G(χ)`. -/
theorem dynamicConnected : DynamicConnectedStatement.{u} := by
  intro k _ G _ _ χ H j
  refine ⟨fun hj => ?_, fun _ => ⟨fun hj => ?_, fun hj => ?_⟩⟩
  · exact connectedSpace_of_isRepresentedBy_unipotent G χ hj
  · exact connectedSpace_of_isRepresentedBy_parabolic G χ hj
  · exact connectedSpace_of_isRepresentedBy_centralizer G χ hj

end Langlands.GroupScheme
