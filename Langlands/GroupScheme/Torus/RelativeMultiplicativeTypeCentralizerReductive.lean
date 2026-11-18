import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeCentralizerReductiveStatement
import Langlands.GroupScheme.Reductive.IdentityComponentClopenStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.RelativeIdentityComponentFiberComparison
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFieldComparison
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Reductive identity components of relative multiplicative-type centralizers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

open RelativeIdentityComponent

variable {S : Scheme.{u}}

/-- A group scheme `Z` over `S` *has a reductive relative identity component* if every open
subgroup `z₀ : Z₀ ⟶ Z` representing the relative identity component of `Z` is a reductive
`S`-group, is closed in `Z`, and has connected reductive residue fibres `Z₀_s`. This is the
conclusion of part (3) of `RelativeMultiplicativeTypeCentralizerStatement` for a
representative `Z` of the centralizer. -/
def HasReductiveIdentityComponent (Z : GroupScheme S) : Prop :=
  ∀ (Z₀ : GroupScheme S) (z₀ : Z₀ ⟶ Z), IsRelativeIdentityComponent Z z₀ →
    IsReductive Z₀ ∧ IsClosedImmersion z₀.hom.hom.left ∧
      ∀ s : S, IsConnectedReductive (residueFiber Z₀ s)

/-- Open-immersion homomorphisms remain open immersions after base change; the proof is that
of `IsClosedSubgroup.baseChange`, with open immersions in place of closed immersions. -/
theorem isOpenImmersion_baseChange_map {S' : Scheme.{u}} (b : S' ⟶ S) {P Q : GroupScheme S}
    (j : P ⟶ Q) [IsOpenImmersion j.hom.hom.left] :
    IsOpenImmersion ((GroupScheme.baseChange b).map j).hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map j).hom.hom.left ≫ pullback.snd Q.X.hom b)
      (pullback.fst P.X.hom b) b (j.hom.hom.left ≫ Q.X.hom) := by
    change IsPullback (((Over.pullback b).map j.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w j.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback P.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map j).hom.hom.left ≫ pullback.fst Q.X.hom b =
        pullback.fst P.X.hom b ≫ j.hom.hom.left by
      change ((Over.pullback b).map j.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback Q.X.hom b).flip
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hp.flip ‹_›

/-- Over a field, a group with an open-immersion homomorphism onto the identity component of a
smooth affine group `C` is connected reductive as soon as `C⁰` is. -/
theorem IsConnectedReductive.of_isOpenImmersion_range_eq_identitySet {k : Type u} [Field k]
    {C P : GroupScheme (Spec (CommRingCat.of k))} [hsm : Smooth C.X.hom]
    [haff : IsAffineHom C.X.hom] (j : P ⟶ C) [hj : IsOpenImmersion j.hom.hom.left]
    (hrange : Set.range j.hom.hom.left = IdentityComponent.identitySet C)
    (hC : IsConnectedReductive (identityComponent C)) : IsConnectedReductive P := by
  have : IsClosedImmersion j.hom.hom.left :=
    IsClosedImmersion.of_isPreimmersion _ (by
      rw [hrange]
      exact (IdentityComponent.isClopen_identitySet C).isClosed)
  have : ConnectedSpace P.X.left := by
    rw [connectedSpace_iff_univ]
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ : (IdentityComponent.identitySet C).Nonempty :=
        ⟨_, mem_connectedComponent⟩
      rw [← hrange] at hx
      obtain ⟨y, -⟩ := hx
      exact ⟨y, Set.mem_univ _⟩
    · have hc : _root_.IsPreconnected (Set.range j.hom.hom.left) := by
        rw [hrange]
        exact isPreconnected_connectedComponent
      rw [← Set.image_univ] at hc
      exact j.hom.hom.left.isOpenEmbedding.isInducing.isPreconnected_image.mp hc
  exact IsConnectedReductive.of_iso (IdentityComponent.isoOfIsOpenImmersion C j) hC

/-- **Residue fibres of the relative identity component of a multiplicative-type
centralizer.** Given the field case `MultiplicativeTypeCentralizerReductiveStatement`, every
residue fibre `Z⁰_s` of an open subgroup `Z⁰` representing the relative identity component of
a closed representative `Z` of `Z_G(H)` is connected reductive, when `G` is reductive and `H`
is of multiplicative type. -/
theorem relativeMultiplicativeTypeCentralizer_isConnectedReductive_residueFiber
    (hField : MultiplicativeTypeCentralizerReductiveStatement.{u})
    {G : GroupScheme S} {H : CommGroupScheme S} (i : H.toGrp ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp) (hG : IsReductive G)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hzc : IsClosedSubgroup z)
    {Z₀ : GroupScheme S} {z₀ : Z₀ ⟶ Z} (h₀ : IsRelativeIdentityComponent Z z₀) (s : S) :
    IsConnectedReductive (residueFiber Z₀ s) := by
  let b := S.fromSpecResidueField s
  let B := GroupScheme.baseChange b
  have hGs : IsConnectedReductive (residueFiber G s) := hG.isConnectedReductive_residueFiber s
  have hHs : IsMultiplicativeType ((CommGroupScheme.baseChange b).obj H).toGrp :=
    hH.field_baseChange b
  have hrep : (torusCentralizer (T := (CommGroupScheme.baseChange b).obj H)
      (B.map i)).IsRepresentedBy (B.map z) := by
    rw [torusCentralizer_baseChange b i]
    exact hz.baseChange b
  obtain ⟨hsm, hred⟩ := hField (S.residueField s) (residueFiber G s) hGs
    ((CommGroupScheme.baseChange b).obj H) (B.map i) hHs (residueFiber Z s) (B.map z) hrep
    (hzc.baseChange b)
  have := hG.isAffineHom
  have : IsAffineHom Z.X.hom := by
    have : IsClosedImmersion z.hom.hom.left := hzc
    rw [← Over.w z.hom.hom]
    infer_instance
  have haff : IsAffineHom (pullback.snd Z.X.hom b) := inferInstance
  have := h₀.isOpenImmersion
  exact IsConnectedReductive.of_isOpenImmersion_range_eq_identitySet (C := residueFiber Z s)
    (hsm := hsm) (haff := haff) (B.map z₀) (hj := isOpenImmersion_baseChange_map b z₀)
    (range_residueFiberInclusion Z z₀ h₀ s) hred

/-- **Reductive identity components of multiplicative-type centralizers** (part (3) of
`RelativeMultiplicativeTypeCentralizerStatement`, conditional on Conrad's Proposition 3.1.3 and
on the field case). Let `G` be reductive over `S`, `H` of multiplicative type and
`i : H ⟶ G` a homomorphism such that `Z_G(H)` has a closed representative. For every smooth
representative `Z` of `Z_G(H)` and every `Z⁰ ⟶ Z` representing the relative identity
component, `Z⁰` is reductive, closed in `Z`, and has connected reductive residue fibres. -/
theorem relativeMultiplicativeTypeCentralizer_reductive
    (hClopen : IdentityComponentClopenStatement.{u})
    (hField : MultiplicativeTypeCentralizerReductiveStatement.{u})
    {G : GroupScheme S} {H : CommGroupScheme S} (i : H.toGrp ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp) (hG : IsReductive G)
    (hcl : (torusCentralizer i).IsClosedRepresentable)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hZ : Smooth Z.X.hom)
    {Z₀ : GroupScheme S} {z₀ : Z₀ ⟶ Z} (h₀ : IsRelativeIdentityComponent Z z₀) :
    IsReductive Z₀ ∧ IsClosedImmersion z₀.hom.hom.left ∧
      ∀ s : S, IsConnectedReductive (residueFiber Z₀ s) := by
  obtain ⟨C, c, hc, hclosed⟩ := hcl
  have hzc : IsClosedSubgroup z := hz.isClosedSubgroup hc hclosed
  have := hG.isAffineHom
  have : IsAffineHom Z.X.hom := by
    have : IsClosedImmersion z.hom.hom.left := hzc
    rw [← Over.w z.hom.hom]
    infer_instance
  have hfib : ∀ s : S, IsConnectedReductive (residueFiber Z₀ s) := fun s =>
    relativeMultiplicativeTypeCentralizer_isConnectedReductive_residueFiber hField i hH hG hz
      hzc h₀ s
  obtain ⟨hred, hcl₀, -⟩ := hClopen S Z Z₀ z₀ h₀ hfib
  exact ⟨hred, hcl₀, hfib⟩

/-- `relativeMultiplicativeTypeCentralizer_reductive` in terms of
`HasReductiveIdentityComponent`: under the same hypotheses, every smooth representative `Z` of
`Z_G(H)` has a reductive relative identity component. -/
theorem relativeMultiplicativeTypeCentralizer_hasReductiveIdentityComponent
    (hClopen : IdentityComponentClopenStatement.{u})
    (hField : MultiplicativeTypeCentralizerReductiveStatement.{u})
    {G : GroupScheme S} {H : CommGroupScheme S} (i : H.toGrp ⟶ G)
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H.toGrp) (hG : IsReductive G)
    (hcl : (torusCentralizer i).IsClosedRepresentable)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hZ : Smooth Z.X.hom) : HasReductiveIdentityComponent Z :=
  fun _ _ h₀ =>
    relativeMultiplicativeTypeCentralizer_reductive hClopen hField i hH hG hcl hz hZ h₀

end Langlands.GroupScheme
