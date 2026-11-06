import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Torus.CharacterFaithfullyFlat
import Langlands.GroupScheme.Rational.SplitTorusKernelCentralityProof
import Langlands.GroupScheme.ActionDescent
import Langlands.GroupScheme.Rational.ActionCharacterWeights

/-! # The simple-root quotient torus and its descended conjugation action -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : DecidableEq p.base.support := Classical.decEq _

/-- The split torus with one coordinate for each supplied simple root. -/
def rootScalingTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) p.base.support

theorem rootScalingTorus_isSplit : IsSplitTorus p.rootScalingTorus.toGrp :=
  ⟨p.base.support, inferInstance, ⟨Iso.refl _⟩⟩

/-- The map from the quotient character lattice sends each coordinate to its
actual simple root in the full character lattice of the supplied torus. -/
def rootScalingCharacterMap :
    characterLattice p.rootScalingTorus →+ characterLattice p.torus :=
  (Fintype.linearCombination ℤ (fun a : p.base.support => p.rootDatum.root a)).toAddMonoidHom.comp
    (splitTorus.characterLatticeEquiv k p.base.support).toAddMonoidHom

theorem rootScalingCharacterMap_injective :
    Function.Injective p.rootScalingCharacterMap := by
  change Function.Injective
    ((Fintype.linearCombination ℤ (fun a : p.base.support => p.rootDatum.root a)) ∘
      (splitTorus.characterLatticeEquiv k p.base.support))
  exact p.base.linearIndepOn_root.linearIndependent.fintypeLinearCombination_injective.comp
    (splitTorus.characterLatticeEquiv k p.base.support).injective

/-- The actual projection from the supplied torus to the simple-root torus. -/
def rootScalingProjection : p.torus ⟶ p.rootScalingTorus :=
  p.rootScalingTorus_isSplit.homOfCharacterMap p.rootScalingCharacterMap

theorem rootScalingProjection_character (χ : characterLattice p.rootScalingTorus) :
    p.rootScalingProjection ≫ χ = p.rootScalingCharacterMap χ :=
  p.rootScalingTorus_isSplit.homOfCharacterMap_comp p.rootScalingCharacterMap χ

theorem rootScalingProjection_comap :
    characterLattice.comapHom (CommGroupScheme.groupHom p.rootScalingProjection) =
      p.rootScalingCharacterMap := by
  ext χ
  exact p.rootScalingProjection_character χ

/-- The pullback of the coordinate character is exactly the prescribed simple root. -/
theorem rootScalingProjection_coordinate (a : p.base.support) :
    p.rootScalingProjection ≫ splitTorus.proj _ p.base.support a =
      p.rootDatum.root a := by
  rw [p.rootScalingProjection_character]
  change (Fintype.linearCombination ℤ (fun b : p.base.support => p.rootDatum.root b))
    ((splitTorus.characterLatticeEquiv k p.base.support)
      (splitTorus.proj _ p.base.support a)) = _
  have hcoord : (splitTorus.characterLatticeEquiv k p.base.support)
      (splitTorus.proj _ p.base.support a) = Pi.single a 1 := by
    ext b
    change gmEndEquiv k (splitTorus.single _ p.base.support b ≫
      splitTorus.proj _ p.base.support a) = _
    rw [splitTorus.single_comp_proj]
    by_cases h : b = a
    · subst b
      simp
    · simp [h]
  rw [hcoord, Fintype.linearCombination_apply_single, one_smul]

/-- The projection is flat, surjective and locally of finite presentation;
its kernel is allowed to be nonsmooth. -/
theorem rootScalingProjection_fppf :
    Flat (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left ∧
    Surjective (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left ∧
    LocallyOfFinitePresentation
      (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left := by
  have hf := IsSplitTorus.flat_and_surjective_of_injective_characterPullback
    p.isSplitTorus p.rootScalingTorus_isSplit
    (CommGroupScheme.groupHom p.rootScalingProjection)
    (by rw [p.rootScalingProjection_comap]; exact p.rootScalingCharacterMap_injective)
  exact ⟨hf.1, hf.2, locallyOfFinitePresentation_of_splitTori
    p.isSplitTorus p.rootScalingTorus_isSplit p.rootScalingProjection⟩

/-- Every actual root factors through the simple-root quotient. -/
theorem rootScalingProjection_roots :
    ∀ α ∈ roots p.inclusion, ∃ ψ : characterLattice p.rootScalingTorus,
      α = characterLattice.comapHom
        (CommGroupScheme.groupHom p.rootScalingProjection) ψ := by
  intro α hα
  rw [← p.isRootDatum.2.1] at hα
  obtain ⟨a, rfl⟩ := hα
  have ha := p.base.root_mem_span_int a
  have hrange : Set.range (fun b : p.base.support => p.rootDatum.root b) =
      p.rootDatum.root '' p.base.support := by
    ext χ
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, b.property, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, rfl⟩
  rw [← hrange, ← Fintype.range_linearCombination] at ha
  obtain ⟨v, hv⟩ := ha
  refine ⟨(splitTorus.characterLatticeEquiv k p.base.support).symm v, ?_⟩
  rw [p.rootScalingProjection_comap]
  change p.rootDatum.root a =
    (Fintype.linearCombination ℤ (fun b : p.base.support => p.rootDatum.root b))
      ((splitTorus.characterLatticeEquiv k p.base.support)
        ((splitTorus.characterLatticeEquiv k p.base.support).symm v))
  rw [AddEquiv.apply_symm_apply]
  exact hv.symm

/-- The full scheme-theoretic kernel of the projection maps centrally into `G`. -/
theorem rootScalingProjection_kernel_central :
    IsCentral (kernelι (CommGroupScheme.groupHom p.rootScalingProjection) ≫ p.inclusion) := by
  let := p.isConnectedReductive.smooth
  let := p.isConnectedReductive.connectedSpace
  exact isCentral_kernelι_comp_of_roots_comapHom p.isSplitTorus
    p.rootScalingTorus_isSplit p.inclusion
    (CommGroupScheme.groupHom p.rootScalingProjection) p.rootScalingProjection_roots

theorem rootScalingProjection_kernel_trivial :
    (AutomorphicAction.conjugation p.inclusion).KernelActsTrivially
      (CommGroupScheme.groupHom p.rootScalingProjection) := by
  intro U x g
  rw [AutomorphicAction.restrict_act, AutomorphicAction.conjugation_act]
  have hc := p.rootScalingProjection_kernel_central U x U (𝟙 U) g
  simp only [Grp.comp_hom_hom, Category.id_comp] at hc
  simp only [Category.assoc]
  rw [hc.eq, mul_inv_cancel_right]

/-- Conjugation descends to an actual action of the simple-root quotient torus.
It does not require rational points of this torus to lift to the supplied torus. -/
def rootScalingAction : AutomorphicAction p.rootScalingTorus.toGrp G := by
  letI := p.isSplitTorus.isAffineHom
  letI := p.rootScalingTorus_isSplit.isAffineHom
  letI := isAffine_of_isAffineHom p.torus.X.hom
  letI := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  letI := p.rootScalingProjection_fppf.1
  letI := p.rootScalingProjection_fppf.2.1
  haveI : IsAffineHom
      (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left := inferInstance
  exact AutomorphicAction.quotientAction
    (AutomorphicAction.conjugation p.inclusion)
    (CommGroupScheme.groupHom p.rootScalingProjection)
    p.rootScalingProjection_kernel_trivial

theorem rootScalingAction_restrict :
    p.rootScalingAction.restrict (CommGroupScheme.groupHom p.rootScalingProjection) =
      AutomorphicAction.conjugation p.inclusion := by
  let := p.isSplitTorus.isAffineHom
  let := p.rootScalingTorus_isSplit.isAffineHom
  let := isAffine_of_isAffineHom p.torus.X.hom
  let := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  let := p.rootScalingProjection_fppf.1
  let := p.rootScalingProjection_fppf.2.1
  unfold rootScalingAction
  exact AutomorphicAction.quotientAction_restrict
    (AutomorphicAction.conjugation p.inclusion)
    (CommGroupScheme.groupHom p.rootScalingProjection)
    p.rootScalingProjection_kernel_trivial

end Langlands.GroupScheme.SplitPinning
