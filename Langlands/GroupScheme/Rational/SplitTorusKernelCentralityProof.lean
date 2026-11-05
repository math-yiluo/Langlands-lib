import Langlands.GroupScheme.Rational.SplitTorusKernelCentralityStatement
import Langlands.GroupScheme.Rational.ActionLieRigidity
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Torus.CharacterMapHom
import Langlands.GroupScheme.Torus.CharacterIsomorphism
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Proof: kernels of torus maps through which every root factors are central -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

open RelativeRoot AutomorphicAction

/-- A character pulled back along `f` is trivial on every point of the actual kernel of `f`. -/
theorem characterValue_comapHom_kernel {R : CommRingCat.{u}} {S Q : CommGroupScheme (Spec R)}
    {A : Type u} [CommRing A] [Algebra R A] (f : S.toGrp ⟶ Q.toGrp) (ψ : characterLattice Q)
    (c : Lie.AffinePoints (kernel f) A) :
    Lie.characterValue (characterLattice.comapHom f ψ) (c ≫ (kernelι f).hom.hom) = 1 := by
  have h : (c ≫ (kernelι f).hom.hom) ≫ f.hom.hom = 1 := (kernelPointsEquiv f _ c).property
  have h' : (c ≫ (kernelι f).hom.hom) ≫
      (CommGroupScheme.groupHom (characterLattice.comapHom f ψ)).hom.hom = 1 := by
    rw [characterLattice.comapHom_groupHom, Grp.comp_hom_hom, ← Category.assoc, h,
      MonObj.one_comp]
  simp only [Lie.characterValue, h', map_one]

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {S Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The weight space of a pulled-back character is fixed by the actual kernel. -/
theorem actionWeightSpace_comapHom_le_kernel_lieInvariants (b : AutomorphicAction S.toGrp G)
    (f : S.toGrp ⟶ Q.toGrp) (ψ : characterLattice Q) :
    actionWeightSpace b (characterLattice.comapHom f ψ) ≤
      (b.restrict (kernelι f)).lieInvariants := by
  intro X hX A _ _ c
  rw [actionWeightSpace_eq_lieWeightSpace] at hX
  have h := hX A (c ≫ (kernelι f).hom.hom)
  simp only [Grp.id_hom_hom, Category.comp_id] at h
  rw [characterValue_comapHom_kernel, Units.val_one, one_smul] at h
  simpa only [differential_restrict] using h

/-- If every root of `i` is pulled back along a homomorphism `f` of split tori, then the actual
kernel of `f` maps centrally into `G`. -/
theorem isCentral_kernelι_comp_of_roots_comapHom [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hS : IsSplitTorus S.toGrp) (hQ : IsSplitTorus Q.toGrp) (i : S.toGrp ⟶ G)
    (f : S.toGrp ⟶ Q.toGrp)
    (hroots : ∀ α ∈ roots i, ∃ ψ : characterLattice Q, α = characterLattice.comapHom f ψ) :
    IsCentral (kernelι f ≫ i) := by
  have : IsAffineHom S.X.hom := hS.isAffineHom
  have : IsAffineHom Q.X.hom := hQ.isAffineHom
  have : IsAffineHom (kernel f).X.hom := by
    rw [← Over.w (kernelι f).hom.hom]
    infer_instance
  have : AddGroup.FG (Diagonalizable.homKernelLattice f) :=
    Diagonalizable.homKernelLattice_fg f hS
  let b := (AutomorphicAction.conjugation i).restrict (kernelι f)
  have hInv : b.lieInvariants = ⊤ := by
    apply top_unique
    rw [← iSup_actionWeightSpace_eq_top (AutomorphicAction.conjugation i) hS]
    refine iSup_le fun χ => ?_
    by_cases hbot : actionWeightSpace (AutomorphicAction.conjugation i) χ = ⊥
    · rw [hbot]
      exact bot_le
    obtain ⟨ψ, rfl⟩ : ∃ ψ : characterLattice Q, χ = characterLattice.comapHom f ψ := by
      by_cases hχ : χ = 0
      · exact ⟨0, by rw [hχ, map_zero]⟩
      · apply hroots
        rw [actionWeightSpace_conjugation] at hbot
        exact ⟨hχ, hbot⟩
    exact actionWeightSpace_comapHom_le_kernel_lieInvariants _ f ψ
  have hfixed := fixedSubgroup_eq_top_of_diagonalizable_lieInvariants_eq_top b
    (Diagonalizable.homKernelDiagonalizableIso f hS hQ) hInv
  intro U x V a h
  have hh : h ∈ b.fixedSubgroup.carrier V := by
    rw [hfixed]
    trivial
  have hc := hh V (𝟙 V) (a ≫ x)
  simp only [b, restrict_act, conjugation_act, Category.id_comp] at hc
  have hc' : (a ≫ x ≫ (kernelι f ≫ i).hom.hom) * h *
      (a ≫ x ≫ (kernelι f ≫ i).hom.hom)⁻¹ = h := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using hc
  exact (mul_inv_eq_iff_eq_mul).mp hc'

/-- If every root of `i` factors through `t`, the actual kernel of `t` maps centrally into `G`.
The kernel of `t` lies in the kernel of the map `ρ` from `T` to the split torus with one
coordinate for each root, and the previous theorem applies to `ρ`. -/
theorem splitTorusKernelCentrality : SplitTorusKernelCentralityStatement.{u} := by
  intro k _ G _ _ _ T T' hT i t hroots
  classical
  -- The finite set of roots, as an index type.
  let J := {α : characterLattice T // α ∈ roots i}
  have hfin : (roots i).Finite := by
    rw [← relativeRoots_eq_roots]
    exact hT.finite_relativeRoots i
  have : Finite J := hfin.to_subtype
  let := Fintype.ofFinite J
  let Q := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) J
  have hQ : IsSplitTorus Q.toGrp := ⟨J, inferInstance, ⟨Iso.refl _⟩⟩
  let w : characterLattice Q →+ characterLattice T :=
    (Fintype.linearCombination ℤ (fun j : J => (j : characterLattice T))).toAddMonoidHom.comp
      (splitTorus.characterLatticeEquiv k J).toAddMonoidHom
  let ρ : T ⟶ Q := hQ.homOfCharacterMap w
  have hρ : ∀ j : J,
      ρ ≫ (splitTorus.characterLatticeEquiv k J).symm (Pi.single j 1) = j.val := by
    intro j
    rw [hQ.homOfCharacterMap_comp]
    change (Fintype.linearCombination ℤ fun j : J => (j : characterLattice T))
      ((splitTorus.characterLatticeEquiv k J)
        ((splitTorus.characterLatticeEquiv k J).symm (Pi.single j 1))) = j.val
    rw [AddEquiv.apply_symm_apply, Fintype.linearCombination_apply_single, one_smul]
  have hcent := isCentral_kernelι_comp_of_roots_comapHom hT hQ i (CommGroupScheme.groupHom ρ)
    (fun α hα => ⟨(splitTorus.characterLatticeEquiv k J).symm (Pi.single ⟨α, hα⟩ 1),
      (hρ ⟨α, hα⟩).symm⟩)
  -- The kernel of `t` maps into the kernel of `ρ`.
  have hzero : CommGroupScheme.kernelι t ≫ ρ = 0 := by
    apply hQ.hom_ext_of_characters
    intro χ
    rw [Category.assoc, hQ.homOfCharacterMap_comp, Limits.zero_comp]
    simp only [w, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      Fintype.linearCombination_apply, Preadditive.comp_sum, Preadditive.comp_zsmul]
    refine Finset.sum_eq_zero fun j _ => ?_
    obtain ⟨α', hα'⟩ := hroots j.val j.property
    rw [hα', ← Category.assoc, CommGroupScheme.kernelι_comp, Limits.zero_comp, smul_zero]
  rw [← CommGroupScheme.kernelLift_ι ρ (CommGroupScheme.kernelι t) hzero]
  exact hcent.comp (CommGroupScheme.groupHom (CommGroupScheme.kernelLift ρ _ hzero))

end Langlands.GroupScheme
