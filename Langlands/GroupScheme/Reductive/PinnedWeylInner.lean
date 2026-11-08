import Langlands.GroupScheme.Reductive.RootScalingAutomorphism
import Langlands.GroupScheme.Reductive.PinnedRigidityProof
import Langlands.GroupScheme.Adjoint.InnerAction
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # Weyl-normalizing automorphisms of pinned groups are inner -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (p : SplitPinning G) {q : G ⟶ A} (hq : IsAdjointQuotient q)

include hq in
/-- The actual kernel of the simple-root projection maps trivially to the
adjoint quotient. -/
theorem rootScalingProjection_kernel_comp_adjoint :
    kernelι (CommGroupScheme.groupHom p.rootScalingProjection) ≫ (p.inclusion ≫ q) = 0 := by
  apply Grp.hom_ext
  change (kernelι (CommGroupScheme.groupHom p.rootScalingProjection)).hom.hom ≫
      p.inclusion.hom.hom ≫ q.hom.hom = 1
  rw [← Category.assoc]
  apply (hq.mem_center_iff_comp_eq_one _ _).mp
  simpa only [Category.id_comp, Grp.comp_hom_hom] using
    p.rootScalingProjection_kernel_central _
      (𝟙 (kernel (CommGroupScheme.groupHom p.rootScalingProjection)).X)

include hq in
/-- The simple-root quotient torus maps to the adjoint quotient, compatibly
with the supplied torus. -/
def rootScalingAdjointHom : p.rootScalingTorus.toGrp ⟶ A := by
  letI := p.isSplitTorus.isAffineHom
  letI := p.rootScalingTorus_isSplit.isAffineHom
  letI := isAffine_of_isAffineHom p.torus.X.hom
  letI := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  letI := p.rootScalingProjection_fppf.1
  letI := p.rootScalingProjection_fppf.2.1
  haveI : IsAffineHom
      (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left := inferInstance
  exact FpqcHomDescent.hom (CommGroupScheme.groupHom p.rootScalingProjection)
    (p.inclusion ≫ q) (p.rootScalingProjection_kernel_comp_adjoint hq)

@[reassoc]
theorem rootScalingProjection_comp_adjointHom :
    CommGroupScheme.groupHom p.rootScalingProjection ≫ p.rootScalingAdjointHom hq =
      p.inclusion ≫ q := by
  let := p.isSplitTorus.isAffineHom
  let := p.rootScalingTorus_isSplit.isAffineHom
  let := isAffine_of_isAffineHom p.torus.X.hom
  let := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  let := p.rootScalingProjection_fppf.1
  let := p.rootScalingProjection_fppf.2.1
  have : IsAffineHom
      (CommGroupScheme.groupHom p.rootScalingProjection).hom.hom.left := inferInstance
  exact FpqcHomDescent.fac _ _ _

/-- The inner action restricted to the simple-root quotient torus is the
descended conjugation action of that torus. -/
theorem innerAction_restrict_rootScalingAdjointHom {T : Over (Spec (CommRingCat.of k))}
    (x : T ⟶ p.rootScalingTorus.X) (g : T ⟶ G.X) :
    hq.innerAction.act (x ≫ (p.rootScalingAdjointHom hq).hom.hom) g =
      p.rootScalingAction.act x g := by
  let := p.isSplitTorus.isAffineHom
  let := p.rootScalingTorus_isSplit.isAffineHom
  let := isAffine_of_isAffineHom p.torus.X.hom
  let := isAffine_of_isAffineHom p.rootScalingTorus.X.hom
  let := p.rootScalingProjection_fppf.1
  let := p.rootScalingProjection_fppf.2.1
  apply AutomorphicAction.hom_ext_of_local_quotient_lift
    (CommGroupScheme.groupHom p.rootScalingProjection) x
  intro V b h hb
  rw [hq.innerAction.naturality, p.rootScalingAction.naturality, ← Category.assoc, hb,
    Category.assoc, ← Grp.comp_hom_hom, p.rootScalingProjection_comp_adjointHom,
    Grp.comp_hom_hom, ← Category.assoc, hq.innerAction_act_lift,
    ← AutomorphicAction.restrict_act, p.rootScalingAction_restrict,
    AutomorphicAction.conjugation_act]

omit [IsAffineHom G.X.hom] in
/-- A quotient point lifted from a base point acts by the corresponding inner
automorphism. -/
theorem innerAction_basePointIso_lift (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    hq.innerAction.basePointIso (n ≫ q.hom.hom) = G.innerIso n := by
  apply Iso.ext
  apply hom_ext_points
  intro T g
  rw [AutomorphicAction.comp_basePointIso_hom, comp_innerIso_hom]
  have hc : A.constantPoint (n ≫ q.hom.hom) T = G.constantPoint n T ≫ q.hom.hom := by
    unfold constantPoint
    rw [Category.assoc]
  rw [hc, hq.innerAction_act_lift]

/-- A simple-root scaling point, mapped to the adjoint quotient, acts by the
corresponding root-scaling automorphism. -/
theorem innerAction_basePointIso_rootScaling (c : p.base.support → kˣ) :
    hq.innerAction.basePointIso
        (p.rootScalingPoint c ≫ (p.rootScalingAdjointHom hq).hom.hom) =
      p.rootScalingIso c := by
  apply Iso.ext
  apply hom_ext_points
  intro T g
  rw [AutomorphicAction.comp_basePointIso_hom]
  change _ = g ≫ (p.rootScalingAction.basePointIso (p.rootScalingPoint c)).hom.hom.hom
  rw [AutomorphicAction.comp_basePointIso_hom]
  have hc : A.constantPoint (p.rootScalingPoint c ≫ (p.rootScalingAdjointHom hq).hom.hom) T =
      constantPoint p.rootScalingTorus.toGrp (p.rootScalingPoint c) T ≫
        (p.rootScalingAdjointHom hq).hom.hom := by
    unfold constantPoint
    rw [Category.assoc]
  rw [hc, p.innerAction_restrict_rootScalingAdjointHom hq]

/-- An automorphism fixing the pinned torus is a simple-root scaling. -/
theorem exists_eq_rootScalingIso (f : G ≅ G) (hf : p.inclusion ≫ f.hom = p.inclusion) :
    ∃ c : p.base.support → kˣ, f = p.rootScalingIso c := by
  have hw (a : p.base.support) :
      Lie.targetMapLinear f.hom (CommRingCat.of k) (p.pinning.rootVector a) ∈
        weightSpace p.inclusion (p.rootDatum.root a) := by
    have h := lieKernelHomLinear_mem_weightSpace f.hom p.inclusion (p.rootDatum.root a)
      (p.pinning.rootVector_mem a)
    rwa [hf] at h
  let d : p.base.support → k := fun a => (p.pinning.trivialization a).symm ⟨_, hw a⟩
  have hd (a : p.base.support) :
      Lie.targetMapLinear f.hom (CommRingCat.of k) (p.pinning.rootVector a) =
        d a • p.pinning.rootVector a := by
    rw [← p.pinning.trivialization_apply_val]
    simp only [d, LinearEquiv.apply_symm_apply]
  have hd0 (a : p.base.support) : d a ≠ 0 := by
    intro h0
    have h := hd a
    rw [h0, zero_smul] at h
    apply p.pinning.rootVector_ne_zero a
    have h' := congrArg (Lie.targetMapLinear f.inv (CommRingCat.of k)) h
    rwa [Lie.targetMapLinear_hom_inv, map_zero] at h'
  let c : p.base.support → kˣ := fun a => Units.mk0 (d a) (hd0 a)
  refine ⟨c, ?_⟩
  have hr : f ≪≫ (p.rootScalingIso c).symm = Iso.refl G := by
    apply pinnedAutomorphismRigidity k G p
    · change p.inclusion ≫ f.hom ≫ (p.rootScalingIso c).inv = p.inclusion
      rw [← Category.assoc, hf, Iso.comp_inv_eq, p.rootScalingIso_inclusion]
    · intro a
      change Lie.targetMapLinear (f.hom ≫ (p.rootScalingIso c).inv) (CommRingCat.of k)
        (p.pinning.rootVector a) = _
      rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, hd a]
      have hs := p.rootScalingIso_rootVector c a
      change _ = (d a) • p.pinning.rootVector a at hs
      rw [← hs, Lie.targetMapLinear_hom_inv]
  calc f = (f ≪≫ (p.rootScalingIso c).symm) ≪≫ p.rootScalingIso c := by
        ext; simp
    _ = p.rootScalingIso c := by rw [hr, Iso.refl_trans]

/-- An automorphism normalizing the pinned torus through an element of the actual
Weyl image is the action of a ground-field point of the adjoint quotient. -/
theorem exists_adjointPoint_of_weylImage [Mono p.inclusion.hom.hom.left]
    (f : G ≅ G) (σ : p.torus ≅ p.torus)
    (hf : p.inclusion ≫ f.hom = CommGroupScheme.groupHom σ.hom ≫ p.inclusion)
    (hσ : characterAut σ ∈ weylImage p.inclusion) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X,
      hq.innerAction.basePointIso x = f := by
  obtain ⟨n, hn⟩ := hσ
  have hτ : normalizingAut p.inclusion n = σ := by
    have hinv : (normalizingAut p.inclusion n).inv = σ.inv := by
      apply p.isSplitTorus.hom_ext_characters
      intro χ
      have h := congrArg (fun e : characterLattice p.torus ≃ₗ[ℤ] characterLattice p.torus =>
        e χ) hn
      exact h
    apply Iso.ext
    rw [← Category.comp_id (normalizingAut p.inclusion n).hom, ← σ.inv_hom_id, ← hinv,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hnorm : IsNormalizingPoint p.inclusion n σ :=
    hτ ▸ isNormalizingPoint_normalizingAut p.inclusion n
  have hf' : p.inclusion ≫ (f ≪≫ (G.innerIso n.val).symm).hom = p.inclusion := by
    change p.inclusion ≫ f.hom ≫ (G.innerIso n.val).inv = p.inclusion
    rw [← Category.assoc, hf, Iso.comp_inv_eq]
    exact hnorm.symm
  obtain ⟨c, hc⟩ := p.exists_eq_rootScalingIso _ hf'
  refine ⟨(n.val ≫ q.hom.hom) *
    (p.rootScalingPoint c ≫ (p.rootScalingAdjointHom hq).hom.hom), ?_⟩
  have hfc : f = p.rootScalingIso c ≪≫ G.innerIso n.val := by
    rw [← hc]
    ext
    simp
  rw [hfc]
  apply Iso.ext
  apply hom_ext_points
  intro T g
  rw [AutomorphicAction.comp_basePointIso_hom, constantPoint_mul,
    AutomorphicAction.act_mul_left, ← AutomorphicAction.comp_basePointIso_hom,
    ← AutomorphicAction.comp_basePointIso_hom, p.innerAction_basePointIso_rootScaling hq,
    innerAction_basePointIso_lift hq]
  rfl

end Langlands.GroupScheme.SplitPinning
