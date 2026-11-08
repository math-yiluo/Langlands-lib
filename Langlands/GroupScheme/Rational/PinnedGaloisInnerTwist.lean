import Langlands.GroupScheme.Reductive.PinnedGaloisDatum
import Langlands.GroupScheme.Reductive.PinnedWeylInner
import Langlands.GroupScheme.Reductive.BasedRootDatumProjection
import Langlands.GroupScheme.Rational.FiniteGaloisBaseChangeDiscrepancy
import Langlands.GroupScheme.Rational.UnipotentRadicalDescent
import Langlands.GroupScheme.Adjoint.Isomorphism

/-! # Galois twists of pinned descents are inner -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme

namespace IsAdjointQuotient

variable {k : Type u} [Field k] {G H A B : GroupScheme (Spec (CommRingCat.of k))}
  {q : G ⟶ A} {p : H ⟶ B} (hq : IsAdjointQuotient q) (hp : IsAdjointQuotient p)

/-- Conjugating the inner automorphism of a base point along an isomorphism gives the inner
automorphism of the image point under the induced isomorphism of adjoint quotients. -/
theorem basePointIso_trans (e : G ≅ H) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ A.X) :
    hq.innerAction.basePointIso x ≪≫ e =
      e ≪≫ hp.innerAction.basePointIso (x ≫ (hq.mapIso hp e).hom.hom.hom) := by
  apply Iso.ext
  apply hom_ext_points
  intro T g
  rw [Iso.trans_hom, Iso.trans_hom, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc,
    ← Category.assoc, AutomorphicAction.comp_basePointIso_hom,
    AutomorphicAction.comp_basePointIso_hom, hq.mapIso_innerAction hp e, constantPoint_comp]

end IsAdjointQuotient

namespace SplitPinning

open Descent

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom ((GroupScheme.baseChange (fieldMap k K)).obj H).X.hom]
  (p : SplitPinning ((GroupScheme.baseChange (fieldMap k K)).obj H))
  (ρ : (K ≃ₐ[k] K) →* p.basedRootDatumAut)

/-- The automorphism of the base change of a ground-field group obtained by inverting
the pinned semilinear lift of `σ` and then applying the canonical descent identification. -/
def galoisTwistIso (σ : K ≃ₐ[k] K) :
    (GroupScheme.baseChange (fieldMap k K)).obj H ≅
      (GroupScheme.baseChange (fieldMap k K)).obj H :=
  (p.galoisSemilinearIso ρ σ).symm ≪≫
    descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) H

variable [FiniteDimensional k K] [IsGalois k K]

private theorem pullbackComparison_eq_descent {S T : Scheme.{u}} (f : T ⟶ S) (a : T ⟶ T)
    (h : a ≫ f = f) (X : GroupScheme S) :
    pullbackComparison f a f h X = descentBaseChangeIso f a h X := rfl

/-- Pulling the identification of a descent solution back along `Spec σ` composes it
with the Galois twist automorphism. -/
theorem pullIso_solution_iso (s : Solution (p.galoisDatum ρ)) (σ : K ≃ₐ[k] K) :
    pullIso (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) (galoisBaseMap_over k K σ)
        s.iso = s.iso ≪≫ p.galoisTwistIso ρ σ := by
  obtain ⟨j, rfl⟩ := (galoisIndexEquiv k K).surjective σ
  let q := finiteGaloisComponent k K j
  let a := galoisBaseMap k K (galoisIndexEquiv k K j)
  have hq₁ : q ≫ fst (fieldMap k K) = 𝟙 _ := finiteGaloisComponent_fst k K j
  have hq₂ : q ≫ snd (fieldMap k K) = a := finiteGaloisComponent_snd k K j
  have hc : pullHom q hq₁ hq₂
      ((GroupScheme.baseChange (fst (fieldMap k K))).map s.iso.hom ≫
        (p.galoisDatum ρ).overlap.hom) =
    pullHom q hq₁ hq₂
      ((canonicalOverlap (fieldMap k K) s.obj).hom ≫
        (GroupScheme.baseChange (snd (fieldMap k K))).map s.iso.hom) :=
    congrArg (pullHom q hq₁ hq₂) s.compatible
  rw [pullHom_comp q hq₁ hq₁ hq₂, pullHom_map,
    pullHom_comp q hq₁ hq₂ hq₂, pullHom_map, ← pullIso_hom, ← pullIso_hom,
    pullIso_galoisDatum,
    pullIso_canonicalOverlap_eq (fieldMap k K) s.obj a
      (galoisBaseMap_over k K (galoisIndexEquiv k K j))] at hc
  have hid : (GroupScheme.baseChange (𝟙 _)).map s.iso.hom ≫
      (baseChangeIdIso ((GroupScheme.baseChange (fieldMap k K)).obj H)).hom =
    (baseChangeIdIso ((GroupScheme.baseChange (fieldMap k K)).obj s.obj)).hom ≫ s.iso.hom :=
    (((Functor.mapGrpNatIso Over.pullbackId) ≪≫ Functor.mapGrpIdIso).hom.naturality
      s.iso.hom)
  simp only [semilinearComponent, Iso.trans_hom, Iso.symm_hom] at hc
  rw [← Category.assoc, hid, Category.assoc, Category.assoc, cancel_epi] at hc
  apply Iso.ext
  rw [pullIso_hom, Iso.trans_hom, galoisTwistIso, Iso.trans_hom, Iso.symm_hom,
    ← Category.assoc, hc, ← pullIso_hom]
  simp only [pullIso, Iso.trans_hom, Iso.symm_hom, pullbackComparison_eq_descent,
    Category.assoc]
  rfl

omit [FiniteDimensional k K] [IsGalois k K] in
/-- Precomposing the pinned torus with the Galois twist is the inverse pinned torus lift
followed by a supplied torus comparison over the canonical descent identification. -/
theorem inclusion_comp_galoisTwistIso (σ : K ≃ₐ[k] K)
    (τ : (CommGroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus ≅ p.torus)
    (hτ : (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion ≫
        (descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) H).hom =
      CommGroupScheme.groupHom τ.hom ≫ p.inclusion) :
    p.inclusion ≫ (p.galoisTwistIso ρ σ).hom =
      CommGroupScheme.groupHom
          ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.symm ≪≫ τ).hom ≫
        p.inclusion := by
  have hsq := (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).square
  have h' : p.inclusion ≫ (p.galoisSemilinearIso ρ σ).inv =
      CommGroupScheme.groupHom (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.inv ≫
        (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc]
    change _ = _ ≫ (p.baseChangeAlong σ.toRingEquiv).inclusion ≫
      (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).groupIso.hom
    rw [hsq, ← Category.assoc]
    change p.inclusion = CommGroupScheme.groupHom
      ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.inv ≫
        (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.hom) ≫ p.inclusion
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  rw [galoisTwistIso, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h', Category.assoc, hτ]
  rfl

omit [FiniteDimensional k K] [IsGalois k K] in
/-- If a full root-datum automorphism `δ` is the canonical character pullback along `Spec σ`
followed by `τ`, and the based automorphism `ρ σ` differs from `δ` by the Weyl group, then
the torus automorphism `φ_σ⁻¹ ≫ τ` acts on characters through the actual Weyl image. -/
theorem characterAut_galoisTwistTorus_mem_weylImage [Mono p.inclusion.hom.hom.left]
    (σ : K ≃ₐ[k] K)
    (τ : (CommGroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus ≅ p.torus)
    (δ : p.rootDatum.Aut)
    (hδ : ∀ χ, δ.weightEquiv χ =
      τ.inv ≫ characterLattice.baseChange (galoisBaseMap k K σ) p.torus χ)
    (hw : (ρ σ).val * δ⁻¹ ∈ p.rootDatum.weylGroup) :
    characterAut ((p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso.symm ≪≫ τ) ∈
      weylImage p.inclusion := by
  have hw' : δ * (ρ σ).val⁻¹ ∈ p.rootDatum.weylGroup := by
    simpa only [mul_inv_rev, inv_inv] using p.rootDatum.weylGroup.inv_mem hw
  refine p.isRootDatum.abstractWeylImage_le ⟨δ * (ρ σ).val⁻¹, hw', ?_⟩
  let φt := (p.semilinearPinnedIso σ.toRingEquiv (ρ σ)).torusIso
  let e := p.semilinearRootDatumEquiv σ.toRingEquiv (ρ σ)
  have hc : (characterLattice.congr φt).toIntLinearEquiv = e.weightEquiv :=
    (p.baseChangeAlong σ.toRingEquiv).isoOfRootDatumEquiv_character p e
      (p.semilinearRootDatumEquiv_simple_iff σ.toRingEquiv (ρ σ))
  apply LinearEquiv.ext
  intro χ
  have key : φt.hom ≫ χ = characterLattice.baseChange (galoisBaseMap k K σ) p.torus
      ((ρ σ).val⁻¹.weightEquiv χ) := by
    apply e.weightEquiv.injective
    have h1 : e.weightEquiv (φt.hom ≫ χ) = χ := by
      rw [← hc]
      exact φt.inv_hom_id_assoc χ
    rw [h1]
    change χ = (ρ σ).val.weightEquiv
      ((p.baseChangeAlongRootDatumEquiv σ.toRingEquiv).weightEquiv.symm
        ((p.baseChangeAlongRootDatumEquiv σ.toRingEquiv).weightEquiv
          ((ρ σ).val⁻¹.weightEquiv χ)))
    rw [LinearEquiv.symm_apply_apply, RootPairing.Equiv.weightEquiv_inv]
    exact (LinearEquiv.apply_symm_apply _ χ).symm
  rw [map_mul, LinearEquiv.mul_apply, RootPairing.Equiv.weightHom_apply,
    RootPairing.Equiv.weightHom_apply, hδ, characterAut_apply, Iso.trans_inv, Iso.symm_inv,
    Category.assoc]
  exact congrArg (τ.inv ≫ ·) key.symm

omit [FiniteDimensional k K] [IsGalois k K] in
/-- The Galois twist automorphism is inner: it is the inner automorphism of a rational point
of any actual adjoint quotient of the split group. -/
theorem exists_adjointPoint_galoisTwistIso [Mono p.inclusion.hom.hom.left]
    {A : GroupScheme (Spec (CommRingCat.of K))}
    {q : (GroupScheme.baseChange (fieldMap k K)).obj H ⟶ A} (hq : IsAdjointQuotient q)
    (σ : K ≃ₐ[k] K)
    (τ : (CommGroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus ≅ p.torus)
    (hτ : (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion ≫
        (descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) H).hom =
      CommGroupScheme.groupHom τ.hom ≫ p.inclusion)
    (δ : p.rootDatum.Aut)
    (hδ : ∀ χ, δ.weightEquiv χ =
      τ.inv ≫ characterLattice.baseChange (galoisBaseMap k K σ) p.torus χ)
    (hw : (ρ σ).val * δ⁻¹ ∈ p.rootDatum.weylGroup) :
    ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
      hq.innerAction.basePointIso x = p.galoisTwistIso ρ σ :=
  p.exists_adjointPoint_of_weylImage hq (p.galoisTwistIso ρ σ) _
    (p.inclusion_comp_galoisTwistIso ρ σ τ hτ)
    (p.characterAut_galoisTwistTorus_mem_weylImage ρ σ τ δ hδ hw)

/-- If the full Galois action on the root datum is the canonical character pullback through
torus comparisons lying over the descent identifications, and `ρ` agrees with it modulo the
Weyl group, then every descent solution of the pinned Galois datum has all-test inner
discrepancy with respect to any actual adjoint quotient of its ground-field group. -/
theorem hasInnerDiscrepancy_solution [Mono p.inclusion.hom.hom.left]
    (τ : ∀ σ : K ≃ₐ[k] K,
      (CommGroupScheme.baseChange (galoisBaseMap k K σ)).obj p.torus ≅ p.torus)
    (hτ : ∀ σ, (GroupScheme.baseChange (galoisBaseMap k K σ)).map p.inclusion ≫
        (descentBaseChangeIso (fieldMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) H).hom =
      CommGroupScheme.groupHom (τ σ).hom ≫ p.inclusion)
    (δ : (K ≃ₐ[k] K) → p.rootDatum.Aut)
    (hδ : ∀ σ χ, (δ σ).weightEquiv χ =
      (τ σ).inv ≫ characterLattice.baseChange (galoisBaseMap k K σ) p.torus χ)
    (hw : ∀ σ, (ρ σ).val * (δ σ)⁻¹ ∈ p.rootDatum.weylGroup)
    {A' : GroupScheme (Spec (CommRingCat.of K))}
    {q' : (GroupScheme.baseChange (fieldMap k K)).obj H ⟶ A'} (hq' : IsAdjointQuotient q')
    (s : Solution (p.galoisDatum ρ)) {A : GroupScheme (Spec (CommRingCat.of k))}
    {q : s.obj ⟶ A} (hq : IsAdjointQuotient q) :
    (LocalGroupIso.ofBaseChangeIso (U := Langlands.AlgebraicGeometry.PointTopology.ringTest k K) s.iso).HasInnerDiscrepancy hq.innerAction := by
  apply IsAdjointQuotient.hasInnerDiscrepancy_of_galois_baseChange hq s.iso
  intro σ
  let hqK := adjointQuotientBaseChangeStatement.isAdjointQuotient (K := K) hq
  let M := hqK.mapIso hq' s.iso
  obtain ⟨y, hy⟩ := p.exists_adjointPoint_galoisTwistIso ρ hq' σ (τ σ) (hτ σ) (δ σ)
    (hδ σ) (hw σ)
  refine ⟨y ≫ M.inv.hom.hom, ?_⟩
  have hxy : (y ≫ M.inv.hom.hom) ≫ M.hom.hom.hom = y := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id]
    exact Category.comp_id y
  rw [hqK.basePointIso_trans hq' s.iso, hxy, hy, p.pullIso_solution_iso ρ s σ]

end SplitPinning

end Langlands.GroupScheme
