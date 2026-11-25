/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits

/-!
# Zariski locality of preservation of pro-etale inverse-image limits

Source: Stacks Project, Tag 09AA, proof of lemma-closed-immersion.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def inverseImageRestrictionIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] :
    proEtaleSheafInverseImage f (Type (u + 1)) ≅
      (MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
        (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
          (Type (u + 1)) (ProEt.topology Y) (ProEt.topology X) := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) _root_.trivial).sheafPushforwardContinuous
      (E := Type (u + 1)) (ProEt.topology Y) (ProEt.topology X)
  exact (proEtaleSheafAdjunction f (Type (u + 1))).leftAdjointUniq a

/-- Restriction along a weakly etale morphism preserves all limits of the fixed size.

Source: Stacks Project, Tag 09AA, using the pro-etale over-category map/base-change
adjunction and sectionwise limit preservation of restriction.

Proof: the inverse-image functor is identified with the sheaf pushforward induced by
composition on pro-etale objects, by uniqueness of left adjoints.  This restriction
functor preserves limits sectionwise, hence the inverse image preserves all limits.
-/
theorem restriction_preservesLimits {X Y : Scheme.{u}} (f : Y ⟶ X)
    [WeaklyEtale f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1))) := by
  exact preservesLimits_of_natIso (inverseImageRestrictionIso f).symm

private noncomputable def inverseImageCompIso {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) :
    proEtaleSheafInverseImage (f ≫ g) (Type (u + 1)) ≅
      proEtaleSheafInverseImage g (Type (u + 1)) ⋙
        proEtaleSheafInverseImage f (Type (u + 1)) := by
  let a := (proEtaleSheafAdjunction g (Type (u + 1))).comp
    (proEtaleSheafAdjunction f (Type (u + 1)))
  let e := Functor.sheafPushforwardContinuousComp'
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) f g).symm
    (Type (u + 1)) (ProEt.topology X) (ProEt.topology Y) (ProEt.topology Z)
  exact (proEtaleSheafAdjunction (f ≫ g) (Type (u + 1))).leftAdjointUniq
    (a.ofNatIsoRight e)

/-- Preservation of small limits by inverse image is local on affine opens of the target.

Source: Stacks Project, Tag 09AA, proof of lemma-closed-immersion.
(auxiliary; not a blueprint node)

Proof: for every affine open U in X, the Cartesian square with Y restricted over U
identifies the two composites of inverse images by uniqueness of adjoints.  Restriction
along either open immersion is sectionwise, so commutes with limits.  Consequently the
restriction of the limit comparison for f is the comparison for the restricted morphism,
which is invertible by hypothesis.  The inverse images of the affine opens cover Y.
On every pro-etale object over Y their pullbacks form a covering family; the local inverses
of a sheaf morphism agree on pairwise intersections and glue uniquely.  Thus the original
limit comparison is invertible, proving the claim for every diagram of the fixed size.
This argument applies also to empty schemes and imposes no separation condition.
-/
theorem proEtale_inverseImage_limits_zariski_local
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : ∀ U : X.affineOpens,
      PreservesLimitsOfSize.{u + 1, u + 1}
        (proEtaleSheafInverseImage (f ∣_ U.1) (Type (u + 1)))) :
    PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f (Type (u + 1))) := by
  let K := fun U : X.affineOpens ↦
    proEtaleSheafInverseImage (f ⁻¹ᵁ U.1).ι (Type (u + 1))
  have hK : ∀ U, PreservesLimitsOfSize.{u + 1, u + 1} (K U) :=
    fun U ↦ restriction_preservesLimits (f ⁻¹ᵁ U.1).ι
  have hcomp : ∀ U, PreservesLimitsOfSize.{u + 1, u + 1}
      (proEtaleSheafInverseImage f (Type (u + 1)) ⋙ K U) := by
    intro U
    let := h U
    let := restriction_preservesLimits U.1.ι
    have : PreservesLimitsOfSize.{u + 1, u + 1}
        (proEtaleSheafInverseImage (f ∣_ U.1 ≫ U.1.ι) (Type (u + 1))) :=
      preservesLimits_of_natIso (inverseImageCompIso (f ∣_ U.1) U.1.ι).symm
    rw [morphismRestrict_ι] at this
    exact preservesLimits_of_natIso (inverseImageCompIso (f ⁻¹ᵁ U.1).ι f)
  have hc : Presieve.ofArrows (fun U : X.affineOpens ↦ (f ⁻¹ᵁ U.1).toScheme)
      (fun U ↦ (f ⁻¹ᵁ U.1).ι) ∈ proetalePrecoverage Y := by
    apply zariskiPrecoverage_le_proetalePrecoverage
    apply (ofArrows_mem_precoverage_iff _).mpr
    refine ⟨?_, fun U ↦ inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U.1).ι)⟩
    intro y
    have hy : f.base y ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X, TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨U, hU⟩ := hy
    exact ⟨U, by simpa using hU⟩
  have hcon : JointlyReflectIsomorphisms K := by
    constructor
    intro F G a ha
    have hr (U : X.affineOpens) : IsIso
        (((MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
          (inferInstance : WeaklyEtale (f ⁻¹ᵁ U.1).ι)).sheafPushforwardContinuous
            (Type (u + 1)) (ProEt.topology (f ⁻¹ᵁ U.1)) (ProEt.topology Y)).map a) := by
      exact (NatIso.isIso_map_iff (inverseImageRestrictionIso (f ⁻¹ᵁ U.1).ι) a).mp (ha U)
    refine Sheaf.isIso_of_isIso_app_of_mem _ a fun V ↦
      ⟨_, ProEt.ofArrows_baseChange_mem_topology V
        (fun U : X.affineOpens ↦ (f ⁻¹ᵁ U.1).ι) hc, ?_⟩
    rintro T k ⟨W, b, Z, ⟨U⟩, rfl⟩
    let g := (f ⁻¹ᵁ U.1).ι
    let p := b.left ≫ pullback.snd V.hom g
    have hp : p ≫ g = T.hom := by
      dsimp [p]
      rw [Category.assoc, ← pullback.condition]
      exact MorphismProperty.Over.w b
    have hpwe : WeaklyEtale p :=
      MorphismProperty.of_postcomp (W := @WeaklyEtale) (W' := @WeaklyEtale)
        p g (inferInstance : WeaklyEtale g) (by rw [hp]; exact T.prop)
    have h1 : IsIso
        ((((MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
          (inferInstance : WeaklyEtale g)).sheafPushforwardContinuous
            (Type (u + 1)) (ProEt.topology (f ⁻¹ᵁ U.1)) (ProEt.topology _)).map a).hom.app
              (op (MorphismProperty.Over.mk ⊤ p hpwe))) := by
      let := hr U
      infer_instance
    have e : (MorphismProperty.Over.map (⊤ : MorphismProperty Scheme.{u})
        (inferInstance : WeaklyEtale g)).obj (MorphismProperty.Over.mk ⊤ p hpwe) ≅ T :=
      MorphismProperty.Over.isoMk (Iso.refl _) (by simpa using hp.symm)
    exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ a.hom _ _ e.op h1
  constructor
  intro J _
  constructor
  intro D
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit D)
  apply hcon.jointlyReflectsLimit
  intro U
  let := hcomp U
  exact isLimitOfPreserves (proEtaleSheafInverseImage f (Type (u + 1)) ⋙ K U)
    (limit.isLimit D)

end AlgebraicGeometry.Scheme
