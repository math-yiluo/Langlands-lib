/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale

import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia

/-! Generic section comparison for a normalization over a local trait.

## References

* Stacks Project, Tag 0EYJ, local trait reduction, and Tag 0EYI
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The normalization over the local trait agrees with the original cover on a generic section.

Let `a: Spec 𝒪_{S,s} ⟶ S` be the canonical morphism, `n` the base change along
`C ×_S Spec 𝒪_{S,s} ⟶ C` of the relative normalization of `C` in the finite étale cover
`PA` of `C_U`, and `τ` the section of `C ×_S Spec 𝒪_{S,s}` induced by `σ`. For an injective
ring map `δ: 𝒪_{S,s} →+* A` into a domain with fraction field `K`, the composite
`𝒪_{S,s} → A → K` extends to `ε: k(S) →+* K`, and the pullback of `n` along
`t: Spec K ⟶ Spec 𝒪_{S,s}` followed by `τ` is identified over `Spec K` with the pullback of
the Galois cover `Z` along `b = Spec ε` followed by the generic section `sη`. -/
theorem GaloisCover.trait_normalization_generic_section_comparison {S C : Scheme.{u}}
    [IsNoetherian S] [IsIntegral S]
    (c : C ⟶ S) (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    {G : Type (u + 1)} [Group G] [Finite G]
    {Cη : Scheme.{u}} (j : Cη ⟶ C) (sη : Spec S.functionField ⟶ Cη)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη)
    (U : S.Opens) (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU) (s : S)
    (A : CommRingCat.{u}) [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] (δ : S.presheaf.stalk s →+* A) (hδ : Function.Injective δ) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let a := S.fromSpecStalk s
    let n := pullback.snd (PA.obj.hom ≫ (c ⁻¹ᵁ U).ι).fromNormalization (pullback.fst c a)
    let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
      pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
    let t := Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ))
    ∃ ε : S.functionField →+* K,
      ε.comp (algebraMap (S.presheaf.stalk s) S.functionField) = (algebraMap A K).comp δ ∧
      ∃ β : pullback n (t ≫ τ) ≅ pullback Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη),
        β.hom ≫ pullback.snd Z.π (Spec.map (CommRingCat.ofHom ε) ≫ sη) =
          pullback.snd n (t ≫ τ) := by
  classical
  let : IsFinite PA.obj.hom := PA.property
  let : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  dsimp only
  let a := S.fromSpecStalk s
  let i := (c ⁻¹ᵁ U).ι
  let f := PA.obj.hom ≫ i
  let l := pullback.fst c a
  let n := pullback.snd f.fromNormalization l
  let τ : Spec (S.presheaf.stalk s) ⟶ pullback c a :=
    pullback.lift (a ≫ σ) (𝟙 _) (by simp [Category.assoc, hσ])
  let t := Spec.map (CommRingCat.ofHom ((algebraMap A K).comp δ))
  let ε : S.functionField →+* K :=
    IsFractionRing.lift (g := (algebraMap A K).comp δ)
      ((IsFractionRing.injective A K).comp hδ)
  let b := Spec.map (CommRingCat.ofHom ε)
  have hε : ε.comp (algebraMap (S.presheaf.stalk s) S.functionField) =
      (algebraMap A K).comp δ := by
    ext r
    exact IsFractionRing.lift_algebraMap (g := (algebraMap A K).comp δ)
      ((IsFractionRing.injective A K).comp hδ) r
  have ht : t ≫ a = b ≫ S.fromSpecStalk (genericPoint S) := by
    rw [show t = b ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (S.presheaf.stalk s) S.functionField)) by
        simp only [b, t, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hε]]
    rw [Category.assoc]
    congr 1
    exact SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec S).specializes trivial)
  have hbase : (t ≫ τ) ≫ l = ((b ≫ sη) ≫ jU) ≫ i := by
    simp only [τ, l, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, ht, Category.assoc, ← hsj]
    simpa only [Category.assoc, i] using
      congrArg (fun z ↦ b ≫ sη ≫ z) hjU.symm
  let ν := Hom.pullbackFromNormalizationIso PA.obj.hom i
  have ha : ν.inv ≫ pullback.snd f.fromNormalization i = PA.obj.hom := by
    apply (cancel_epi ν.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact (Hom.pullbackFromNormalizationIso_hom_comp PA.obj.hom i).symm
  have hν : IsPullback (ν.inv ≫ pullback.fst f.fromNormalization i)
      PA.obj.hom f.fromNormalization i :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, ha]⟩ ν.symm rfl ha
  have hZ := ((IsPullback.of_hasPullback Z.π (b ≫ sη)).paste_horiz hψ).paste_horiz hν
  have hN := (IsPullback.of_hasPullback n (t ≫ τ)).paste_horiz
    (IsPullback.of_hasPullback f.fromNormalization l)
  have hZ' : IsPullback
      ((pullback.fst Z.π (b ≫ sη) ≫ ψ) ≫
        (ν.inv ≫ pullback.fst f.fromNormalization i))
      (pullback.snd Z.π (b ≫ sη)) f.fromNormalization ((t ≫ τ) ≫ l) := by
    rw [hbase]
    exact hZ
  exact ⟨ε, hε, hN.isoIsPullback _ _ hZ', hN.isoIsPullback_hom_snd _ _ hZ'⟩

end AlgebraicGeometry.Scheme
