/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.StalkNormalizationEtale
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Extension over a stalk before spreading

## References

* Stacks Project, Tag 0EYJ, proof of the local claim
* Stacks Project, Tags 004W and 004X, maximal components and generic points
* Stacks Project, local claim
* Tags 0BQM, 0EYG, 0EYH, 0EYI, 0EYE, 0EY6, 0EY9, and 0EYB
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A generic point of a boundary component has no proper boundary generalization. -/
private theorem exists_minimal_boundary (S : Scheme.{u}) (U : S.Opens) (hU : U ≠ ⊤) :
    ∃ s : S, s ∉ U ∧ ∀ t : S, t ⤳ s → t ∉ U → t = s := by
  classical
  have hne : (U : Set S)ᶜ.Nonempty := by
    by_contra h
    apply hU
    apply top_unique
    intro x _
    by_contra hx
    exact h ⟨x, hx⟩
  let B := (U : Set S)ᶜ
  let : Nonempty B := hne.to_subtype
  have hB : IsClosed B := U.isOpen.isClosed_compl
  let : QuasiSober B := hB.isClosedEmbedding_subtypeVal.quasiSober
  let x : B := Classical.choice inferInstance
  let s := genericPoints.ofComponent
    (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩)
  refine ⟨s.1.1, s.1.2, ?_⟩
  intro t hts ht
  let t' : B := ⟨t, ht⟩
  have hts' : t' ⤳ s.1 := (Topology.IsInducing.subtypeVal.specializes_iff).mp hts
  have hcl : closure ({s.1} : Set B) ⊆ closure ({t'} : Set B) :=
    hts'.closure_subset
  have heq : closure ({s.1} : Set B) = closure ({t'} : Set B) :=
    le_antisymm hcl (s.2.2 isIrreducible_singleton.closure hcl)
  exact congrArg Subtype.val ((isGenericPoint_closure (x := t')).eq
    (heq ▸ isGenericPoint_closure (x := s.1)))

/-- The cover on the open extends after base change to a suitable stalk. -/
theorem GaloisCover.exists_stalk_finiteEtale_model {S C : Scheme.{u}} [IsNoetherian S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη)
    (U : S.Opens) (hηU : genericPoint S ∈ U) (hU : U ≠ ⊤)
    (jU : Cη ⟶ (c ⁻¹ᵁ U).toScheme) (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (ψ : Z.P ⟶ PA.obj.left) (hjU : jU ≫ (c ⁻¹ᵁ U).ι = j)
    (hψ : IsPullback ψ Z.π PA.obj.hom jU) :
    ∃ (s : S), s ∉ U ∧
      ∃ Q : (Limits.pullback c (S.fromSpecStalk s)).FiniteEtale,
        Nonempty ((FiniteEtale.pullback
          (pullback.fst (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj PA ≅
          (FiniteEtale.pullback
          (pullback.snd (c ⁻¹ᵁ U).ι (pullback.fst c (S.fromSpecStalk s)))).obj Q) := by
  classical
  obtain ⟨s, hs, hmin⟩ := exists_minimal_boundary S U hU
  have : IsFinite PA.obj.hom := PA.property
  have : QuasiCompact (c ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
      (inferInstance : QuasiCompact U.ι)
  let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
  let l := pullback.fst c (S.fromSpecStalk s)
  have hfin : IsFinite (pullback.snd f.fromNormalization l) :=
    stalk_normalization_finite hS c q j hCη U PA s
  have het : Etale (pullback.snd f.fromNormalization l) :=
    GaloisCover.stalk_normalization_etale hS c σ hσ G hG q j hCη sη hsq hsj
      Z hZ U hηU jU PA ψ hjU hψ s hs hmin hfin
  let Q : (pullback c (S.fromSpecStalk s)).FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (pullback.snd f.fromNormalization l) het, hfin⟩
  refine ⟨s, hs, Q, ?_⟩
  let i := (c ⁻¹ᵁ U).ι
  have hp : IsPullback (𝟙 PA.obj.left) PA.obj.hom f i :=
    IsPullback.of_horiz_isIso_mono ⟨by simp [f, i]⟩
  let e := hp.isoPullback
  have : IsFinite (pullback.snd f i) := by
    have he : e.inv ≫ PA.obj.hom = pullback.snd f i := hp.isoPullback_inv_snd
    rw [← he]
    infer_instance
  let a := e ≪≫ asIso (pullback.snd f i).toNormalization ≪≫
    asIso (f.normalizationPullback i)
  have ha : a.hom ≫ pullback.snd f.fromNormalization i = PA.obj.hom := by
    simp only [a, Iso.trans_hom, asIso_hom, Category.assoc,
      Hom.normalizationPullback_snd, Hom.toNormalization_fromNormalization]
    exact hp.isoPullback_hom_snd
  have hn : IsPullback (a.hom ≫ pullback.fst f.fromNormalization i)
      PA.obj.hom f.fromNormalization i :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, ha]⟩ a
      rfl ha
  let v := pullback.fst i l
  let w := pullback.snd i l
  have hA := (IsPullback.of_hasPullback PA.obj.hom v).paste_horiz hn
  have hB := (IsPullback.of_hasPullback Q.obj.hom w).paste_horiz
    (IsPullback.of_hasPullback f.fromNormalization l)
  have hB' : IsPullback
      (pullback.fst Q.obj.hom w ≫ pullback.fst f.fromNormalization l)
      (pullback.snd Q.obj.hom w) f.fromNormalization (v ≫ i) := by
    simpa only [v, w, pullback.condition] using hB
  let b := hA.isoIsPullback _ _ hB'
  exact ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk b
    (hA.isoIsPullback_hom_snd _ _ hB'))⟩

end AlgebraicGeometry.Scheme
