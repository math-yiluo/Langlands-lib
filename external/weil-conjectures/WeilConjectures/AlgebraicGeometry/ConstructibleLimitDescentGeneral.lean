/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral
import WeilConjectures.AlgebraicGeometry.AffineEtaleBaseChangeSystem
import WeilConjectures.AlgebraicGeometry.AffineEtaleDescentData
import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleEventualHomLift
import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.Data.Finset.Order

/-!
# Constructible module descent with Noetherian coefficients

Source: Stacks Project, Tags 09YU (3), 095N and 09YQ.
(blueprint: new-constructible-limit-descent-general).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
private noncomputable def evalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃ F.obj.obj (op W) :=
  ((sheafificationAdjunction _ _).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans
      uliftYonedaEquiv)

private lemma evalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (b : F ⟶ G) :
    evalEquiv W G (a ≫ b) = b.hom.app (op W) (evalEquiv W F a) := by
  unfold evalEquiv
  simp only [Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_naturality_right]
  exact uliftYonedaEquiv_comp _ _

/-- Extension by zero of the constant rank-one module represents evaluation. -/
private noncomputable def shriekEvalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) ≃ F.obj.obj (op W) := by
  let T : W.left.Etale := Etale.mk (𝟙 W.left)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let e : (MorphismProperty.Over.map ⊤ W.prop).obj T ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp [T])
  let adj := (Etale.etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom W.prop).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)
  exact (adj.homEquiv _ _).trans
    (((constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ) hT).homEquiv _ _).trans
      ((ModuleCat.homEquiv.trans
        (LinearMap.ringLmapEquivSelf Λ ℕ _).toEquiv).trans
          (F.obj.mapIso e.op).symm.toLinearEquiv.toEquiv))

/-- The section equivalence is natural under postcomposition. -/
private lemma shriekEvalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ⟶ F) (b : F ⟶ G) :
    shriekEvalEquiv W G (a ≫ b) = b.hom.app (op W) (shriekEvalEquiv W F a) := by
  let adj := (Etale.etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} Λ) W.hom W.prop).ofNatIsoRight
      (Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop)
  let adjc := constantSheafAdj W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (MorphismProperty.Over.mkIdTerminal @Etale W.left)
  have h1 := adj.homEquiv_naturality_right a b
  have h2 := adjc.homEquiv_naturality_right (adj.homEquiv _ _ a)
    ((Etale.localizationRestriction (ModuleCat.{u + 1} Λ) W.hom W.prop).map b)
  dsimp only [shriekEvalEquiv, Equiv.trans_apply]
  rw [h1, h2]
  let e : (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.mk (𝟙 W.left)) ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp)
  let z := adjc.homEquiv _ _ (adj.homEquiv _ _ a)
  change G.obj.map e.op.inv (b.hom.app _ (z 1)) =
    b.hom.app _ (F.obj.map e.op.inv (z 1))
  exact congrArg (fun k ↦ k (z 1)) (b.hom.naturality e.op.inv).symm

private noncomputable def freeYonedaEvalEquiv (W : X.Etale)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) ≃
      F.obj.obj (op W) :=
  Sheaf.freeYonedaHomEquiv.trans (ModuleCat.homEquiv.trans
    (LinearMap.ringLmapEquivSelf Λ ℕ _).toEquiv)

private lemma freeYonedaEvalEquiv_comp (W : X.Etale)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (a : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) (b : F ⟶ G) :
    freeYonedaEvalEquiv W G (a ≫ b) = b.hom.app (op W) (freeYonedaEvalEquiv W F a) := by
  change Sheaf.freeYonedaHomEquiv (a ≫ b) 1 =
    b.hom.app (op W) (Sheaf.freeYonedaHomEquiv a 1)
  rw [Etale.freeYonedaHomEquiv_comp]
  rfl

private noncomputable def shriekFreeYonedaIso (W : X.Etale) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)) ≅ Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (shriekEvalEquiv W F).trans (freeYonedaEvalEquiv W F).symm
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f g ↦ by
      apply (shriekEvalEquiv W _).injective
      simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        freeYonedaEvalEquiv_comp, shriekEvalEquiv_comp])

private noncomputable def freeModelIso (W : X.Etale) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ≅
        Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) :=
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (evalEquiv W F).trans (freeYonedaEvalEquiv W F).symm
  Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f g ↦ by
      apply (evalEquiv W _).injective
      simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        freeYonedaEvalEquiv_comp, evalEquiv_comp])

/-- Two finite affine etale families admit free-sum models at one stage.
This statement descends objects only; it makes no assertion about arrows between them.

Source: Stacks Project, Tag 09YU (3), essential surjectivity of the affine etale site
using 095N, and Tag 03S6.
(blueprint: lem-weil-pbc-affine-free-etale-family-models).

Proof:
1. Regard each U and V as an object of the full affine etale site. Apply the essential
   surjectivity clause of `exists_affineEtaleSite_colimit` to each of these finitely
   many objects. Nonemptiness and directedness give a common upper bound i, even
   when both families are empty. Move every object to i by the site's transition
   functors. The cartesian squares and composition comparisons identify its base
   change to the limit with the original U or V. Affineness is preserved because
   the scheme transitions and limit projections are affine.
2. For an affine etale object W, its sheaf P(W) represents evaluation on W: compose
   the sheafification adjunction, the free-module adjunction and ulift Yoneda.
   The etale lower shriek of the constant rank-one module represents the same
   evaluation, by the shriek/pullback and constant-sheaf adjunctions. The natural
   equivalences of represented functors give their unique comparison isomorphism.
   Inverse image of P(W) is P of the base-changed object: apply the upperStar/lowerStar
   adjunction and use that lowerStar evaluates on the base-changed etale object.
   This is also `Etale.upperStarFreeYonedaIso` after comparing the two free models.
3. Inverse image preserves coproducts since it is a left adjoint. Combine its
   coproduct comparison with the comparisons in step 2 to obtain eU and eV.
   In these stage models use the lower shriek of the constant rank-one module.
   This is the free sheaf by step 2. The witnesses WU and WV, their affine proofs,
   and eU and eV give the asserted common-stage models. Empty sums are handled
   by preservation of the initial object. -/
private theorem family_models_general
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ]
    (n m : ℕ) (U : Fin n → c.pt.Etale) (V : Fin m → c.pt.Etale)
    (hU : ∀ k : Fin n, IsAffine (U k).left)
    (hV : ∀ k : Fin m, IsAffine (V k).left) :
    let P : c.pt.Etale → Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun W ↦ (presheafToSheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (i : I) (WU : Fin n → (D.obj (op i)).Etale)
      (WV : Fin m → (D.obj (op i)).Etale),
      let Q : (D.obj (op i)).Etale →
          Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
        fun W ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
          ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))
      (∀ k, IsAffine (WU k).left) ∧ (∀ k, IsAffine (WV k).left) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj
        (∐ fun k : Fin n ↦ Q (WU k)) ≅ (∐ fun k : Fin n ↦ P (U k))) ∧
      Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj
        (∐ fun k : Fin m ↦ Q (WV k)) ≅ (∐ fun k : Fin m ↦ P (V k))) := by
  classical
  intro P
  obtain ⟨T, v, p, q, gamma, delta,
    _, h1, hpb, _, _, _, _, h7, _, _, h10, _, h12, _, _⟩ :=
    exists_affineEtale_baseChange_system D c hc
  obtain ⟨hdesc, _⟩ := affineEtale_descent_data D c hc T v p q gamma delta
    h1 hpb h7 h10 h12
  let Z : Fin n ⊕ Fin m → c.pt.FullAffineEtale :=
    Sum.elim (fun k ↦ ⟨U k, hU k⟩) (fun k ↦ ⟨V k, hV k⟩)
  choose idx M e using fun k ↦ hdesc (Z k)
  obtain ⟨i, hi⟩ := (Finset.univ.image idx).exists_le
  have h (k : Fin n ⊕ Fin m) : idx k ≤ i := hi _ (Finset.mem_image.mpr ⟨k, by simp, rfl⟩)
  let N (k : Fin n ⊕ Fin m) := (T (idx k) i (h k)).obj (M k)
  let W (k : Fin n ⊕ Fin m) := (N k).obj
  have ei (k : Fin n ⊕ Fin m) : (v i).obj (N k) ≅ Z k :=
    (delta (idx k) i (h k)).app (M k) ≪≫ Classical.choice (e k)
  have eW (k : Fin n ⊕ Fin m) : (c.π.app (op i)).Etale.obj (W k) ≅ (Z k).obj := by
    let hp := hpb i (N k)
    let a : ((v i).obj (N k)).obj ≅ (c.π.app (op i)).Etale.obj (W k) :=
      MorphismProperty.Over.isoMk hp.isoPullback (by
        change hp.isoPullback.hom ≫ pullback.snd _ _ = _
        exact hp.isoPullback_hom_snd)
    exact a.symm ≪≫ (fullAffineEtaleInclusion c.pt).mapIso (ei k)
  let Q : (D.obj (op i)).Etale →
      Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun Z ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) Z.hom inferInstance).obj
      ((constantSheaf Z.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  have eq (k : Fin n ⊕ Fin m) : L.obj (Q (W k)) ≅ P ((Z k).obj) :=
    L.mapIso (shriekFreeYonedaIso (W k)) ≪≫
      Etale.upperStarFreeYonedaIso (c.π.app (op i)) (W k) ≪≫
      Etale.freeYonedaMapIso (eW k) ≪≫ (freeModelIso ((Z k).obj)).symm
  refine ⟨i, fun k ↦ W (.inl k), fun k ↦ W (.inr k),
    fun k ↦ (N (.inl k)).property, fun k ↦ (N (.inr k)).property, ?_, ?_⟩
  · exact ⟨PreservesCoproduct.iso L (fun k : Fin n ↦ Q (W (.inl k))) ≪≫
      Sigma.mapIso (fun k ↦ eq (.inl k))⟩
  · exact ⟨PreservesCoproduct.iso L (fun k : Fin m ↦ Q (W (.inr k))) ≪≫
      Sigma.mapIso (fun k ↦ eq (.inr k))⟩


private noncomputable def affineFreeHomEquiv
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) ≃
      F.obj.obj (op W) :=
  ((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).homEquiv _ _).trans
    (((ModuleCat.adj Λ).whiskerRight X.Etaleᵒᵖ).homEquiv _ _ |>.trans uliftYonedaEquiv)

private theorem affineFreeHomEquiv_comp
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ⟶ F) (f : F ⟶ H) :
    affineFreeHomEquiv W H (p ≫ f) = f.hom.app (op W) (affineFreeHomEquiv W F p) := by
  simp only [affineFreeHomEquiv, Equiv.trans_apply, Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def freeYonedaSectionEquiv
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) ≃
      F.obj.obj (op W) :=
  Sheaf.freeYonedaHomEquiv.trans (ModuleCat.homEquiv.trans
    (LinearMap.ringLmapEquivSelf Λ Λ _).toEquiv)

private theorem freeYonedaSectionEquiv_comp
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    (W : X.Etale) {F H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (p : Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) ⟶ F) (f : F ⟶ H) :
    freeYonedaSectionEquiv W H (p ≫ f) =
      f.hom.app (op W) (freeYonedaSectionEquiv W F p) := by
  simp only [freeYonedaSectionEquiv, Equiv.trans_apply, Etale.freeYonedaHomEquiv_comp]
  rfl

private noncomputable def affineFreeIso
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ] (W : X.Etale) :
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ) ≅
      Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ) := by
  let e (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (affineFreeHomEquiv W F).trans (freeYonedaSectionEquiv W F).symm
  refine Coyoneda.ext _ _ (fun f ↦ e _ f) (fun f ↦ (e _).symm f)
    (fun f ↦ by simp) (fun f ↦ by simp) (fun f h ↦ ?_)
  apply (affineFreeHomEquiv W _).injective
  dsimp only [e, Equiv.symm_trans, Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, affineFreeHomEquiv_comp, Equiv.apply_symm_apply]
  simpa only [Equiv.symm_symm] using freeYonedaSectionEquiv_comp W f h

private theorem affineFree_constructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] (W : X.Etale) [IsAffine W.left] :
    IsConstructibleSheaf
      ((presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)) := by
  have : CompactSpace W.left := inferInstance
  have : QuasiSeparatedSpace W.left := inferInstance
  obtain ⟨S, _, hf⟩ := exists_etale_stratified_finite (X := X) (U := W.left) W.hom
  let T : Stratification X :=
    { toStratification := S.toStratification
      domain := S.domain
      immersion := S.immersion
      isImmersion := S.isImmersion
      range_immersion := S.range_immersion }
  have h : IsConstructibleSheaf
      (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of Λ Λ)) := by
    refine ⟨T, fun i ↦ ?_⟩
    have : IsFinite ((S.immersion i).Etale.obj W).hom := by
      change IsFinite (pullback.snd W.hom (S.immersion i))
      exact (hf i).1
    have := Etale.isFiniteLocallyConstantSheaf_freeYoneda_of_isFinite
      (Λ := Λ) ((S.immersion i).Etale.obj W)
    exact IsFiniteLocallyConstantSheaf.of_iso
      (Etale.upperStarFreeYonedaIso (Λ := Λ) (S.immersion i) W).symm
  exact IsConstructibleSheaf.of_iso (affineFreeIso W).symm



private theorem arrow_descent_general
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ]
    (n m : ℕ) (U : Fin n → c.pt.Etale) (V : Fin m → c.pt.Etale)
    (hU : ∀ k : Fin n, IsAffine (U k).left)
    (hV : ∀ k : Fin m, IsAffine (V k).left) :
    let P : c.pt.Etale → Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun W => (presheafToSheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∀ f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun k : Fin n => P (U k)),
      ∃ (i : I)
        (A B : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (a : A ⟶ B),
        IsConstructibleSheaf A ∧ IsConstructibleSheaf B ∧
        ∃ (eA : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj A ≅
            (∐ fun j : Fin m => P (V j)))
          (eB : (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj B ≅
            (∐ fun k : Fin n => P (U k))),
          (Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).map a ≫ eB.hom =
            eA.hom ≫ f := by
  classical
  intro P f
  obtain ⟨i, WU, WV, hWU, hWV, ⟨eB⟩, ⟨eA⟩⟩ :=
    family_models_general D c hc Λ n m U V hU hV
  let Q : (D.obj (op i)).Etale →
      Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun W ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) W.hom inferInstance).obj
      ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ))
  let A₀ := ∐ fun k : Fin m ↦ Q (WV k)
  let B₀ := ∐ fun k : Fin n ↦ Q (WU k)
  obtain ⟨j, h, a, ha⟩ := exists_affine_free_etaleModule_eventual_hom_lift
    D c hc Λ i m WV hWV B₀ (eA.hom ≫ f ≫ eB.inv)
  let t := Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)
  let E := Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op j))
    (D.map (homOfLE h).op) (c.π.app (op i)) (c.w (homOfLE h).op).symm
  have : ∀ k, IsAffine (WU k).left := hWU
  have : ∀ k, IsAffine (WV k).left := hWV
  have hQ (W : (D.obj (op i)).Etale) [IsAffine W.left] :
      IsConstructibleSheaf (Q W) := by
    have := affineFree_constructible (Λ := Λ) W
    obtain ⟨e⟩ := free_etale_module_shriek_comparison (D.obj (op i)) Λ W
    exact IsConstructibleSheaf.of_iso e
  have hQA (k : Fin m) : IsConstructibleSheaf (Q (WV k)) := hQ (WV k)
  have hQB (k : Fin n) : IsConstructibleSheaf (Q (WU k)) := hQ (WU k)
  have : HasFiniteBiproducts
      (Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    Abelian.hasFiniteBiproducts
  have : IsConstructibleSheaf (⨁ fun k : Fin m ↦ Q (WV k)) :=
    IsConstructibleSheaf.biproduct _
  have : IsConstructibleSheaf (⨁ fun k : Fin n ↦ Q (WU k)) :=
    IsConstructibleSheaf.biproduct _
  have hA₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) A₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin m ↦ Q (WV k))
  have hB₀ : IsConstructibleSheaf
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) B₀ :=
    IsConstructibleSheaf.of_iso (biproduct.isoCoproduct _)
      (F := ⨁ fun k : Fin n ↦ Q (WU k))
  have hAj : IsConstructibleSheaf (t.obj A₀) :=
    IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) A₀
  have hBj : IsConstructibleSheaf (t.obj B₀) :=
    IsConstructibleSheaf.upperStar (D.map (homOfLE h).op) B₀
  refine ⟨j, t.obj A₀, t.obj B₀, a, hAj, hBj,
    (E.app A₀).symm ≪≫ eA, (E.app B₀).symm ≪≫ eB, ?_⟩
  change _ ≫ (E.inv.app B₀ ≫ eB.hom) = (E.inv.app A₀ ≫ eA.hom) ≫ f
  rw [← Category.assoc, ha]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl



/-- A constructible module sheaf on an affine-transition limit of qcqs schemes descends
with its constructibility to a stage, for any Noetherian coefficient ring.

Source: Stacks Project, Tag 09YU (3), essential surjectivity, using Tags 095N and 09YQ.
(blueprint: new-constructible-limit-descent-general).

Proof: Present the sheaf by two finite sums of affine free etale sheaves (095N). Descend
the finitely many etale objects to a common stage by the affine etale site limit theorem.
The free-Yoneda and sheafification adjunctions identify each component of the presentation
arrow with a section. The section limit theorem descends these finitely many sections to
a later common stage, and naturality of the adjunction unit and inverse-image composition
identifies the pulled-back arrow with the original arrow. Both descended sums are
constructible: finite-etale stratification makes affine free sheaves constructible, and
finite sums and pullback preserve constructibility. Their cokernel is constructible and
pulls back to the original cokernel, hence to the given sheaf. Empty families are included
by directedness and preservation of zero objects. -/
theorem exists_constructible_limit_descent_general
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleSheaf Fᵢ ∧
        Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F) := by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  let i₀ : I := Classical.choice inferInstance
  have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app D c hc (op i₀)
  have : QuasiSeparatedSpace c.pt :=
    quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  obtain ⟨n, m, U, V, hU, hV, f, g, w, ⟨hg⟩⟩ :=
    exists_affine_free_etale_presentation_general c.pt Λ F
  obtain ⟨i, A, B, a, hA, hB, eA, eB, ha⟩ :=
    arrow_descent_general D c hc Λ n m U V hU hV f
  have := hA
  have := hB
  have hC : IsConstructibleSheaf (cokernel a) := IsConstructibleSheaf.cokernel a
  refine ⟨i, cokernel a, hC, ?_⟩
  let L := Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))
  exact ⟨PreservesCokernel.iso L a ≪≫ cokernel.mapIso (L.map a) f eA eB ha ≪≫
    (colimit.isColimit (parallelPair f 0)).coconePointUniqueUpToIso hg⟩


end AlgebraicGeometry.Scheme
