/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSupportGeneral
import WeilConjectures.AlgebraicGeometry.AffineFreeFiniteStalkGeneration
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.Topology.SpectralConstructibleFiniteIntersection
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Affine free presentations with Noetherian coefficients

Source: Stacks Project, Tag 095N.
(blueprint: new-constructible-affine-free-presentation-general).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

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

private theorem failureLocus_constructible
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ]
    (G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf G] [IsConstructibleSheaf F]
    (g : G ⟶ F) :
    Topology.IsConstructible {x : X | ¬ Function.Surjective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map g)}  := by
  have := IsConstructibleSheaf.cokernel g
  let C := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (cokernel g)
  obtain ⟨hind, _, hc⟩ := constructibleModuleSupport_general (cokernel g)
  have heq : {x : X | ¬ Function.Surjective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map g)} = etaleSheafSupport C := by
    ext x
    let s := X.algClosurePoint x
    let Q := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hz : IsZero (Q.obj (cokernel g)) ↔ Function.Surjective (Q.map g) := by
      exact (PreservesCokernel.iso Q g).isZero_iff.trans
        ((Preadditive.epi_iff_isZero_cokernel (Q.map g)).symm.trans
          (ModuleCat.epi_iff_surjective _))
    let : PreservesColimitsOfSize.{u, u}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app (cokernel g)
    have hzero : IsZero ((pointSmallEtale s).sheafFiber.obj C) ↔
        Function.Surjective (Q.map g) := by
      refine e.isZero_iff.trans (?_ : IsZero
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          (Q.obj (cokernel g))) ↔ Function.Surjective (Q.map g))
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      change Subsingleton (Q.obj (cokernel g)) ↔ Function.Surjective (Q.map g)
      exact ModuleCat.isZero_iff_subsingleton.symm.trans hz
    constructor
    · intro hn
      exact ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
        s, by simp [s], fun h => hn (hzero.mp h)⟩
    · rintro ⟨Ω, hfield, hclosed, s', hs', hn⟩ hsurj
      exact hn ((hind x _ Ω s s' (by simp [s]) hs').mp (hzero.mpr hsurj))
  rw [heq]
  exact hc


private theorem finite_affine_free_epimorphism
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n : ℕ) (U : Fin n → X.Etale), (∀ i, IsAffine (U i).left) ∧
      ∃ g : (∐ fun i : Fin n => P (U i)) ⟶ F,
        Epi g := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  let I := Σ W : {W : X.Etale // IsAffine W.left}, P W.val ⟶ F
  let g (S : Finset I) : (∐ fun i : S => P i.val.1.val) ⟶ F :=
    Sigma.desc (fun i : S => i.val.2)
  let E (S : Finset I) : Set X := {x | ¬ Function.Surjective
    (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).map (g S))}
  have hP (W : X.Etale) (hW : IsAffine W.left) : IsConstructibleSheaf (P W) := by
    have : IsAffine W.left := hW
    exact affineFree_constructible W
  have hE (S : Finset I) : Topology.IsConstructible (E S) := by
    let e := (Fintype.equivFin S).symm
    let H : Fin (Fintype.card S) → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      fun i => P (e i).val.1.val
    have : ∀ i : Fin (Fintype.card S), IsConstructibleSheaf (H i) :=
      fun i => hP _ (e i).val.1.property
    have := Abelian.hasFiniteBiproducts
      (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    have := IsConstructibleSheaf.biproduct H
    have := IsConstructibleSheaf.of_iso
      (biproduct.isoCoproduct H ≪≫ Sigma.reindex e (fun i : S => P i.val.1.val))
    exact failureLocus_constructible _ F (g S)
  have hEmpty : (⋂ S : Finset I, E S) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨S, hS⟩ := exists_finset_affine_free_stalk_surjective X Λ F x
      ((ModuleCat.isFinitelyGenerated_iff _).mp
        ((IsConstructibleSheaf.isFiniteSheaf
          (inferInstance : IsConstructibleSheaf F)).isFinitelyGenerated_sheafFiber
            _ (X.algClosurePoint x)))
    exact Set.mem_iInter.mp hx S hS
  have : SpectralSpace X := {}
  obtain ⟨A, hA⟩ := finite_subfamily_iInter_eq_empty_of_isConstructible X
    (Finset I) E hE hEmpty
  let S : Finset I := A.biUnion id
  let e := Fintype.equivFin S
  let U : Fin (Fintype.card S) → X.Etale := fun i => (e.symm i).val.1.val
  let d : (∐ fun i : Fin (Fintype.card S) => P (U i)) ⟶ F :=
    (Sigma.reindex e.symm (fun i : S => P i.val.1.val)).hom ≫ g S
  have hd : Epi (g S) := by
    constructor
    intro Z a b hab
    apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
    intro x
    obtain ⟨K, hK, hxK⟩ : ∃ K ∈ A, x ∉ E K := by
      by_contra hn
      have hx : x ∈ ⋂ K ∈ A, E K := by
        simp only [Set.mem_iInter]
        intro K hK
        by_contra hxK
        exact hn ⟨K, hK, hxK⟩
      rw [hA] at hx
      exact hx
    have hKS : K ⊆ S := fun i hi => Finset.mem_biUnion.mpr ⟨K, hK, hi⟩
    let t : (∐ fun i : K => P i.val.1.val) ⟶ (∐ fun i : S => P i.val.1.val) :=
      Sigma.desc (fun i : K => Sigma.ι (fun j : S => P j.val.1.val)
        ⟨i.val, hKS i.property⟩)
    have ht : t ≫ g S = g K := by
      apply Sigma.hom_ext
      intro i
      simp [t, g]
    let Q := (pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)
    have hsurj : Function.Surjective (Q.map (g K)) := not_not.mp hxK
    have : Epi (Q.map (g K)) := (ModuleCat.epi_iff_surjective _).mpr hsurj
    change Q.map a = Q.map b
    apply (cancel_epi (Q.map (g K))).mp
    rw [← ht, ← Q.map_comp, ← Q.map_comp, Category.assoc, Category.assoc, hab]
  have : Epi d := inferInstance
  exact ⟨Fintype.card S, U, fun i => (e.symm i).val.1.property,
    d, inferInstance⟩


/-- A constructible module sheaf over a Noetherian ring has a finite affine free presentation.

Source: Stacks Project, Tag 095N.
(blueprint: new-constructible-affine-free-presentation-general).

Proof: Affine free etale sheaves are constructible by the finite-etale stratification
of their representing morphisms. Finite generation of each stalk provides finitely many
sections, represented on affine pointed etale neighborhoods, surjecting on that stalk.
The failure locus of each finite family is the constructible support of its cokernel.
Compactness of the constructible topology selects finitely many families with empty
intersection of failure loci. Their union gives an epimorphism. Its kernel is constructible
because the coefficient ring is Noetherian. Apply the same construction to the kernel,
then compose with its inclusion. The original epimorphism is the cokernel of this composite.
Zero sheaves and empty bases allow the empty family throughout. -/
theorem exists_affine_free_etale_presentation_general
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W =>
      (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
    ∃ (n m : ℕ) (U : Fin n → X.Etale) (V : Fin m → X.Etale),
      (∀ i : Fin n, IsAffine (U i).left) ∧ (∀ j : Fin m, IsAffine (V j).left) ∧
      ∃ (f : (∐ fun j : Fin m => P (V j)) ⟶ (∐ fun i : Fin n => P (U i)))
        (g : (∐ fun i : Fin n => P (U i)) ⟶ F)
        (w : f ≫ g = 0), Nonempty (IsColimit (CokernelCofork.ofπ g w)) := by
  classical
  let P : X.Etale → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := fun W ↦
    (presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free Λ)
  have hP (W : X.Etale) (hW : IsAffine W.left) :
      IsConstructibleSheaf (P W) := by
    have : IsAffine W.left := hW
    exact affineFree_constructible W
  obtain ⟨n, U, hU, g, hg⟩ := finite_affine_free_epimorphism X Λ F
  have : Epi g := hg
  have : ∀ i : Fin n, IsConstructibleSheaf (P (U i)) := fun i ↦ hP (U i) (hU i)
  have := Abelian.hasFiniteBiproducts
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have := IsConstructibleSheaf.biproduct (fun i : Fin n ↦ P (U i))
  have := IsConstructibleSheaf.of_iso
    (biproduct.isoCoproduct (fun i : Fin n ↦ P (U i)))
  have := IsConstructibleSheaf.kernel g
  obtain ⟨m, V, hV, h, hh⟩ := finite_affine_free_epimorphism X Λ (kernel g)
  have : Epi h := hh
  refine ⟨n, m, U, V, hU, hV, h ≫ kernel.ι g, g, ?_, ?_⟩
  · simp
  · exact ⟨isCokernelEpiComp
      (Abelian.epiIsCokernelOfKernel
        (KernelFork.ofι (kernel.ι g) (kernel.condition g)) (kernelIsKernel g)) h rfl⟩


end AlgebraicGeometry.Scheme
