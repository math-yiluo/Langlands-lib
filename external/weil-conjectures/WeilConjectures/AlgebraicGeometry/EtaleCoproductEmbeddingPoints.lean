/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldPointFunctor

/-!
# Geometric points of a coproduct of field spectra

Source: Stacks Project, Tags 03QR and 01JB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

/-- Geometric points of a prescribed coproduct of field spectra are the sum of embeddings.
Source: Stacks Project, Tag 03QR, coproduct construction; Tag 01JB, scheme coproducts.
(blueprint: lem-exc-etale-coproduct-embedding-points).

Proof: A map from Spec Ksep into the coproduct has its unique topological point in a
unique component. The coproduct inclusion of that component is an open immersion,
so the map factors uniquely through it. The Spec anti-equivalence identifies maps
from Spec Ksep to Spec (E i) over Spec K with K-algebra maps E i to Ksep. These two
constructions are inverse, giving the displayed equivalence. Precomposition by the
spectrum map of g corresponds under the anti-equivalence to postcomposition of the
embedding by g, and does not change the component. This proves the equivariance
formula. For empty I there is no map from the nonempty Spec Ksep to the empty scheme;
for a singleton I the assertion is precisely the affine anti-equivalence. -/
theorem etaleCoproduct_embedding_points
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (I : Type u) (E : I → IntermediateField K Ksep)
    [Etale (Sigma.desc (fun i : I ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))] :
    let X := Scheme.Etale.mk (Sigma.desc (fun i : I ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))
    ∃ e : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V ≃
        (Σ i, E i →ₐ[K] Ksep),
      ∀ (g : Gal(Ksep/K)) (x : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V),
        e (((etaleFieldPointFunctor K Ksep).obj X).obj.obj.ρ g x) =
          ⟨(e x).1, g.toAlgHom.comp (e x).2⟩ := by
  classical
  let S : I → Scheme := fun i ↦ Spec (CommRingCat.of (E i))
  let b : (∐ S) ⟶ Spec (CommRingCat.of K) :=
    Sigma.desc (fun i : I ↦ Spec.map (CommRingCat.ofHom (algebraMap K (E i))))
  change ∃ e : (etaleFieldBasePoint K Ksep ⟶ Over.mk b) ≃ (Σ i, E i →ₐ[K] Ksep),
    ∀ g x, e (etaleFieldPointAutomorphism K Ksep g ≫ x) =
      ⟨(e x).1, g.toAlgHom.comp (e x).2⟩
  let F : (Σ i, E i →ₐ[K] Ksep) → (etaleFieldBasePoint K Ksep ⟶ Over.mk b) :=
    fun p ↦ Over.homMk
      (Spec.map (CommRingCat.ofHom p.2.toRingHom) ≫ Sigma.ι S p.1) (by
        change (Spec.map (CommRingCat.ofHom p.2.toRingHom) ≫ Sigma.ι S p.1) ≫
          b = Spec.map (CommRingCat.ofHom (algebraMap K Ksep))
        rw [Category.assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
        congr 1
        ext k
        exact p.2.commutes k)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, φ⟩ ⟨j, ψ⟩ h
      have hl := congrArg Over.Hom.left h
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Sigma.ι S i =
        Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ Sigma.ι S j at hl
      have hp := congrArg (fun f : Spec (CommRingCat.of Ksep) ⟶ ∐ S ↦
        f (default : Spec (CommRingCat.of Ksep))) hl
      simp only [Scheme.Hom.comp_apply] at hp
      have hij : i = j := congrArg Sigma.fst ((sigmaι_eq_iff S i j _ _).mp hp)
      subst j
      have hm := (cancel_mono (Sigma.ι S i)).mp hl
      have hr := Spec.homEquiv.symm.injective hm
      have he : φ = ψ := by
        ext a
        exact congrArg (fun f ↦ f.hom a) hr
      cases he
      rfl
    · intro x
      obtain ⟨⟨i, y⟩, hy⟩ := (sigmaMk S).surjective
        (x.left (default : Spec (CommRingCat.of Ksep)))
      have hr : Set.range x.left ⊆ Set.range (Sigma.ι S i) := by
        rintro _ ⟨t, rfl⟩
        refine ⟨y, ?_⟩
        rw [Subsingleton.elim (α := Spec (CommRingCat.of Ksep)) t default]
        simpa using hy
      let l := IsOpenImmersion.lift (Sigma.ι S i) x.left hr
      have hl : l ≫ Sigma.ι S i = x.left := IsOpenImmersion.lift_fac _ _ _
      let σ := Spec.homEquiv l
      have hσ : Spec.map σ = l := Spec.homEquiv.symm_apply_apply _
      have hb : CommRingCat.ofHom (algebraMap K (E i)) ≫ σ =
          CommRingCat.ofHom (algebraMap K Ksep) := by
        apply Spec.homEquiv.symm.injective
        change Spec.map (_ ≫ σ) = _
        rw [Spec.map_comp, hσ]
        have hw := Over.w x
        change x.left ≫ b = Spec.map (CommRingCat.ofHom (algebraMap K Ksep)) at hw
        rw [← hl, Category.assoc, Sigma.ι_comp_desc] at hw
        exact hw
      let φ : E i →ₐ[K] Ksep :=
        { σ.hom with
          commutes' := fun k ↦ congrArg (fun f ↦ f.hom k) hb }
      refine ⟨⟨i, φ⟩, ?_⟩
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Sigma.ι S i = x.left
      change Spec.map σ ≫ Sigma.ι S i = x.left
      rw [hσ, hl]
  let e := (Equiv.ofBijective F hF).symm
  refine ⟨e, ?_⟩
  intro g x
  obtain ⟨⟨i, φ⟩, rfl⟩ := hF.surjective x
  have hact : etaleFieldPointAutomorphism K Ksep g ≫ F ⟨i, φ⟩ =
      F ⟨i, g.toAlgHom.comp φ⟩ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Sigma.ι S i) =
        Spec.map (CommRingCat.ofHom (g.toAlgHom.comp φ).toRingHom) ≫ Sigma.ι S i
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have heφ : e (F ⟨i, φ⟩) = ⟨i, φ⟩ := e.apply_symm_apply _
  rw [hact, heφ]
  exact e.apply_symm_apply _

end AlgebraicGeometry
