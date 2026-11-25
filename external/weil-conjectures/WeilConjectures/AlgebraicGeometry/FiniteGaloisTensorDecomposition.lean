/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.FiniteGaloisTensorCoproduct
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tensor decomposition of a finite Galois field extension

Source: Stacks Project, Fundamental Groups, Tag 03SF
(blueprint: lem-exc-finite-galois-tensor-decomposition).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry

private theorem finiteGaloisTensorAlgEquiv
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E] :
    ∃ φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E),
      ∀ (a b : E) (q : E ≃ₐ[L] E), φ (a ⊗ₜ[L] b) q = a * q b := by
  classical
  let f : (E ⊗[L] E) →ₐ[E] ((E ≃ₐ[L] E) → E) :=
    AlgHom.pi fun q ↦ Algebra.TensorProduct.lift
      (AlgHom.id E E) q.toAlgHom (fun _ _ ↦ Commute.all _ _)
  have hf (a b : E) (q : E ≃ₐ[L] E) : f (a ⊗ₜ[L] b) q = a * q b := rfl
  -- Dedekind independence makes the evaluation vectors span the product.
  have hli : LinearIndependent E (fun q : E ≃ₐ[L] E ↦ (q : E → E)) := by
    exact (linearIndependent_monoidHom E E).comp
      (fun q : E ≃ₐ[L] E ↦ q.toRingEquiv.toMonoidHom)
      (fun _ _ h ↦ AlgEquiv.ext fun x ↦ DFunLike.congr_fun h x)
  have hspan : Submodule.span E (Set.range (fun b : E ↦
      fun q : E ≃ₐ[L] E ↦ q b)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hli
  have hsurj : Function.Surjective f := by
    apply (LinearMap.range_eq_top (f := f.toLinearMap)).mp
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨b, rfl⟩
    exact ⟨1 ⊗ₜ[L] b, by ext q; simp [hf]⟩
  -- The two E-vector spaces have the same dimension, namely [E : L].
  have hdim : Module.finrank E (E ⊗[L] E) =
      Module.finrank E ((E ≃ₐ[L] E) → E) := by
    rw [Module.finrank_baseChange, Module.finrank_pi]
    simp [← IsGalois.card_aut_eq_finrank L E, Nat.card_eq_fintype_card]
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mpr hsurj
  exact ⟨(AlgEquiv.ofBijective f ⟨hinj, hsurj⟩).restrictScalars L, hf⟩

/-- For a finite Galois extension `E/L`, the map from `E ⊗[L] E` to the product indexed
by `Gal(E/L)`, taking `a ⊗ b` to `(a * q b)`, is an isomorphism. Its affine spectrum
identifies the self-fibre-product of `Spec E` over `Spec L` with a finite disjoint union.
For every sheaf on the small etale site, the corresponding bijection of sections takes
restriction along the first projection to the constant family and restriction along the
second projection to the family of Galois translates.

For the algebraic part, choose a primitive element by the finite separable primitive-element
lemma and identify `E` with its minimal-polynomial quotient (the primitive-element and
quotient-field nodes). Base-change that quotient to `E` by the tensor universal property;
the monomial bases on both sides show the resulting map is an isomorphism. Normality and
separability identify the distinct roots with the `L`-automorphisms of `E` (the conjugate-root
and finite-Galois fixed-field nodes). The distinct-linear-factor Chinese remainder theorem
then gives the displayed tensor isomorphism and its formula on pure tensors. The affine
tensor/pullback consequence identifies the components and both projection maps. Finally,
the finite-separable-spectrum etale lemma supplies the site objects, and the finite-coproduct
sheaf-sections theorem gives the bijection and both restriction formulas (Stacks, Tag 03SF).
(blueprint: lem-exc-finite-galois-tensor-decomposition) -/
theorem finiteGaloisTensorDecomposition
    (L E : Type u) [Field L] [Field E] [Algebra L E]
    [FiniteDimensional L E] [IsGalois L E]
    (F : Sheaf ((Spec (CommRingCat.of L)).smallEtaleTopology) (Type v)) :
    (∃ φ : (E ⊗[L] E) ≃ₐ[L] ((E ≃ₐ[L] E) → E),
      ∀ (a b : E) (q : E ≃ₐ[L] E), φ (a ⊗ₜ[L] b) q = a * q b) ∧
    (let π : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L) :=
        Spec.map (CommRingCat.ofHom (algebraMap L E))
      ∃ (hπ : Etale π) (hW : Etale (pullback.fst π π ≫ π)),
        letI : Etale π := hπ
        letI : Etale (pullback.fst π π ≫ π) := hW
        let U : (Spec (CommRingCat.of L)).Etale := .mk π
        let V : (Spec (CommRingCat.of L)).Etale := .mk (pullback.fst π π ≫ π)
        ∃ (p₁ p₂ : V ⟶ U) (σ : (E ≃ₐ[L] E) → (U ⟶ U)),
          p₁.left = pullback.fst π π ∧
          p₂.left = pullback.snd π π ∧
          (∀ q : E ≃ₐ[L] E, (σ q).left =
            Spec.map (CommRingCat.ofHom q.toRingEquiv.toRingHom)) ∧
          ∃ β : F.obj.obj (Opposite.op V) ≃
              ((E ≃ₐ[L] E) → F.obj.obj (Opposite.op U)),
            (∀ s q, β (F.obj.map p₁.op s) q = s) ∧
            (∀ s q, β (F.obj.map p₂.op s) q = F.obj.map (σ q).op s)) := by
  classical
  obtain ⟨φ, hφ⟩ := finiteGaloisTensorAlgEquiv L E
  refine ⟨⟨φ, hφ⟩, ?_⟩
  let π : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of L) :=
    Spec.map (CommRingCat.ofHom (algebraMap L E))
  have hπ : Etale π := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr Algebra.Etale.of_finite_of_isSeparable
  let : Etale π := hπ
  have hW : Etale (pullback.fst π π ≫ π) := inferInstance
  refine ⟨hπ, hW, ?_⟩
  let : Etale (pullback.fst π π ≫ π) := hW
  let U : (Spec (CommRingCat.of L)).Etale := .mk π
  let V : (Spec (CommRingCat.of L)).Etale := .mk (pullback.fst π π ≫ π)
  let p₁ : V ⟶ U := MorphismProperty.Over.homMk (pullback.fst π π) rfl
  let p₂ : V ⟶ U :=
    MorphismProperty.Over.homMk (pullback.snd π π) (pullback.condition.symm)
  let σ : (E ≃ₐ[L] E) → (U ⟶ U) := fun q ↦
    MorphismProperty.Over.homMk
      (Spec.map (CommRingCat.ofHom q.toRingEquiv.toRingHom)) (by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext x
        exact q.commutes x)
  obtain ⟨e, he₁, he₂⟩ := finiteGaloisTensorCoproduct L E φ hφ
  let A := fun _ : E ≃ₐ[L] E ↦ Spec (CommRingCat.of E)
  let j : (E ≃ₐ[L] E) → (U ⟶ V) := fun q ↦
    MorphismProperty.Over.homMk (Sigma.ι A q ≫ e.hom) (by
      change (Sigma.ι A q ≫ e.hom) ≫ pullback.fst π π ≫ π = π
      rw [← Category.assoc, Category.assoc (Sigma.ι A q), he₁ q, Category.id_comp])
  have hj₁ (q) : j q ≫ p₁ = 𝟙 U := by
    apply MorphismProperty.Over.Hom.ext
    exact he₁ q
  have hj₂ (q) : j q ≫ p₂ = σ q := by
    apply MorphismProperty.Over.Hom.ext
    exact he₂ q
  have hm (q : E ≃ₐ[L] E) : Mono ((j q).left) := by
    change Mono (Sigma.ι A q ≫ e.hom)
    infer_instance
  have (q : E ≃ₐ[L] E) : Mono (j q) :=
    (Scheme.Etale.forget _ ⋙ Over.forget _).mono_of_mono_map (hm q)
  have hcov : Sieve.ofArrows (fun _ ↦ U) j ∈
      (Spec (CommRingCat.of L)).smallEtaleTopology V := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, rfl⟩ := e.hom.surjective x
    obtain ⟨⟨q, z⟩, rfl⟩ := (sigmaMk A).surjective y
    refine Set.mem_iUnion.mpr ⟨q, z, ?_⟩
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply]
    rfl
  have hd (q r : E ≃ₐ[L] E) (hqr : q ≠ r) :
      Disjoint (Set.range (j q).left.base) (Set.range (j r).left.base) := by
    apply Set.disjoint_iff_forall_ne.mpr
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have hxy' : Sigma.ι A q x = Sigma.ι A r y := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.forgetToTop.map e.hom)).1
      change e.hom (Sigma.ι A q x) = e.hom (Sigma.ι A r y)
      change (Sigma.ι A q ≫ e.hom) x = (Sigma.ι A r ≫ e.hom) y at hxy
      simpa only [Scheme.Hom.comp_apply] using hxy
    exact hqr (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff A q r x y).mp hxy')).1
  let := Scheme.Etale.isIso_piLift_of_disjoint F (fun _ ↦ U) j hcov hd
  have hb : Function.Bijective (fun s : F.obj.obj (Opposite.op V) ↦
      fun q ↦ F.obj.map (j q).op s) := by
    let B : (E ≃ₐ[L] E) → Type v := fun _ ↦ F.obj.obj (Opposite.op U)
    let t : F.obj.obj (Opposite.op V) ⟶ (∏ᶜ B : Type v) :=
      Pi.lift fun q ↦ F.obj.map (j q).op
    let c := Types.Small.productIso.{u, v} B
    have h := (equivShrink.{v} (∀ q, B q)).symm.bijective.comp
      (c.toEquiv.bijective.comp (ConcreteCategory.bijective_of_isIso t))
    convert h using 1
    ext s q
    change _ = (equivShrink.{v} (∀ q, B q)).symm (c.hom (t s)) q
    have hc := ConcreteCategory.congr_hom
      (Types.Small.productIso_hom_comp_eval B q) (t s)
    change (equivShrink.{v} (∀ q, B q)).symm (c.hom (t s)) q = Pi.π B q (t s) at hc
    rw [hc, ← ConcreteCategory.comp_apply, Pi.lift_comp_π]
  let β := Equiv.ofBijective _ hb
  refine ⟨p₁, p₂, σ, rfl, rfl, (fun _ ↦ rfl), β, ?_, ?_⟩
  · intro s q
    change F.obj.map (j q).op (F.obj.map p₁.op s) = s
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, hj₁]
    simp
  · intro s q
    change F.obj.map (j q).op (F.obj.map p₂.op s) = F.obj.map (σ q).op s
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp, ← op_comp, hj₂]

end AlgebraicGeometry
