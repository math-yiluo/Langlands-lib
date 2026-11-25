/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification

/-!
# Local realization of equivariant geometric-point maps

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The singleton at a point of an étale K-scheme is the spectrum of its residue field.
The base algebra is the canonical map recovered from the residue-field point by Spec.
Source: Stacks Project, Tag 02GL(1). Discreteness follows from quasi-finiteness over a
one-point base. The residue-field map is étale, so the extension is finite separable.
The residue-field point lifts to the singleton open; it is a surjective closed immersion
into a reduced scheme, hence an isomorphism. -/
private theorem singleton_chart
    (K : Type u) [Field K] (X : Scheme.Etale (Spec (CommRingCat.of K))) (x : X.left) :
    let i := Spec.homEquiv (X.left.fromSpecResidueField x ≫ X.hom)
    let := i.hom.toAlgebra
    Module.Finite K (X.left.residueField x) ∧
      Algebra.IsSeparable K (X.left.residueField x) ∧
      ∃ U : X.left.Opens, (U : Set X.left) = {x} ∧
        ∃ e : U.toScheme ≅ Spec (X.left.residueField x),
          e.hom ≫ Spec.map i = U.ι ≫ X.hom:= by
  classical
  let q : X.left ⟶ Spec (CommRingCat.of K) := X.hom
  have : DiscreteTopology X.left := by
    have hd := q.isDiscrete_preimage_singleton (default : Spec (CommRingCat.of K))
    have heq : q ⁻¹' {default} = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq] at hd
    exact isDiscrete_univ_iff.mp hd
  let g := X.left.fromSpecResidueField x
  let i := Spec.homEquiv (g ≫ q)
  let := i.hom.toAlgebra
  have : IsClosedImmersion ((Spec (CommRingCat.of K)).fromSpecResidueField (q x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp (isClosed_discrete _)
  have : Surjective ((Spec (CommRingCat.of K)).fromSpecResidueField (q x)) :=
    ⟨fun z ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective
    ((Spec (CommRingCat.of K)).fromSpecResidueField (q x))
  have : Etale (Spec.map (q.residueFieldMap x)) :=
    HasRingHomProperty.Spec_iff.mpr (q.etale_residueFieldMap x)
  have : Etale (g ≫ q) := by
    dsimp [g]
    rw [← q.SpecMap_residueFieldMap_fromSpecResidueField x]
    infer_instance
  have heq : Spec.map i = g ≫ q := Spec.homEquiv.symm_apply_apply _
  have : Etale (Spec.map i) := heq ▸ ‹Etale (g ≫ q)›
  have : Algebra.Etale K (X.left.residueField x) := by
    rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
    exact HasRingHomProperty.Spec_iff.mp ‹Etale (Spec.map i)›
  have : Module.Finite K (X.left.residueField x) :=
    Algebra.FormallyUnramified.finite_of_free _ _
  have : Algebra.IsSeparable K (X.left.residueField x) :=
    (Algebra.FormallyEtale.iff_isSeparable _ _).mp inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have : IsReduced X.left := isReduced_of_etale q
  let U : X.left.Opens := ⟨{x}, isOpen_discrete _⟩
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, Scheme.range_fromSpecResidueField]
    exact Set.Subset.rfl
  let l := IsOpenImmersion.lift U.ι g hr
  have hl : l ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have : IsPreimmersion (l ≫ U.ι) := hl ▸ inferInstance
  have : IsPreimmersion l := .of_comp l U.ι
  have : Surjective l := by
    constructor
    intro z
    refine ⟨default, ?_⟩
    apply (U.ι).isOpenEmbedding.injective
    change (l ≫ U.ι) default = z.val
    rw [hl, Scheme.fromSpecResidueField_apply]
    exact z.property.symm
  have : IsClosedImmersion l := .of_isPreimmersion l (isClosed_discrete _)
  have : IsReduced U.toScheme := isReduced_of_isOpenImmersion U.ι
  have : IsIso l := isIso_of_isClosedImmersion_of_surjective l
  refine ⟨U, rfl, (asIso l).symm, ?_⟩
  change inv l ≫ Spec.map i = U.ι ≫ q
  rw [heq]
  rw [← hl]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- An equivariant geometric-point map is realized on a neighbourhood of each source point.
Source: Stacks Project, Tag 03QR, finite-spectrum classification in the equivalence proof
(blueprint: lem-exc-etale-field-point-map-local).

Proof: Take the singleton open U at the given point. By the étale fibre decomposition
it is Spec L for a finite separable K-extension L. Its geometric points identify with
K-embeddings L → Ksep and form a nonempty transitive Galois set. Equivariance makes
their images lie in one orbit, hence in the singleton open Spec L' of the target.
The finite Galois classification gives a K-algebra homomorphism L' → L whose map on
embeddings is exactly the restriction of the given equivariant map. Apply Spec,
transport through the singleton-open isomorphisms, and compose with the target open
immersion. This gives f, its equality over Spec K, and the displayed identity for
every geometric point of U. There is no source point to consider for an empty source;
if the target is empty, existence of the given map excludes any nonempty source. -/
theorem etaleFieldPointMap_local
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (X Y : Scheme.Etale (Spec (CommRingCat.of K)))
    (φ : etaleFieldGeometricAction K Ksep X ⟶ etaleFieldGeometricAction K Ksep Y)
    (x : X.left) :
    ∃ U : X.left.Opens, x ∈ U ∧ ∃ f : U.toScheme ⟶ Y.left,
      f ≫ Y.hom = U.ι ≫ X.hom ∧
        ∀ (p : Spec (CommRingCat.of Ksep) ⟶ U.toScheme)
          (hp : p ≫ (U.ι ≫ X.hom) = (etaleFieldBasePoint K Ksep).hom),
          p ≫ f = (φ.hom (Over.homMk (p ≫ U.ι) (by simpa using hp))).left := by
  classical
  let q : X.left ⟶ Spec (CommRingCat.of K) := X.hom
  let L := X.left.residueField x
  let i := Spec.homEquiv (X.left.fromSpecResidueField x ≫ q)
  let : Algebra K L := i.hom.toAlgebra
  obtain ⟨hfin, hsep, U, hU, e, he⟩ := singleton_chart K X x
  let : Module.Finite K L := hfin
  let : Algebra.IsSeparable K L := hsep
  let j : Spec (CommRingCat.of L) ⟶ X.left := e.inv ≫ U.ι
  have hj : j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    change e.inv ≫ U.ι ≫ q = Spec.map i
    rw [← he]
    simp only [Iso.inv_hom_id_assoc]
    rfl
  let a : (L →ₐ[K] Ksep) →
      (etaleFieldBasePoint K Ksep ⟶ (Scheme.Etale.forget _).obj X) := fun σ ↦
    Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j) (by
      change (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j) ≫ q = _
      rw [Category.assoc, hj, ← Spec.map_comp]
      congr 1
      ext k
      exact σ.commutes k)
  have hag (g : Gal(Ksep/K)) (σ : L →ₐ[K] Ksep) :
      a (g.toAlgHom.comp σ) = etaleFieldPointAutomorphism K Ksep g ≫ a σ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (g.toAlgHom.comp σ).toRingHom) ≫ j =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j)
    have hh : CommRingCat.ofHom (g.toAlgHom.comp σ).toRingHom =
        CommRingCat.ofHom σ.toRingHom ≫ CommRingCat.ofHom g.toRingHom := rfl
    rw [hh, Spec.map_comp]
    exact Category.assoc _ _ _
  let b : (L →ₐ[K] Ksep) → (Spec (CommRingCat.of Ksep) ⟶ Y.left) :=
    fun σ ↦ (φ.hom (a σ)).left
  have hbg (g : Gal(Ksep/K)) (σ : L →ₐ[K] Ksep) :
      b (g.toAlgHom.comp σ) = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ b σ := by
    have h := ConcreteCategory.congr_hom (φ.comm g) (a σ)
    change φ.hom (etaleFieldPointAutomorphism K Ksep g ≫ a σ) =
      etaleFieldPointAutomorphism K Ksep g ≫ φ.hom (a σ) at h
    rw [← hag] at h
    exact congrArg Over.Hom.left h
  have hb (σ : L →ₐ[K] Ksep) :
      b σ ≫ Y.hom = (etaleFieldBasePoint K Ksep).hom := Over.w (φ.hom (a σ))
  have hc := FieldTheory.finite_separable_extension_galois_classification.{u, u, u, u, u} K Ksep L L
  obtain ⟨σ₀⟩ := hc.1.1
  let y : Y.left := b σ₀ default
  have hby (σ : L →ₐ[K] Ksep) (z : Spec (CommRingCat.of Ksep)) : b σ z = y := by
    obtain ⟨g, hg⟩ := hc.1.2.2.1 σ₀ σ
    rw [← hg, hbg]
    change b σ₀ ((Spec.map (CommRingCat.ofHom g.toRingHom)) z) = b σ₀ default
    congr 1
    exact Subsingleton.elim _ _
  let M := Y.left.residueField y
  let i' := Spec.homEquiv (Y.left.fromSpecResidueField y ≫ Y.hom)
  let : Algebra K M := i'.hom.toAlgebra
  obtain ⟨hfin', hsep', V, hV, e', he'⟩ := singleton_chart K Y y
  let : Module.Finite K M := hfin'
  let : Algebra.IsSeparable K M := hsep'
  let k : Spec (CommRingCat.of M) ⟶ Y.left := e'.inv ≫ V.ι
  have hk : k ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    change e'.inv ≫ V.ι ≫ Y.hom = Spec.map i'
    rw [← he']
    simp only [Iso.inv_hom_id_assoc]
    rfl
  have hr (σ : L →ₐ[K] Ksep) : Set.range (b σ) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, hV]
    rintro _ ⟨z, rfl⟩
    exact hby σ z
  let t : (L →ₐ[K] Ksep) →
      (Spec (CommRingCat.of Ksep) ⟶ Spec (CommRingCat.of M)) :=
    fun σ ↦ IsOpenImmersion.lift V.ι (b σ) (hr σ) ≫ e'.hom
  have ht (σ : L →ₐ[K] Ksep) : t σ ≫ k = b σ := by
    dsimp [t, k]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact IsOpenImmersion.lift_fac _ _ _
  have htbase (σ : L →ₐ[K] Ksep) :
      t σ ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) =
        (etaleFieldBasePoint K Ksep).hom := by
    rw [← hk, ← Category.assoc, ht, hb]
  have htg (g : Gal(Ksep/K)) (σ : L →ₐ[K] Ksep) :
      t (g.toAlgHom.comp σ) = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ t σ := by
    apply (cancel_mono k).mp
    rw [ht, Category.assoc, ht, hbg]
  let τ : (L →ₐ[K] Ksep) → (M →ₐ[K] Ksep) := fun σ ↦
    { (Spec.homEquiv (t σ)).hom with
      commutes' := by
        intro c
        have h := htbase σ
        have heq : Spec.map (Spec.homEquiv (t σ)) = t σ :=
          Spec.homEquiv.symm_apply_apply _
        rw [← heq] at h
        change Spec.map (Spec.homEquiv (t σ)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap K M)) =
            Spec.map (CommRingCat.ofHom (algebraMap K Ksep)) at h
        rw [← Spec.map_comp] at h
        have h' := Spec.homEquiv.symm.injective h
        exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c }
  have hτ (σ : L →ₐ[K] Ksep) :
      Spec.map (CommRingCat.ofHom (τ σ).toRingHom) = t σ :=
    Spec.homEquiv.symm_apply_apply _
  have hτg (g : Gal(Ksep/K)) (σ : L →ₐ[K] Ksep) :
      τ (g.toAlgHom.comp σ) = g.toAlgHom.comp (τ σ) := by
    apply AlgHom.ext
    intro c
    have h := htg g σ
    rw [← hτ, ← hτ, ← Spec.map_comp] at h
    have h' := Spec.homEquiv.symm.injective h
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c
  obtain ⟨f₀, hf₀⟩ :=
    (FieldTheory.finite_separable_extension_galois_classification.{u, u, u, u, u}
      K Ksep L M).2.2.2 ⟨τ, hτg⟩
  have hf (σ : L →ₐ[K] Ksep) : σ.comp f₀ = τ σ :=
    congrArg (fun ψ ↦ ψ.val σ) hf₀
  let f : U.toScheme ⟶ Y.left := e.hom ≫ Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ k
  have hfbase : f ≫ Y.hom = U.ι ≫ X.hom := by
    dsimp [f]
    rw [Category.assoc, Category.assoc, hk, ← Spec.map_comp]
    have hcomm : CommRingCat.ofHom (algebraMap K M) ≫
        CommRingCat.ofHom f₀.toRingHom = CommRingCat.ofHom (algebraMap K L) := by
      ext c
      exact f₀.commutes c
    change e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K M) ≫
      CommRingCat.ofHom f₀.toRingHom) = U.ι ≫ X.hom
    rw [hcomm]
    exact he
  refine ⟨U, ?_, f, hfbase, ?_⟩
  · change x ∈ (U : Set X.left)
    rw [hU]
    rfl
  · intro p hp
    let r := p ≫ e.hom
    have hrbase : r ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        (etaleFieldBasePoint K Ksep).hom := by
      dsimp [r]
      rw [Category.assoc]
      change p ≫ (e.hom ≫ Spec.map i) = _
      rw [he]
      exact hp
    let σ : L →ₐ[K] Ksep :=
      { (Spec.homEquiv r).hom with
        commutes' := by
          intro c
          have heq : Spec.map (Spec.homEquiv r) = r :=
            Spec.homEquiv.symm_apply_apply _
          have h := hrbase
          rw [← heq] at h
          change Spec.map (Spec.homEquiv r) ≫
            Spec.map (CommRingCat.ofHom (algebraMap K L)) =
              Spec.map (CommRingCat.ofHom (algebraMap K Ksep)) at h
          rw [← Spec.map_comp] at h
          have h' := Spec.homEquiv.symm.injective h
          exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h') c }
    have hσ : Spec.map (CommRingCat.ofHom σ.toRingHom) = r :=
      Spec.homEquiv.symm_apply_apply _
    have ha : a σ = Over.homMk (p ≫ U.ι) (by simpa using hp) := by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ j = p ≫ U.ι
      rw [hσ]
      dsimp [r, j]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change p ≫ f = _
    calc
      p ≫ f = r ≫ Spec.map (CommRingCat.ofHom f₀.toRingHom) ≫ k := by
        simp only [f, r, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (σ.comp f₀).toRingHom) ≫ k := by
        rw [← hσ, ← Spec.map_comp_assoc]
        rfl
      _ = b σ := by rw [hf, hτ, ht]
      _ = _ := congrArg (fun z ↦ (φ.hom z).left) ha

end AlgebraicGeometry
