/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TangentVectorsVectorSpace
public import WeilConjectures.AlgebraicGeometry.DualNumbers

/-!
# Linearity of the map on dual-number tangent vectors

Source: Stacks Project, Tag 0B2F, with base `Spec k`
(blueprint: lem-sc-tangent-map-linear).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

-- Change coefficients in the two-direction square-zero algebra.
private def tangentPairMap {R S : Type u} [CommRing R] [CommRing S]
    (e : R →+* S) :
    TrivSqZeroExt R (Fin 2 → R) →+* TrivSqZeroExt S (Fin 2 → S) where
  toFun z := ⟨e z.fst, fun i ↦ e (z.snd i)⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · funext i; simp
  map_mul' z w := by
    apply TrivSqZeroExt.ext
    · simp
    · funext i; simp [TrivSqZeroExt.snd_mul, smul_eq_mul]
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · funext i; simp
  map_add' z w := by
    apply TrivSqZeroExt.ext
    · simp
    · funext i; simp

open Classical in
/-- Postcomposition with a morphism over `k` induces a linear map on tangent vectors when
its residue-field map is an isomorphism.
Source: Stacks Project, Tag 0B2F (blueprint: lem-sc-tangent-map-linear).

The additive groups and modules are selected from `exists_tangentVectors_vectorSpace`.
The target scalars are transported along the inverse residue-field isomorphism `e.symm`.
Likewise `d` identifies the two dual-number spectra, so `d ≫ θ.val ≫ f` is precisely
postcomposition with `f` after the residue fields have been identified.

Proof:
1. Residue-field point naturality (lem-weil-pbc-residue-field-point-naturality) gives
   `Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x) =
   X.fromSpecResidueField x ≫ f`. Hence the composite has the required closed point.
   Associativity and `hf` also show that it is a morphism over `k`.
2. By the scalar formula of lem-sc-tangent-space-vector-space, multiplication by a scalar
   is precomposition with the dual-number scaling map. Under `e`, these scaling maps
   agree. Precomposition commutes with postcomposition, including for the zero scalar.
3. By the pushout and addition formula of lem-sc-tangent-space-vector-space, two tangent
   vectors glue uniquely to a map from the two-direction square-zero spectrum. Composing
   this map with `f` gives the gluing of the two images, by uniqueness. Precomposition
   with the sum map therefore proves additivity. This and step 2 give the linear map.
-/
theorem exists_tangentMap_linear
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X)
    (he : Function.Bijective (f.residueFieldMap x).hom) :
    let KX := X.residueField x
    let KY := Y.residueField (f x)
    let DX := Spec (.of (DualNumber KX))
    let DY := Spec (.of (DualNumber KY))
    let cX : Spec KX ⟶ DX :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KX KX KX).toRingHom)
    let cY : Spec KY ⟶ DY :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KY KY KY).toRingHom)
    let qX : DX ⟶ Spec KX :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KX KX))
    let qY : DY ⟶ Spec KY :=
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KY KY))
    let bX := X.fromSpecResidueField x
    let bY := Y.fromSpecResidueField (f x)
    let TX := {θ : DX ⟶ X // cX ≫ θ = bX ∧ θ ≫ pX = qX ≫ bX ≫ pX}
    let TY := {θ : DY ⟶ Y // cY ≫ θ = bY ∧ θ ≫ pY = qY ≫ bY ≫ pY}
    let hX := (exists_tangentVectors_vectorSpace k X pX x).2.2.2
    let hY := (exists_tangentVectors_vectorSpace k Y pY (f x)).2.2.2
    letI : AddCommGroup TX := Classical.choose hX
    letI : AddCommGroup TY := Classical.choose hY
    letI : Module KX TX := Classical.choose (Classical.choose_spec hX)
    letI : Module KY TY := Classical.choose (Classical.choose_spec hY)
    let e : KY ≃+* KX := RingEquiv.ofBijective (f.residueFieldMap x).hom he
    letI : Module KX TY := Module.compHom TY e.symm.toRingHom
    let d : DY ⟶ DX := Spec.map (CommRingCat.ofHom
      (DualNumber.mapRingHom e.symm.toRingHom))
    ∃ L : TX →ₗ[KX] TY, ∀ θ : TX, (L θ).val = d ≫ θ.val ≫ f := by
  let KX := X.residueField x
  let KY := Y.residueField (f x)
  let DX := Spec (.of (DualNumber KX))
  let DY := Spec (.of (DualNumber KY))
  let cX : Spec KX ⟶ DX :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KX KX KX).toRingHom)
  let cY : Spec KY ⟶ DY :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom KY KY KY).toRingHom)
  let qX : DX ⟶ Spec KX :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KX KX))
  let qY : DY ⟶ Spec KY :=
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom KY KY))
  let bX := X.fromSpecResidueField x
  let bY := Y.fromSpecResidueField (f x)
  let TX := {θ : DX ⟶ X // cX ≫ θ = bX ∧ θ ≫ pX = qX ≫ bX ≫ pX}
  let TY := {θ : DY ⟶ Y // cY ≫ θ = bY ∧ θ ≫ pY = qY ≫ bY ≫ pY}
  let hX := (exists_tangentVectors_vectorSpace k X pX x).2.2.2
  let hY := (exists_tangentVectors_vectorSpace k Y pY (f x)).2.2.2
  let : AddCommGroup TX := Classical.choose hX
  let : AddCommGroup TY := Classical.choose hY
  let : Module KX TX := Classical.choose (Classical.choose_spec hX)
  let : Module KY TY := Classical.choose (Classical.choose_spec hY)
  let e : KY ≃+* KX := RingEquiv.ofBijective (f.residueFieldMap x).hom he
  let : Module KX TY := Module.compHom TY e.symm.toRingHom
  let d : DY ⟶ DX := Spec.map (CommRingCat.ofHom
    (DualNumber.mapRingHom e.symm.toRingHom))
  change ∃ L : TX →ₗ[KX] TY, ∀ θ : TX, (L θ).val = d ≫ θ.val ≫ f
  let a : Spec KY ⟶ Spec KX := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  have hab : a ≫ bX ≫ f = bY := by
    rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x, ← Spec.map_comp_assoc]
    have hi : f.residueFieldMap x ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 KY := by
      ext z
      exact e.symm_apply_apply z
    rw [hi, Spec.map_id, Category.id_comp]
  have hcd : cY ≫ d = a ≫ cX := by
    dsimp [cY, d, a, cX]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change (DualNumber.mapRingHom e.symm.toRingHom z).fst = e.symm z.fst
    simp
  have hdq : d ≫ qX = qY ≫ a := by
    dsimp [d, qX, qY, a]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change DualNumber.mapRingHom e.symm.toRingHom (TrivSqZeroExt.inl z) =
      TrivSqZeroExt.inl (e.symm z)
    apply TrivSqZeroExt.ext <;> simp
  let F : TX → TY := fun θ ↦ ⟨d ≫ θ.val ≫ f, by
    constructor
    · calc
        cY ≫ (d ≫ θ.val ≫ f) = (cY ≫ d) ≫ θ.val ≫ f := by
          simp only [Category.assoc]
        _ = (a ≫ cX) ≫ θ.val ≫ f := by rw [hcd]
        _ = a ≫ (cX ≫ θ.val) ≫ f := by simp only [Category.assoc]
        _ = a ≫ bX ≫ f := by rw [θ.property.1]
        _ = bY := hab
    · calc
        (d ≫ θ.val ≫ f) ≫ pY = d ≫ (θ.val ≫ pX) := by
          simp only [Category.assoc, hf]
        _ = d ≫ qX ≫ bX ≫ pX := by rw [θ.property.2]
        _ = (qY ≫ a) ≫ bX ≫ pX := by rw [← Category.assoc d qX, hdq]
        _ = qY ≫ bY ≫ pY := by
          rw [← hf]
          simpa only [Category.assoc] using congrArg (fun z ↦ qY ≫ z ≫ pY) hab⟩
  let mX (t : KX) : DX ⟶ DX := Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (t • (LinearMap.id : KX →ₗ[KX] KX))).toRingHom)
  let mY (t : KY) : DY ⟶ DY := Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (t • (LinearMap.id : KY →ₗ[KY] KY))).toRingHom)
  have hscale (t : KX) : d ≫ mX t = mY (e.symm t) ≫ d := by
    dsimp [d, mX, mY]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change DualNumber.mapRingHom e.symm.toRingHom
        (TrivSqZeroExt.map (t • (LinearMap.id : KX →ₗ[KX] KX)) z) =
      TrivSqZeroExt.map (e.symm t • (LinearMap.id : KY →ₗ[KY] KY))
        (DualNumber.mapRingHom e.symm.toRingHom z)
    apply TrivSqZeroExt.ext <;> simp [smul_eq_mul]
  have hopsX := Classical.choose_spec (Classical.choose_spec hX)
  have hopsY := Classical.choose_spec (Classical.choose_spec hY)
  have hsmulX (t : KX) (θ : TX) : (t • θ).val = mX t ≫ θ.val :=
    hopsX.2.2 t θ
  have hsmulY (t : KY) (θ : TY) : (t • θ).val = mY t ≫ θ.val :=
    hopsY.2.2 t θ
  have hFsmul (t : KX) (θ : TX) : F (t • θ) = t • F θ := by
    apply Subtype.ext
    change d ≫ (t • θ).val ≫ f = (e.symm t • F θ).val
    rw [hsmulX, hsmulY]
    change d ≫ (mX t ≫ θ.val) ≫ f = mY (e.symm t) ≫ d ≫ θ.val ≫ f
    simp only [Category.assoc]
    rw [← Category.assoc d (mX t), hscale]
    simp only [Category.assoc]
  let EX := Spec (.of (TrivSqZeroExt KX (Fin 2 → KX)))
  let EY := Spec (.of (TrivSqZeroExt KY (Fin 2 → KY)))
  let jX (i : Fin 2) : DX ⟶ EX := Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → KX) →ₗ[KX] KX)).toRingHom)
  let jY (i : Fin 2) : DY ⟶ EY := Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → KY) →ₗ[KY] KY)).toRingHom)
  let sX : DX ⟶ EX := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map
    ((LinearMap.proj 0 : (Fin 2 → KX) →ₗ[KX] KX) + LinearMap.proj 1)).toRingHom)
  let sY : DY ⟶ EY := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map
    ((LinearMap.proj 0 : (Fin 2 → KY) →ₗ[KY] KY) + LinearMap.proj 1)).toRingHom)
  let δ : EY ⟶ EX := Spec.map (CommRingCat.ofHom (tangentPairMap e.symm.toRingHom))
  have hproj (i : Fin 2) : jY i ≫ δ = d ≫ jX i := by
    dsimp [jX, jY, δ, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → KY) →ₗ[KY] KY)
        (tangentPairMap e.symm.toRingHom z) =
      DualNumber.mapRingHom e.symm.toRingHom
        (TrivSqZeroExt.map (LinearMap.proj i : (Fin 2 → KX) →ₗ[KX] KX) z)
    apply TrivSqZeroExt.ext <;> simp [tangentPairMap]
  have hsum : sY ≫ δ = d ≫ sX := by
    dsimp [sX, sY, δ, d]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    change TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → KY) →ₗ[KY] KY) + LinearMap.proj 1)
        (tangentPairMap e.symm.toRingHom z) =
      DualNumber.mapRingHom e.symm.toRingHom (TrivSqZeroExt.map
        ((LinearMap.proj 0 : (Fin 2 → KX) →ₗ[KX] KX) + LinearMap.proj 1) z)
    apply TrivSqZeroExt.ext <;> simp [tangentPairMap]
  have haddX (θ η : TX) (Θ : EX ⟶ X)
      (h0 : jX 0 ≫ Θ = θ.val) (h1 : jX 1 ≫ Θ = η.val) :
      (θ + η).val = sX ≫ Θ := hopsX.2.1 θ η Θ h0 h1
  have haddY (θ η : TY) (Θ : EY ⟶ Y)
      (h0 : jY 0 ≫ Θ = θ.val) (h1 : jY 1 ≫ Θ = η.val) :
      (θ + η).val = sY ≫ Θ := hopsY.2.1 θ η Θ h0 h1
  refine ⟨{ toFun := F, map_add' := ?_, map_smul' := hFsmul }, fun θ ↦ rfl⟩
  intro θ η
  obtain ⟨Θ, ⟨h0, h1⟩, _⟩ := (exists_tangentVectors_vectorSpace k X pX x).2.1 θ η
  change jX 0 ≫ Θ = θ.val at h0
  change jX 1 ≫ Θ = η.val at h1
  have hrestrict (i : Fin 2) : jY i ≫ (δ ≫ Θ ≫ f) = d ≫ (jX i ≫ Θ) ≫ f := by
    rw [← Category.assoc, hproj]
    simp only [Category.assoc]
  have hy0 : jY 0 ≫ (δ ≫ Θ ≫ f) = (F θ).val := by
    rw [hrestrict, h0]
  have hy1 : jY 1 ≫ (δ ≫ Θ ≫ f) = (F η).val := by
    rw [hrestrict, h1]
  apply Subtype.ext
  change d ≫ (θ + η).val ≫ f = (F θ + F η).val
  rw [haddX θ η Θ h0 h1, haddY (F θ) (F η) (δ ≫ Θ ≫ f) hy0 hy1]
  simp only [Category.assoc]
  rw [← Category.assoc sY δ, hsum]
  simp only [Category.assoc]

end AlgebraicGeometry
