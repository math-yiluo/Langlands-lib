/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TangentMapLinear

/-!
# Tangent spaces at arbitrary points of schemes over a field

Source: Stacks Project, Tags 0B2B, 0B2C and 0B2F, with base `Spec k`
(blueprint: def-sc-scheme-tangent-space).

## Main definitions

* `schemeTangentSpace`: dual-number morphisms over the base with the prescribed closed point.
* `schemeTangentSpaceAddCommGroup` and `schemeTangentSpaceModule`: the canonical vector space
  structure supplied by `exists_tangentVectors_vectorSpace`, with its specified operations.
* `schemeTangentMap`: the linear map supplied by `exists_tangentMap_linear`, given by
  postcomposition after the residue fields are identified.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Tangent vectors at `x` are morphisms from the residue-field dual-number spectrum to `X`
restricting to the canonical point and commuting with the structure morphism to `Spec k`.
Source: Stacks Project, Tag 0B2C (blueprint: def-sc-scheme-tangent-space). -/
def schemeTangentSpace (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (.of k)) (x : X) : Type u :=
  let K := X.residueField x
  let c := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
  let q := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom K K))
  {θ : Spec (.of (DualNumber K)) ⟶ X //
    c ≫ θ = X.fromSpecResidueField x ∧ θ ≫ p = q ≫ X.fromSpecResidueField x ≫ p}

/-- The additive group of tangent vectors is selected from the vector-space existence lemma.
Its zero is the constant point morphism; its addition is gluing along the common closed point,
followed by the map sending both square-zero coordinates to epsilon.
Source: Stacks Project, Tag 0B2B (blueprint: def-sc-scheme-tangent-space). -/
noncomputable instance schemeTangentSpaceAddCommGroup
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    AddCommGroup (schemeTangentSpace k X p x) :=
  Classical.choose (exists_tangentVectors_vectorSpace k X p x).2.2.2

/-- The canonical residue-field module structure, selected together with its additive group.
Multiplication by `t` is precomposition with the spectrum of the map epsilon to `t * epsilon`.
Source: Stacks Project, Tag 0B2B (blueprint: def-sc-scheme-tangent-space). -/
noncomputable instance schemeTangentSpaceModule
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    Module (X.residueField x) (schemeTangentSpace k X p x) :=
  Classical.choose
    (Classical.choose_spec (exists_tangentVectors_vectorSpace k X p x).2.2.2)

/-- The differential of a morphism over `k` with bijective induced residue-field map.
The target scalar action is transported by the inverse residue-field isomorphism. The chosen
linear map has value `d ≫ θ.val ≫ f`, where `d` is the induced identification of dual-number
spectra. This is postcomposition with `f` under the identification of the two residue fields.
Source: Stacks Project, Tag 0B2F (blueprint: def-sc-scheme-tangent-space). -/
noncomputable def schemeTangentMap
    (k : Type u) [Field k] (X Y : Scheme.{u})
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X)
    (he : Function.Bijective (f.residueFieldMap x).hom) :
    let e := RingEquiv.ofBijective (f.residueFieldMap x).hom he
    letI : Module (X.residueField x) (schemeTangentSpace k Y pY (f x)) :=
      Module.compHom (schemeTangentSpace k Y pY (f x)) e.symm.toRingHom
    schemeTangentSpace k X pX x →ₗ[X.residueField x] schemeTangentSpace k Y pY (f x) :=
  Classical.choose (exists_tangentMap_linear k X Y pX pY f hf x he)

end AlgebraicGeometry
