/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.AdelicStructureSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.LocalCommensurable
public import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
public import WeilConjectures.AlgebraicGeometry.DensePoints

/-!
# The local rings of a smooth curve at closed points

Let `X` be an integral scheme smooth of relative dimension one over a field `k`, with function
field `K`, and `x` a closed point. The local ring `𝒪_{X,x} ⊆ K`
(`AlgebraicGeometry.Scheme.localSubalgebra k X x`) is a discrete valuation ring with fraction field
`K`, and its residue field is `k`-isomorphic to `κ(x)`, hence finite over `k`. Consequently:

- for every `f ∈ K`, `f 𝒪_{X,x}` and `𝒪_{X,x}` are commensurable
  (`AlgebraicGeometry.Scheme.finiteDimensional_sup_quotient_inf_localSubalgebra`);
- if `κ(x)` is separable over `k` (such closed points are dense,
  `AlgebraicGeometry.Scheme.Hom.dense_setOf_isClosed_finite_isSeparable`), then for a uniformiser
  `ϖ` some `u ∈ 𝒪_{X,x}` acts on `𝒪_{X,x} ⧸ ϖ 𝒪_{X,x}` with nonzero trace
  (`AlgebraicGeometry.Scheme.exists_trace_mapQ_ne_zero_of_isSeparable`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace Pointwise

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- The embedding `k → κ(x)` is the residue of the germ at `x` of the structure map. -/
lemma Hom.residueFieldAlgebraMap_apply (x : X) (c : k) :
    (X ↘ Spec (.of k)).residueFieldAlgebraMap x c =
      X.residue x (X.presheaf.germ ⊤ x trivial (globalSectionsRingHom k (X := X) c)) := by
  have : CommRingCat.ofHom (algebraMap (CommRingCat.of k)
      ((X ↘ Spec (.of k)).base x).asIdeal.ResidueField) ≫
      (Spec.residueFieldIso (.of k) ((X ↘ Spec (.of k)).base x)).inv ≫
        (X ↘ Spec (.of k)).residueFieldMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
    rw [Spec.algebraMap_residueFieldIso_inv_assoc, Scheme.residue_residueFieldMap,
      Scheme.Hom.germ_stalkMap_assoc]
    rfl
  exact congr_arg (fun φ ↦ φ.hom c) this

variable (k X) [IsIntegral X] [Algebra k X.functionField] [IsFunctionFieldAlgebra k X]

/-- The local ring `𝒪_{X,x} ⊆ K` has fraction field `K`. -/
instance isFractionRing_localSubalgebra (x : X) :
    IsFractionRing (localSubalgebra k X x) X.functionField := by
  have : FaithfulSMul (localSubalgebra k X x) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨U, hU, hxU, -⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show x ∈ (⊤ : X.Opens) from trivial)
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(X, U)) z
  exact ⟨⟨_, ⟨U, hxU, a, rfl⟩⟩, ⟨_, ⟨U, hxU, b, rfl⟩⟩, rfl⟩

/-- The local subalgebra `𝒪_{X,x} ⊆ K` is a local ring. -/
instance isLocalRing_localSubalgebra (x : X) : IsLocalRing (localSubalgebra k X x) :=
  (stalkEquivLocalSubalgebra k X x).isLocalRing

/-- The residue field of `𝒪_{X,x} ⊆ K` is `k`-isomorphic to `κ(x)`. -/
noncomputable def residueFieldLocalSubalgebraEquiv (x : X) :
    letI := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
    IsLocalRing.ResidueField (localSubalgebra k X x) ≃ₐ[k] X.residueField x :=
  letI := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
  AlgEquiv.ofRingEquiv
    (f := (IsLocalRing.ResidueField.mapEquiv (stalkEquivLocalSubalgebra k X x).symm :
      IsLocalRing.ResidueField (localSubalgebra k X x) ≃+* X.residueField x)) fun c ↦ by
    have h : (stalkEquivLocalSubalgebra k X x).symm (algebraMap k (localSubalgebra k X x) c) =
        X.presheaf.germ ⊤ x trivial (globalSectionsRingHom k (X := X) c) := by
      have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
      rw [RingEquiv.symm_apply_eq]
      refine Subtype.ext ?_
      rw [coe_stalkEquivLocalSubalgebra, Scheme.algebraMap_germ_eq_germToFunctionField]
      exact IsFunctionFieldAlgebra.algebraMap_eq c
    rw [IsScalarTower.algebraMap_apply k (localSubalgebra k X x)
      (IsLocalRing.ResidueField (localSubalgebra k X x)), IsLocalRing.ResidueField.algebraMap_eq]
    change IsLocalRing.residue _ ((stalkEquivLocalSubalgebra k X x).symm
      (algebraMap k (localSubalgebra k X x) c)) = _
    rw [h, RingHom.algebraMap_toAlgebra, Hom.residueFieldAlgebraMap_apply]
    rfl

section Smooth

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] {x : X} (hx : IsClosed {x})
include hx

/-- At a closed point of a smooth curve, the local ring `𝒪_{X,x} ⊆ K` is a discrete valuation
ring. -/
lemma isDiscreteValuationRing_localSubalgebra :
    IsDiscreteValuationRing (localSubalgebra k X x) :=
  have ⟨_, _⟩ := isDiscreteValuationRing_stalk_of_isClosed (X ↘ Spec (.of k)) hx
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing (stalkEquivLocalSubalgebra k X x)

/-- At a closed point of a smooth curve, the residue field of `𝒪_{X,x} ⊆ K` is finite over
`k`. -/
lemma finite_residueField_localSubalgebra :
    Module.Finite k (IsLocalRing.ResidueField (localSubalgebra k X x)) := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  let := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
  have := (X ↘ Spec (.of k)).finite_residueField_of_isClosed x hx
  exact Module.Finite.equiv (residueFieldLocalSubalgebraEquiv k X x).symm.toLinearEquiv

/-- **Commensurability of the local rings** (one-sided): `(f 𝒪_{X,x} + 𝒪_{X,x}) ⧸ 𝒪_{X,x}` is
finite-dimensional over `k` for every `f ∈ K`. -/
theorem finiteDimensional_sup_quotient_localSubalgebra (f : X.functionField) :
    FiniteDimensional k (↥(f • Subalgebra.toSubmodule (localSubalgebra k X x) ⊔
      Subalgebra.toSubmodule (localSubalgebra k X x)) ⧸
      (Subalgebra.toSubmodule (localSubalgebra k X x)).comap
        (f • Subalgebra.toSubmodule (localSubalgebra k X x) ⊔
          Subalgebra.toSubmodule (localSubalgebra k X x)).subtype) :=
  have := isDiscreteValuationRing_localSubalgebra k X hx
  have := finite_residueField_localSubalgebra k X hx
  Subalgebra.finiteDimensional_sup_quotient _ f

/-- **Commensurability of the local rings**: `(f 𝒪_{X,x} + 𝒪_{X,x}) ⧸ (f 𝒪_{X,x} ∩ 𝒪_{X,x})` is
finite-dimensional over `k` for every nonzero `f ∈ K`. -/
theorem finiteDimensional_sup_quotient_inf_localSubalgebra {f : X.functionField} (hf : f ≠ 0) :
    FiniteDimensional k (↥(f • Subalgebra.toSubmodule (localSubalgebra k X x) ⊔
      Subalgebra.toSubmodule (localSubalgebra k X x)) ⧸
      (f • Subalgebra.toSubmodule (localSubalgebra k X x) ⊓
        Subalgebra.toSubmodule (localSubalgebra k X x)).comap
        (f • Subalgebra.toSubmodule (localSubalgebra k X x) ⊔
          Subalgebra.toSubmodule (localSubalgebra k X x)).subtype) :=
  have := isDiscreteValuationRing_localSubalgebra k X hx
  have := finite_residueField_localSubalgebra k X hx
  Subalgebra.finiteDimensional_sup_quotient_inf _ hf

/-- **Nonzero trace at a separable closed point.** Let `x` be a closed point of a smooth curve
with `κ(x)` separable over `k` and `ϖ` a uniformiser of `𝒪_{X,x}`. Then some `u ∈ 𝒪_{X,x}` acts
on `𝒪_{X,x} ⧸ ϖ 𝒪_{X,x}` (finite-dimensional, `≅ κ(x)`) with nonzero trace over `k`. -/
theorem exists_trace_mapQ_ne_zero_of_isSeparable
    (hsep : letI := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
      Algebra.IsSeparable k (X.residueField x))
    {ϖ : localSubalgebra k X x} (hϖ : Irreducible ϖ) :
    ∃ u : localSubalgebra k X x,
      LinearMap.trace k _ (Submodule.mapQ _ _ (Subalgebra.mulToSubmodule _ u)
        (Subalgebra.mulToSubmodule_le_comap _ u (ϖ : X.functionField))) ≠ 0 := by
  have := isDiscreteValuationRing_localSubalgebra k X hx
  have := finite_residueField_localSubalgebra k X hx
  let := ((X ↘ Spec (.of k)).residueFieldAlgebraMap x).toAlgebra
  have : Algebra.IsSeparable k (IsLocalRing.ResidueField (localSubalgebra k X x)) :=
    Algebra.IsSeparable.of_algHom _ _ (residueFieldLocalSubalgebraEquiv k X x).toAlgHom
  obtain ⟨u, hu⟩ := Subalgebra.exists_trace_residue_ne_zero (localSubalgebra k X x)
  exact ⟨u, by rwa [Subalgebra.trace_mapQ_mulToSubmodule _ hϖ]⟩

end Smooth

end AlgebraicGeometry.Scheme
