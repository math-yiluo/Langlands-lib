/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PointCount
public import WeilConjectures.FieldTheory.SepClosedFiniteExtension

/-! # Residue fields of closed points of schemes of finite type over a field

For a scheme `X` locally of finite type over a field `k`, a point is closed if and only if its
residue field is finite over `k` (Zariski's lemma). Over a separably closed field, residue
fields of closed points are finite purely inseparable and separably closed.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1` (a): a point `x` of a scheme
locally of finite type over a field `k` is closed if and only if its residue field `κ(x)` is finite
over `k`.

Proof: one direction is `Hom.finite_residueField_of_isClosed` (Zariski's lemma). Conversely,
if `κ(x)` is finite over `k`, the composite `Spec κ(x) ⟶ X ⟶ Spec k` is finite, so
`Spec κ(x) ⟶ X` is locally of finite type, and in the Jacobson scheme `X` this forces `x` to
be closed. -/
theorem Hom.isClosed_singleton_iff_finite_residueField (f : X.Hom (Spec (.of k)))
    [LocallyOfFiniteType f] (x : X) :
    letI := (f.residueFieldAlgebraMap x).toAlgebra
    IsClosed {x} ↔ Module.Finite k (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  refine ⟨f.finite_residueField_of_isClosed x, fun h ↦ ?_⟩
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [← f.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff]
    exact h
  have := locallyOfFiniteType_of_comp (X.fromSpecResidueField x) f
  exact isClosed_singleton_iff_locallyOfFiniteType.2 this

/-- The residue field `κ(x)` of a point of a scheme locally of finite type over `k` is
essentially of finite type over `k`, i.e. a finitely generated field extension of `k`. -/
theorem Hom.essFiniteType_residueFieldAlgebraMap (f : X.Hom (Spec (.of k)))
    [LocallyOfFiniteType f] (x : X) : (f.residueFieldAlgebraMap x).EssFiniteType := by
  rw [Hom.residueFieldAlgebraMap, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.EssFiniteType.comp ?_ (RingHom.EssFiniteType.comp ?_ ?_)
  · exact RingHom.essFiniteType_algebraMap.2 inferInstance
  · exact (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Spec.residueFieldIso _ _).inv).2).essFiniteType
  · exact RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)

/-- A finitely generated algebraic field extension is finite. -/
theorem _root_.Module.Finite.of_essFiniteType_of_isAlgebraic (K L : Type*) [Field K] [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] [Algebra.IsAlgebraic K L] : Module.Finite K L := by
  obtain ⟨s, hs⟩ := IntermediateField.fg_top_iff.2 (inferInstance : Algebra.EssFiniteType K L)
  have : FiniteDimensional K (IntermediateField.adjoin K (s : Set L)) :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  rw [hs] at this
  exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1` (a), transcendence degree form: a
point `x` of a scheme locally of finite type over a field `k` is closed if and only if `κ(x)` is
algebraic over `k` (i.e. `trdeg_k κ(x) = 0`).

Proof: `κ(x)` is a finitely generated field extension of `k`, so it is algebraic if and only if
it is finite; conclude by `Hom.isClosed_singleton_iff_finite_residueField`. -/
theorem Hom.isClosed_singleton_iff_isAlgebraic_residueField (f : X.Hom (Spec (.of k)))
    [LocallyOfFiniteType f] (x : X) :
    letI := (f.residueFieldAlgebraMap x).toAlgebra
    IsClosed {x} ↔ Algebra.IsAlgebraic k (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  rw [f.isClosed_singleton_iff_finite_residueField x]
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ?_⟩
  have : Algebra.EssFiniteType k (X.residueField x) :=
    RingHom.essFiniteType_algebraMap.1 (f.essFiniteType_residueFieldAlgebraMap x)
  exact Module.Finite.of_essFiniteType_of_isAlgebraic k _

/-- Blueprint `lemma-sheaves-finite-support-finite-morphisms--1` (b): if `k` is separably closed and
`x` is a closed point of a scheme locally of finite type over `k`, then `κ(x)` is finite and purely
inseparable over `k`, and `κ(x)` is separably closed.

Proof: finiteness is part (a); a finite extension of a separably closed field is purely
inseparable (`lemma-sheaves-finite-support-finite-morphisms--1`) and separably closed
(`lemma-sheaves-finite-support-finite-morphisms--1`). -/
theorem Hom.residueField_of_isClosed_of_isSepClosed [IsSepClosed k] (f : X.Hom (Spec (.of k)))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed {x}) :
    letI := (f.residueFieldAlgebraMap x).toAlgebra
    Module.Finite k (X.residueField x) ∧ IsPurelyInseparable k (X.residueField x) ∧
      IsSepClosed (X.residueField x) := by
  let := (f.residueFieldAlgebraMap x).toAlgebra
  have := f.finite_residueField_of_isClosed x hx
  exact ⟨this, IsSepClosed.isPurelyInseparable_of_finite k _, IsSepClosed.of_finite k _⟩

end AlgebraicGeometry.Scheme
