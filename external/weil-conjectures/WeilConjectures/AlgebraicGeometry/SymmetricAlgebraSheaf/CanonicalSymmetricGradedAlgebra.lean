/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraSheafConstruction
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineSectionComparison
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Canonical affine-basis symmetric algebra

Source: Stacks Project, Constructions, Tag 01OB; Modules, Tags 01CG and 01CL
(blueprint: def-trf-canonical-symmetric-graded-algebra).

The rings, grades and restriction homomorphisms are specified constructions. Restriction
preserves the grading and is coefficientwise base change for quasi-coherent modules.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.SymmetricAlgebraSheaf

open scoped TensorProduct

/-- The canonical symmetric grading on an affine section algebra. The decomposition is the
unique inverse of the summation map, using the internality recorded by the symmetric-grading
node; it chooses no algebra or grading.
Source: Stacks Project, Algebra, Section 00DM; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable instance sectionGradedAlgebra {X : Scheme.{u}} (E : X.Modules)
    (U : X.affineOpens) :
    GradedAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, U.1)
      (E.val.obj (op U.1))).range ^ n) := by
  have h := (SymmetricAlgebra.graded_by_tensor_images Γ(X, U.1)
    (E.val.obj (op U.1))).2.2.2.2.1
  simp only [Submodule.map_pow, ← LinearMap.range_comp] at h
  exact DirectSum.IsInternal.gradedAlgebra h

/-- Restriction preserves every symmetric degree.
Source: Stacks Project, Modules, Tag 01CG; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra).

Proof: the degree-n submodule is spanned by products of n degree-one generators.
Restriction sends each generator to the restricted module section and sends scalars by
structure-sheaf restriction. It therefore sends each such product to a product of the same
length, and additivity and semilinearity extend this to its span. -/
theorem restriction_mem_symmetricDegree {X : Scheme.{u}} (E : X.Modules)
    {U V : X.affineOpens} (h : U ≤ V) (n : ℕ)
    (a : sections E (op V.1))
    (ha : a ∈ (SymmetricAlgebra.ι Γ(X, V.1) (E.val.obj (op V.1))).range ^ n) :
    restriction E (homOfLE (X := X.Opens) h).op a ∈
      (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [restriction_algebraMap]
    exact Submodule.algebraMap_mem _
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, restriction_ι, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

/-- The actual symmetric-algebra restriction, bundled with its degree-preservation proof.
Source: Stacks Project, Modules, Tag 01CG; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable def gradedRestriction {X : Scheme.{u}} (E : X.Modules)
    {U V : X.affineOpens} (h : U ≤ V) :
    (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, V.1) (E.val.obj (op V.1))).range ^ n) →+*ᵍ
      (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n) where
  toRingHom := restriction E (homOfLE (X := X.Opens) h).op
  map_mem := fun {n} {a} ha ↦ restriction_mem_symmetricDegree E h n a ha

private theorem graded_bijective_degree
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    {D : ℕ → Submodule R A} {D' : ℕ → Submodule S B}
    [GradedAlgebra D] [GradedAlgebra D']
    (f : D →+*ᵍ D') (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (f.gradedAddHom n) := by
  classical
  constructor
  · intro a b hab
    exact Subtype.ext (hf.injective (congrArg Subtype.val hab))
  · intro b
    obtain ⟨a, ha⟩ := hf.surjective b
    refine ⟨DirectSum.decompose D a n, ?_⟩
    apply Subtype.ext
    change f (DirectSum.decompose D a n) = (b : B)
    rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same D' b.property]

/-- Affine restriction is coefficientwise base change in each symmetric degree.
Source: Stacks Project, Modules, Tags 01CG and 01CL; Constructions, Tag 01LN
(blueprint: def-trf-canonical-symmetric-graded-algebra).

Proof: for affine U contained in V, quasi-coherence identifies E(U) with
O(U) tensor over O(V) E(V), through m tensor r mapping to r times the restricted m.
Symmetric powers commute with this base change: the tensor-algebra base-change
isomorphism preserves degree and takes the commutator ideal to the corresponding
commutator ideal, hence descends degree by degree to symmetric algebras. On generators
this is precisely restriction E, and its scalar equation is restriction_algebraMap.
The resulting bijections in every degree give IsGradedBaseChangeAlong. -/
theorem gradedRestriction_isGradedBaseChangeAlong {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {U V : X.affineOpens} (h : U ≤ V) :
    (gradedRestriction E h).IsGradedBaseChangeAlong
      (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom := by
  classical
  let R := Γ(X, V.1)
  let S := Γ(X, U.1)
  let A := sections E (op V.1)
  let B := sections E (op U.1)
  let D : ℕ → Submodule R A := fun n ↦ (SymmetricAlgebra.ι R _).range ^ n
  let D' : ℕ → Submodule S B := fun n ↦ (SymmetricAlgebra.ι S _).range ^ n
  let : Algebra R S := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  let : Algebra R B := ((algebraMap S B).comp
    (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom).toAlgebra
  have : IsScalarTower R S B := .of_algebraMap_eq' rfl
  let f : D →ₐᵍ[R] (fun n ↦ (D' n).restrictScalars R) :=
    { toRingHom := restriction E (homOfLE (X := X.Opens) h).op
      commutes' := restriction_algebraMap E _
      map_mem := fun {n} {a} ha ↦ restriction_mem_symmetricDegree E h n a ha }
  let Φ := GradedAlgHom.liftEquiv D D' f
  obtain ⟨e, he⟩ := exists_sectionTensorEquiv E U.2 V.2 h
  have hΦ : Function.Bijective Φ := by
    have heq : (fun t ↦ e t) = Φ := by
      funext t
      induction t using TensorProduct.inductionOn with
      | tmul r a => exact he r a
      | add t t' ht ht' => simp only [map_add, ht, ht']
    rw [← heq]
    exact e.bijective
  refine ⟨restriction_algebraMap E _, fun n ↦ ?_⟩
  let l : (D n).baseChange S →ₗ[S] D' n :=
    (Φ.toAlgHom.toLinearMap.domRestrict ((D n).baseChange S)).codRestrict
      (D' n) (fun a ↦ Φ.map_mem a.property)
  have hl : Function.Bijective l := graded_bijective_degree Φ.toGradedRingHom hΦ n
  let e₁ := LinearEquiv.ofBijective ((D n).toBaseChange S)
    (DirectSum.toBaseChange_bijective D n)
  let e₂ := LinearEquiv.ofBijective l hl
  apply IsBaseChange.of_equiv (e₁.trans e₂)
  intro a
  apply Subtype.ext
  change Φ (1 ⊗ₜ[R] (a : A)) =
    restriction E (homOfLE (X := X.Opens) h).op (a : A)
  rw [GradedAlgHom.liftEquiv_tmul, one_smul]
  rfl

/-- The canonical affine-basis graded algebra of Sym(E). Its section rings are the
sectionwise symmetric algebras, its degree-n part is the nth power of the degree-one
inclusion range, and its restrictions are the canonical symmetric-algebra restrictions.
Source: Stacks Project, Constructions, Tag 01OB; Modules, Tags 01CG and 01CL
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable def gradedAlgebraData {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] : X.GradedAlgebraData where
  obj U := sections E (op U.1)
  commRing _ := inferInstance
  algebra _ := inferInstance
  grading U n := (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n
  gradedAlgebra U := sectionGradedAlgebra E U
  res h := gradedRestriction E h
  res_id U x :=
    congrArg (fun q ↦ q.hom x) ((presheaf E).map_id (op U.1))
  res_res h₁ h₂ x :=
    congrArg (fun q ↦ q.hom x) ((presheaf E).map_comp
      ((homOfLE (X := X.Opens) h₂).op)
      ((homOfLE (X := X.Opens) h₁).op)).symm
  isGradedBaseChangeAlong h := gradedRestriction_isGradedBaseChangeAlong E h

end AlgebraicGeometry.SymmetricAlgebraSheaf
