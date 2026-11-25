/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

/-!
# Multiplicative, additive, roots-of-unity and Frobenius-kernel group schemes

Blueprint `def-sc-gm-ga`; Stacks Project, Tags 022U, 022V, 040M and 0CC9.

The underlying affine schemes and all coordinate maps are explicit. Group structures
are chosen from unique-existence theorems fixing all three structure maps
(`additiveGroup_existsUnique`, `rootsGroup_existsUnique`, `alphaGroup_existsUnique`), so they
are determined by the displayed coordinate maps.

## Main definitions

- `GroupScheme.multiplicative`: Spec k[t,t⁻¹], with its Laurent Hopf group law.
- `GroupScheme.additive`: Spec k[y], with its additive group law.
- `GroupScheme.roots`: Spec k[t]/(t^n-1), with `rootsInclusion` into Gₘ.
- `GroupScheme.alpha`: Spec k[y]/(y^p), with `alphaInclusion` into Gₐ.
- `GroupScheme.frobenius`: the coefficient-fixing map induced by z ↦ y^p.

## Main statements

The two inclusion theorems assert the closed subgroup properties;
`GroupScheme.alpha_isFrobeniusKernel` identifies the latter subgroup
with the scheme-theoretic kernel, respecting its inclusion.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry
namespace GroupScheme

noncomputable section

variable (k : Type u) [Field k]

/-- Spec of a coordinate algebra over the field (Stacks, Tag 01I1;
blueprint `def-sc-gm-ga`). -/
noncomputable def affine (A : Type u) [CommRing A] [Algebra k A] :
    Over (Spec (.of k)) :=
  (algSpec (.of k)).obj (op (CommAlgCat.of k A))

/-- Contravariant Spec of a coordinate algebra map (Stacks, Tag 01I1;
blueprint `def-sc-gm-ga`). -/
noncomputable def map {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) : affine k B ⟶ affine k A :=
  (algSpec (.of k)).map (CommAlgCat.ofHom f).op

/-- Multiplication from comultiplication, using the canonical affine-product
identification (Stacks, Tags 022U, 022V, 01I4; blueprint `def-sc-gm-ga`). -/
noncomputable def multiplication {A : Type u} [CommRing A] [Algebra k A]
    (d : A →ₐ[k] A ⊗[k] A) : affine k A ⊗ affine k A ⟶ affine k A :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.μ (algSpec (.of k)) (op (CommAlgCat.of k A))
    (op (CommAlgCat.of k A)) ≫ map k d

/-- Identity section from the counit, using Spec k as tensor unit (Stacks,
Tags 022U, 022V; blueprint `def-sc-gm-ga`). -/
noncomputable def identitySection {A : Type u} [CommRing A] [Algebra k A]
    (e : A →ₐ[k] k) : 𝟙_ (Over (Spec (.of k))) ⟶ affine k A :=
  letI := braidedAlgSpec (R := .of k)
  Functor.LaxMonoidal.ε (algSpec (.of k)) ≫ map k e

/-- The multiplicative group Spec k[t,t⁻¹], with Mathlib's canonical Laurent
Hopf algebra (Stacks, Tag 022U; blueprint `def-sc-gm-ga`). -/
noncomputable def multiplicative : Over (Spec (.of k)) := affine k (LaurentPolynomial k)

/-- The canonical multiplicative group structure from the Laurent Hopf algebra:
t maps to t⊗t, 1 and t⁻¹ (Stacks, Tag 022U; blueprint `def-sc-gm-ga`). -/
noncomputable instance multiplicativeGroup : GrpObj (multiplicative k) :=
  inferInstanceAs (GrpObj ((Spec (.of (LaurentPolynomial k))).asOver (Spec (.of k))))

/-- The additive group Spec k[y] (Stacks, Tag 022V; blueprint `def-sc-gm-ga`). -/
noncomputable def additive : Over (Spec (.of k)) := affine k (Polynomial k)

/-- Additive comultiplication y ↦ y⊗1+1⊗y (Stacks, Tag 022V;
blueprint `def-sc-gm-ga`). -/
noncomputable def additiveComul : Polynomial k →ₐ[k] Polynomial k ⊗[k] Polynomial k :=
  Polynomial.aeval (Polynomial.X ⊗ₜ[k] 1 + 1 ⊗ₜ[k] Polynomial.X)

/-- Additive counit y ↦ 0 (Stacks, Tag 022V; blueprint `def-sc-gm-ga`). -/
noncomputable def additiveCounit : Polynomial k →ₐ[k] k := Polynomial.aeval 0

/-- Additive antipode y ↦ -y (Stacks, Tag 022V; blueprint `def-sc-gm-ga`). -/
noncomputable def additiveAntipode : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (-Polynomial.X)

private theorem hopf_group_existsUnique {A : Type u} [CommRing A] [HopfAlgebra k A] :
    ∃! h : GrpObj (affine k A),
      h.one = identitySection k (Bialgebra.counitAlgHom k A) ∧
      h.mul = multiplication k (Bialgebra.comulAlgHom k A) ∧
      h.inv = map k (HopfAlgebra.antipodeAlgHom k A) := by
  refine ⟨inferInstanceAs (GrpObj ((Spec (.of A)).asOver (Spec (.of k)))),
    ⟨rfl, rfl, rfl⟩, ?_⟩
  intro g' hg'
  apply GrpObj.ext
  apply MonObj.ext
  exact hg'.2.1

@[instance_reducible] private noncomputable def additiveBialgebra : Bialgebra k (Polynomial k) :=
  Bialgebra.ofAlgHom (additiveComul k) (additiveCounit k)
    (by
      apply Polynomial.algHom_ext
      simp [additiveComul, Algebra.TensorProduct.one_def, TensorProduct.tmul_add,
        TensorProduct.add_tmul, add_assoc])
    (by apply Polynomial.algHom_ext; simp [additiveComul, additiveCounit])
    (by apply Polynomial.algHom_ext; simp [additiveComul, additiveCounit])

@[instance_reducible] private noncomputable def additiveHopf : HopfAlgebra k (Polynomial k) := by
  letI := additiveBialgebra k
  exact HopfAlgebra.ofAlgHom (additiveAntipode k)
    (by
      change (Algebra.TensorProduct.lift (additiveAntipode k) (.id k _) _).comp
        (additiveComul k) = (Algebra.ofId k _).comp (additiveCounit k)
      apply Polynomial.algHom_ext
      simp [additiveComul, additiveCounit, additiveAntipode])
    (by
      change (Algebra.TensorProduct.lift (.id k _) (additiveAntipode k) _).comp
        (additiveComul k) = (Algebra.ofId k _).comp (additiveCounit k)
      apply Polynomial.algHom_ext
      simp [additiveComul, additiveCounit, additiveAntipode])

/-- The three displayed coordinate maps give a unique group structure on the
additive affine line (Stacks, Tag 022V; blueprint `def-sc-gm-ga`).
Proof: substitute y in the two triple comultiplications to obtain
 y⊗1⊗1+1⊗y⊗1+1⊗1⊗y; both counit composites fix y, and the inverse
composites send y to -y+y=0=y-y. Algebra maps are determined by y; the
fully faithful affine Spec functor gives the group diagrams. All three
structure maps have been fixed, so the structure is unique by proof irrelevance. -/
theorem additiveGroup_existsUnique :
    ∃! h : GrpObj (additive k),
      h.one = identitySection k (additiveCounit k) ∧
      h.mul = multiplication k (additiveComul k) ∧
      h.inv = map k (additiveAntipode k) := by
  let _ := additiveHopf k
  exact hopf_group_existsUnique k


/-- The uniquely specified additive group structure (Stacks, Tag 022V;
blueprint `def-sc-gm-ga`). -/
noncomputable instance additiveGroup : GrpObj (additive k) :=
  (additiveGroup_existsUnique k).exists.choose

/-- The defining ideal for the roots of unity (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def rootsIdeal (n : ℕ) : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X ^ n - 1} : Set (Polynomial k))

/-- The coordinate algebra of the roots of unity (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
abbrev rootsAlgebra (n : ℕ) := Polynomial k ⧸ rootsIdeal k n

/-- The residue class of the coordinate (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def rootsCoordinate (n : ℕ) : rootsAlgebra k n :=
  Ideal.Quotient.mkₐ k (rootsIdeal k n) Polynomial.X

/-- The affine roots of unity scheme (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def roots (n : ℕ) : Over (Spec (.of k)) :=
  affine k (rootsAlgebra k n)

private theorem rootsCoordinate_pow (n : ℕ) : rootsCoordinate k n ^ n = 1 := by
  have h : Ideal.Quotient.mk (rootsIdeal k n) (Polynomial.X ^ n - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa [rootsCoordinate, map_sub, map_pow, sub_eq_zero] using h

private theorem kills_principal {B : Type u} [CommRing B] [Algebra k B]
    (g : Polynomial k) (f : Polynomial k →ₐ[k] B) (h : f g = 0) :
    ∀ x ∈ Ideal.span ({g} : Set (Polynomial k)), f x = 0 := by
  intro x hx
  exact (Ideal.span_le.mpr (by simpa [Set.singleton_subset_iff, RingHom.mem_ker] using h)
    hx : x ∈ RingHom.ker f.toRingHom)

/-- The coordinate substitutions kill the defining ideal (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`).
Proof: the quotient coordinate satisfies its defining relation. For roots of
unity, its n-th power is 1, so its tensor square and inverse also have n-th
power 1. For alpha, characteristic p makes the p-th power additive, so the
p-th power of the tensor sum is zero; zero and the negative also satisfy the
relation. Each substitution is an algebra map and hence kills the generated ideal. -/
theorem rootsRelations (n : ℕ) [NeZero n] :
    (∀ f ∈ rootsIdeal k n,
      Polynomial.aeval (rootsCoordinate k n ⊗ₜ[k] rootsCoordinate k n) f = 0) ∧
    (∀ f ∈ rootsIdeal k n,
      (Polynomial.aeval (1 : k)) f = 0) ∧
    (∀ f ∈ rootsIdeal k n,
      Polynomial.aeval (rootsCoordinate k n ^ (n - 1)) f = 0) := by
  have hn := rootsCoordinate_pow k n
  refine ⟨kills_principal k _ _ ?_, kills_principal k _ _ ?_,
    kills_principal k _ _ ?_⟩
  · simp [Algebra.TensorProduct.tmul_pow, hn, ← Algebra.TensorProduct.one_def]
  · simp
  · simp only [map_sub, map_pow, Polynomial.aeval_X, map_one]
    rw [← pow_mul, Nat.mul_comm (n - 1) n, pow_mul, hn, one_pow, sub_self]

/-- The descended comultiplication (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def rootsComul (n : ℕ) [NeZero n] :
    rootsAlgebra k n →ₐ[k] rootsAlgebra k n ⊗[k] rootsAlgebra k n :=
  Ideal.Quotient.liftₐ (rootsIdeal k n)
    (Polynomial.aeval (rootsCoordinate k n ⊗ₜ[k] rootsCoordinate k n))
    (rootsRelations k n).1

/-- The descended counit (Stacks, Tag 040M; blueprint `def-sc-gm-ga`). -/
noncomputable def rootsCounit (n : ℕ) [NeZero n] : rootsAlgebra k n →ₐ[k] k :=
  Ideal.Quotient.liftₐ (rootsIdeal k n) (Polynomial.aeval 1)
    (rootsRelations k n).2.1

/-- The descended antipode (Stacks, Tag 040M; blueprint `def-sc-gm-ga`). -/
noncomputable def rootsAntipode (n : ℕ) [NeZero n] :
    rootsAlgebra k n →ₐ[k] rootsAlgebra k n :=
  Ideal.Quotient.liftₐ (rootsIdeal k n)
    (Polynomial.aeval (rootsCoordinate k n ^ (n - 1)))
    (rootsRelations k n).2.2

private theorem quotient_coordinate_ext {I : Ideal (Polynomial k)}
    {B : Type u} [CommRing B] [Algebra k B]
    {f g : Polynomial k ⧸ I →ₐ[k] B}
    (h : f (Ideal.Quotient.mkₐ k I Polynomial.X) =
      g (Ideal.Quotient.mkₐ k I Polynomial.X)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply Polynomial.algHom_ext
  exact h

private theorem roots_ext (n : ℕ) {B : Type u} [CommRing B] [Algebra k B]
    {f g : rootsAlgebra k n →ₐ[k] B}
    (h : f (rootsCoordinate k n) = g (rootsCoordinate k n)) : f = g :=
  quotient_coordinate_ext k h

@[simp] private theorem rootsComul_coordinate (n : ℕ) [NeZero n] :
    rootsComul k n (rootsCoordinate k n) = rootsCoordinate k n ⊗ₜ[k] rootsCoordinate k n := by
  simp [rootsComul, rootsCoordinate]

@[simp] private theorem rootsCounit_coordinate (n : ℕ) [NeZero n] :
    rootsCounit k n (rootsCoordinate k n) = 1 := by
  simp [rootsCounit, rootsCoordinate]

@[simp] private theorem rootsAntipode_coordinate (n : ℕ) [NeZero n] :
    rootsAntipode k n (rootsCoordinate k n) = rootsCoordinate k n ^ (n - 1) := by
  simp [rootsAntipode, rootsCoordinate]

@[instance_reducible] private noncomputable def rootsBialgebra (n : ℕ) [NeZero n] :
    Bialgebra k (rootsAlgebra k n) :=
  Bialgebra.ofAlgHom (rootsComul k n) (rootsCounit k n)
    (by
      apply roots_ext k n
      simp)
    (by
      apply roots_ext k n
      simp)
    (by
      apply roots_ext k n
      simp)

@[instance_reducible] private noncomputable def rootsHopf (n : ℕ) [NeZero n] :
    HopfAlgebra k (rootsAlgebra k n) := by
  letI := rootsBialgebra k n
  have hi : rootsCoordinate k n ^ (n - 1) * rootsCoordinate k n = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
    exact rootsCoordinate_pow k n
  exact HopfAlgebra.ofAlgHom (rootsAntipode k n)
    (by
      change (Algebra.TensorProduct.lift (rootsAntipode k n) (.id k _) _).comp
        (rootsComul k n) = (Algebra.ofId k _).comp (rootsCounit k n)
      apply roots_ext k n
      simpa using hi)
    (by
      change (Algebra.TensorProduct.lift (.id k _) (rootsAntipode k n) _).comp
        (rootsComul k n) = (Algebra.ofId k _).comp (rootsCounit k n)
      apply roots_ext k n
      simpa [mul_comm] using hi)

/-- The displayed maps uniquely specify the roots of unity group structure
(Stacks, Tag 040M; blueprint `def-sc-gm-ga`).
Proof: check all diagrams on the quotient coordinate. In the roots case the
iterated comultiplications are x⊗x⊗x, the counits fix x, and multiplication
with the inverse gives x^n=1. In the alpha case the iterated sums agree,
the counits fix x, and x+(-x)=0=(-x)+x. Quotient algebra maps are determined
by the coordinate, and faithful Spec turns these into the group diagrams.
All three structure maps are fixed, giving uniqueness by proof irrelevance. -/
theorem rootsGroup_existsUnique (n : ℕ) [NeZero n] :
    ∃! h : GrpObj (roots k n),
      h.one = identitySection k (rootsCounit k n) ∧
      h.mul = multiplication k (rootsComul k n) ∧
      h.inv = map k (rootsAntipode k n) := by
  let _ := rootsHopf k n
  exact hopf_group_existsUnique k

/-- The unique roots of unity group structure with the displayed coordinates
(Stacks, Tag 040M; blueprint `def-sc-gm-ga`). -/
noncomputable instance rootsGroup (n : ℕ) [NeZero n] : GrpObj (roots k n) :=
  (rootsGroup_existsUnique k n).exists.choose

/-- The defining ideal for the Frobenius kernel (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def alphaIdeal (p : ℕ) : Ideal (Polynomial k) :=
  Ideal.span ({Polynomial.X ^ p} : Set (Polynomial k))

/-- The coordinate algebra of the Frobenius kernel (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
abbrev alphaAlgebra (p : ℕ) := Polynomial k ⧸ alphaIdeal k p

/-- The residue class of the coordinate (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def alphaCoordinate (p : ℕ) : alphaAlgebra k p :=
  Ideal.Quotient.mkₐ k (alphaIdeal k p) Polynomial.X

/-- The affine Frobenius kernel scheme (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def alpha (p : ℕ) : Over (Spec (.of k)) :=
  affine k (alphaAlgebra k p)

private theorem alphaCoordinate_pow (p : ℕ) : alphaCoordinate k p ^ p = 0 := by
  have h : Ideal.Quotient.mk (alphaIdeal k p) (Polynomial.X ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa [alphaCoordinate, map_pow] using h

/-- The coordinate substitutions kill the defining ideal (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`).
Proof: the quotient coordinate satisfies its defining relation. For roots of
unity, its n-th power is 1, so its tensor square and inverse also have n-th
power 1. For alpha, characteristic p makes the p-th power additive, so the
p-th power of the tensor sum is zero; zero and the negative also satisfy the
relation. Each substitution is an algebra map and hence kills the generated ideal. -/
theorem alphaRelations (p : ℕ) [NeZero p] [CharP k p] :
    (∀ f ∈ alphaIdeal k p,
      Polynomial.aeval (alphaCoordinate k p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] alphaCoordinate k p) f = 0) ∧
    (∀ f ∈ alphaIdeal k p,
      (Polynomial.aeval (0 : k)) f = 0) ∧
    (∀ f ∈ alphaIdeal k p,
      Polynomial.aeval (-alphaCoordinate k p) f = 0) := by
  have hp : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k (NeZero.ne p)⟩
  have hchar : (p : alphaAlgebra k p ⊗[k] alphaAlgebra k p) = 0 := by
    rw [← map_natCast (algebraMap k _), CharP.cast_eq_zero, map_zero]
  have hn := alphaCoordinate_pow k p
  refine ⟨kills_principal k _ _ ?_, kills_principal k _ _ ?_,
    kills_principal k _ _ ?_⟩
  · simp only [map_pow, Polynomial.aeval_X]
    rw [add_pow_prime_eq' hp.out, hchar, zero_mul, add_zero]
    simp [Algebra.TensorProduct.tmul_pow, hn]
  · simp [NeZero.ne p]
  · simp only [map_pow, Polynomial.aeval_X]
    rw [neg_pow, hn, mul_zero]

/-- The descended comultiplication (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def alphaComul (p : ℕ) [NeZero p] [CharP k p] :
    alphaAlgebra k p →ₐ[k] alphaAlgebra k p ⊗[k] alphaAlgebra k p :=
  Ideal.Quotient.liftₐ (alphaIdeal k p)
    (Polynomial.aeval (alphaCoordinate k p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] alphaCoordinate k p))
    (alphaRelations k p).1

/-- The descended counit (Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`). -/
noncomputable def alphaCounit (p : ℕ) [NeZero p] [CharP k p] : alphaAlgebra k p →ₐ[k] k :=
  Ideal.Quotient.liftₐ (alphaIdeal k p) (Polynomial.aeval 0)
    (alphaRelations k p).2.1

/-- The descended antipode (Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`). -/
noncomputable def alphaAntipode (p : ℕ) [NeZero p] [CharP k p] :
    alphaAlgebra k p →ₐ[k] alphaAlgebra k p :=
  Ideal.Quotient.liftₐ (alphaIdeal k p)
    (Polynomial.aeval (-alphaCoordinate k p))
    (alphaRelations k p).2.2

private theorem alpha_ext (p : ℕ) {B : Type u} [CommRing B] [Algebra k B]
    {f g : alphaAlgebra k p →ₐ[k] B}
    (h : f (alphaCoordinate k p) = g (alphaCoordinate k p)) : f = g :=
  quotient_coordinate_ext k h

@[simp] private theorem alphaComul_coordinate (p : ℕ) [NeZero p] [CharP k p] :
    alphaComul k p (alphaCoordinate k p) =
      alphaCoordinate k p ⊗ₜ[k] 1 + 1 ⊗ₜ[k] alphaCoordinate k p := by
  simp [alphaComul, alphaCoordinate]

@[simp] private theorem alphaCounit_coordinate (p : ℕ) [NeZero p] [CharP k p] :
    alphaCounit k p (alphaCoordinate k p) = 0 := by
  simp [alphaCounit, alphaCoordinate]

@[simp] private theorem alphaAntipode_coordinate (p : ℕ) [NeZero p] [CharP k p] :
    alphaAntipode k p (alphaCoordinate k p) = -alphaCoordinate k p := by
  simp [alphaAntipode, alphaCoordinate]

@[instance_reducible] private noncomputable def alphaBialgebra (p : ℕ)
    [NeZero p] [CharP k p] : Bialgebra k (alphaAlgebra k p) :=
  Bialgebra.ofAlgHom (alphaComul k p) (alphaCounit k p)
    (by
      apply alpha_ext k p
      simp [Algebra.TensorProduct.one_def, TensorProduct.tmul_add,
        TensorProduct.add_tmul, add_assoc])
    (by
      apply alpha_ext k p
      simp)
    (by
      apply alpha_ext k p
      simp)

@[instance_reducible] private noncomputable def alphaHopf (p : ℕ)
    [NeZero p] [CharP k p] : HopfAlgebra k (alphaAlgebra k p) := by
  letI := alphaBialgebra k p
  exact HopfAlgebra.ofAlgHom (alphaAntipode k p)
    (by
      change (Algebra.TensorProduct.lift (alphaAntipode k p) (.id k _) _).comp
        (alphaComul k p) = (Algebra.ofId k _).comp (alphaCounit k p)
      apply alpha_ext k p
      simp)
    (by
      change (Algebra.TensorProduct.lift (.id k _) (alphaAntipode k p) _).comp
        (alphaComul k p) = (Algebra.ofId k _).comp (alphaCounit k p)
      apply alpha_ext k p
      simp)

/-- The displayed maps uniquely specify the Frobenius kernel group structure
(Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`).
Proof: check all diagrams on the quotient coordinate. In the roots case the
iterated comultiplications are x⊗x⊗x, the counits fix x, and multiplication
with the inverse gives x^n=1. In the alpha case the iterated sums agree,
the counits fix x, and x+(-x)=0=(-x)+x. Quotient algebra maps are determined
by the coordinate, and faithful Spec turns these into the group diagrams.
All three structure maps are fixed, giving uniqueness by proof irrelevance. -/
theorem alphaGroup_existsUnique (p : ℕ) [NeZero p] [CharP k p] :
    ∃! h : GrpObj (alpha k p),
      h.one = identitySection k (alphaCounit k p) ∧
      h.mul = multiplication k (alphaComul k p) ∧
      h.inv = map k (alphaAntipode k p) := by
  let _ := alphaHopf k p
  exact hopf_group_existsUnique k

/-- The unique Frobenius kernel group structure with the displayed coordinates
(Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`). -/
noncomputable instance alphaGroup (p : ℕ) [NeZero p] [CharP k p] : GrpObj (alpha k p) :=
  (alphaGroup_existsUnique k p).exists.choose

/-- The coordinate of μₙ is a unit, with inverse x^(n-1) (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`).
Proof: the relation x^n=1 and n≥1 give x*x^(n-1)=1=x^(n-1)*x. -/
theorem rootsCoordinate_inverse (n : ℕ) [NeZero n] :
    rootsCoordinate k n * rootsCoordinate k n ^ (n - 1) = 1 ∧
      rootsCoordinate k n ^ (n - 1) * rootsCoordinate k n = 1 := by
  have h : rootsCoordinate k n * rootsCoordinate k n ^ (n - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))]
    exact rootsCoordinate_pow k n
  exact ⟨h, by simpa [mul_comm] using h⟩

/-- The explicit unit defining the Laurent quotient map (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def rootsCoordinateUnit (n : ℕ) [NeZero n] : (rootsAlgebra k n)ˣ where
  val := rootsCoordinate k n
  inv := rootsCoordinate k n ^ (n - 1)
  val_inv := (rootsCoordinate_inverse k n).1
  inv_val := (rootsCoordinate_inverse k n).2

/-- Laurent substitution fixes all coefficients (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`).
Proof: a constant Laurent polynomial evaluates to its coefficient under the
coefficient algebra map. This is exactly compatibility with the k-algebra structure. -/
theorem rootsLaurent_commutes (n : ℕ) [NeZero n] (c : k) :
    LaurentPolynomial.eval₂ (algebraMap k (rootsAlgebra k n)) (rootsCoordinateUnit k n)
      (algebraMap k (LaurentPolynomial k) c) = algebraMap k (rootsAlgebra k n) c := by
  simp [← LaurentPolynomial.C_eq_algebraMap, LaurentPolynomial.eval₂_C]

/-- The displayed quotient surjection k[t,t⁻¹] → k[t]/(t^n-1), sending
t to its residue class and t⁻¹ to its (n-1)-st power (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`). -/
noncomputable def rootsQuotient (n : ℕ) [NeZero n] :
    LaurentPolynomial k →ₐ[k] rootsAlgebra k n :=
  { LaurentPolynomial.eval₂ (algebraMap k (rootsAlgebra k n)) (rootsCoordinateUnit k n) with
    commutes' := rootsLaurent_commutes k n }

/-- The closed subgroup inclusion μₙ → Gₘ induced by the quotient map
(Stacks, Tag 040M; blueprint `def-sc-gm-ga`). -/
noncomputable def rootsInclusion (n : ℕ) [NeZero n] : roots k n ⟶ multiplicative k :=
  map k (rootsQuotient k n)

/-- The quotient k[y] → k[y]/(y^p) (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def alphaQuotient (p : ℕ) : Polynomial k →ₐ[k] alphaAlgebra k p :=
  Ideal.Quotient.mkₐ k (alphaIdeal k p)

/-- The closed subgroup inclusion αₚ → Gₐ induced by the quotient map
(Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`). -/
noncomputable def alphaInclusion (p : ℕ) : alpha k p ⟶ additive k :=
  map k (alphaQuotient k p)

/-- Both defining coordinate maps are surjective (Stacks, Tags 040M, 0CC9;
blueprint `def-sc-gm-ga`).
Proof: every quotient class is represented by a polynomial. For roots of
unity use the same polynomial as a Laurent polynomial; the Laurent substitution
restricts to the polynomial quotient map. For alpha use surjectivity of the quotient map. -/
theorem quotient_surjective (n p : ℕ) [NeZero n] :
    Function.Surjective (rootsQuotient k n) ∧
      Function.Surjective (alphaQuotient k p) := by
  constructor
  · intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨Polynomial.toLaurent f, ?_⟩
    change LaurentPolynomial.eval₂ _ _ (Polynomial.toLaurent f) = _
    rw [LaurentPolynomial.eval₂_toLaurent]
    change (Polynomial.aeval (rootsCoordinate k n)) f = _
    have he : Polynomial.aeval (rootsCoordinate k n) =
        Ideal.Quotient.mkₐ k (rootsIdeal k n) := by
      ext
      simp [rootsCoordinate]
    rw [he]
    rfl
  · exact Ideal.Quotient.mk_surjective

private theorem map_isMonHom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [MonObj (affine k A)] [MonObj (affine k B)]
    (dA : A →ₐ[k] A ⊗[k] A) (eA : A →ₐ[k] k)
    (dB : B →ₐ[k] B ⊗[k] B) (eB : B →ₐ[k] k)
    (hA : MonObj.one (X := affine k A) = identitySection k eA ∧
      MonObj.mul (X := affine k A) = multiplication k dA)
    (hB : MonObj.one (X := affine k B) = identitySection k eB ∧
      MonObj.mul (X := affine k B) = multiplication k dB)
    (f : A →ₐ[k] B) (he : eB.comp f = eA)
    (hd : dB.comp f = (Algebra.TensorProduct.map f f).comp dA) :
    IsMonHom (map k f) := by
  let := braidedAlgSpec (R := .of k)
  have hcomp {D E F : Type u} [CommRing D] [CommRing E] [CommRing F]
      [Algebra k D] [Algebra k E] [Algebra k F] (g : D →ₐ[k] E) (h : E →ₐ[k] F) :
      map k h ≫ map k g = map k (h.comp g) :=
    ((algSpec (.of k)).map_comp (CommAlgCat.ofHom h).op (CommAlgCat.ofHom g).op).symm
  constructor
  · rw [hA.1, hB.1]
    simp only [identitySection, Category.assoc, hcomp, he]
  · rw [hA.2, hB.2]
    dsimp only [multiplication]
    rw [Category.assoc, hcomp, hd, ← hcomp, ← Category.assoc]
    have ht : ((CommAlgCat.ofHom f).op ⊗ₘ (CommAlgCat.ofHom f).op) =
        (CommAlgCat.ofHom (Algebra.TensorProduct.map f f)).op := rfl
    have hn := (Functor.LaxMonoidal.μ_natural (algSpec (.of k))
      (CommAlgCat.ofHom f).op (CommAlgCat.ofHom f).op).symm
    rw [ht] at hn
    simpa only [map, Category.assoc] using congrArg (fun z ↦ z ≫ map k dA) hn

/-- μₙ is a closed subgroup of Gₘ (Stacks, Tag 040M;
blueprint `def-sc-gm-ga`).
Proof: the Laurent quotient is surjective, hence Spec gives a closed immersion
and is injective on points. Its coordinate generator respects all three
structure maps, so it is a group homomorphism and a closed subgroup scheme. -/
theorem roots_isClosedSubgroupScheme (n : ℕ) [NeZero n] :
    IsClosedSubgroupScheme (rootsInclusion k n) := by
  let : GrpObj (affine k (rootsAlgebra k n)) := rootsGroup k n
  let : GrpObj (affine k (LaurentPolynomial k)) := multiplicativeGroup k
  have : IsMonHom (rootsInclusion k n) := by
    apply map_isMonHom k (Bialgebra.comulAlgHom k (LaurentPolynomial k))
      (Bialgebra.counitAlgHom k (LaurentPolynomial k)) (rootsComul k n) (rootsCounit k n)
    · exact ⟨rfl, rfl⟩
    · exact ⟨(rootsGroup_existsUnique k n).exists.choose_spec.1,
        (rootsGroup_existsUnique k n).exists.choose_spec.2.1⟩
    · ext m
      cases m <;> simp [rootsQuotient, rootsCoordinateUnit, zpow_negSucc]
    · ext m
      cases m <;> simp [rootsQuotient, rootsCoordinateUnit, zpow_negSucc,
        Algebra.TensorProduct.tmul_pow]
  have hc : IsClosedImmersion (rootsInclusion k n).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (rootsQuotient k n).toRingHom)
      (quotient_surjective k n n).1
  have hm : Mono (rootsInclusion k n).left := inferInstance
  have : Mono (rootsInclusion k n) := (Over.forget _).mono_of_mono_map hm
  have : IsSubgroupScheme (rootsInclusion k n) := IsSubgroupScheme.of_mono _
  exact { isClosedImmersion := hc }

/-- αₚ is a closed subgroup of Gₐ in positive characteristic p (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`).
Proof: the polynomial quotient is surjective, giving a closed immersion and
injectivity on points. Its coordinate respects addition, zero and negation;
these formulas descend because p-th powers are additive in characteristic p. -/
theorem alpha_isClosedSubgroupScheme (p : ℕ) [NeZero p] [CharP k p] :
    IsClosedSubgroupScheme (alphaInclusion k p) := by
  let : GrpObj (affine k (alphaAlgebra k p)) := alphaGroup k p
  let : GrpObj (affine k (Polynomial k)) := additiveGroup k
  have : IsMonHom (alphaInclusion k p) := by
    apply map_isMonHom k (additiveComul k) (additiveCounit k)
      (alphaComul k p) (alphaCounit k p)
    · exact ⟨(additiveGroup_existsUnique k).exists.choose_spec.1,
        (additiveGroup_existsUnique k).exists.choose_spec.2.1⟩
    · exact ⟨(alphaGroup_existsUnique k p).exists.choose_spec.1,
        (alphaGroup_existsUnique k p).exists.choose_spec.2.1⟩
    · apply Polynomial.algHom_ext
      change alphaCounit k p (alphaCoordinate k p) = additiveCounit k Polynomial.X
      simp [additiveCounit]
    · apply Polynomial.algHom_ext
      change alphaComul k p (alphaCoordinate k p) =
        (Algebra.TensorProduct.map (alphaQuotient k p) (alphaQuotient k p))
          (additiveComul k Polynomial.X)
      rw [alphaComul_coordinate]
      simp [additiveComul, alphaQuotient, alphaCoordinate]
  have hc : IsClosedImmersion (alphaInclusion k p).left :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (alphaQuotient k p).toRingHom)
      (quotient_surjective k p p).2
  have hm : Mono (alphaInclusion k p).left := inferInstance
  have : Mono (alphaInclusion k p) := (Over.forget _).mono_of_mono_map hm
  have : IsSubgroupScheme (alphaInclusion k p) := IsSubgroupScheme.of_mono _
  exact { isClosedImmersion := hc }

/-- The k-linear Frobenius coordinate map z ↦ y^p. Coefficients are fixed:
this is the relative Frobenius after identifying the twist by its coordinate,
not the absolute Frobenius of k[y] (Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`). -/
noncomputable def frobeniusCoordinates (p : ℕ) : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (Polynomial.X ^ p)

/-- Frobenius on Gₐ, induced by z ↦ y^p fixing k (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`). -/
noncomputable def frobenius (p : ℕ) : additive k ⟶ additive k :=
  map k (frobeniusCoordinates k p)

/-- The relative Frobenius is a group homomorphism (Stacks, Tag 0CC9;
blueprint `def-sc-gm-ga`).
Proof: in positive field characteristic p, p is prime and (a+b)^p=a^p+b^p.
This verifies compatibility with the additive comultiplication on the generator;
zero and negation are preserved as well. Faithful Spec gives the group identity. -/
theorem frobenius_isMonHom (p : ℕ) [NeZero p] [CharP k p] :
    IsMonHom (frobenius k p) := by
  let : GrpObj (affine k (Polynomial k)) := additiveGroup k
  apply map_isMonHom k (additiveComul k) (additiveCounit k)
    (additiveComul k) (additiveCounit k)
  · exact ⟨(additiveGroup_existsUnique k).exists.choose_spec.1,
      (additiveGroup_existsUnique k).exists.choose_spec.2.1⟩
  · exact ⟨(additiveGroup_existsUnique k).exists.choose_spec.1,
      (additiveGroup_existsUnique k).exists.choose_spec.2.1⟩
  · apply Polynomial.algHom_ext
    simp [frobeniusCoordinates, additiveCounit, NeZero.ne p]
  · apply Polynomial.algHom_ext
    have hp : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k (NeZero.ne p)⟩
    have hchar : (p : Polynomial k ⊗[k] Polynomial k) = 0 := by
      rw [← map_natCast (algebraMap k _), CharP.cast_eq_zero, map_zero]
    simp [frobeniusCoordinates, additiveComul, add_pow_prime_eq' hp.out, hchar,
      Algebra.TensorProduct.tmul_pow]

private theorem alpha_pushout (p : ℕ) :
    IsPushout (CommAlgCat.ofHom (frobeniusCoordinates k p))
      (CommAlgCat.ofHom (additiveCounit k)) (CommAlgCat.ofHom (alphaQuotient k p))
      (CommAlgCat.ofHom (Algebra.ofId k (alphaAlgebra k p))) := by
  have hw : CommAlgCat.ofHom (frobeniusCoordinates k p) ≫
        CommAlgCat.ofHom (alphaQuotient k p) =
      CommAlgCat.ofHom (additiveCounit k) ≫
        CommAlgCat.ofHom (Algebra.ofId k (alphaAlgebra k p)) := by
    apply CommAlgCat.hom_ext
    apply Polynomial.algHom_ext
    simpa [frobeniusCoordinates, alphaQuotient, additiveCounit, alphaCoordinate]
      using alphaCoordinate_pow k p
  refine IsPushout.of_isColimit (c := Limits.PushoutCocone.mk _ _ hw) ?_
  apply Limits.PushoutCocone.isColimitAux'
  intro s
  have hs : s.inl.hom (Polynomial.X ^ p) = 0 := by
    have h := congrArg (fun z ↦ z.hom Polynomial.X) s.condition
    simpa [frobeniusCoordinates, additiveCounit] using h
  let l := Ideal.Quotient.liftₐ (alphaIdeal k p) s.inl.hom
    (kills_principal k _ _ hs)
  refine ⟨CommAlgCat.ofHom l, ?_, ?_, ?_⟩
  · apply CommAlgCat.hom_ext
    exact Ideal.Quotient.liftₐ_comp _ _ _
  · apply CommAlgCat.hom_ext
    ext
  · intro m hm _
    apply CommAlgCat.hom_ext
    apply Ideal.Quotient.algHom_ext
    exact congrArg CommAlgCat.Hom.hom hm

/-- The quotient αₚ is the scheme-theoretic Frobenius kernel, compatibly
with its specified inclusion (Stacks, Tag 0CC9; blueprint `def-sc-gm-ga`).
Proof: the kernel fibre product has coordinate algebra k[y]⊗_{k[z]}k,
where z maps to y^p and to zero. The map f⊗c ↦ c*f modulo (y^p)
has inverse induced by y ↦ y⊗1, since y^p⊗1=1⊗0=0. The two
composites fix k and y, so they are inverse; Spec gives the required
isomorphism and compatibility with the kernel inclusion. This calculation
uses no perfectness or reducedness hypothesis. To check the relative Frobenius
identification, its twist algebra is k[y]⊗_{k,F_k}k. The coefficient-fixing
isomorphism to k[z] sends a*y^i⊗b to a^p*b*z^i; its inverse sends z to y⊗1
and b to 1⊗b. The balancing relation a*c⊗b=a⊗c^p*b proves that these
maps are inverse. They preserve the additive comultiplication and zero counit.
The relative Frobenius map f⊗b ↦ f^p*b therefore becomes precisely the
coefficient-fixing substitution z ↦ y^p used here. -/
theorem alpha_isFrobeniusKernel (p : ℕ) [NeZero p] [CharP k p] :
    ∃ e : alpha k p ≅ GrpObj.ker (frobenius k p),
      e.hom ≫ GrpObj.kerι (frobenius k p) = alphaInclusion k p := by
  let := braidedAlgSpec (R := .of k)
  let : Limits.PreservesLimitsOfSize.{0, 0} (algSpec (.of k)) :=
    preservesLimitsOfSize_algSpec
  have h := ((alpha_pushout k p).op.map (algSpec (.of k))).flip
  have he : MonObj.one (X := additive k) = identitySection k (additiveCounit k) :=
    (additiveGroup_existsUnique k).exists.choose_spec.1
  have hp : IsPullback (alphaInclusion k p)
      (CartesianMonoidalCategory.toUnit (alpha k p)) (frobenius k p)
      (MonObj.one (X := additive k)) := by
    apply h.of_iso' (Iso.refl _) (Iso.refl _)
      (Functor.Monoidal.εIso (algSpec (.of k))) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · apply (cancel_mono (Functor.Monoidal.εIso (algSpec (.of k))).inv).1
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      exact CartesianMonoidalCategory.toUnit_unique _ _
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simpa only [Iso.refl_hom, Category.comp_id, Functor.Monoidal.εIso_hom,
        identitySection, map] using he.symm
  exact ⟨hp.isoPullback, hp.isoPullback_hom_fst⟩

end

end GroupScheme
end AlgebraicGeometry
