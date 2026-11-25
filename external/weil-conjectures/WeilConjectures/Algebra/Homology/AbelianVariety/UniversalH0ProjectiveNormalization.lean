/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective

import WeilConjectures.Algebra.Homology.UniversalConnectiveProjectiveModel
import WeilConjectures.Algebra.Homology.AbelianVariety.ConnectiveUniversalH0ZeroDifferential
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Global normalization of a universally rank-one projective complex

Source: Stacks Project, Tags 00O0, 0BCD and 0BF2 (projective affine adaptation).
(blueprint: lem-sc-universal-h0-projective-normalization).
-/

@[expose] public section
set_option autoImplicit false
universe v w
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A bounded finite projective complex with universally connective rank-one
homology has a global projective model starting in degree zero with d-zero zero.
The output terms are exhibited as retracts of finite free modules.

Source: Stacks Project, Tags 00O0 and 0BCD; the target-complex argument of 0BF2,
with finite projective terms on a fixed affine instead of shrinking to free terms.
(blueprint: lem-sc-universal-h0-projective-normalization).

Proof: Cancel negative terms from the bottom. Choose finite support bounds for P.
If its bottom degree is negative, negative residue homology says that its outgoing
differential is injective on every residue field. The finite-projective residue
criterion gives principal neighbourhoods on which its cokernel is finite projective.
That cokernel is finitely presented globally, so local projectivity makes it finite
projective over R. Thus the injection splits globally. Remove the contractible
pair consisting of the bottom term and its image in the next term. The complement
is still bounded finite projective and starts one degree higher. The resulting
homotopy equivalence remains a homotopy equivalence after every scalar extension,
so it preserves hbase. Induct on the number of negative degrees between the
chosen lower bound and zero, obtaining a connective finite projective model.
On local affine charts take minimal finite free representatives as in 0BCD.
Their zeroth terms have rank one and their negative terms vanish. For a chart
A = R_f, hbase applied to A identifies the kernel of d0 : A -> A^m with A.
The inclusion of this kernel is multiplication by an element a of A. Injectivity
makes a a non-zero-divisor. Since d0(a) = 0, every coordinate of d0(1) is killed
by a and is therefore zero. Thus d0 = 0, even when A has nilpotents. Bounded
projective representatives of the same derived object are homotopy equivalent;
these equivalences survive residue scalar extension. Their homology comparisons
show that H0 of the connective complex commutes with residue base change. The
identity base change identifies H0 with R. A generator therefore defines a cycle
whose inclusion in the
zeroth term is a split injection at every prime, with finite projective cokernel.
Split off this R summand globally. On the complementary degree-zero summand the
outgoing differential is residue-injective everywhere; its finitely presented
cokernel is locally free, hence projective. Split and cancel that pair. The
remaining bounded finite projective complex Q has no negative terms and has
zero outgoing differential in degree zero. Each finite projective term is a
retract of R^m, giving the displayed maps. All cancellations
are homotopy equivalences, giving the derived isomorphism. Over the zero ring the
zero complex satisfies every conclusion, and no prime or generator is needed. -/
theorem universalH0_projective_normalization
    (R : Type v) [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (P : CochainComplex (ModuleCat.{v} R) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hf : ∀ n : ℤ, Module.Finite R (P.X n))
    (hp : ∀ n : ℤ, Module.Projective R (P.X n))
    (hbase : ∀ (B : Type v) [CommRing B] (φ : R →+* B),
      let PB := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P
      (∀ i : ℤ, i < 0 → IsZero (PB.homology i)) ∧
        Nonempty (PB.homology 0 ≅ ModuleCat.of B B)) :
    ∃ Q : CochainComplex (ModuleCat.{v} R) ℤ,
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Q.X n)) ∧
      (∀ n : ℤ, ∃ m : ℕ,
        ∃ (ι : Q.X n ⟶ ModuleCat.of R (ULift.{v} (Fin m) →₀ R))
          (π : ModuleCat.of R (ULift.{v} (Fin m) →₀ R) ⟶ Q.X n),
          ι ≫ π = 𝟙 (Q.X n)) ∧
      (∀ n : ℤ, n < 0 → IsZero (Q.X n)) ∧ Q.d 0 1 = 0 ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) := by
  classical
  obtain ⟨C, hCb, hCf, hCp, hCneg, ⟨ePC⟩⟩ :=
    universalConnective_projective_model R P hb hf hp
      (fun B _ φ ↦ (hbase B φ).1)
  have hCzero (B : Type v) [CommRing B] (φ : R →+* B) :
      Nonempty
        ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj C).homology 0 ≅
          ModuleCat.of B B) := by
    have : (ModuleCat.extendScalars φ).Additive :=
      (ModuleCat.extendRestrictScalarsAdj φ).left_adjoint_additive
    let e := (ModuleCat.extendScalars φ).mapHomotopyEquiv ePC
    exact ⟨(e.toHomologyIso 0).symm ≪≫ (hbase B φ).2.some⟩
  obtain ⟨Q, hQb, hQf, hQp, hQneg, hQd, ⟨eCQ⟩⟩ :=
    connective_universalH0_zero_differential R C hCb hCf hCp hCneg hCzero
  refine ⟨Q, hQb, ?_, hQneg, hQd, ?_⟩
  · intro n
    let := hQf n
    let := hQp n
    obtain ⟨m, π, ι, _, _, hιπ⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective R (Q.X n)
    let e : (ULift.{v} (Fin m) →₀ R) ≃ₗ[R] (Fin m → R) :=
      (Finsupp.linearEquivFunOnFinite R R _).trans
        (LinearEquiv.piCongrLeft R (fun _ ↦ R) Equiv.ulift)
    refine ⟨m, ModuleCat.ofHom (e.symm.toLinearMap.comp ι),
      ModuleCat.ofHom (π.comp e.toLinearMap), ?_⟩
    ext x
    change π (e (e.symm (ι x))) = x
    simpa only [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearMap.id_apply]
      using LinearMap.congr_fun hιπ x
  · let e := ePC.trans eCQ
    exact ⟨asIso (DerivedCategory.Q.map e.hom)⟩

end CochainComplex
