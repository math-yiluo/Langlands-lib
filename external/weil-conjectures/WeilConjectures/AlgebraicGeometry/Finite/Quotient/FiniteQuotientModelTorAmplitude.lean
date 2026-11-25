/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientModelResidueProjective
import WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Algebra.Homology.DerivedChangeOfRings
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import WeilConjectures.AlgebraicGeometry.ComplexLiftClassProjective
import WeilConjectures.Algebra.Homology.BoundedAboveProjectiveModel
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.CochainComplexOpposite
import Mathlib.Algebra.Homology.Factorizations.CM5a
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.NilpotentDerivedUpperBoundSupplement
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionDerivedIso
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.RingTheory.NilpotentProjectiveModuleLift
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.Idempotents

/-! # Detecting Tor amplitude of a finite-quotient constant model

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I)
(blueprint: lem-weil-pbc-finite-quotient-model-tor-amplitude).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem zero_of_nilpotent_reduction
    {B : Type t} [CommRing B] (J : Ideal B) (k : ℕ) (hk : J ^ k = ⊥)
    (N : ModuleCat.{t} B)
    (hN : IsZero ((ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj N)) : IsZero N := by
  have := ModuleCat.subsingleton_of_isZero hN
  let e := TensorProduct.quotTensorEquivQuotSMul N J
  let e' : (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj N ≃ₗ[B ⧸ J]
      (N ⧸ J • (⊤ : Submodule B N)) :=
    { __ := e.toAddEquiv
      map_smul' := by
        intro a x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact e.map_smul a x }
  have : Subsingleton (N ⧸ J • (⊤ : Submodule B N)) := e'.symm.injective.subsingleton
  have htop : J • (⊤ : Submodule B N) = ⊤ := by
    apply top_unique
    intro x _
    exact (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  have hp (m : ℕ) : J ^ m • (⊤ : Submodule B N) = ⊤ := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, Submodule.mul_smul, htop, ih]
  have hz : (⊤ : Submodule B N) = ⊥ := by rw [← hp k, hk, Submodule.bot_smul]
  have : Subsingleton N := ⟨fun x y ↦ by
    have hx : x = 0 := hz.le (Submodule.mem_top (x := x))
    have hy : y = 0 := hz.le (Submodule.mem_top (x := y))
    exact hx.trans hy.symm⟩
  exact ModuleCat.isZero_of_subsingleton N

/-- A constant model on a nonempty chart has the Tor interval of the residue.
The zero-complex alternative permits the zero model on empty charts. No finiteness
or projectivity of the model is assumed.

Source: Stacks Project, sites-cohomology.tex, lemma-bounded (094I), part (2).
(blueprint: lem-weil-pbc-finite-quotient-model-tor-amplitude).

Proof: if P is zero, its localized object and every derived tensor are zero.
On a nonempty chart, extract the algebraic derived residue model using the geometric
stalk and the normalized coefficient squares. Put B = A/I^(n+1), and let J be the
image of I in B; then J^(n+1) = 0. The residue model is a projective complex E in
[a,b] over B/J. Stacks Tag 09AR lifts it to a bounded-above projective B-complex F
representing Q(P), with an actual isomorphism F/JF = E of complexes. If E^i = 0,
then F^i = JF^i = ... = J^(n+1)F^i = 0. Thus F has both bounds a and b. Its terms
are projective, hence flat, so its derived tensor with any module in degree zero
is computed termwise and vanishes outside [a,b]. Transport this Tor bound along
the isomorphism Q(F) = Q(P). No finiteness hypothesis on P or on the tensor test
module is used. -/
theorem finiteQuotient_model_torAmplitude
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale) (a b : ℤ)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b)
    (n : ℕ) (W : X.Etale) (g : W ⟶ V)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) ℤ)
    (hchart : Nonempty W.left ∨ IsZero P)
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicQuotientReduction X d n).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d n)
          ((toProEt X).obj W) ((completedAdicDerivedChange X (φ n)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1))) a b
      (DerivedCategory.Q.obj P) := by
  rcases hchart with hW | hP
  · let B := A ⧸ d.ideal ^ (n + 1)
    let J := d.ideal.map (Ideal.Quotient.mk (d.ideal ^ (n + 1)))
    have hnil : J ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow, Ideal.map_quotient_self]
    obtain ⟨L, ε, hL, E, hEa, hEb, hEproj, hE⟩ :=
      finiteQuotient_model_residueProjective X d φ hφ hcompat M V a b hresidue
        n W g P hW e
    let := hL
    obtain ⟨F, _, hFproj, ⟨eF⟩, ⟨ered⟩⟩ :=
      CochainComplex.exists_projective_lift_of_nilpotent B J
        ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), hnil⟩ L ε
        (DerivedCategory.Q.obj P) E ⟨b, hEb⟩ hEproj hE
    have et (i : ℤ) : (ModuleCat.extendScalars (Ideal.Quotient.mk J)).obj (F.X i) ≅
        E.X i := (HomologicalComplex.eval _ _ i).mapIso ered
    have : F.IsStrictlyGE a := (F.isStrictlyGE_iff a).2 fun i hi ↦
      zero_of_nilpotent_reduction J (n + 1) hnil (F.X i)
        (((E.isStrictlyGE_iff a).1 hEa i hi).of_iso (et i))
    have : F.IsStrictlyLE b := (F.isStrictlyLE_iff b).2 fun i hi ↦
      zero_of_nilpotent_reduction J (n + 1) hnil (F.X i)
        (((E.isStrictlyLE_iff b).1 hEb i hi).of_iso (et i))
    apply (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eF
    apply DerivedCategory.torAmplitudeIn_Q_obj_of_flat F a b
    intro i
    have := hFproj i
    exact (ModuleCat.flat_iff_flat _).2 Module.Flat.of_projective
  · have hQ := DerivedCategory.Q.map_isZero hP
    intro N
    have hz := (MonoidalCategory.tensorRight
      ((DerivedCategory.singleFunctor _ 0).obj N)).map_isZero hQ
    exact ⟨DerivedCategory.TStructure.t.isGE_of_isZero hz a,
      DerivedCategory.TStructure.t.isLE_of_isZero hz b⟩

end AlgebraicGeometry.Scheme
