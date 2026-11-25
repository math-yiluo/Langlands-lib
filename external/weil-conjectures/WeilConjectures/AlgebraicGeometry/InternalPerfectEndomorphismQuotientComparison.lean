/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData

public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen
import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectEndomorphismHomComparison
import WeilConjectures.Algebra.Homology.Module.ModulePerfectDualTensorHom

/-! # Actual internal endomorphism reductions and scalar quotient cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

private def scalarQuotientIso {R : Type u} [CommRing R]
    (t : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ≅ Q) (n : ℕ) :
    Padic.scalarQuotient t P n ≅ Padic.scalarQuotient t Q n :=
  cokernel.mapIso (t ^ n • 𝟙 P) (t ^ n • 𝟙 Q) e e (by simp)

private theorem scalarQuotientIso_naturality {R : Type u} [CommRing R]
    (t : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ≅ Q)
    (m n : ℕ) (h : n ≤ m) :
    (scalarQuotientIso t e m).hom ≫ Padic.scalarQuotientTransition t Q m n h =
      Padic.scalarQuotientTransition t P m n h ≫ (scalarQuotientIso t e n).hom := by
  apply (cancel_epi (cokernel.π (t ^ m • 𝟙 P))).1
  simp [scalarQuotientIso, Padic.scalarQuotientTransition, Category.assoc]

private theorem quotientHomologyIso_naturality {R : Type u} [CommRing R]
    (t : R) {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (e : P ≅ Q)
    (m n : ℕ) (h : n ≤ m) :
    HomologicalComplex.homologyMap (scalarQuotientIso t e m).hom 0 ≫
        HomologicalComplex.homologyMap (Padic.scalarQuotientTransition t Q m n h) 0 =
      HomologicalComplex.homologyMap (Padic.scalarQuotientTransition t P m n h) 0 ≫
        HomologicalComplex.homologyMap (scalarQuotientIso t e n).hom 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    scalarQuotientIso_naturality]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The actual internal endomorphism tower has the scalar quotient cohomology model,
including all its quotient arrows.

Source: current blueprint, `proposition-local-structure-integral-constructible-complexes`,
Compatible isomorphisms, paragraph beginning These Hom groups can be infinite; Stacks Tag 09C5.
(blueprint: lem-pe-internal-perfect-endomorphism-quotient-comparison).

Proof: apply the actual internal endomorphism/Hom comparison to obtain natural
bijections with locally constant H^0 of the quotient of moduleHomComplex(P,P).
Apply the finite-free dual-tensor/Hom isomorphism, in the inverse direction, to
identify that complex with the explicit dual tensor Q. The induced cokernel
isomorphisms on scalar quotients commute with quotient transitions: this follows
after precomposing with the epimorphic cokernel projection. Functoriality of homology
gives commuting homology isomorphisms. Postcompose the locally constant functions
with these isomorphisms. The two naturality squares compose to give the displayed
formula, for every n<=m. No choice of an arbitrary target model enters. -/
theorem internalPerfectEndomorphism_quotientComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ∀ n : ℕ,
      (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op n) ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (internalPerfectScalarDualTensor l E P) (n + 1)).homology 0),
      ∀ (n m : ℕ) (h : n ≤ m) (x : (internalReductionHomTower l E W.left
        (internalPerfectScalarModel l E W.left P)
        (internalPerfectScalarModel l E W.left P)).obj (op m)),
        e n ((internalReductionHomTower l E W.left
          (internalPerfectScalarModel l E W.left P)
          (internalPerfectScalarModel l E W.left P)).map (homOfLE h).op x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (internalPerfectScalarDualTensor l E P) (m + 1) (n + 1)
              (Nat.succ_le_succ h)) 0) (e m x)  := by
  obtain ⟨e, he⟩ := internalPerfectEndomorphism_homComparison l E X W
    _hAffine _hweak P a b _ha _hb _hfree
  obtain ⟨g⟩ := CochainComplex.modulePerfectDualTensorHom_iso P a b _ha _hb _hfree
  let g' : CochainComplex.moduleHomComplex P P ≅ internalPerfectScalarDualTensor l E P :=
    g.symm
  let h (n : ℕ) := HomologicalComplex.homologyMapIso
    (scalarQuotientIso (Padic.coefficientExtensionUniformizer l E) g' (n + 1)) 0
  let k (n : ℕ) := (h n).toLinearEquiv.toEquiv
  refine ⟨fun n ↦ (e n).trans (LocallyConstant.congrRight (k n)), ?_⟩
  intro n m hnm x
  change LocallyConstant.map (k n) (e n (_)) = _
  rw [he]
  ext y
  exact ConcreteCategory.congr_hom
    (quotientHomologyIso_naturality (Padic.coefficientExtensionUniformizer l E)
      g' (m + 1) (n + 1) (Nat.succ_le_succ hnm)) (e m x y) |>.symm


end AlgebraicGeometry.ProEtale
