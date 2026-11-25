/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalPerfectOrdinaryReductions
public import WeilConjectures.NumberTheory.Padics.IntegralScalarTowers
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import all WeilConjectures.AlgebraicGeometry.AdicPerfectModelHomCohomology
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectBasisSuccessor
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectCoefficientTransitions
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectDifferentialCompatibility
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectFiniteCochainCoordinates
public import WeilConjectures.AlgebraicGeometry.InternalPerfectMatrix.InternalPerfectSuccessorCompatibility

/-! # Ordinary quotient endomorphisms and scalar Hom cohomology -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem cohomology_of_cochainComparison
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i))
    (comparison : ∀ n : ℕ, InternalPerfectMatrix.quotientCochains l E W.left P n ≅
      CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W.left P n)
        (internalPerfectOrdinaryReduction l E W.left P n))
    (square : ∀ n : ℕ,
      (comparison (n + 1)).hom ≫ InternalPerfectMatrix.successorMap l E W.left P n =
        InternalPerfectMatrix.quotientStep l E W.left P n ≫ (comparison n).hom) :
    ∃ e : ∀ n : ℕ, internalPerfectOrdinaryHom l E W.left P n ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n : ℕ) (x : internalPerfectOrdinaryHom l E W.left P (n + 1)),
        e n (internalPerfectOrdinaryHomStep l E W.left P n x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
              (Nat.succ_le_succ (Nat.le_succ n))) 0) (e (n + 1) x) := by
  let G := InternalPerfectMatrix.sections l E W.left
  let Q := fun n : ℕ ↦ Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
    (CochainComplex.moduleHomComplex P P) (n + 1)
  let r : ∀ n : ℕ,
      (CochainComplex.HomComplex (internalPerfectOrdinaryReduction l E W.left P n)
        (internalPerfectOrdinaryReduction l E W.left P n)).homology 0 ≅
          G.obj ((Q n).homology 0) := fun n ↦
    (HomologicalComplex.homologyFunctor _ _ 0).mapIso (comparison n).symm ≪≫
      ((Q n).sc 0).mapHomologyIso G
  refine ⟨fun n ↦ (Scheme.homologyHomEquiv _ _).trans
    ((r n).addCommGroupIsoToAddEquiv.toEquiv.trans Equiv.ulift), ?_⟩
  intro n x
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ (.up ℤ)).map_surjective x
  rw [internalPerfectOrdinaryHomStep_map]
  let Φ := Mod.extendScalars (AdicCompletion.transition l E W.left n)
  let α := internalPerfectOrdinaryReductionStep l E W.left P n
  let γ := InternalPerfectMatrix.successorMap l E W.left P n
  let ψ := InternalPerfectMatrix.quotientStep l E W.left P n
  have hs : γ ≫ (comparison n).inv = (comparison (n + 1)).inv ≫ ψ := by
    apply (cancel_epi (comparison (n + 1)).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [square n, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hH := congrArg (fun k ↦ HomologicalComplex.homologyMap k 0) hs
  simp only [HomologicalComplex.homologyMap_comp] at hH
  let τ := Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
    (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
    (Nat.succ_le_succ (Nat.le_succ n))
  have hnat : HomologicalComplex.homologyMap γ 0 ≫ (r n).hom =
      (r (n + 1)).hom ≫ G.map (HomologicalComplex.homologyMap τ 0) := by
    dsimp only [r, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.homologyFunctor]
    rw [← Category.assoc, hH, Category.assoc]
    exact congrArg (fun k ↦ HomologicalComplex.homologyMap (comparison (n + 1)).inv 0 ≫ k)
      (ShortComplex.mapHomologyIso_hom_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ 0).map τ) G)
  have hh := Scheme.homologyHomEquiv_scalar Φ α α f
  change ((r n).hom (Scheme.homologyHomEquiv _ _
      ((HomotopyCategory.quotient _ (.up ℤ)).map
        (α.inv ≫ (Φ.mapHomologicalComplex (.up ℤ)).map f ≫ α.hom)))).down = _
  rw [hh]
  change ((r n).hom (HomologicalComplex.homologyMap γ 0
    (Scheme.homologyHomEquiv _ _ ((HomotopyCategory.quotient _ (.up ℤ)).map f)))).down = _
  rw [← AddCommGrpCat.comp_apply, hnat, AddCommGrpCat.comp_apply]
  rfl

/-- Homotopy endomorphisms of the ordinary quotient model are locally constant quotient
Hom cohomology, with the formula for ordinary successor reduction. This statement
concerns ordinary complexes only and makes no assertion about derived reductions.

Source: Stacks Tags 09C5, 09C6 and 0A8H; blueprint Compatible isomorphisms.
(blueprint: lem-pe-internal-perfect-ordinary-hom-cohomology).

Proof: identify maps modulo homotopy with degree-zero homology of the signed Hom
complex. Fix finite integral bases in every degree and extend these same bases to
all ordinary quotient levels. Finite matrix evaluation identifies internal Hom
cochains with locally constant scalar quotient cochains. Degreewise bijectivity
uses finite support, basis coordinates and the actual cokernel projection.
Integral scalar normalization identifies the realized differentials with their
constant residue matrices; the signed matrix formula then proves that evaluation
is a chain map. Locally constant module-valued functions preserve exactness:
choose preimages of their values, so the resulting functions remain locally
constant. Their homology comparison and the signed Hom equivalence give the
asserted equivalence. Normalized coefficient-section naturality and composition
of the fixed free-basis comparisons prove compatibility with actual successor
scalar extension and balancing. Homology naturality gives the asserted formula.
The zero complex, rank-zero terms, empty intervals and the empty scheme require
no separate nonemptiness choices. -/
theorem internalPerfectOrdinary_homCohomology
    (X : Scheme.{u}) (W : X.ProEt) (_hAffine : IsAffine W.left)
    (_hweak : (Scheme.ProEt.topology X).IsWeaklyContractible.{u + 1} W)
    (P : CochainComplex (ModuleCat.{u} (Padic.coefficientExtensionIntegers l E)) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hfree : ∀ i : ℤ, Module.Finite (Padic.coefficientExtensionIntegers l E) (P.X i) ∧
      Module.Free (Padic.coefficientExtensionIntegers l E) (P.X i)) :
    ∃ e : ∀ n : ℕ, internalPerfectOrdinaryHom l E W.left P n ≃
      LocallyConstant (ConnectedComponents W.left)
        ((Padic.scalarQuotient (Padic.coefficientExtensionUniformizer l E)
          (CochainComplex.moduleHomComplex P P) (n + 1)).homology 0),
      ∀ (n : ℕ) (x : internalPerfectOrdinaryHom l E W.left P (n + 1)),
        e n (internalPerfectOrdinaryHomStep l E W.left P n x) =
        LocallyConstant.map
          (HomologicalComplex.homologyMap
            (Padic.scalarQuotientTransition (Padic.coefficientExtensionUniformizer l E)
              (CochainComplex.moduleHomComplex P P) (n + 2) (n + 1)
              (Nat.succ_le_succ (Nat.le_succ n))) 0) (e (n + 1) x) := by
  let C := fun n : ℕ ↦ CochainComplex.HomComplex
    (internalPerfectOrdinaryReduction l E W.left P n)
    (internalPerfectOrdinaryReduction l E W.left P n)
  let D := InternalPerfectMatrix.quotientCochains l E W.left P
  have hd : ∀ (n : ℕ) (i j : ℤ),
      InternalPerfectMatrix.evaluationHom l E W.left P _hfree n i ≫ (C n).d i j =
        (D n).d i j ≫ InternalPerfectMatrix.evaluationHom l E W.left P _hfree n j := fun n i j ↦
    InternalPerfectMatrix.evaluation_differential l E W.left P _hfree n i j
  have hs : ∀ (n : ℕ) (q : ℤ),
      InternalPerfectMatrix.evaluationHom l E W.left P _hfree (n + 1) q ≫
          (InternalPerfectMatrix.successorMap l E W.left P n).f q =
        (InternalPerfectMatrix.quotientStep l E W.left P n).f q ≫
          InternalPerfectMatrix.evaluationHom l E W.left P _hfree n q := fun n q ↦
    InternalPerfectMatrix.evaluation_successor_of_squares l E W.left P _hfree n
      (InternalPerfectMatrix.coefficientEnd_step l E W.left n)
      (InternalPerfectMatrix.quotientIso_successor l E W.left P _hfree n) q
  let comparison : ∀ n : ℕ, D n ≅ C n := fun n ↦ by
    let f : D n ⟶ C n :=
      { f := fun q ↦ InternalPerfectMatrix.evaluationHom l E W.left P _hfree n q
        comm' := fun i j _ ↦ hd n i j }
    haveI (q : ℤ) : IsIso (f.f q) :=
      (ConcreteCategory.isIso_iff_bijective _).2
        (InternalPerfectMatrix.evaluation_bijective l E W.left P _hfree a b q _ha _hb n)
    haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
    exact asIso f
  apply cohomology_of_cochainComparison l E X W _hAffine _hweak P a b _ha _hb
    _hfree comparison
  intro n
  apply HomologicalComplex.hom_ext
  intro q
  exact hs n q

end AlgebraicGeometry.ProEtale
