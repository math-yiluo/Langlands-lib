/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import all WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine

/-! # Cardinalities of the two projective-line fibre homology groups

Source: blueprint lemma-cohomology-projective-line-trace, geometric-fibre calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors
  AlgebraicGeometry.ProjectiveSpace Scheme.finiteEtaleTateLine ordinaryFinitePushforward
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
set_option allowUnsafeReducibility true in
attribute [local reducible] ordinaryFiniteDegreeZero ordinaryFiniteLine ordinaryFiniteUnit

/-- Given the scalar generator calculation in H2, sections of either nonzero
homology of the shifted projective-line direct image have the cardinality of A.
Source: blueprint lemma-cohomology-projective-line-trace, geometric-fibre calculation.
(auxiliary; not a blueprint node).

Proof: the canonical homology/global-cohomology comparison identifies degree zero
homology with H2 on the projective line. The specified scalar bijection identifies
that group with A. In degree minus two, a primitive root trivializes the Tate line.
Connectedness of the projective line identifies its constant H0 with A. Transport
these equivalences back through the canonical comparison. The same argument
includes the zero coefficient ring. -/
theorem ordinaryFiniteP1_fibre_target_card
    (N : ℕ) (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (k : Type u) [Field k] [IsAlgClosed k] (hNk : (N : k) ≠ 0)
    (hκ : ∀ (hP : IsUnit (N : Γ(ProjectiveLine (Spec (.of k)), ⊤))),
      Function.Bijective (fun a : A ↦ Sheaf.H.map
        ((moduleAbelianForget A (ProjectiveLine (Spec (.of k)))).map
          (a • 𝟙 (Scheme.finiteEtaleTateLine (ProjectiveLine (Spec (.of k))) N A hA))) 2
        (ordinaryFiniteP1KummerClass A N hA (Spec (.of k)) hP)))
    (n : ℤ) (hn : n = 0 ∨ n = -2) :
    Nonempty (
      ((constantSheafEquivalenceOfIsSepClosed A (k := k)).inverse.obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((ordinaryFinitePushforward A
            (ProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).obj
              ((ordinaryFiniteLine A N hA
                (ProjectiveLine (Spec (.of k))))⟦(2 : ℤ)⟧)))) ≃ A) := by
  obtain ⟨hcurve, hsmooth, hproper, -, -⟩ :=
    ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
  have := hcurve
  have := hsmooth
  have := hproper
  let P := ProjectiveLine (Spec (.of k))
  have : CompactSpace P :=
    QuasiCompact.compactSpace_of_compactSpace (P ↘ Spec (.of k))
  have : QuasiSeparatedSpace P :=
    quasiSeparatedSpace_of_quasiSeparated (P ↘ Spec (.of k))
  let F := Scheme.finiteEtaleTateLine P N A hA
  rcases hn with rfl | rfl
  · let e := (ordinaryFinitePushforward_single_shift_homology_iso A)
      k (P ↘ Spec (.of k)) F 0 2 (by norm_num)
    obtain ⟨eH⟩ := nonempty_cohomology_singleFunctor_iso_sheafH A P F 2
    let hP := AffineSpace.isUnit_natCast_of_ne_zero (P ↘ Spec (.of k)) hNk
    let d := Equiv.ofBijective _ (hκ hP)
    let e' := (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}).mapIso e ≪≫ eH
    exact ⟨e'.addCommGroupIsoToAddEquiv.toEquiv.trans d.symm⟩
  · let e := (ordinaryFinitePushforward_single_shift_homology_iso A)
      k (P ↘ Spec (.of k)) F (-2) 0 (by norm_num)
    obtain ⟨σ⟩ := (kummer_line_as_constant N A hA) k (P ↘ Spec (.of k)) hNk
    obtain ⟨hcurve, -, -, -, -⟩ :=
      ProjectiveSpace.isConnectedCurve_smooth_proper_genus_zero k
    have := hcurve
    have : ConnectedSpace P := IsConnectedCurve.connectedSpace (P ↘ Spec (.of k))
    let d := (DerivedCategory.singleFunctor _ 0).mapIso σ ≪≫
      (constantComplexIsoSingleFunctorConstantSheaf A P).symm
    exact ⟨(CategoryTheory.Iso.toLinearEquiv (e ≪≫
      (cohomology (ModuleCat.{u + 1} A) P 0).mapIso d ≪≫
        cohomologyZeroConstantComplexIso A P)).toEquiv⟩

end AlgebraicGeometry.Etale
