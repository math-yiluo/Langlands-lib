/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
import WeilConjectures.AlgebraicGeometry.Curve.DenseOpenIntegralBoundaryFiniteness
import WeilConjectures.AlgebraicGeometry.Curve.IntegralOpenExtensionComparison
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.Gabber
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Dense-open finiteness with integral torsion coefficients

Source: Stacks Project, Tag 0GJA, proof, using Tag 095L.
(blueprint: lem-pbc-h2-dense-open-integral-cohomology-finiteness). -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

private noncomputable def cohomologyEquiv {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (q : ℕ) :
    Sheaf.H F q ≃ Sheaf.H G q where
  toFun := Sheaf.H.map e.hom q
  invFun := Sheaf.H.map e.inv q
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id]; simp
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id]; simp

/-- Finiteness of all cohomology groups transfers across the dense-open counit
for a constructible torsion abelian sheaf, encoded with integral coefficients.
Source: Stacks Project, Tag 0GJA, proof (five-term sequence), with Tag 095L.
(blueprint: lem-pbc-h2-dense-open-integral-cohomology-finiteness).

Proof: Use the open-closed short exact sequence for the integral module sheaf F,
and forget it to an exact sequence of abelian sheaves. Its boundary term Q has finite
cohomology in every degree by dense_open_integral_boundary_finiteness. The integral
open-extension comparison identifies its first term J with the encoded G, hence also
identifies their cohomology. If F has finite cohomology, H^0(J) injects into H^0(F);
for each q=n+1 the exact segment H^n(Q) -> H^q(J) -> H^q(F) has finite outer terms,
so H^q(J) is finite. Conversely the exact segment H^q(J) -> H^q(F) -> H^q(Q)
has finite outer terms in every degree. Apply ShortComplex.Exact.ab_finite to both
segments and transport along the cohomology isomorphism J=G. This argument needs only
finiteness of the boundary groups, not a separate higher-degree comparison theorem.
No finite coefficient ring or ambient reducedness is required. Empty X and U=X
are included in the same exact-sequence argument. -/
theorem dense_open_integral_cohomology_finiteness {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) (hP : (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F)))
    (U : P.C.Opens) (hU : Dense (U : Set P.C)) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let B := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
    let G := (sheafCompose P.C.smallEtaleTopology E).obj B
    let T := sheafCompose P.C.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
    (∀ q : ℕ, Finite (Sheaf.H (T.obj F) q)) ↔
      (∀ q : ℕ, Finite (Sheaf.H (T.obj G) q)) := by
  classical
  dsimp only
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let F := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let B := (Etale.openImmersionLowerShriek AddCommGrpCat.{u + 1} U.ι).obj
    ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj P.F)
  let G := (sheafCompose P.C.smallEtaleTopology E).obj B
  let T := sheafCompose P.C.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1})
  let S := Etale.openClosedShortComplex (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    U.ι U.closedComplement
    (disjoint_range_of_range_eq_compl U.ι U.closedComplement
      (by rw [U.range_closedComplement, Scheme.Opens.range_ι])) F
  let A := S.map T
  have hS := Etale.shortExact_openClosedShortComplex
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) U.ι U.closedComplement F
      (by rw [U.range_closedComplement, Scheme.Opens.range_ι])
  have hA : A.ShortExact := Etale.shortExact_map_forget₂ (ULift.{u + 1} ℤ) hS
  have hQ : ∀ q : ℕ, Finite (Sheaf.H A.X₃ q) :=
    dense_open_integral_boundary_finiteness P hP U hU
  obtain ⟨e⟩ := Etale.integral_open_extension_comparison P.F U
  have eH (q : ℕ) : Sheaf.H (T.obj G) q ≃ Sheaf.H A.X₁ q :=
    cohomologyEquiv (T.mapIso e) q
  constructor
  · intro h q
    have hleft : Finite (Sheaf.H A.X₁ q) := by
      cases q with
      | zero =>
        have : Finite (Sheaf.H A.X₂ 0) := h 0
        have := hA.mono_f
        exact Finite.of_injective _
          (Abelian.Ext.postcomp_mk₀_injective_of_mono _ A.f)
      | succ n =>
        have : Finite (Sheaf.H A.X₂ (n + 1)) := h (n + 1)
        have := hQ n
        exact (Abelian.Ext.covariant_sequence_exact₁' _ hA n (n + 1) rfl).ab_finite
    exact Finite.of_equiv _ (eH q).symm
  · intro h q
    have := h q
    have : Finite (Sheaf.H A.X₁ q) := Finite.of_equiv _ (eH q)
    have := hQ q
    exact (Abelian.Ext.covariant_sequence_exact₂' _ hA q).ab_finite


end AlgebraicGeometry.IsCurve
