/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Field.ULift
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.AlgebraicGeometry.CondensedConstantConstructibility
public import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
public import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteSchemeRing
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison

/-!
# Transport of finite constant-model stratification witnesses

proof.md, Constructibility paragraph
(auxiliary; not a blueprint node).

The adapters keep all partition and immersion data. The transport statements fix the
cover and scalar modules before changing the module being modelled. Constructibility
and bounded constructible cohomology use the finite constant-model convention.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.Scheme

/-- Forget only constructibility proofs, retaining every partition and immersion field.
Source: the Constructibility paragraph of sk-prop-proper-image-localizing-open.proof.md,
stratification adapter (auxiliary; not a blueprint node). -/
def Stratification.toFiniteLocallyClosed {T : Scheme.{u}} (S : Stratification T) :
    FiniteLocallyClosedStratification T where
  n := S.n
  stratum := S.stratum
  isLocallyClosed_stratum := S.isLocallyClosed_stratum
  iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
  domain := S.domain
  immersion := S.immersion
  isImmersion := S.isImmersion
  range_immersion := S.range_immersion

/-- Adjoin the separate constructibility proofs without choosing new stratum schemes.
Source: the Constructibility paragraph of sk-prop-proper-image-localizing-open.proof.md,
stratification adapter (auxiliary; not a blueprint node). -/
def FiniteLocallyClosedStratification.withConstructibleStrata {T : Scheme.{u}}
    (S : FiniteLocallyClosedStratification T)
    (c : ∀ a : Fin S.n, Topology.IsConstructible (S.stratum a)) : Stratification T where
  n := S.n
  stratum := S.stratum
  isLocallyClosed_stratum := S.isLocallyClosed_stratum
  isConstructible_stratum := c
  iUnion_stratum_eq_univ := S.iUnion_stratum_eq_univ
  pairwise_disjoint_stratum := S.pairwise_disjoint_stratum
  domain := S.domain
  immersion := S.immersion
  isImmersion := S.isImmersion
  range_immersion := S.range_immersion

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Constructibility in the affine-local finite constant-model convention transports.
Source: sk-prop-proper-image-localizing-open.proof.md, Constructibility paragraph
(auxiliary; not a blueprint node).

Proof: in the qcqs branch retain the stratification and apply step 2 on each stratum
as in step 3. In the other branch restrict the isomorphism to each affine open and
repeat there, as in step 4. Unpack and repack the same defining existential witnesses. -/
theorem constantModelConstructible_transport {T : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ T M) :
    IsConstantModelConstructible Λ T N := by
  have hlocal (Y : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (f : A ≅ B) (hA : HasFiniteConstantLocalModel Λ Y A) :
      HasFiniteConstantLocalModel Λ Y B := by
    obtain ⟨𝒰, h𝒰⟩ := hA
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨(CondensedRing.upperStar Λ (𝒰.f i)).mapIso f.symm ≪≫ eP⟩⟩
  have hstrat (Y : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
      (f : A ≅ B) (hA : IsFiniteConstantStratified Λ Y A) :
      IsFiniteConstantStratified Λ Y B := by
    obtain ⟨S, hS⟩ := hA
    exact ⟨S, fun a ↦ hlocal _
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso f) (hS a)⟩
  classical
  unfold IsConstantModelConstructible at hM ⊢
  split_ifs at hM ⊢ with hT
  · exact hstrat _ e hM
  · exact fun U hU ↦ hstrat _ ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

end AlgebraicGeometry.ProEtale
