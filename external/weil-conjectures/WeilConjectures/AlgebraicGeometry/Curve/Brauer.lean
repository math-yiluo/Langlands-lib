/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.BrauerGroup
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.FieldTheory.Tsen
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.NoetherianSpace

import WeilConjectures.AlgebraicGeometry.Curve.BrauerReductionInjection
import WeilConjectures.AlgebraicGeometry.Curve.BrauerFiniteModificationInjection
import WeilConjectures.AlgebraicGeometry.ReducedCurveNormalization
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.EtaleAffineQcoherent
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Sites.FiniteSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Tsen's theorem and the Brauer group of a curve

The function field of an integral curve over an algebraically closed field is `C₁`, so its
Brauer group vanishes; the Brauer group of a smooth curve over an algebraically closed field
vanishes, since it injects into that of its function field on each connected component; and the
Brauer group of every curve over an algebraically closed field vanishes.

Curves are given by a structure morphism `f : C ⟶ Spec k` satisfying
`AlgebraicGeometry.IsCurve`.

## Main statements

- `AlgebraicGeometry.IsCurve.isQuasiAlgClosed_functionField`: Tsen's theorem, the function
  field of an integral curve over an algebraically closed field is `C₁`.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_functionField`: the Brauer
  group of that function field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_connectedSpace`: the
  Brauer group of a smooth connected curve over an algebraically closed field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup_of_smooth`: the Brauer group
  of a smooth curve over an algebraically closed field vanishes.
- `AlgebraicGeometry.IsCurve.subsingleton_cohomologicalBrauerGroup`: the Brauer group of a
  curve over an algebraically closed field vanishes.

## Implementation notes

The field-theoretic statements, Tsen's theorem `IsQuasiAlgClosed.of_trdeg_le_one` and the
vanishing `IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup`, are the reusable ones; the
function-field statements here are their specialisations to curves.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **Tsen's theorem for curves.** For an integral curve `C` over an algebraically closed
field `k`, the function field `k(C)` is quasi-algebraically closed: every homogeneous form of
degree `d` in `N > d` variables over `k(C)` has a nontrivial zero. Neither smoothness nor
properness of `C` is assumed.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem isQuasiAlgClosed_functionField (f : C ⟶ Spec (.of k)) [IsCurve f] [IsIntegral C] :
    IsQuasiAlgClosed C.functionField := by
  -- `k(C)` is the fraction field of `A = Γ(C, U)` for a nonempty affine open `U`, a finitely
  -- generated `k`-domain of dimension at most one; so `trdeg_k k(C) = trdeg_k A = dim A ≤ 1`.
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hft : RingHom.FiniteType (f.appLE ⊤ U (by simp)).hom :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  let φ : k →+* Γ(C, U) := (f.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have hφ : φ.FiniteType := hft.comp (RingHom.FiniteType.of_surjective _
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let := φ.toAlgebra
  have : Algebra.FiniteType k Γ(C, U) := hφ
  let := (C.germToFunctionField U).hom.toAlgebra
  let : Algebra k C.functionField := ((C.germToFunctionField U).hom.comp φ).toAlgebra
  have : IsScalarTower k Γ(C, U) C.functionField := .of_algebraMap_eq fun _ ↦ rfl
  have : IsFractionRing Γ(C, U) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C U hU
  have : FaithfulSMul Γ(C, U) C.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  have : Algebra.IsAlgebraic Γ(C, U) C.functionField :=
    IsLocalization.isAlgebraic C.functionField (nonZeroDivisors Γ(C, U))
  have hdim : ringKrullDim Γ(C, U) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact (IsHomeomorph.topologicalKrullDim_eq _
      hU.isoSpec.hom.homeomorph.isHomeomorph).symm.trans_le
      ((topologicalKrullDim_subspace_le C U).trans (IsCurve.krullDim_le_one (f := f)))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim Γ(C, U) = n := by
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := Γ(C, U))
    generalize ringKrullDim Γ(C, U) = d at h0 hdim
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd (WithBot.coe_le_coe.mp hdim) (by simp)
      | coe n => exact ⟨n, rfl⟩
  rw [hn] at hdim
  apply IsQuasiAlgClosed.of_trdeg_le_one k
  rw [← trdeg_add_eq k Γ(C, U) (A := C.functionField), trdeg_eq_zero (R := Γ(C, U)), add_zero,
    Algebra.trdeg_eq_of_ringKrullDim_eq k _ hn]
  exact_mod_cast hdim

/-- The Brauer group of the function field of an integral curve over an algebraically closed
field vanishes, `Br(k(C)) = H²(k(C), 𝔾ₘ) = 0`.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
theorem subsingleton_cohomologicalBrauerGroup_functionField (f : C ⟶ Spec (.of k)) [IsCurve f]
    [IsIntegral C] : Subsingleton (Spec C.functionField).CohomologicalBrauerGroup :=
  have := isQuasiAlgClosed_functionField f
  IsQuasiAlgClosed.subsingleton_cohomologicalBrauerGroup C.functionField

/-- **The Brauer group of a smooth connected curve vanishes.** For a smooth connected curve
`C` over an algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. The curve `C` is
integral, noetherian and regular, so `Br(C)` injects into `Br(k(C))`
(`AlgebraicGeometry.Scheme.injective_cohomologyMap_gmSheaf_two`), and `Br(k(C)) = 0` by Tsen's
theorem. Properness is not needed, so no compactification is used.
(blueprint: `lemma-cohomology-multiplicative-group--6`) 
(blueprint: lemma-cohomology-multiplicative-group--6)
-/
theorem subsingleton_cohomologicalBrauerGroup_of_connectedSpace (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] : Subsingleton C.CohomologicalBrauerGroup := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  have : IsRegular C := IsRegular.of_smooth f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  -- `Br(k(C)) = 0`, and the pullback of `𝔾ₘ` to the generic point is `𝔾ₘ`
  have := subsingleton_cohomologicalBrauerGroup_functionField f
  have := C.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
      C.fromSpecFunctionField).obj C.gmSheaf) 2) :=
    let e := asIso (Scheme.upperStarGmSheafToGmSheaf C.fromSpecFunctionField)
    (Function.LeftInverse.injective (f := Sheaf.H.map e.hom 2) (g := Sheaf.H.map e.inv 2)
      fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton
  exact C.injective_cohomologyMap_gmSheaf_two.subsingleton

/-- **The Brauer group of a smooth curve vanishes.** For a smooth curve `C` over an
algebraically closed field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. The blueprint states this for
smooth proper curves; properness is not needed.

The finitely many connected components of `C` are clopen, so `Br(C)` vanishes as soon as the
Brauer group of every component does
(`AlgebraicGeometry.Etale.subsingleton_H_of_isClopen`), and each component is a smooth
connected curve, to which `subsingleton_cohomologicalBrauerGroup_of_connectedSpace` applies.
(blueprint: `lemma-cohomology-multiplicative-group`) -/
theorem subsingleton_cohomologicalBrauerGroup_of_smooth (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] : Subsingleton C.CohomologicalBrauerGroup := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  -- the connected components of `C`, indexed by `ConnectedComponents C`
  choose x hx using ConnectedComponents.surjective_coe (α := C)
  let U (c : ConnectedComponents C) : C.Opens :=
    ⟨connectedComponent (x c), TopologicalSpace.NoetherianSpace.isOpen_connectedComponent _⟩
  have hU (y : C) : y ∈ U y := by
    change y ∈ connectedComponent (x y)
    rw [ConnectedComponents.coe_eq_coe.mp (hx y)]
    exact mem_connectedComponent
  refine Etale.subsingleton_H_of_isClopen U (fun c ↦ isClosed_connectedComponent)
    (fun c d hcd ↦ ?_) (fun y ↦ ⟨y, hU y⟩) _ 2 fun c ↦ ?_
  · refine Set.disjoint_left.mpr fun y (hyc : y ∈ connectedComponent (x c))
      (hyd : y ∈ connectedComponent (x d)) ↦ hcd ?_
    rw [← hx c, ← hx d, ConnectedComponents.coe_eq_coe,
      connectedComponent_eq hyc, connectedComponent_eq hyd]
  -- each connected component is a smooth connected curve
  have : ConnectedSpace (U c) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : IsCurve ((U c).ι ≫ f) :=
    { krullDim_le_one :=
        (topologicalKrullDim_subspace_le C (U c)).trans (IsCurve.krullDim_le_one f) }
  have := subsingleton_cohomologicalBrauerGroup_of_connectedSpace ((U c).ι ≫ f)
  let e := Scheme.upperStarGmSheafIso (U c).ι
  exact (Function.LeftInverse.injective (f := Sheaf.H.map e.hom 2) (g := Sheaf.H.map e.inv 2)
    fun x ↦ by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]).subsingleton

/-- **The Brauer group of a curve vanishes.** For a curve `C` over an algebraically closed
field `k`, `Br(C) = H²(C_ét, 𝔾ₘ) = 0`. Neither smoothness nor properness is assumed.
(blueprint: `lemma-cohomology-multiplicative-group--6`) 
(blueprint: lemma-cohomology-multiplicative-group--6)
-/
theorem subsingleton_cohomologicalBrauerGroup (f : C ⟶ Spec (.of k)) [IsCurve f] :
    Subsingleton C.CohomologicalBrauerGroup := by
  let C₀ := C.nilradical.subscheme
  let i : C₀ ⟶ C := C.nilradical.subschemeι
  have hi : Function.Surjective i := by
    apply Set.range_eq_univ.mp
    change Set.range C.nilradical.subschemeι = Set.univ
    rw [Scheme.IdealSheafData.range_subschemeι, C.support_nilradical]
    rfl
  have hi_homeo : IsHomeomorph i :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨i.isClosedEmbedding.isEmbedding, hi⟩
  have : IsCurve (i ≫ f) :=
    { krullDim_le_one := by
        rw [IsHomeomorph.topologicalKrullDim_eq i hi_homeo]
        exact IsCurve.krullDim_le_one f }
  let : C₀.Over (Spec (.of k)) := ⟨i ≫ f⟩
  have : IsSeparated (C₀ ↘ Spec (.of k)) := inferInstanceAs (IsSeparated (i ≫ f))
  have : LocallyOfFiniteType (C₀ ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ f))
  have : QuasiCompact (C₀ ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact (i ≫ f))
  obtain ⟨Y, ν, hsep, hft, hqc, hdim, hsm, hfin, V, hV, hiso⟩ :=
    exists_finite_smooth_modification_of_reduced_curve (k := k) C₀
      (IsCurve.krullDim_le_one (i ≫ f))
  have : IsSeparated (ν ≫ (i ≫ f)) := hsep
  have : LocallyOfFiniteType (ν ≫ (i ≫ f)) := hft
  have : QuasiCompact (ν ≫ (i ≫ f)) := hqc
  have : IsCurve (ν ≫ (i ≫ f)) := { krullDim_le_one := hdim }
  have : Smooth (ν ≫ (i ≫ f)) := hsm
  have : IsFinite ν := hfin
  have : IsIso (ν ∣_ V) := hiso
  have : Subsingleton Y.CohomologicalBrauerGroup :=
    subsingleton_cohomologicalBrauerGroup_of_smooth (ν ≫ (i ≫ f))
  have : Subsingleton C₀.CohomologicalBrauerGroup :=
    (injective_brauer_pullback_finite_modification (i ≫ f) ν V hV).subsingleton
  exact (injective_brauer_pullback_reduction f).subsingleton

end AlgebraicGeometry.IsCurve
