/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteRetractTensorComplexTerms
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionUniverses
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Local cohomology calculation for a strictly perfect tensor

Source: Stacks Project, Tags 0DJQ, 08C4, 06YH and 01Y0.
(blueprint: lem-pc-strict-perfect-tensor-local-cohomology).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

noncomputable local instance localCohomologyTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

private theorem tensorComplex_isZero_X (Y : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (a b c d : ℤ)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hN : ∀ n : ℤ, n < c ∨ d < n → IsZero (N.X n))
    (i : ℤ) (hi : i < a + c ∨ b + d < i) :
    IsZero ((CochainComplex.mapBifunctor P N (curriedTensor _)).X i) := by
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change p + q = i at hpq
  have hz : IsZero (P.X p ⊗ N.X q) := by
    by_cases hp : p < a ∨ b < p
    · exact (tensorRight (N.X q)).map_isZero (hP p hp)
    · have hq : q < c ∨ d < q := by omega
      exact (tensorLeft (P.X p)).map_isZero (hN q hq)
  exact hz.eq_of_src _ _

private theorem coherent_homology_of_coherent_terms (Y : Scheme.{u})
    (T : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hc : ∀ n : ℤ, RingedSpace.IsCoherent Y.toRingedSpace (T.X n)) (i : ℤ) :
    RingedSpace.IsCoherent Y.toRingedSpace (T.homology i) := by
  let S := T.sc i
  have hclosure := RingedSpace.coherent_kernel_cokernel_sum Y.toRingedSpace
  have hk : RingedSpace.IsCoherent Y.toRingedSpace (kernel S.g) :=
    (hclosure.1 _ _ S.g (hc i) (hc ((ComplexShape.up ℤ).next i))).1
  have hh := (hclosure.1 _ _ (kernel.lift S.g S.f S.zero)
    (hc ((ComplexShape.up ℤ).prev i)) hk).2
  exact hclosure.2.2.2.2 _ _ S.homologyIsoCokernelLift.symm hh

/-- A strictly perfect representative on one open computes the restricted tensor
cohomology, with the sum of the two termwise degree intervals as a vanishing interval.
Source: Stacks Project, perfect.tex, Tag 0DJQ, local tensor calculation in Lemma 36.27.2;
cohomology.tex, Tags 08C4 and 06YH; coherent.tex, Tag 01Y0.
(blueprint: lem-pc-strict-perfect-tensor-local-cohomology).

Proof: Restrict G termwise to U and transport through Modules.overEquiv U to the
open subscheme. Exact restriction preserves its bounds [c,d] and coherence of its
terms. Transport K and its finite-free retractions through the same equivalence.
Each transported term of K is a retract of a finite free module, hence flat.
The bounded complex K is therefore K-flat. The derived tensor restricted to U is
computed by the ordinary signed total tensor of this K with the restriction of G:
open restriction commutes with derived tensor, the given e identifies the first
factor, and the K-flat tensor comparison identifies its total complex with the
localized tensor. Exact restriction and the derived homology comparison identify
its i-th homology with the restriction of the global tensor's i-th homology.
In total degree n only pairs p+q=n with a<=p<=b and c<=q<=d contribute.
Consequently the total term is zero outside [a+c,b+d]. Its terms are coherent:
each tensor summand is a retract of a finite direct sum of coherent terms of G,
and only finitely many summands are nonzero. Coherent modules form an abelian
subcategory (01Y0), so kernels, images and the quotient of cycles by boundaries
are coherent. A zero total term has zero homology in that degree. Transport these
facts across the homology isomorphism. This argument works for empty U, zero
terms and reversed intervals; an interval with a>b forces every term of K to
vanish, and similarly for c>d. It uses only local Noetherianity, not compactness. -/
theorem strictPerfect_tensor_local_cohomology
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a b c d : ℤ)
    (hKb : ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (hGb : ∀ n : ℤ, n < c ∨ d < n → IsZero (G.X n))
    (hGcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (G.X n)) :
    ∀ i : ℤ,
      (i < a + c ∨ b + d < i →
        IsZero ((Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
              (E ⊗ DerivedCategory.Q.obj G)))) ∧
      RingedSpace.IsCoherent U.toScheme.toRingedSpace
        ((Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
              (E ⊗ DerivedCategory.Q.obj G))) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  let A : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    (Modules.overEquiv U).functor
  let S := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let R := S ⋙ A
  let P := (A.mapHomologicalComplex (.up ℤ)).obj K
  let N := (R.mapHomologicalComplex (.up ℤ)).obj G
  have hPb : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n) :=
    fun n hn ↦ A.map_isZero (hKb n hn)
  have hPf : ∀ n : ℤ, ∃ m : ℕ,
      ∃ (ι : P.X n ⟶ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin m)) ⟶ P.X n),
        ι ≫ π = 𝟙 (P.X n) := by
    intro n
    obtain ⟨m, j, r, hjr⟩ := hK.2 n
    let ei : A.obj (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m))) ≅
        SheafOfModules.free (R := moduleRings U.toScheme.toRingedSpace)
          (ULift.{u} (Fin m)) :=
      (asIso (sigmaComparison A (fun _ : ULift.{u} (Fin m) ↦
        SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
      Sigma.mapIso (fun _ ↦ U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))
    refine ⟨m, A.map j ≫ ei.hom, ei.inv ≫ A.map r, ?_⟩
    change (A.map j ≫ ei.hom) ≫ ei.inv ≫ A.map r = 𝟙 (A.obj (K.X n))
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, hjr]
    exact A.map_id _
  have hPflat : ∀ n : ℤ, SheafOfModules.IsFlat (P.X n) := by
    intro n
    obtain ⟨m, j, r, hjr⟩ := hPf n
    let := SheafOfModules.symmetricCategory U.toScheme.sheaf
    obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed U.toScheme.sheaf
    let := mp
    let := mc
    have := SheafOfModules.isGrothendieckAbelian (moduleRings U.toScheme.toRingedSpace)
    exact (ObjectProperty.flat_of_retract ⟨j, r, hjr⟩
      (ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _))).2
  have hPKflat := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    U.toScheme.toRingedSpace P ⟨b, fun n hn ↦ hPb n (Or.inr hn)⟩ hPflat
  have hNb : ∀ n : ℤ, n < c ∨ d < n → IsZero (N.X n) :=
    fun n hn ↦ R.map_isZero (hGb n hn)
  have hNc : ∀ n : ℤ, RingedSpace.IsCoherent U.toScheme.toRingedSpace (N.X n) := by
    intro n
    have hc := (coherent_module_local_on_open_cover X (G.X n) PUnit
      (fun _ ↦ ⊤) (by simp)).1 (hGcoherent n) U
    exact (RingedSpace.coherent_kernel_cokernel_sum U.toScheme.toRingedSpace).2.2.2.2
      _ _ ((Modules.overFunctorEquiv U).app (G.X n)).symm hc
  let eP : R.mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P :=
    (Functor.mapDerivedCategoryCompIso S A).symm.app E ≪≫
      A.mapDerivedCategory.mapIso e ≪≫ A.mapDerivedCategoryFactors.app K
  let eN : R.mapDerivedCategory.obj (DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj N := R.mapDerivedCategoryFactors.app G
  obtain ⟨eTensor⟩ := derivedTensor_openRestriction_iso_universes X U
    E (DerivedCategory.Q.obj G)
  obtain ⟨eModel⟩ := kFlat_derivedTensor_comparison_natIso U.toScheme
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hPKflat)
  let cmp : R.mapDerivedCategory.obj (E ⊗ DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N (curriedTensor _)) :=
    eTensor ≪≫ tensorIso eP eN ≪≫ (eModel.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  intro i
  let eH : (Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
          (E ⊗ DerivedCategory.Q.obj G)) ≅
      (CochainComplex.mapBifunctor P N (curriedTensor _)).homology i :=
    ((Modules.overFunctorEquiv U).app _).symm ≪≫
      ((R.mapDerivedCategoryHomologyFunctorIso i).app _) ≪≫
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).mapIso cmp ≪≫
      (DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) i).app _
  have hT := finiteRetract_tensorComplex_coherent_terms P N a b hPb hPf hNc
  have hz : i < a + c ∨ b + d < i →
      IsZero ((CochainComplex.mapBifunctor P N (curriedTensor _)).homology i) := by
    intro hi
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (tensorComplex_isZero_X U.toScheme P N a b c d hPb hNb i hi)
  have hc := coherent_homology_of_coherent_terms U.toScheme
    (CochainComplex.mapBifunctor P N (curriedTensor _)) hT i
  exact ⟨fun hi ↦ (hz hi).of_iso eH,
    (RingedSpace.coherent_kernel_cokernel_sum U.toScheme.toRingedSpace).2.2.2.2
      _ _ eH.symm hc⟩

end AlgebraicGeometry.Scheme
