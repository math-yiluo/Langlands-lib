/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant
import WeilConjectures.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison

/-!
# Cokernels of monomorphisms in the normalization comparison

Source: the normalization exact-sequence blueprint, unit
`proposition-proper-base-change-projective-line`. This module isolates the constructibility and
support calculation, after the comparison monomorphism has been constructed from the adjunction unit
and finite/open comparison.
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem constantModSheaf_constructible (Y : Scheme.{u}) (ℓ : ℕ) :
    Scheme.IsConstructibleSheaf (Etale.constantModSheaf Λ Y ℓ) := by
  let : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u, u + 1}
  let M := ModuleCat.of Λ (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))
  let F := Etale.constantModSheaf Λ Y ℓ
  have hconst : F.IsConstant Y.smallEtaleTopology := by
    exact Sheaf.isConstant_of_iso _ (Iso.refl _)
  let : Scheme.IsLocallyConstantSheaf F := by
    have : Scheme.etalePrecoverage.{u}.HasIsos :=
      inferInstanceAs (Scheme.precoverage @Etale).HasIsos
    refine ⟨⟨⟨.singleton (𝟙 Y) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩⟩
    rw [Scheme.isConstant_over_iff_upperStar]
    have := hconst
    exact Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} Λ) (𝟙 Y) F
  let : Scheme.IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F := ⟨fun Ω _ _ s ↦ by
    let Φ := (Scheme.pointSmallEtale s).ulift.{u + 1}
    let e : (Scheme.pointSmallEtale s).sheafFiber.obj F ≅ M :=
      (((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} Λ)).app F).symm ≪≫ Φ.sheafFiberConstantSheafIso M
    exact ((ModuleCat.isFinitelyGenerated_iff M).mpr inferInstance).of_iso e.symm⟩
  let : Scheme.IsFiniteLocallyConstantSheaf F := {}
  refine ⟨Scheme.Stratification.trivial Y, fun i ↦ ?_⟩
  exact Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 Y) F

private theorem open_constantModSheaf_constructible {X U : Scheme.{u}}
    [IsNoetherian X] (j : U ⟶ X) [IsOpenImmersion j] (ℓ : ℕ) :
    Scheme.IsConstructibleSheaf
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)) := by
  let := constantModSheaf_constructible Λ U ℓ
  exact Scheme.IsConstructibleSheaf.openImmersionLowerShriek j
    j.closedComplement j.range_closedComplement _

private theorem finite_open_constantModSheaf_stalk {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (ℓ : ℕ)
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Finite ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))) := by
  classical
  let : LocallySmall.{u + 1} U.Etale := locallySmall_max.{u + 1, u, u + 1}
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range j.base
  · have hrange : Set.range s.base ⊆ Set.range j.base := by
      rintro _ ⟨y, rfl⟩
      simpa only [Subsingleton.elim y (IsLocalRing.closedPoint Ω)] using hs
    let t := IsOpenImmersion.lift j s hrange
    have hts : t ≫ j = s := IsOpenImmersion.lift_fac j s hrange
    let M := ModuleCat.of Λ (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))
    let e : ((Scheme.pointSmallEtale (t ≫ j)).ulift.{u + 1}).sheafFiber.obj
        ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)) ≅ M :=
      (Etale.openImmersionLowerShriekCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ)
        j t).app (Etale.constantModSheaf Λ U ℓ) ≪≫
      ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiberConstantSheafIso M
    rw [← hts]
    exact Finite.of_equiv M e.toLinearEquiv.toEquiv.symm
  · have hz := Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj
      (ModuleCat.{u + 1} Λ) j s hs (Etale.constantModSheaf Λ U ℓ)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

/-- The cokernel of any monomorphism between the two normalization comparison sheaves
is constructible and vanishes on the dense isomorphism locus.

Source: `sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`,
construction of the cokernel and its finite support.
(blueprint: lem-weil-pbc-normalization-mono-cokernel)

Proof: Write R = Λ/ℓΛ. The curve X is Noetherian since it is of finite type over k;
X' is Noetherian since ν is finite. The constant R-sheaves are finite locally constant:
R is cyclic as a Λ-module. Extension by zero along j and j' preserves constructibility,
using the two strata U and its closed complement, respectively U' and its complement.
Finite direct image preserves constructibility on a Noetherian scheme, as follows from
finite base change and the finite geometric-fibre stalk formula. For the passage from
finite set sheaves to module sheaves, all operations factor through the finite ring R:
extension by zero and finite direct image preserve ℓ-annihilation, and a finite set
trivialization can be refined to trivialize the finitely many R-operations. Thus both
source and target of α are constructible. Refine their finite stratifications to a common one;
the cokernel of a morphism of finite locally constant module sheaves on each stratum
is finite locally constant (trivialise the morphism étale-locally and take its module
cokernel). Exact inverse image identifies this with the restriction of cokernel α.
This proves constructibility without imposing Noetherianity on Λ.

Over V, finite base change and ν|V being an isomorphism identify the two sheaves with
the same extension-by-zero constant R-sheaf on U ∩ V. At a geometric point in U ∩ V,
the restricted map α is an injection between two copies of the finite set R, hence
is a bijection. At a point outside U both stalks vanish. Pullback preserves monos,
and geometric stalks detect isomorphisms, so V^*α is an isomorphism. Pullback also
preserves cokernels; consequently V^*(cokernel α) is zero. This argument applies to
any mono α, not just the canonical diagonal. Finiteness of R is essential for this
last argument; no such general claim is made for infinite coefficient sets. -/
theorem normalization_mono_properties {k : Type u} [Field k] [IsAlgClosed k]
    {X X' U U' : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (ν : X' ⟶ X) [IsFinite ν] [Surjective ν] (V : X.Opens) (hV : Dense (V : Set X))
    [IsIso (ν ∣_ V)] (j : U ⟶ X) [IsOpenImmersion j] {j' : U' ⟶ X'}
    [IsOpenImmersion j'] {ν' : U' ⟶ U} (hj : IsPullback j' ν' ν j) (ℓ : ℕ)
    [Fact ℓ.Prime] [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})]
    (α : (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ) ⟶
        (ν)_*[ModuleCat.{u + 1} Λ].obj
          ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ)))
    (hα : Mono α) : Scheme.IsConstructibleSheaf (cokernel α) ∧
      IsZero ((V.ι)^*[ModuleCat.{u + 1} Λ].obj (cokernel α)) := by
  have _ := hV
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  let F := (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)
  let G := (ν)_*[ModuleCat.{u + 1} Λ].obj
    ((j')_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U' ℓ))
  let L := (V.ι)^*[ModuleCat.{u + 1} Λ]
  let : Scheme.IsConstructibleSheaf F := open_constantModSheaf_constructible Λ j ℓ
  let : Scheme.IsConstructibleSheaf G :=
    finite_pushforward_open_constantModSheaf_constructible Λ ν j' ℓ
  let : Mono α := hα
  have hiso : IsIso (L.map α) := by
    apply Scheme.isIso_of_isIso_sheafFiber_map
    intro x
    let : LocallySmall.{u + 1} V.toScheme.Etale := locallySmall_max.{u + 1, u, u + 1}
    let Φ := (V.toScheme.uliftPointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} Λ)
    obtain ⟨eV⟩ := normalization_comparison_on_iso_locus Λ ν V j hj ℓ
    let e := (Φ.mapIso eV).toLinearEquiv.toEquiv
    let s := V.toScheme.algClosurePoint x
    let eF := (Etale.upperStarCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ) V.ι s).app F
    let : Finite ((((Scheme.pointSmallEtale (s ≫ V.ι)).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F) :=
      finite_open_constantModSheaf_stalk Λ j ℓ (s ≫ V.ι)
    let : Finite (Φ.obj (L.obj F)) := Finite.of_equiv _ eF.toLinearEquiv.toEquiv.symm
    let : Mono (L.map α) := inferInstance
    have hinj : Function.Injective (Φ.map (L.map α)) :=
      (ModuleCat.mono_iff_injective _).mp inferInstance
    exact (ConcreteCategory.isIso_iff_bijective (Φ.map (L.map α))).mpr
      ⟨hinj, hinj.surjective_of_finite e⟩
  exact ⟨Scheme.IsConstructibleSheaf.cokernel α,
    (isZero_cokernel_of_epi (L.map α)).of_iso (PreservesCokernel.iso L α)⟩
end AlgebraicGeometry
