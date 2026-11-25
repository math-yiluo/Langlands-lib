/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.AlgebraicGeometry.Curve.DenseIrreducibleOpens
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomologyExtension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.Etale.Gabber
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen
import WeilConjectures.ConstructibleSheaf.Monoidal
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # Finite global sections of a prime-annihilated boundary sheaf

Source: Stacks Project, Tag 0GJA, proof, the finite product of boundary stalks.
-/

@[expose] public section

universe u
open CategoryTheory Limits AlgebraicGeometry.Etale
namespace AlgebraicGeometry.IsCurve

private theorem finite_of_annihilated (Λ : Type (u + 1)) [CommRing Λ]
    (M : Type (u + 1)) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M]
    (ℓ : ℕ) [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] (hM : ∀ x : M, ℓ • x = 0) :
    Finite M := by
  let I := Ideal.span {(ℓ : Λ)}
  have hzero : I • (⊤ : Submodule Λ M) = ⊥ := by
    rw [Submodule.ideal_span_singleton_smul]
    apply le_antisymm _ bot_le
    rintro x ⟨y, _, rfl⟩
    change (ℓ : Λ) • y = 0
    simpa only [Nat.cast_smul_eq_nsmul] using hM y
  have : Finite (M ⧸ I • (⊤ : Submodule Λ M)) :=
    Submodule.finite_quotient_smul I (Module.Finite.fg_top (R := Λ) (M := M))
  exact Finite.of_equiv _ ((I • (⊤ : Submodule Λ M)).quotEquivOfEqBot hzero).toEquiv

/-- A constructible sheaf killed by a prime and supported outside a dense open of a
curve has finite degree-zero cohomology when the coefficient quotient is finite.
Source: Stacks Project, Tag 0GJA, proof, finite product of boundary stalks;
module coefficient adaptation of the finite-stalk argument.
(blueprint: lem-pbc-m1-finite-support-prime-global-sections)

Proof: The complement of the dense open is a finite set of closed points with
residue fields equal to the algebraically closed base field. Give it its reduced
closed subscheme structure i:Z -> X. The zero restriction identifies Q with i_*i^*Q
by the open-closed short exact sequence. Closed direct image preserves global
sections, and the etale site of the finite disjoint union Z of spectra of k has
global sections equal to the finite product of the geometric stalks at its points.
Each stalk is finitely generated as a Lambda-module by constructibility. Since ell
kills the sheaf, it kills every stalk; the scalar action factors through
Lambda/(ell), and the same generators generate over this quotient. This quotient
is a finite ring, so its finitely generated modules are finite sets. The finite
product of these finite stalks is finite. The canonical degree-zero identification
of Sheaf.H with global sections gives the conclusion. Empty curves and empty
complements give the zero group; if the coefficient quotient is the zero ring,
every stalk is zero. Neither reducedness of X nor Noetherianity of Lambda is used. -/
theorem finite_support_prime_global_sections (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f]
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsConstructibleSheaf Q] (ℓ : ℕ) [Fact ℓ.Prime]
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] (hℓ : ℓ • 𝟙 Q = 0)
    (V : X.Opens) (hV : Dense (V : Set X))
    (hQ : IsZero (((V.ι)^*[ModuleCat.{u + 1} Λ]).obj Q)) :
    Finite (Sheaf.H ((sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj Q) 0) := by
  classical
  let I := Scheme.IdealSheafData.vanishingIdeal V.compl
  let Z := I.subscheme
  let i : Z ⟶ X := I.subschemeι
  let G := ((i)^*[ModuleCat.{u + 1} Λ]).obj Q
  let E : ModuleCat.{u + 1} Λ ⥤ AddCommGrpCat.{u + 1} :=
    forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesColimitsOfSize.{u, u} E :=
    ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
  let A := (sheafCompose Z.smallEtaleTopology E).obj G
  have hi : Set.range i.base = (Set.range V.ι.base)ᶜ := by
    rw [Scheme.Opens.range_ι]
    exact V.range_closedComplement
  let S := openClosedShortComplex (ModuleCat.{u + 1} Λ) V.ι i
    (disjoint_range_of_range_eq_compl _ _ hi) Q
  have hS := shortExact_map_forget₂ Λ
    (shortExact_openClosedShortComplex (ModuleCat.{u + 1} Λ) V.ι i Q hi)
  have hz : IsZero (S.map (sheafCompose X.smallEtaleTopology E)).X₁ :=
    (sheafCompose X.smallEtaleTopology E).map_isZero
      ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) V.ι).map_isZero hQ)
  have : IsIso (S.map (sheafCompose X.smallEtaleTopology E)).g :=
    hS.isIso_g_iff.mpr hz
  have hdim : topologicalKrullDim Z ≤ 0 := by
    obtain ⟨n, U, hUV, _, _, _, hUdim, _⟩ := exists_dense_irreducible_opens f V hV
    let b : Z → ↥(⋃ a, (U a : Set X))ᶜ := fun z ↦ ⟨i.base z, by
      have hz : i.base z ∈ (V : Set X)ᶜ := V.range_closedComplement ▸ ⟨z, rfl⟩
      intro hu
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hu
      exact hz (hUV a ha)⟩
    have hb : Topology.IsInducing b :=
      (Topology.IsInducing.of_comp_iff Topology.IsInducing.subtypeVal).mp
        i.isClosedEmbedding.isInducing
    exact hb.topologicalKrullDim_le.trans hUdim
  have hG : Scheme.IsConstructibleSheaf G := Scheme.IsConstructibleSheaf.upperStar i Q
  have : Scheme.IsFiniteSheaf G := hG.isFiniteSheaf
  have hGℓ : ℓ • 𝟙 G = 0 := by
    have hh := congrArg (((i)^*[ModuleCat.{u + 1} Λ]).map) hℓ
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using hh
  have : LocallySmall.{u} Z.Etale := locallySmall_self _
  have : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let s := Z.algClosurePoint
  have hcoh := zero_dimensional_etale_cohomology k Z (i ≫ f) hdim A
    (fun z ↦ AlgebraicClosure (Z.residueField z)) s
    (fun z ↦ Z.algClosurePoint_base z default)
  have : Finite Z := hcoh.1
  let T : Z → AddCommGrpCat.{u + 1} := fun z ↦
    (Scheme.pointSmallEtale (s z)).presheafFiber.obj A.obj
  have hT (z : Z) : Finite (T z) := by
    let P := Scheme.pointSmallEtale (s z)
    let M : ModuleCat.{u + 1} Λ := (P.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G
    have : Module.Finite Λ M := (ModuleCat.isFinitelyGenerated_iff M).mp
      (Scheme.IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := G) _ (s z))
    have hM : ∀ x : M, ℓ • x = 0 := by
      have := P.sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
      have hh := congrArg (P.sheafFiber (A := ModuleCat.{u + 1} Λ)).map hGℓ
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at hh
      intro x
      exact congrArg (fun t ↦ t.hom x) hh
    have : Finite M := finite_of_annihilated Λ M ℓ hM
    let e : T z ≅ E.obj M := (P.sheafFiberCompIso E).app G
    exact Finite.of_injective e.addCommGroupIsoToAddEquiv
      e.addCommGroupIsoToAddEquiv.injective
  have : ∀ z, Finite (T z) := hT
  have : Finite ↑(∏ᶜ T) := Finite.of_injective
    (fun (a : ↑(∏ᶜ T)) (z : Z) ↦ Limits.Pi.π T z a) (by
      intro a b h
      apply Limits.Concrete.isLimit_ext (Discrete.functor T) (Limits.productIsProduct T) a b
      intro z
      exact congrFun h z.as)
  let c :=
    (Functor.homologyRightDerivedFunctorObjSingleFunctorIso
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}) A 0).hom ≫
    (Functor.rightDerivedZeroIsoSelf
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1})).hom.app A ≫
    A.ΓRes (Opposite.op (Scheme.Etale.mk (𝟙 Z))) ≫
    Limits.Pi.lift (fun z : Z ↦ (Scheme.pointSmallEtale (s z)).toPresheafFiber
      (Scheme.Etale.mk (𝟙 Z))
      (Over.homMk (s z) (Category.comp_id (s z))) A.obj)
  have : IsIso c := hcoh.2.2
  have hA0 : Finite (Sheaf.H A 0) := by
    let e := (Scheme.nonempty_sheafH_extDerivedIso Z 0).some.app A
    exact Finite.of_injective (fun a ↦ c (e.hom a))
      ((asIso c).addCommGroupIsoToAddEquiv.injective.comp
        e.addCommGroupIsoToAddEquiv.injective)
  have : Finite (Sheaf.H
      ((𝟭 (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})).obj A) 0) := hA0
  have hB : Finite (Sheaf.H
      ((i)_*[AddCommGrpCat.{u + 1}].obj A) 0) :=
    Finite.of_injective _ (bijective_edgeMap_of_isFinite i A 0).injective
  have : Finite (Sheaf.H (S.map (sheafCompose X.smallEtaleTopology E)).X₃ 0) := hB
  let β := (S.map (sheafCompose X.smallEtaleTopology E)).g
  apply Finite.of_injective (Sheaf.H.map β 0)
  apply Function.LeftInverse.injective (g := Sheaf.H.map (inv β) 0)
  intro x
  rw [← Sheaf.H.map_comp_apply, IsIso.hom_inv_id, Sheaf.H.map_id_apply]

end AlgebraicGeometry.IsCurve
