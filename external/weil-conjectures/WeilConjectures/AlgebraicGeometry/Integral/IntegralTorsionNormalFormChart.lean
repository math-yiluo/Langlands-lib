/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import WeilConjectures.Mathlib.Algebra.Module.PID
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstantFreeChart
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionTorTransport
import WeilConjectures.AlgebraicGeometry.Integral.IntegralTorsionTorConstant

/-!
# Torsion normal form on a perfect chart

On a chart where a complete integral complex is the completed realization of a perfect
complex over the valuation ring, its cohomology splits as a finite free sheaf and a
nilpotent-uniformizer torsion sheaf, and the cokernel of the uniformizer on the torsion
part is a quotient of the consecutive-quotient Tor sheaf.

## References

* Bhatt--Scholze, Proposition 6.6.11
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

/-- The cohomology modules of a perfect complex over a Noetherian ring are finite. -/
private theorem perfect_finite_homology {A : Type (u + 1)} [CommRing A]
    [IsNoetherianRing A] (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _
      (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P) (q : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj P) := by
  obtain ⟨C, a, b, -, -, hC, ⟨e⟩⟩ := hP
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} A) q).obj P ≅ C.homology q :=
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).app C
  have := (hC q).2
  have : Module.Finite A (C.cycles q) :=
    Module.Finite.of_injective (C.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite A (C.homology q) :=
    Module.Finite.of_surjective (C.homologyπ q).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv eH.toLinearEquiv.symm

section Helpers

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The lifted valuation ring is a domain. -/
theorem pbcIntegralRing_isDomain : IsDomain (PbcIntegralRing l E) :=
  (ULift.ringEquiv : PbcIntegralRing l E ≃+*
    Padic.coefficientExtensionIntegers l E).toMulEquiv.isDomain _

/-- The lifted valuation ring is a discrete valuation ring with uniformizer
`pbcUniformizer l E`. -/
theorem pbcIntegralRing_isDiscreteValuationRing :
    @IsDiscreteValuationRing (PbcIntegralRing l E) _ (pbcIntegralRing_isDomain l E) ∧
      Irreducible (pbcUniformizer l E) := by
  let := pbcIntegralRing_isDomain l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have : IsDiscreteValuationRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.1
  have hJ : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      (Padic.coefficientExtensionIntegers_dvr l E).choose :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hm : (Padic.coefficientExtensionIntegers_dvr l E).choose =
      IsLocalRing.maximalIdeal (Padic.coefficientExtensionIntegers l E) :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  refine ⟨IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (ULift.ringEquiv.symm : Padic.coefficientExtensionIntegers l E ≃+* PbcIntegralRing l E), ?_⟩
  have hi : Irreducible (Padic.coefficientExtensionUniformizer l E) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (hJ.trans hm).symm
  exact (MulEquiv.irreducible_iff (ULift.ringEquiv.symm :
    Padic.coefficientExtensionIntegers l E ≃+* PbcIntegralRing l E).toMulEquiv).2 hi

variable {l E}

/-- On a perfect chart, the inverse image of the cohomology sheaf is the inverse image of
the realization of the cohomology module. -/
def chartHomologyIso (T : Scheme.{u}) {S : Scheme.{u}} (g : S ⟶ T)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (q : ℤ) (C : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (e : (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj C)) :
    (proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) _
        (Iso.refl _)).obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅
      (proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) _
        (Iso.refl _)).obj ((integralConstantModule T (pbcIntegralDatum l E)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj
            C)) := by
  let : PreservesFiniteLimits (integralConstantModule T (pbcIntegralDatum l E)) :=
    (integralConstantModule_exact T (pbcIntegralDatum l E)).1
  let : PreservesFiniteColimits (integralConstantModule T (pbcIntegralDatum l E)) :=
    (integralConstantModule_exact T (pbcIntegralDatum l E)).2
  let P := proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) _
    (Iso.refl _)
  exact (P.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor _ q).mapIso e ≪≫
    ((P.mapDerivedCategoryHomologyFunctorIso q).app _).symm ≪≫
    P.mapIso (((integralConstantModule T (pbcIntegralDatum l E)
      ).mapDerivedCategoryHomologyFunctorIso q).app C).symm

/-- The inverse image of the realization of a finite free module is a finite free module
sheaf: it has a basis on every object. -/
theorem chart_free_sheaf (T : Scheme.{u}) {S : Scheme.{u}} (g : S ⟶ T) (r : ℕ) :
    ∃ F : pbcModules S ((adicTowerInverseImage g).obj
        (pbcAdicCompletion T (pbcIntegralDatum l E))),
      (∀ U : S.ProEtᵒᵖ, Nonempty (Module.Basis (Fin r)
        (((adicTowerInverseImage g).obj
          (pbcAdicCompletion T (pbcIntegralDatum l E))).obj.obj U) (F.val.obj U))) ∧
      Nonempty ((proEtaleRingModulePullback g (pbcAdicCompletion T (pbcIntegralDatum l E)) _
        (Iso.refl _)).obj ((integralConstantModule T (pbcIntegralDatum l E)).obj
          (ModuleCat.of (PbcIntegralRing l E) (Fin r →₀ PbcIntegralRing l E))) ≅ F) := by
  exact exists_basis_pullback_integralConstantModule_free (pbcIntegralDatum l E) g r

/-- On the base, the consecutive-quotient Tor sheaf of the realization of a perfect complex
surjects, after restriction of scalars, onto the cokernel of the uniformizer on the
realization of the torsion summand of its degree-`q` cohomology. -/
theorem tor_const_epi (T : Scheme.{u}) (q : ℤ)
    (C : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (hC : @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C)
    (r : ℕ) (N₀ : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (ε : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj C ≅
      ModuleCat.of (PbcIntegralRing l E) (Fin r →₀ PbcIntegralRing l E) ⊞ N₀)
    (k : ℕ) (hk : ∀ x : N₀, pbcUniformizer l E ^ k • x = 0) :
    let d := pbcIntegralDatum l E
    ∃ n : ℕ, ∃ t : (pbcRestrict (pbcAdicProjection T d n)).obj
        ((DerivedCategory.homologyFunctor _ (-1)).obj
          ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((pbcCompletedReduction T d (n + 1)).obj
                  ((integralConstantDerived T d).obj C)))))) ⟶
        cokernel ((integralConstantModule T d).map
          (ModuleCat.ofHom (pbcUniformizer l E • LinearMap.id : N₀ →ₗ[_] N₀))),
      Epi t := by
  intro d
  let := pbcIntegralRing_isDomain l E
  obtain ⟨hdvr, hπ⟩ := pbcIntegralRing_isDiscreteValuationRing l E
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hC
  let εP : P.homology q ≅ ModuleCat.of (PbcIntegralRing l E)
      (Fin r →₀ PbcIntegralRing l E) ⊞ N₀ :=
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} (PbcIntegralRing l E))
      q).app P).symm ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso e.symm ≪≫ ε
  have hk' : ∀ x ∈ d.ideal ^ (k + 1 + 1), ∀ y : N₀, x • y = 0 := by
    intro x hx y
    change x ∈ Ideal.span {pbcUniformizer l E} ^ (k + 1 + 1) at hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rw [mul_comm, mul_smul, show k + 1 + 1 = (2 : ℕ) + k by omega, pow_add, mul_smul, hk,
      smul_zero, smul_zero]
  obtain ⟨s, r', hsr⟩ :=
    ModuleCat.exists_homology_reduction_retraction d.ideal (k + 1 + 1) P hP q _ N₀
    εP hk'
  obtain ⟨eH⟩ := nonempty_reduction_homology_iso T d q C P a b ha hb hP e (k + 1)
  obtain ⟨eT⟩ := nonempty_tor_constant_iso T d k (((((ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
    (Ideal.Quotient.mk (d.ideal ^ (k + 1 + 1)))).mapHomologicalComplex (.up ℤ)).obj
      P).homology q))
  have hk1 : ∀ x : N₀, pbcUniformizer l E ^ (k + 1) • x = 0 := by
    intro x
    rw [pow_succ, mul_comm, mul_smul, hk, smul_zero]
  obtain ⟨t, ht⟩ :=
    ModuleCat.exists_levelTor_epi d.ideal k (pbcUniformizer l E) hπ.ne_zero rfl _ N₀ s r'
    hsr hk1
  let φ := ModuleCat.ofHom (pbcUniformizer l E • LinearMap.id : N₀ →ₗ[PbcIntegralRing l E] N₀)
  have hX : ∀ x ∈ d.ideal ^ (k + 1),
      ∀ y : (cokernel φ : ModuleCat.{u + 1} (PbcIntegralRing l E)), x • y = 0 := by
    intro x hx y
    change x ∈ Ideal.span {pbcUniformizer l E} ^ (k + 1) at hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    have hy : pbcUniformizer l E • y = 0 := by
      obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (cokernel.π φ)).1 inferInstance y
      rw [← map_smul]
      change (φ ≫ cokernel.π φ).hom z = 0
      rw [cokernel.condition, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [mul_comm, mul_smul, pow_succ, mul_smul, hy, smul_zero, smul_zero]
  obtain ⟨eR⟩ := nonempty_restrict_level_constant_iso T d k (cokernel φ) hX
  let : PreservesFiniteColimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).2
  refine ⟨k, (pbcRestrict (pbcAdicProjection T d k)).map
    ((DerivedCategory.homologyFunctor _ (-1)).map
      ((pbcDerivedExtend (pbcAdicQuotient T d (k + 1) k (Nat.le_succ k))).map
        ((DerivedCategory.singleFunctor _ 0).map eH.hom)) ≫ eT.hom ≫
      (pbcRestrict (pbcLevelConstantComparison T d k).inv).map
        ((adicLisseConstantModules T _).map t)) ≫ eR.hom ≫
    (PreservesCokernel.iso (integralConstantModule T d) φ).hom, ?_⟩
  have := (constantAdicFinite_constant_exact T (PbcIntegralRing l E ⧸ d.ideal ^ (k + 1))).2
  have e1 : Epi ((pbcRestrict (pbcLevelConstantComparison T d k).inv).map
      ((adicLisseConstantModules T _).map t)) := Functor.map_epi _ _
  exact epi_comp _ _

/-- On a perfect chart, the consecutive-quotient Tor sheaf surjects onto the cokernel of
the uniformizer on the realization of the torsion summand of its cohomology module. -/
theorem chart_tor_epi (T : Scheme.{u}) {S : Scheme.{u}} (g : S ⟶ T)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (q : ℤ) (C : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (hC : @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C)
    (e : (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj C))
    (r : ℕ) (N₀ : ModuleCat.{u + 1} (PbcIntegralRing l E))
    (ε : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj C ≅
      ModuleCat.of (PbcIntegralRing l E) (Fin r →₀ PbcIntegralRing l E) ⊞ N₀)
    (k : ℕ) (hk : ∀ x : N₀, pbcUniformizer l E ^ k • x = 0) :
    let d := pbcIntegralDatum l E
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K))))
    let P := proEtaleRingModulePullback g (pbcAdicCompletion T d) _ (Iso.refl _)
    ∃ n : ℕ, ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicProjection T d n))).obj
        ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
          ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
          (Iso.refl _)).obj (tor n)) ⟶
        cokernel (P.map ((integralConstantModule T d).map
          (ModuleCat.ofHom (pbcUniformizer l E • LinearMap.id : N₀ →ₗ[_] N₀)))),
      Epi t := by
  intro d tor P
  obtain ⟨n, t₀, ht₀⟩ := tor_const_epi T q C hC r N₀ ε k hk
  obtain ⟨eT⟩ := nonempty_pullback_tor_iso d g q n e
  let a := proEtaleRingRestrictionPullbackInv g (pbcAdicCompletion T d)
    ((pbcAdicRings T d).obj (op n)) ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
    (pbcAdicProjection T d n) ((adicTowerInverseImage g).map (pbcAdicProjection T d n))
    (Iso.refl _) (Iso.refl _) (by simp)
  have := proEtaleRingRestrictionPullbackInv_isIso g (pbcAdicCompletion T d)
    ((pbcAdicRings T d).obj (op n)) ((adicTowerInverseImage g).obj (pbcAdicCompletion T d))
    ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
    (pbcAdicProjection T d n) ((adicTowerInverseImage g).map (pbcAdicProjection T d n))
    (Iso.refl _) (Iso.refl _) (by simp)
  let φ := (integralConstantModule T d).map
    (ModuleCat.ofHom (pbcUniformizer l E • LinearMap.id : N₀ →ₗ[_] N₀))
  refine ⟨n, (pbcRestrict _).map eT.hom ≫ inv (a.app _) ≫ P.map t₀ ≫
    (PreservesCokernel.iso P φ).hom, ?_⟩
  infer_instance

end Helpers

/-- The torsion normal form on one perfect chart. -/
theorem torsion_normal_form_chart (T : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {S : Scheme.{u}} (g : S ⟶ T)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E))))
    (q : ℤ)
    (C : completedConstantDerived (ModuleCat.{u + 1} (PbcIntegralRing l E)))
    (hC : @DerivedCategory.IsPerfectRingComplex _ _ (HasDerivedCategory.standard _) C)
    (e : (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj K ≅
      (adicTowerPullback g (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
        ((integralConstantDerived T (pbcIntegralDatum l E)).obj C)) :
    let d := pbcIntegralDatum l E
    let B := pbcAdicCompletion T d
    let tor (n : ℕ) := (DerivedCategory.homologyFunctor _ (-1)).obj
      ((pbcDerivedExtend (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((pbcCompletedReduction T d (n + 1)).obj K))))
    let B' := (adicTowerInverseImage g).obj B
    let P := proEtaleRingModulePullback g B B' (Iso.refl _)
    ∃ (r : ℕ) (F N : pbcModules S B'),
      (∀ U : S.ProEtᵒᵖ, Nonempty (Module.Basis (Fin r) (B'.obj.obj U) (F.val.obj U))) ∧
      Nonempty (P.obj ((DerivedCategory.homologyFunctor _ q).obj K) ≅ F ⊞ N) ∧
      ∃ f : End N, IsNilpotent f ∧ ∃ n : ℕ,
        ∃ t : (pbcRestrict ((adicTowerInverseImage g).map
            (pbcAdicProjection T d n))).obj
          ((proEtaleRingModulePullback g ((pbcAdicRings T d).obj (op n))
            ((adicTowerInverseImage g).obj ((pbcAdicRings T d).obj (op n)))
            (Iso.refl _)).obj (tor n)) ⟶ cokernel f.asHom,
          Epi t := by
  intro d B tor B' P
  let := pbcIntegralRing_isDomain l E
  obtain ⟨hdvr, hπ⟩ := pbcIntegralRing_isDiscreteValuationRing l E
  let : IsNoetherianRing (PbcIntegralRing l E) := d.noetherian
  have : Module.Finite (PbcIntegralRing l E)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj C) :=
    perfect_finite_homology C hC q
  obtain ⟨r, N₀, _, _, k, ⟨ε⟩, hk⟩ :=
    Module.exists_equiv_free_prod_pow_smul_eq_zero hπ
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj C)
  let N₀' := ModuleCat.of (PbcIntegralRing l E) N₀
  let ε' : (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PbcIntegralRing l E)) q).obj C ≅
      ModuleCat.of (PbcIntegralRing l E) (Fin r →₀ PbcIntegralRing l E) ⊞ N₀' :=
    ε.toModuleIso ≪≫ (ModuleCat.biprodIsoProd
      (ModuleCat.of (PbcIntegralRing l E) (Fin r →₀ PbcIntegralRing l E)) N₀').symm
  let G := integralConstantModule T d ⋙ P
  have : PreservesFiniteLimits (integralConstantModule T d) :=
    (integralConstantModule_exact T d).1
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have := preservesBinaryBiproducts_of_preservesBinaryProducts G
  obtain ⟨F, hF, ⟨eF⟩⟩ := chart_free_sheaf (l := l) (E := E) T g r
  let φ : End N₀' := .of (ModuleCat.ofHom (pbcUniformizer l E • LinearMap.id))
  refine ⟨r, F, G.obj N₀', hF, ⟨chartHomologyIso T g K q C e ≪≫ G.mapIso ε' ≪≫
    G.mapBiprod _ _ ≪≫ biprod.mapIso eF (Iso.refl _)⟩, G.mapEnd N₀' φ, ⟨k, ?_⟩, ?_⟩
  · have hpow (m : ℕ) :
        φ ^ m = .of (ModuleCat.ofHom (pbcUniformizer l E ^ m • LinearMap.id)) := by
      induction m with
      | zero =>
        refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
        change x = pbcUniformizer l E ^ 0 • x
        rw [pow_zero, one_smul]
      | succ m ih =>
        rw [pow_succ, ih]
        refine End.ext (ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))
        change pbcUniformizer l E ^ m • (pbcUniformizer l E • x) =
          pbcUniformizer l E ^ (m + 1) • x
        rw [pow_succ, mul_smul]
    have hφ : φ ^ k = 0 := by
      rw [hpow]
      exact End.ext (ModuleCat.hom_ext (LinearMap.ext fun x ↦ hk x))
    change (G.mapEnd N₀') φ ^ k = 0
    rw [← map_pow, hφ]
    exact End.ext (G.map_zero N₀' N₀')
  · exact chart_tor_epi T g K q C hC e r N₀' ε' k hk

end AlgebraicGeometry.Scheme
