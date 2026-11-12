import Langlands.Automorphic.InducedReciprocityBasic
import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.AdelicFunctoriality.UnramifiedUnitNorm
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.LocalFactor.UnramifiedDegree
import Langlands.VirtualRepresentation.ExactInertiaDegree

/-!
# Weak induction association from local class field theory inputs

`WeakInductionAssociationStatement` follows from existence of geometric local Weil
reciprocity, existence of local-to-relative Weil maps, and the local restriction formula
for induced relative Weil representations. At a place `v` where the weak induction
matches, the restriction formula and the L-factor homomorphism on continuous exact
virtual groups compute the Euler polynomial on inertia invariants of `S ∘ ι` as the
induced Euler polynomial. Its degree is `[E' : F]`, so inertia acts trivially.
The internal proposition `WeakInductionAssociationReductionStatement` records this
implication and `weakInductionAssociation_reduction` proves it; the three antecedents
are not proved here.
-/

noncomputable section

set_option autoImplicit false

universe u uV uP uG

open Polynomial

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G] (I : Subgroup G) [I.Normal]

/-- On an unramified representation the Euler polynomial on inertia invariants is the
Euler polynomial on the whole carrier. -/
theorem eulerPolynomial_invariants_of_isUnramified
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsUnramified I) (g : G) :
    LocalFactor.eulerPolynomial ((invariants I A).representation g) =
      LocalFactor.eulerPolynomial (A.representation g) := by
  have htop := (invariantSubspace_eq_top_iff_isUnramified I A).mpr hA
  let e : invariants I A ≃ₗ[ℂ] A := LinearEquiv.ofTop (invariantSubspace A I) htop
  have hconj : e.conj ((invariants I A).representation g) = A.representation g := by
    ext x
    rfl
  rw [← hconj, LocalFactor.eulerPolynomial_conj]

/-- An Euler polynomial on inertia invariants of full degree forces trivial inertia. -/
theorem isUnramified_of_natDegree_eulerPolynomial_invariants
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (g : G)
    (h : (LocalFactor.eulerPolynomial ((invariants I A).representation g)).natDegree =
      A.rank) :
    A.IsUnramified I := by
  rw [LocalFactor.eulerPolynomial_natDegree_representation] at h
  exact (invariants_rank_eq_iff_isUnramified I A).mp h

end Langlands.FiniteRepresentation

namespace Langlands.Weil.Local.InertiaEuler

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance reductionFieldTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- For a geometric reciprocity candidate `e` and an unramified quasi-character `χ`, the
classical Euler polynomial of the Weil character `χ ∘ e` is `1 - χ(ϖ) X`. -/
theorem characterEulerPolynomial_weilCharacter_of_isUnramified
    {e : LocalFactor.RankOne.ReciprocityCandidate F}
    (he : Correspondence.IsGeometricReciprocity F e) {χ : Correspondence.QuasiCharacter F}
    (hχ : F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom) :
    characterEulerPolynomial F (LocalFactor.RankOne.weilCharacter F e χ) =
      1 - C ((χ.toMonoidHom F.canonicalTopologicalData.uniformizerUnit : ℂˣ) : ℂ) * X := by
  have hI : ∀ x ∈ localInertia F, LocalFactor.RankOne.weilCharacter F e χ x = 1 :=
    fun x hx => Correspondence.weilCharacter_eq_one_of_mem_localInertia F he hχ hx
  have hFr := Correspondence.weilCharacter_apply_of_isUnramified F he hχ
    (localGeometricFrobenius F)
  have hdeg : localDegreeInt F (localGeometricFrobenius F) = 1 := by
    rw [localDegreeInt, localGeometricFrobenius_degree]
    rfl
  rw [hdeg, zpow_one] at hFr
  unfold characterEulerPolynomial
  rw [ite_eq_left hI]
  change 1 - C ((Correspondence.weilCharacter F e χ (localGeometricFrobenius F) : ℂˣ) : ℂ) * X
    = _
  rw [hFr]
  rfl

end Langlands.Weil.Local.InertiaEuler

namespace Langlands.Global.CompletionPadic

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero

section Place

variable {K : Type u} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

/-- The normalized discrete valuation of the canonical package at an equal prime is the
valuation of the completion. -/
theorem discreteValuation_padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    (padicFieldAt w h).canonicalTopologicalData.discreteValuation =
      (Valued.v : Valuation (w.adicCompletion K) ℤᵐ⁰) := by
  subst h
  have hv := AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation w
  rw [topologicalData_eq_canonicalTopologicalData] at hv
  exact hv

/-- The uniformizer of the canonical package at an equal prime has completion
valuation `exp (-1)`. -/
theorem valued_uniformizerUnit_padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime w = p) :
    Valued.v (((padicFieldAt w h).canonicalTopologicalData.uniformizerUnit :
        (w.adicCompletion K)ˣ) : w.adicCompletion K) = WithZero.exp (-1) := by
  rw [← discreteValuation_padicFieldAt w h]
  simpa using LocalFactor.PadicAbelian.uniformizerUnit_zpow_value
    (padicFieldAt w h).canonicalTopologicalData 1

/-- The component at `w` of a Hecke character unramified at `w` is an unramified character
of the canonical package. -/
theorem isUnramifiedCharacter_quasicharacterAt {p : ℕ} [Fact p.Prime]
    (h : residuePrime w = p) (χ : HeckeCharacter K) (hχ : χ.IsUnramifiedAt w) :
    (padicFieldAt w h).canonicalTopologicalData.IsUnramifiedCharacter
      (χ.finiteComponent w).toMonoidHom := by
  rw [PadicField.TopologicalData.IsUnramifiedCharacter,
    ← PadicField.TopologicalData.ker_ordUnits]
  intro a ha
  change Multiplicative.ofAdd
    ((padicFieldAt w h).canonicalTopologicalData.ord (a : w.adicCompletion K)) = 1 at ha
  change χ.finiteComponent w a = 1
  rw [ofAdd_eq_one, PadicField.TopologicalData.ord, discreteValuation_padicFieldAt w h,
    neg_eq_zero] at ha
  have hne : Valued.v (a : w.adicCompletion K) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr a.ne_zero
  have hv : Valued.v (a : w.adicCompletion K) = 1 := by
    rw [← WithZero.exp_log hne, ha, WithZero.exp_zero]
  refine hχ a ((Submonoid.mem_units_iff _ a).mpr ⟨?_, ?_⟩)
  · change (a : w.adicCompletion K) ∈ w.adicCompletionIntegers K
    rw [mem_adicCompletionIntegers, hv]
  · change ((a⁻¹ : (w.adicCompletion K)ˣ) : w.adicCompletion K) ∈ w.adicCompletionIntegers K
    rw [mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]

end Place

section Tower

variable {F K : Type u} [Field F] [Field K] [NumberField F] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]

/-- The residue degree of the completion embedding `F_v → K_w` is the inertia degree of
`w` over `v`. -/
theorem extensionResidueDegree_completionPadicAlgHom :
    Weil.Local.extensionResidueDegree (padicField v) (towerPadicField v w)
        (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom v w) =
      w.asIdeal.inertiaDeg (𝓞 F) := by
  have hcard := Weil.Local.extensionResidueCardinality (padicField v) (towerPadicField v w)
    (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom v w)
  rw [residueCardinality_padicFieldAt w (residuePrime_eq v w),
    HeckeEulerProduct.residueCardinality_eq, ← topologicalData_eq_canonicalTopologicalData,
    HeckeEulerProduct.residueCardinality_eq,
    ← Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal] at hcard
  exact (Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm v) hcard).symm

end Tower

end Langlands.Global.CompletionPadic

namespace Langlands.ClassField.Global.RelativeWeilGroup

open NumberField
open scoped NumberField
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.Automorphic Langlands.VirtualRepresentation Langlands.Unramified
open Langlands.Automorphic.Unramified.WeakInduction

/-- `1 - z X` has degree one for `z ≠ 0`. -/
theorem natDegree_one_sub_C_mul_X {z : ℂ} (hz : z ≠ 0) : (1 - C z * X : ℂ[X]).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt] <;> rw [natDegree_C_mul_X z hz]
  simp

section Discrete

attribute [local instance] relativeGaloisTopology

variable {c : FundamentalClass.ClassFamily.{u}}

/-- At a place `u` of `K` above `v` where the Hecke character `ξ` is unramified: along a local
map `φ` whose transfer is inverse geometric reciprocity, the classical Euler polynomial of
`(ξ ∘ τ_K) ∘ φ` is `1 - ξ_u(ϖ_u) X`, for the uniformizer `ϖ_u` of the canonical package. -/
theorem characterEulerPolynomial_reciprocityCharacter_comp
    (hrec : LocalClassField.WeilReciprocityExistenceUniqueness.{u})
    {F K E : Type u} [Field F] [NumberField F] [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra F K] [Algebra K E] [IsGalois K E]
    (ξ : HeckeCharacter K) {v : Langlands.Global.FinitePlace F}
    (u : Langlands.Global.FinitePlace K)
    [u.asIdeal.LiesOver v.asIdeal] (hξ : ξ.IsUnramifiedAt u)
    (φ : Weil.Local.localWeilGroup (towerPadicField v u) →ₜ* RelativeWeilGroup c K E)
    (hφ : ∀ eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v u),
      LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v u)
          (towerPadicField v u).canonicalTopologicalData eu →
        ∀ y, transfer c K E (φ y) =
          (IdeleClassGroup.ofAdicCompletion (𝓞 K) K u
            (LocalFactor.RankOne.reciprocityUnits (towerPadicField v u) eu y))⁻¹) :
    Weil.Local.InertiaEuler.characterEulerPolynomial (towerPadicField v u)
        ((continuousReciprocityCharacter c K E ξ).comp φ) =
      1 - C ((ξ.finiteComponent u
        (towerPadicField v u).canonicalTopologicalData.uniformizerUnit : ℂˣ) : ℂ) * X := by
  obtain ⟨eu, heu, -⟩ := hrec (residuePrime v) (towerPadicField v u)
    (towerPadicField v u).canonicalTopologicalData
  rw [continuousReciprocityCharacter_comp_eq_weilCharacter ξ u (residuePrime_eq v u) eu φ
    (hφ eu heu)]
  have hη := isUnramifiedCharacter_quasicharacterAt u (residuePrime_eq v u) ξ hξ
  rw [← quasicharacterAt_toMonoidHom u (residuePrime_eq v u)] at hη
  rw [Weil.Local.InertiaEuler.characterEulerPolynomial_weilCharacter_of_isUnramified _ heu hη,
    quasicharacterAt_toMonoidHom]
  rfl

variable {F E' L : Type u} [Field F] [NumberField F] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L]
  [IsScalarTower F E' L] [IsGalois F L]

/-- Along a local map `ι` for a place `w` of `L` above `v`, the local restriction formula
gives local maps `ιᵤ` with the transfer property, and the Euler polynomial on inertia
invariants of the local component of `Ind (ξ ∘ τ_{E'})` is the product over the places `u`
of `E'` above `v` of the classical Euler polynomials of `(ξ ∘ τ_{E'}) ∘ ιᵤ`, evaluated at
`X^{f_u}`. -/
theorem exists_eulerPolynomial_localComponent_eq_prod
    (hres : LocalInducedRestrictionStatement.{uV, u})
    (h : FundamentalClass.Restriction c) (ξ : HeckeCharacter E')
    {v : Langlands.Global.FinitePlace F} {w : Langlands.Global.FinitePlace L}
    [w.asIdeal.LiesOver v.asIdeal]
    {e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)}
    {ι : KrullLocalMap c F L v} (hι : IsLocalRelativeWeilMap v w e ι) :
    haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
    ∃ ιu : ∀ u : FinitePlacesAbove E' v,
        Weil.Local.localWeilGroup (towerPadicField v u.1) →ₜ* RelativeWeilGroup c E' L,
      (∀ (u : FinitePlacesAbove E' v)
          (eu : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v u.1)),
        LocalClassField.GeometricWeilReciprocityRelation (towerPadicField v u.1)
            (towerPadicField v u.1).canonicalTopologicalData eu →
          ∀ y, transfer c E' L (ιu u y) =
            (IdeleClassGroup.ofAdicCompletion (𝓞 E') E' u.1
              (LocalFactor.RankOne.reciprocityUnits (towerPadicField v u.1) eu y))⁻¹) ∧
      Weil.Local.InertiaEuler.eulerPolynomial (padicField v)
          (localComponent (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ) ι) =
        ∏ u : FinitePlacesAbove E' v,
          expand ℂ (Weil.Local.extensionResidueDegree (padicField v) (towerPadicField v u.1)
              (completionPadicAlgHom v u.1))
            (Weil.Local.InertiaEuler.characterEulerPolynomial (towerPadicField v u.1)
              ((continuousReciprocityCharacter c E' L ξ).comp (ιu u))) := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  obtain ⟨ιu, htr, hform⟩ := hres c F E' L h v w e ι hι
  refine ⟨ιu, htr, ?_⟩
  have key := congrArg (Weil.Local.InertiaEuler.lFactorHom.{u, max u uV} (padicField v))
    (hform (ExactGrothendieckGroup.characterClass.{u, uV}
      (continuousReciprocityCharacter c E' L ξ)))
  rw [← inducedReciprocityRepresentation_class, map_sum] at key
  simp only [ExactGrothendieckGroup.continuousRestrict_characterClass,
    Weil.Local.InertiaEuler.lFactorHom_continuousInduceAlong_characterClass] at key
  rw [ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation,
    Weil.Local.InertiaEuler.lFactorHom_ofRepresentation, ← ofMul_prod] at key
  have hunit := congrArg Units.val (Additive.ofMul.injective key)
  simp only [Units.coe_prod, Weil.Local.InertiaEuler.coe_lFactorUnit] at hunit
  rw [Finset.prod_inv_distrib, ← map_prod, inv_inj] at hunit
  have hpoly := RatFunc.algebraMap_injective ℂ hunit
  exact hpoly.trans (Finset.prod_congr rfl fun u _ =>
    Weil.Local.InertiaEuler.eulerPolynomial_induceAlong_characterLine _ _ _ _)

end Discrete

variable {c : FundamentalClass.ClassFamily.{u}}
  {F E' L : Type u} [Field F] [NumberField F] [Field E'] [NumberField E']
  [Field L] [NumberField L] [Algebra F E'] [Algebra F L] [Algebra E' L]
  [IsScalarTower F E' L] [IsGalois F L]

/-- At a finite place `v` of `F` where `E' / F` and `ξ` are unramified above `v`, the
representation `Ind (ξ ∘ τ_{E'})` is unramified along every local map and matches every
polynomial equal to the induced Euler polynomial of `ξ` at all uniformizer families. -/
theorem isUnramifiedMatchAt_inducedReciprocityRepresentation
    (hrec : LocalClassField.WeilReciprocityExistenceUniqueness.{u})
    (hmap : LocalRelativeWeilMapExistenceStatement.{u})
    (hres : LocalInducedRestrictionStatement.{uV, u})
    (hc : IsArithmeticClassFamily c) (h : FundamentalClass.Restriction c)
    (ξ : HeckeCharacter E') (v : Langlands.Global.FinitePlace F) (hv : IsUnramifiedAbove ξ v)
    {P : ℂ[X]}
    (hP : ∀ ϖ : ∀ u : FinitePlacesAbove E' v, (FiniteCompletion E' u.1)ˣ,
      IsUniformizerFamily v ϖ → P = inducedEulerPolynomial ξ v ϖ) :
    IsUnramifiedMatchAt (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ) v P := by
  have : IsGalois E' L := IsGalois.tower_top_of_isGalois F E' L
  intro w
  refine ⟨?_, fun e ι hι => ?_⟩
  · obtain ⟨e, he, -⟩ := hrec (residuePrime v) (towerPadicField v w.1)
      (towerPadicField v w.1).canonicalTopologicalData
    obtain ⟨I, hI, hgen, hres', hinf, hloc⟩ := hc
    obtain ⟨ι, hι⟩ := hmap I hI c ⟨hgen, hres', hinf, hloc⟩ F L v w.1 e he
    exact ⟨e, ι, hι⟩
  · obtain ⟨ιu, htr, hform⟩ := exists_eulerPolynomial_localComponent_eq_prod hres h ξ hι
    let ϖ : ∀ u : FinitePlacesAbove E' v, (FiniteCompletion E' u.1)ˣ := fun u =>
      (towerPadicField v u.1).canonicalTopologicalData.uniformizerUnit
    have hϖ : IsUniformizerFamily v ϖ := fun u =>
      valued_uniformizerUnit_padicFieldAt u.1 (residuePrime_eq v u.1)
    let z : FinitePlacesAbove E' v → ℂ := fun u => ((ξ.finiteComponent u.1 (ϖ u) : ℂˣ) : ℂ)
    have hz : ∀ u, z u ≠ 0 := fun u => Units.ne_zero _
    let f : FinitePlacesAbove E' v → ℕ := fun u =>
      Weil.Local.extensionResidueDegree (padicField v) (towerPadicField v u.1)
        (completionPadicAlgHom v u.1)
    have hf : ∀ u, f u = u.1.asIdeal.inertiaDeg (𝓞 F) := fun u =>
      extensionResidueDegree_completionPadicAlgHom v u.1
    have hprod : Weil.Local.InertiaEuler.eulerPolynomial (padicField v)
        (localComponent (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ) ι) =
          ∏ u : FinitePlacesAbove E' v, expand ℂ (f u) (1 - C (z u) * X) := by
      rw [hform]
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [characterEulerPolynomial_reciprocityCharacter_comp hrec ξ u.1 (hv u).2 (ιu u) (htr u)]
    have hind : ∏ u : FinitePlacesAbove E' v, expand ℂ (f u) (1 - C (z u) * X) =
        inducedEulerPolynomial ξ v ϖ := by
      refine Finset.prod_congr rfl fun u _ => ?_
      rw [map_sub, map_one, map_mul, expand_C, expand_X, hf u]
    have hdeg : (∏ u : FinitePlacesAbove E' v, expand ℂ (f u) (1 - C (z u) * X)).natDegree =
        (localComponent (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ) ι).rank := by
      rw [natDegree_prod]
      · change _ = (inducedReciprocityRepresentation.{u, uV} c F E' L h ξ).rank
        rw [inducedReciprocityRepresentation_rank,
          ← finitePlacesAbove_sum_ramification_inertia (L := E') v]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [natDegree_expand, natDegree_one_sub_C_mul_X (hz u), one_mul, hf u, (hv u).1,
          one_mul]
      · intro u _ hzero
        rw [expand_eq_zero (Weil.Local.extensionResidueDegree_pos _ _ _)] at hzero
        have h1 := natDegree_one_sub_C_mul_X (hz u)
        rw [hzero, natDegree_zero] at h1
        exact zero_ne_one h1
    rw [← hprod] at hdeg
    have : (Weil.Local.localInertia (padicField v)).Normal := Weil.Local.localInertia_normal _
    have hunr := FiniteRepresentation.isUnramified_of_natDegree_eulerPolynomial_invariants
      (Weil.Local.localInertia (padicField v)) _
      (Weil.Local.localGeometricFrobenius (padicField v)) hdeg
    refine ⟨hunr, ?_⟩
    rw [localEulerPolynomial, ← FiniteRepresentation.eulerPolynomial_invariants_of_isUnramified
      _ _ hunr]
    change Weil.Local.InertiaEuler.eulerPolynomial (padicField v) _ = P
    rw [hprod, hind, hP ϖ hϖ]

/-- Internal reduction: existence of geometric local Weil reciprocity, existence of
local-to-relative Weil maps for arithmetic class families, and the local restriction
formula for induced relative Weil representations imply
`WeakInductionAssociationStatement`. -/
def WeakInductionAssociationReductionStatement : Prop :=
  LocalClassField.WeilReciprocityExistenceUniqueness.{u} →
    LocalRelativeWeilMapExistenceStatement.{u} →
      LocalInducedRestrictionStatement.{uV, u} →
        WeakInductionAssociationStatement.{u, uV, uP}

/-- `WeakInductionAssociationStatement` from existence of geometric local Weil
reciprocity, existence of local-to-relative Weil maps for arithmetic class families, and
the local restriction formula for induced relative Weil representations. -/
theorem weakInductionAssociation_of_local
    (hrec : LocalClassField.WeilReciprocityExistenceUniqueness.{u})
    (hmap : LocalRelativeWeilMapExistenceStatement.{u})
    (hres : LocalInducedRestrictionStatement.{uV, u}) :
    WeakInductionAssociationStatement.{u, uV, uP} := by
  intro c hc h F E' L _ _ _ _ _ _ _ _ _ _ _ _ r π ξ hπ
  obtain ⟨s, hs, hind⟩ := hπ
  refine ⟨s, hs, inducedReciprocityRepresentation_isContinuous c F E' L h ξ, ?_, ?_⟩
  · rw [inducedReciprocityRepresentation_rank, hind.1]
  · filter_upwards [hind.2, s.exceptional.eventually_cofinite_notMem] with v hv hvs
    obtain ⟨hunr, heuler⟩ := hv hvs
    exact ⟨hvs, isUnramifiedMatchAt_inducedReciprocityRepresentation hrec hmap hres hc h ξ v
      hunr heuler⟩

/-- The internal reduction holds. -/
theorem weakInductionAssociation_reduction :
    WeakInductionAssociationReductionStatement.{u, uV, uP} :=
  fun hrec hmap hres => weakInductionAssociation_of_local hrec hmap hres

end Langlands.ClassField.Global.RelativeWeilGroup
