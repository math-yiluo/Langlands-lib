import Langlands.CommutativeAlgebra.CoherentFinitePresentation
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RingHom.Etale

/-! # Regularity and local Picard vanishing for smooth valuation algebras -/

universe u

namespace Langlands.CommutativeAlgebra

open CategoryTheory

variable {R S : Type u} [CommRing R] [CommRing S]

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- The existing coherence and finite-dimension predicate is invariant under
an isomorphism of rings in the same universe. -/
theorem finitelyPresentedRegularRing_of_ringEquiv
    (e : R ≃+* S) (hR : FinitelyPresentedRegularRing R) :
    FinitelyPresentedRegularRing S := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have hk : LinearMap.ker (Algebra.linearMap R S) = ⊥ :=
    LinearMap.ker_eq_bot.mpr e.injective
  have : Module.FinitePresentation R S :=
    Module.finitePresentation_of_free_of_surjective (Algebra.linearMap R S)
      e.surjective (by rw [hk]; exact Submodule.fg_bot)
  refine ⟨finiteFreeSubmoduleCoherent_of_module_finitePresentation hR.1 S, ?_⟩
  intro M _ _ _
  let : Module R M := Module.compHom M e.toRingHom
  have : IsScalarTower R S M :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.FinitePresentation R M := Module.FinitePresentation.trans R M S
  obtain ⟨n, hn⟩ := hR.2 M
  let : HasProjectiveDimensionLE (ModuleCat.of R M) n := hn
  let eM : ModuleCat.of R M ≃ₛₗ[RingHomClass.toRingHom e] ModuleCat.of S M :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact ⟨n, ModuleCat.hasProjectiveDimensionLE_of_semiLinearEquiv e eM n⟩

/-- Regularity passes to any actual algebra model of a localization. -/
theorem finitelyPresentedRegularRing_of_isLocalization
    (hR : FinitelyPresentedRegularRing R) (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] :
    FinitelyPresentedRegularRing S :=
  finitelyPresentedRegularRing_of_ringEquiv
    (IsLocalization.algEquiv M (Localization M) S).toRingEquiv
    (finitelyPresentedRegularRing_localization hR M)

variable [Algebra R S]

/-- An actual basic-open neighborhood and compatible polynomial algebra
structure making that neighborhood etale. -/
structure SmoothEtaleNeighborhood (p : Ideal S) where
  element : S
  not_mem : element ∉ p
  variableCount : ℕ
  polynomialAlgebra :
    Algebra (MvPolynomial (Fin variableCount) R) (Localization.Away element)
  compatible : letI := polynomialAlgebra
    IsScalarTower R (MvPolynomial (Fin variableCount) R) (Localization.Away element)
  etale : letI := polynomialAlgebra
    Algebra.Etale (MvPolynomial (Fin variableCount) R) (Localization.Away element)

/-- Choose the etale polynomial factorization supplied by smoothness at a
prime, retaining its actual basic-open element and polynomial action. -/
noncomputable def smoothEtaleNeighborhood [Algebra.FinitePresentation R S]
    (p : Ideal S) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    SmoothEtaleNeighborhood (R := R) p := by
  classical
  exact Classical.choice (show Nonempty (SmoothEtaleNeighborhood (R := R) p) from by
    obtain ⟨f, hf, n, a, ht, he⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
    let := a
    let := he
    exact ⟨⟨f, hf, n, a, ht, inferInstance⟩⟩)

/-- Every chosen etale polynomial neighborhood over a valuation domain
satisfies the existing regularity predicate. -/
theorem SmoothEtaleNeighborhood.regular [IsDomain R] [ValuationRing R]
    {p : Ideal S} (d : SmoothEtaleNeighborhood (R := R) p) :
    FinitelyPresentedRegularRing (Localization.Away d.element) := by
  let := d.polynomialAlgebra
  let := d.compatible
  let := d.etale
  let e := MvPolynomial.renameEquiv R
    (Equiv.ulift : ULift.{u} (Fin d.variableCount) ≃ Fin d.variableCount)
  let φ := (algebraMap (MvPolynomial (Fin d.variableCount) R)
    (Localization.Away d.element)).comp e.toRingHom
  let : Algebra (MvPolynomial (ULift.{u} (Fin d.variableCount)) R)
      (Localization.Away d.element) := φ.toAlgebra
  have : IsScalarTower R (MvPolynomial (ULift.{u} (Fin d.variableCount)) R)
      (Localization.Away d.element) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    symm
    change algebraMap (MvPolynomial (Fin d.variableCount) R) (Localization.Away d.element)
      (e (algebraMap R (MvPolynomial (ULift.{u} (Fin d.variableCount)) R) r)) =
        algebraMap R (Localization.Away d.element) r
    rw [e.commutes]
    exact (IsScalarTower.algebraMap_apply R (MvPolynomial (Fin d.variableCount) R)
      (Localization.Away d.element) r).symm
  have : Algebra.Etale (MvPolynomial (ULift.{u} (Fin d.variableCount)) R)
      (Localization.Away d.element) :=
    RingHom.Etale.stableUnderComposition e.toRingHom _ (.of_bijective e.bijective)
      (RingHom.etale_algebraMap.mpr d.etale)
  exact finitelyPresentedRegularRing_etale_mvPolynomial_of_valuationRing
    (R := R) (σ := ULift.{u} (Fin d.variableCount)) _

/-- The local ring at any smooth point of a finitely presented algebra over
an arbitrary valuation domain is coherent and has finite projective dimension
for every finitely presented module. -/
theorem finitelyPresentedRegularRing_atPrime_of_smoothAt_of_valuationRing
    [IsDomain R] [ValuationRing R] [Algebra.FinitePresentation R S]
    (p : Ideal S) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    FinitelyPresentedRegularRing (Localization.AtPrime p) := by
  let d := smoothEtaleNeighborhood (R := R) p
  let A := Localization.Away d.element
  let q := p.map (algebraMap S A)
  have hd : Disjoint (Submonoid.powers d.element : Set S) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime d.element).mpr d.not_mem
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers d.element) A p inferInstance hd
  have hqp : q.comap (algebraMap S A) = p :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers d.element) A inferInstance hd
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hqp] using
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (Submonoid.powers d.element) (Localization.AtPrime q) q)
  have hq : FinitelyPresentedRegularRing (Localization.AtPrime q) :=
    finitelyPresentedRegularRing_localization d.regular q.primeCompl
  exact finitelyPresentedRegularRing_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv hq

/-- Every localization of the local ring at a smooth point of a finitely
presented valuation algebra has trivial Picard group. -/
theorem subsingleton_pic_localization_atPrime_of_smoothAt_of_valuationRing
    [IsDomain R] [ValuationRing R] [Algebra.FinitePresentation R S]
    (p : Ideal S) [p.IsPrime] [Algebra.IsSmoothAt R p]
    (M : Submonoid (Localization.AtPrime p)) :
    Subsingleton (CommRing.Pic (Localization M)) := by
  have h := finitelyPresentedRegularRing_atPrime_of_smoothAt_of_valuationRing
    (R := R) p
  exact subsingleton_pic_localization_of_finitelyPresented_finite_projectiveDimension h.1 h.2 M

end Langlands.CommutativeAlgebra
