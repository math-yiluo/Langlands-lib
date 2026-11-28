import Langlands.AlgebraicGeometry.DvrSmoothening.DefectZeroStatement
import Langlands.AlgebraicGeometry.DvrSmoothening.JacobianPoint
import Langlands.AlgebraicGeometry.DvrSmoothening.Points
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk_of_isDiscreteValuationRing

/-! # Points of defect zero lie in the smooth locus -/

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry.DvrSmoothening

/-- A finitely presented algebra over a discrete valuation ring which is smooth at a prime has a
domain as local ring there: the local rings of smooth schemes over a discrete valuation ring are
regular. -/
theorem isDomain_localization_of_isSmoothAt {R C : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (𝔔 : Ideal C) [𝔔.IsPrime] [Algebra.IsSmoothAt R 𝔔] :
    IsDomain (Localization.AtPrime 𝔔) := by
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R 𝔔
  have hsmS : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr (RingHom.smooth_algebraMap.mpr hsm)
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid C) : Set C) (𝔔 : Set C) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hg (Ideal.IsPrime.mem_of_pow_mem ‹_› n hn)
  have hP' : (𝔔.map (algebraMap C (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) _ 𝔔 inferInstance hdisj
  have hcomap : (𝔔.map (algebraMap C (Localization.Away g))).comap
      (algebraMap C (Localization.Away g)) = 𝔔 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g)
      (inferInstance : 𝔔.IsPrime) hdisj
  let x : PrimeSpectrum (Localization.Away g) := ⟨_, hP'⟩
  have := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk_of_isDiscreteValuationRing R
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) x
  have : IsDomain ((Spec (CommRingCat.of (Localization.Away g))).presheaf.stalk x) :=
    IsRegularLocalRing.isDomainFLT _
  let e := (Spec.stalkIso (CommRingCat.of (Localization.Away g)) x).commRingCatIsoToRingEquiv
  have : IsDomain (Localization.AtPrime x.asIdeal) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have hloc : IsLocalization 𝔔.primeCompl (Localization.AtPrime x.asIdeal) := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers g) (Localization.AtPrime x.asIdeal) x.asIdeal
    have hsub : (x.asIdeal.comap (algebraMap C (Localization.Away g))).primeCompl =
        𝔔.primeCompl := by
      ext a
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff]
      exact not_congr (by rw [show x.asIdeal.comap (algebraMap C (Localization.Away g)) = 𝔔
        from hcomap])
    exact hsub ▸ this
  let e₂ := IsLocalization.algEquiv 𝔔.primeCompl (Localization.AtPrime 𝔔)
    (Localization.AtPrime x.asIdeal)
  exact Function.Injective.isDomain e₂.toRingEquiv.toRingHom e₂.injective

/-- The core of BLR 3.3/1: let `P → A` be a surjection from a formally smooth finitely presented
`R`-algebra with finite free differentials, and let `A → R'` be a point with values in a discrete
valuation ring such that `R' ⊗_A Ω_{A/R}` is free and `A` is smooth at the generic point
`ker (A → Frac R')`. Then `A` is smooth over `R` at the special point. -/
theorem isSmoothAt_of_free_tensor {R A P R' : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
    [Algebra P A] [IsScalarTower R P A] [Algebra.FinitePresentation R P]
    [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (hsurj : Function.Surjective (algebraMap P A)) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [Algebra A R'] [Algebra R R'] [IsScalarTower R A R']
    (hgen : ∀ (q : Ideal A) [q.IsPrime],
      (q = RingHom.ker ((algebraMap R' (FractionRing R')).comp (algebraMap A R'))) →
      Algebra.IsSmoothAt R q)
    (hfree : Module.Free R' (R' ⊗[A] Ω[A⁄R])) :
    Algebra.IsSmoothAt R ((IsLocalRing.maximalIdeal R').comap (algebraMap A R')) := by
  classical
  have : Module.Finite R' (R' ⊗[A] Ω[A⁄R]) := by
    have : Algebra.FiniteType R A := Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom R P A) hsurj
    infer_instance
  set p := (IsLocalRing.maximalIdeal R').comap (algebraMap A R') with hpdef
  -- The residue field and the fraction field of `R'`.
  have : IsScalarTower A R' (IsLocalRing.ResidueField R') := inferInstance
  have : IsScalarTower A R' (FractionRing R') := inferInstance
  letI : Algebra P (IsLocalRing.ResidueField R') :=
    ((algebraMap A (IsLocalRing.ResidueField R')).comp (algebraMap P A)).toAlgebra
  have : IsScalarTower P A (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hpL : p = RingHom.ker (algebraMap A (IsLocalRing.ResidueField R')) := by
    ext x
    rw [hpdef, Ideal.mem_comap, RingHom.mem_ker, IsScalarTower.algebraMap_apply A R'
      (IsLocalRing.ResidueField R'), IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff]
  -- Ranks of the differentials of `A` at the two points of `Spec R'`.
  set n := Module.finrank R' (R' ⊗[A] Ω[A⁄R]) with hndef
  have hnL : Module.finrank (IsLocalRing.ResidueField R')
      (IsLocalRing.ResidueField R' ⊗[A] Ω[A⁄R]) = n := by
    rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A R' (IsLocalRing.ResidueField R')
      (IsLocalRing.ResidueField R') Ω[A⁄R]).finrank_eq, Module.finrank_baseChange]
  have hnK : Module.finrank (FractionRing R') (FractionRing R' ⊗[A] Ω[A⁄R]) = n := by
    rw [← (TensorProduct.AlgebraTensorModule.cancelBaseChange A R' (FractionRing R')
      (FractionRing R') Ω[A⁄R]).finrank_eq, Module.finrank_baseChange]
  -- Equations with independent differentials at the special point.
  obtain ⟨c, f, hfA, hli, hNc⟩ :=
    exists_relations_linearIndependent (R := R) (P := P) (A := A)
      (L := IsLocalRing.ResidueField R') hsurj
  -- The quotient `C = P ⧸ (f)`, which maps onto `A`.
  have hJA : Ideal.span (Set.range f) ≤ RingHom.ker (algebraMap P A) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hfA i
  letI : Algebra (P ⧸ Ideal.span (Set.range f)) A :=
    (Ideal.Quotient.lift (Ideal.span (Set.range f)) (algebraMap P A) hJA).toAlgebra
  have : IsScalarTower P (P ⧸ Ideal.span (Set.range f)) A :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := P ⧸ Ideal.span (Set.range f)) (A := A)
      fun x => rfl
  have : IsScalarTower R (P ⧸ Ideal.span (Set.range f)) A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R P (P ⧸ Ideal.span (Set.range f)),
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hsurjC : Function.Surjective (algebraMap (P ⧸ Ideal.span (Set.range f)) A) := by
    intro a
    obtain ⟨x, rfl⟩ := hsurj a
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  have hfgJ : (Ideal.span (Set.range f)).FG :=
    ⟨Finset.univ.image f, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  have : Algebra.FinitePresentation R (P ⧸ Ideal.span (Set.range f)) :=
    Algebra.FinitePresentation.quotient hfgJ
  -- Smoothness of `C` at the special point, by the Jacobian criterion.
  let 𝔓 : Ideal P := p.comap (algebraMap P A)
  have h𝔓 : 𝔓 = RingHom.ker (algebraMap P (IsLocalRing.ResidueField R')) := by
    ext x
    rw [Ideal.mem_comap, hpL, RingHom.mem_ker, RingHom.mem_ker]
    rfl
  have hunit : ∀ y : 𝔓.primeCompl, IsUnit (algebraMap P (IsLocalRing.ResidueField R') y) :=
    fun y => isUnit_iff_ne_zero.mpr fun h => y.2
      ((show ∀ x, x ∈ 𝔓 ↔ algebraMap P (IsLocalRing.ResidueField R') x = 0 from
        fun x => by rw [h𝔓, RingHom.mem_ker]) y |>.mpr h)
  letI : Algebra (Localization.AtPrime 𝔓) (IsLocalRing.ResidueField R') :=
    (IsLocalization.lift hunit).toAlgebra
  have : IsScalarTower P (Localization.AtPrime 𝔓) (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  have hJac := formallySmooth_quotient_of_linearIndependent (R := R)
    (P' := Localization.AtPrime 𝔓) (L := IsLocalRing.ResidueField R') 𝔓 h𝔓 f
    (fun i => by rw [IsScalarTower.algebraMap_apply P A, hfA i, map_zero]) hli
  let 𝔔 : Ideal (P ⧸ Ideal.span (Set.range f)) := p.comap (algebraMap _ A)
  letI : Algebra (P ⧸ Ideal.span (Set.range f))
      (Localization.AtPrime 𝔓 ⧸ (Ideal.span (Set.range f)).map
        (algebraMap P (Localization.AtPrime 𝔓))) :=
    (Ideal.quotientMap _ (algebraMap P (Localization.AtPrime 𝔓)) Ideal.le_comap_map).toAlgebra
  have hloc : IsLocalization (𝔓.primeCompl.map (Ideal.Quotient.mk (Ideal.span (Set.range f))))
      (Localization.AtPrime 𝔓 ⧸ (Ideal.span (Set.range f)).map
        (algebraMap P (Localization.AtPrime 𝔓))) :=
    isLocalization_quotient 𝔓.primeCompl (Ideal.span (Set.range f))
  have hsubm : 𝔓.primeCompl.map (Ideal.Quotient.mk (Ideal.span (Set.range f))) =
      𝔔.primeCompl := by
    have : 𝔓.primeCompl = 𝔔.primeCompl.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) :=
      Submonoid.ext fun x => Iff.rfl
    rw [this]
    exact Submonoid.map_comap_eq_of_surjective Ideal.Quotient.mk_surjective _
  rw [hsubm] at hloc
  have : IsScalarTower R (P ⧸ Ideal.span (Set.range f))
      (Localization.AtPrime 𝔓 ⧸ (Ideal.span (Set.range f)).map
        (algebraMap P (Localization.AtPrime 𝔓))) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R P (P ⧸ Ideal.span (Set.range f))]
      change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime 𝔓) r) =
        Ideal.Quotient.mk _ (algebraMap P (Localization.AtPrime 𝔓) (algebraMap R P r))
      rw [← IsScalarTower.algebraMap_apply]
  have hsm𝔔 : Algebra.IsSmoothAt R 𝔔 :=
    Algebra.FormallySmooth.of_equiv ((IsLocalization.algEquiv 𝔔.primeCompl
      (Localization.AtPrime 𝔔) (Localization.AtPrime 𝔓 ⧸ (Ideal.span (Set.range f)).map
        (algebraMap P (Localization.AtPrime 𝔓)))).restrictScalars R).symm
  have hdom : IsDomain (Localization.AtPrime 𝔔) := isDomain_localization_of_isSmoothAt (R := R) 𝔔
  -- The rank of the differentials of `C` at `𝔔` is at most `n`.
  letI : Algebra (P ⧸ Ideal.span (Set.range f)) (IsLocalRing.ResidueField R') :=
    ((algebraMap A (IsLocalRing.ResidueField R')).comp
      (algebraMap (P ⧸ Ideal.span (Set.range f)) A)).toAlgebra
  have : IsScalarTower (P ⧸ Ideal.span (Set.range f)) A (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower P (P ⧸ Ideal.span (Set.range f)) (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := P ⧸ Ideal.span (Set.range f))
      (A := IsLocalRing.ResidueField R') fun _ => rfl
  have hfC : ∀ i, algebraMap P (P ⧸ Ideal.span (Set.range f)) (f i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hrkC := finrank_add_le_of_linearIndependent (R := R) (P := P)
    (A := P ⧸ Ideal.span (Set.range f)) (L := IsLocalRing.ResidueField R')
    Ideal.Quotient.mk_surjective f hfC hli
  have hrkC' : Module.finrank (IsLocalRing.ResidueField R')
      (IsLocalRing.ResidueField R' ⊗[P ⧸ Ideal.span (Set.range f)]
        Ω[P ⧸ Ideal.span (Set.range f)⁄R]) ≤ n := by
    omega
  have hmem𝔔 : ∀ x, x ∈ 𝔔 ↔
      algebraMap (P ⧸ Ideal.span (Set.range f)) (IsLocalRing.ResidueField R') x = 0 := by
    intro x
    rw [Ideal.mem_comap, hpL, RingHom.mem_ker]
    rfl
  have hunitC : ∀ y : 𝔔.primeCompl,
      IsUnit (algebraMap (P ⧸ Ideal.span (Set.range f)) (IsLocalRing.ResidueField R') y) :=
    fun y => isUnit_iff_ne_zero.mpr fun h => y.2 ((hmem𝔔 y).mpr h)
  letI : Algebra (Localization.AtPrime 𝔔) (IsLocalRing.ResidueField R') :=
    (IsLocalization.lift hunitC).toAlgebra
  have : IsScalarTower (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔)
      (IsLocalRing.ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitC x).symm
  have : Algebra.FormallyEtale (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔) :=
    Algebra.FormallyEtale.of_isLocalization 𝔔.primeCompl
  have : Module.Free (Localization.AtPrime 𝔔) Ω[Localization.AtPrime 𝔔⁄R] :=
    free_kaehler_of_formallySmooth
  have hL𝔔 := finrank_tensor_kaehler_eq (R := R) (C := P ⧸ Ideal.span (Set.range f))
    (S := Localization.AtPrime 𝔔) (F := IsLocalRing.ResidueField R')
  -- The generic point.
  let qK : Ideal A := RingHom.ker (algebraMap A (FractionRing R'))
  have : qK.IsPrime := RingHom.ker_isPrime _
  have hsmqK : Algebra.IsSmoothAt R qK :=
    hgen qK (by rw [← IsScalarTower.algebraMap_eq])
  have hmemqK : ∀ x, x ∈ qK ↔ algebraMap A R' x = 0 := by
    intro x
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A R' (FractionRing R'),
      map_eq_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))]
  have hqKp : qK ≤ p := by
    intro x hx
    rw [hpdef, Ideal.mem_comap, (hmemqK x).mp hx]
    exact zero_mem _
  let 𝔔K : Ideal (P ⧸ Ideal.span (Set.range f)) := qK.comap (algebraMap _ A)
  have h𝔔K : 𝔔K ≤ 𝔔 := fun x hx => hqKp hx
  have hsm𝔔K : Algebra.IsSmoothAt R 𝔔K := isSmoothAt_of_le 𝔔 𝔔K h𝔔K
  letI : Algebra (Localization.AtPrime 𝔔K) (Localization.AtPrime qK) :=
    (Localization.localRingHom 𝔔K qK (algebraMap _ A) rfl).toAlgebra
  have hsurj' : Function.Surjective
      (algebraMap (Localization.AtPrime 𝔔K) (Localization.AtPrime qK)) :=
    RingHom.surjective_localRingHom_of_surjective (algebraMap _ A) hsurjC qK
  have hCA' : ∀ x, algebraMap (Localization.AtPrime 𝔔K) (Localization.AtPrime qK)
      (algebraMap _ (Localization.AtPrime 𝔔K) x) =
      algebraMap A (Localization.AtPrime qK) (algebraMap (P ⧸ Ideal.span (Set.range f)) A x) :=
    fun x => Localization.localRingHom_to_map 𝔔K qK _ rfl x
  have : IsScalarTower R (Localization.AtPrime 𝔔K) (Localization.AtPrime qK) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply R (P ⧸ Ideal.span (Set.range f))
        (Localization.AtPrime 𝔔K), hCA', ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply]
  have hunitA : ∀ y : qK.primeCompl, IsUnit (algebraMap A (FractionRing R') y) :=
    fun y => isUnit_iff_ne_zero.mpr fun h => y.2 (RingHom.mem_ker.mpr h)
  letI : Algebra (Localization.AtPrime qK) (FractionRing R') :=
    (IsLocalization.lift hunitA).toAlgebra
  have : IsScalarTower A (Localization.AtPrime qK) (FractionRing R') :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitA x).symm
  letI : Algebra (Localization.AtPrime 𝔔K) (FractionRing R') :=
    ((algebraMap (Localization.AtPrime qK) (FractionRing R')).comp
      (algebraMap (Localization.AtPrime 𝔔K) (Localization.AtPrime qK))).toAlgebra
  have : IsScalarTower (Localization.AtPrime 𝔔K) (Localization.AtPrime qK) (FractionRing R') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hK' : IsLocalRing.maximalIdeal (Localization.AtPrime qK) ≤
      RingHom.ker (algebraMap (Localization.AtPrime qK) (FractionRing R')) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal qK (Localization.AtPrime qK),
      Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply]
    exact hx
  -- Ranks at the generic point.
  letI : Algebra (P ⧸ Ideal.span (Set.range f)) (FractionRing R') :=
    ((algebraMap A (FractionRing R')).comp (algebraMap (P ⧸ Ideal.span (Set.range f)) A)).toAlgebra
  have : IsScalarTower (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔K)
      (FractionRing R') :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change _ = algebraMap (Localization.AtPrime qK) (FractionRing R')
        (algebraMap (Localization.AtPrime 𝔔K) (Localization.AtPrime qK)
          (algebraMap _ (Localization.AtPrime 𝔔K) x))
      rw [hCA', ← IsScalarTower.algebraMap_apply]
      rfl
  have : Algebra.FormallyEtale (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔K) :=
    Algebra.FormallyEtale.of_isLocalization 𝔔K.primeCompl
  have : Algebra.FormallySmooth R (Localization.AtPrime 𝔔K) := hsm𝔔K
  have : Algebra.FormallySmooth R (Localization.AtPrime qK) := hsmqK
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom R P A) hsurj
  have : Module.Free (Localization.AtPrime 𝔔K) Ω[Localization.AtPrime 𝔔K⁄R] :=
    free_kaehler_of_formallySmooth
  have : Module.Free (Localization.AtPrime qK) Ω[Localization.AtPrime qK⁄R] :=
    free_kaehler_of_formallySmooth
  have : Algebra.FormallyEtale A (Localization.AtPrime qK) :=
    Algebra.FormallyEtale.of_isLocalization qK.primeCompl
  have hunitK : ∀ y : 𝔔.primeCompl,
      IsUnit (algebraMap (P ⧸ Ideal.span (Set.range f)) (FractionRing R') y) :=
    fun y => isUnit_iff_ne_zero.mpr fun h => y.2 (h𝔔K (RingHom.mem_ker.mpr h))
  letI : Algebra (Localization.AtPrime 𝔔) (FractionRing R') :=
    (IsLocalization.lift hunitK).toAlgebra
  have : IsScalarTower (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔)
      (FractionRing R') :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunitK x).symm
  have e1 : Module.finrank (FractionRing R')
      (FractionRing R' ⊗[Localization.AtPrime 𝔔K] Ω[Localization.AtPrime 𝔔K⁄R]) =
      Module.finrank (Localization.AtPrime 𝔔K) Ω[Localization.AtPrime 𝔔K⁄R] :=
    Module.finrank_baseChange
  have e2 := finrank_tensor_kaehler_eq (R := R) (C := P ⧸ Ideal.span (Set.range f))
    (S := Localization.AtPrime 𝔔K) (F := FractionRing R')
  have e3 := finrank_tensor_kaehler_eq (R := R) (C := P ⧸ Ideal.span (Set.range f))
    (S := Localization.AtPrime 𝔔) (F := FractionRing R')
  have e4 : Module.finrank (FractionRing R')
      (FractionRing R' ⊗[Localization.AtPrime qK] Ω[Localization.AtPrime qK⁄R]) =
      Module.finrank (Localization.AtPrime qK) Ω[Localization.AtPrime qK⁄R] :=
    Module.finrank_baseChange
  have e5 := finrank_tensor_kaehler_eq (R := R) (C := A) (S := Localization.AtPrime qK)
    (F := FractionRing R')
  have hdim : Module.finrank (FractionRing R')
      (FractionRing R' ⊗[Localization.AtPrime 𝔔K] Ω[Localization.AtPrime 𝔔K⁄R]) ≤
      Module.finrank (FractionRing R')
        (FractionRing R' ⊗[Localization.AtPrime qK] Ω[Localization.AtPrime qK⁄R]) := by
    omega
  have : IsNoetherianRing R := inferInstance
  have : Algebra.FiniteType R P := inferInstance
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing R P
  have : IsNoetherianRing (Localization.AtPrime 𝔔K) :=
    IsLocalization.isNoetherianRing 𝔔K.primeCompl _ inferInstance
  have hkerCA := ker_eq_bot_of_finrank_le (R := R) (C := Localization.AtPrime 𝔔K)
    (A := Localization.AtPrime qK) (K := FractionRing R') hsurj' hK' hdim
  -- The local ring of `C` at `𝔔` maps isomorphically onto that of `A` at `p`.
  let φC := Localization.localRingHom 𝔔 p (algebraMap (P ⧸ Ideal.span (Set.range f)) A) rfl
  have hsurjφ : Function.Surjective φC :=
    RingHom.surjective_localRingHom_of_surjective _ hsurjC p
  have hinjφ : Function.Injective φC := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔔.primeCompl x
    simp only [φC, Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨v, hv⟩, hva⟩ := hx
    have h1 : algebraMap A (Localization.AtPrime qK)
        (algebraMap (P ⧸ Ideal.span (Set.range f)) A a) = 0 := by
      rw [IsLocalization.map_eq_zero_iff qK.primeCompl]
      exact ⟨⟨v, fun h => hv (hqKp h)⟩, hva⟩
    have h3 : algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔K) a = 0 := by
      have : algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔K) a ∈
          RingHom.ker (algebraMap (Localization.AtPrime 𝔔K) (Localization.AtPrime qK)) := by
        rw [RingHom.mem_ker, hCA']
        exact h1
      rw [hkerCA] at this
      exact this
    rw [IsLocalization.map_eq_zero_iff 𝔔K.primeCompl] at h3
    obtain ⟨⟨t, ht⟩, hta⟩ := h3
    have ht0 : algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔) t ≠ 0 := by
      intro h
      rw [IsLocalization.map_eq_zero_iff 𝔔.primeCompl] at h
      obtain ⟨⟨w, hw⟩, hwt⟩ := h
      have : w * t ∈ 𝔔K := by rw [hwt]; exact zero_mem _
      rcases Ideal.IsPrime.mem_or_mem inferInstance this with h' | h'
      · exact hw (h𝔔K h')
      · exact ht h'
    have ha0 : algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔) a = 0 := by
      have : algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔) t *
          algebraMap (P ⧸ Ideal.span (Set.range f)) (Localization.AtPrime 𝔔) a = 0 := by
        rw [← map_mul, hta, map_zero]
      exact (mul_eq_zero.mp this).resolve_left ht0
    rw [IsLocalization.map_eq_zero_iff 𝔔.primeCompl] at ha0
    exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ha0
  let e : Localization.AtPrime 𝔔 ≃ₐ[R] Localization.AtPrime p :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective φC ⟨hinjφ, hsurjφ⟩) fun r => by
      change φC (algebraMap R (Localization.AtPrime 𝔔) r) = _
      rw [IsScalarTower.algebraMap_apply R (P ⧸ Ideal.span (Set.range f))
        (Localization.AtPrime 𝔔), Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have : Algebra.FormallySmooth R (Localization.AtPrime 𝔔) := hsm𝔔
  exact Algebra.FormallySmooth.of_equiv e

/-- Points of defect zero lie in the smooth locus: BLR §3.3, Lemma 1, in the form of §3.6 for
points with values in discrete valuation rings of ramification index one. -/
theorem defectZeroSmoothAtStatement : DefectZeroSmoothAtStatement.{u} := by
  intro R A R' _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ hram hsm φ hφ
  letI : Algebra A R' := φ.toRingHom.toAlgebra
  have : IsScalarTower R A R' := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  obtain ⟨N, f₀, hf₀⟩ :=
    Algebra.FiniteType.iff_quotient_mvPolynomial''.mp (inferInstance : Algebra.FiniteType R A)
  letI : Algebra (MvPolynomial (Fin N) R) A := f₀.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin N) R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (f₀.commutes r).symm
  have hfree : Module.Free R' (R' ⊗[A] Ω[A⁄R]) := (torsionLength_eq_zero_iff_free).mp hφ
  have : Algebra.FinitePresentation R A := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hgen : ∀ (q : Ideal A) [q.IsPrime],
      q = RingHom.ker ((algebraMap R' (FractionRing R')).comp (algebraMap A R')) →
      Algebra.IsSmoothAt R q := by
    intro q _ hq
    have hϖq : algebraMap R A ϖ ∉ q := by
      rw [hq, RingHom.mem_ker, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R A R',
        map_eq_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))]
      exact (map_ne_zero_iff _ (algebraMap_injective_of_ram hram)).mpr hϖ.ne_zero
    exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hsm)
      (show (⟨q, ‹_›⟩ : PrimeSpectrum A) ∈ PrimeSpectrum.basicOpen (algebraMap R A ϖ) from hϖq)
  exact isSmoothAt_of_free_tensor (P := MvPolynomial (Fin N) R) hf₀ hgen hfree

end Langlands.AlgebraicGeometry.DvrSmoothening
