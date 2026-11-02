import Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionStatement
import Langlands.AlgebraicGeometry.GeometricallyUnibranchEtaleDomain
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Local algebra for the geometrically unibranch etale criterion -/

universe u v w

open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionProof

lemma finite_minimalPrimes_of_flat_quasiFinite
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Module.Flat R A] [Algebra.QuasiFinite R A] :
    (minimalPrimes A).Finite := by
  apply (Algebra.QuasiFinite.finite_primesOver (R := R) (S := A) (⊥ : Ideal R)).subset
  intro J hJ
  let := hJ.isPrime
  obtain ⟨P, hPJ, hP, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R))
      (q := J.under R) J bot_le
  have hJP : J ≤ P := hJ.2 ⟨hP, bot_le⟩ hPJ
  have hEq : P = J := hPJ.antisymm hJP
  subst P
  exact ⟨hJ.isPrime, hPover⟩

lemma isReduced_of_etale_domain
    (R : Type u) (A : Type v) [CommRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] : IsReduced A := by
  have : IsReduced (FractionRing R ⊗[R] A) :=
    Algebra.FormallyUnramified.isReduced_of_field (FractionRing R) _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[R] FractionRing R ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R (FractionRing R)))

lemma exists_domain_away_of_finite_minimalPrimes
    (A : Type v) [CommRing A] [IsReduced A]
    (hfin : (minimalPrimes A).Finite)
    (q : Ideal A) [q.IsPrime] [IsDomain (Localization.AtPrime q)] :
    ∃ g : A, g ∉ q ∧ IsDomain (Localization.Away g) := by
  classical
  let T := {J : Ideal A | J ∈ minimalPrimes A ∧ ¬ J ≤ q}
  have hT : T.Finite := hfin.subset fun _ h => h.1
  let : Fintype T := hT.fintype
  have hw (J : T) : ∃ a : A, a ∈ J.1 ∧ a ∉ q := by
    exact SetLike.not_le_iff_exists.mp J.2.2
  choose a ha hq using hw
  let g : A := ∏ J : T, a J
  have hg : g ∉ q := q.primeCompl.prod_mem fun J _ => hq J
  have hkill (x : A) (hx : algebraMap A (Localization.AtPrime q) x = 0) :
      g * x = 0 := by
    have hmem : g * x ∈ sInf (minimalPrimes A) := by
      apply Ideal.mem_sInf.mpr
      intro J hJ
      by_cases hle : J ≤ q
      · let := hJ.isPrime
        obtain ⟨s, hs⟩ :=
          (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).mp hx
        have hxJ : x ∈ J :=
          (hJ.isPrime.mem_or_mem (show (s : A) * x ∈ J from hs ▸ J.zero_mem)).resolve_left
            (fun hsJ => s.2 (hle hsJ))
        exact J.mul_mem_left g hxJ
      · let j : T := ⟨J, hJ, hle⟩
        obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem a (Finset.mem_univ j)
        have hgJ : g ∈ J := by
          rw [show g = a j * b from hb]
          exact J.mul_mem_right b (ha j)
        exact J.mul_mem_right x hgJ
    rw [Ideal.sInf_minimalPrimes, Ideal.IsRadical.radical (Ideal.isRadical_bot (R := A))] at hmem
    exact hmem
  let f : A →+* Localization.AtPrime q := algebraMap A _
  have hgf : f g ≠ 0 :=
    (IsLocalization.map_units (Localization.AtPrime q) (⟨g, hg⟩ : q.primeCompl)).ne_zero
  let : IsDomain (Localization.Away (f g)) := Localization.Away.isDomain hgf
  refine ⟨g, hg, Function.Injective.isDomain (Localization.awayMap f g) ?_⟩
  apply Localization.awayMap_injective_iff.mpr
  intro x hx
  exact ⟨1, by simpa only [pow_one] using hkill x hx⟩

lemma injective_of_quasiFinite_domain
    (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra R A] [Algebra R B] [Algebra.QuasiFinite R A]
    (φ : A →ₐ[R] B) (hinj : Function.Injective (algebraMap R B)) :
    Function.Injective φ := by
  have hAinj : Function.Injective (algebraMap R A) := by
    intro x y h
    apply hinj
    simpa only [φ.commutes] using congrArg φ h
  have hbot : (⊥ : Ideal A).under R = ⊥ :=
    Ideal.comap_bot_of_injective (algebraMap R A) hAinj
  have : (RingHom.ker φ.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hker : (RingHom.ker φ.toRingHom).under R = ⊥ := by
    ext r
    change φ (algebraMap R A r) = 0 ↔ r = 0
    rw [φ.commutes]
    constructor
    · intro h
      exact hinj (h.trans (map_zero _).symm)
    · rintro rfl
      exact map_zero _
  have heq : (⊥ : Ideal A) = RingHom.ker φ.toRingHom :=
    Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) _ _ bot_le (hbot.trans hker.symm)
  exact (RingHom.injective_iff_ker_eq_bot _).mpr heq.symm

lemma localCriterion_of_etale_domain_localizations
    (H : ∀ (R : Type u) (A : Type u) (Rp : Type w)
      [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
      (p : Ideal A) [p.IsPrime]
      [CommRing Rp] [IsDomain Rp] [IsLocalRing Rp] [Algebra R Rp]
      [IsLocalization.AtPrime Rp (p.under R)],
      GeometricallyUnibranchDomain Rp → IsDomain (Localization.AtPrime p)) :
    UnramifiedGeometricallyUnibranchLocalCriterionStatement.{u, v, w} := by
  intro R S Rp _ _ _ _ _ _ _ q _ _ _ _ _ _ hub hinj
  obtain ⟨f, hf, P, φ, hφ⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) q
  let Sf := Localization.Away f
  let qf : Ideal Sf := q.map (algebraMap S Sf)
  have hd : Disjoint (Submonoid.powers f : Set S) (q : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  have : qf.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) Sf q inferInstance hd
  have hqf : qf.under S = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) Sf inferInstance hd
  let p : Ideal P.Ring := qf.comap φ.toRingHom
  have : p.IsPrime := Ideal.IsPrime.comap φ.toRingHom
  have hp : p.under R = q.under R := by
    calc
      p.under R = qf.under R := by
        ext r
        change φ (algebraMap R P.Ring r) ∈ qf ↔ algebraMap R Sf r ∈ qf
        rw [φ.commutes]
      _ = q.under R := by rw [← Ideal.under_under (A := R) (B := S) qf, hqf]
  have : IsLocalization.AtPrime Rp (p.under R) := by
    change IsLocalization (p.under R).primeCompl Rp
    simpa only [hp] using (inferInstance : IsLocalization (q.under R).primeCompl Rp)
  have : IsDomain (Localization.AtPrime p) := H R P.Ring Rp p hub
  have : IsReduced P.Ring := isReduced_of_etale_domain R P.Ring
  obtain ⟨g, hg, hdomain⟩ :=
    exists_domain_away_of_finite_minimalPrimes P.Ring
      (finite_minimalPrimes_of_flat_quasiFinite R P.Ring) p
  let := hdomain
  have hφg : φ g ∉ qf := hg
  have hf0 : f ≠ 0 := fun h => hf (h.symm ▸ q.zero_mem)
  have : IsDomain Sf := Localization.Away.isDomain hf0
  let T := Localization.Away (φ g)
  have hφg0 : φ g ≠ 0 := fun h => hφg (h.symm ▸ qf.zero_mem)
  have : IsDomain T := Localization.Away.isDomain hφg0
  let ψ : Localization.Away g →ₐ[R] T :=
    IsLocalization.Away.mapₐ (Localization.Away g) T φ g
  have hψsurj : Function.Surjective ψ :=
    IsLocalization.Away.mapₐ_surjective_of_surjective g hφ
  have hinjT : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R Sf T, IsScalarTower.algebraMap_eq R S Sf]
    exact (IsLocalization.injective T
      (powers_le_nonZeroDivisors_of_noZeroDivisors hφg0)).comp
      ((IsLocalization.injective Sf
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)).comp hinj)
  have hψinj : Function.Injective ψ :=
    injective_of_quasiFinite_domain R (Localization.Away g) T ψ hinjT
  have : Algebra.Etale R T := Algebra.Etale.of_equiv (AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  let s := (IsLocalization.Away.sec f (φ g)).1
  have hassoc : Associated (algebraMap S Sf s) (φ g) :=
    IsLocalization.Away.associated_sec_fst f (φ g)
  have hs : s ∉ q := by
    intro hs
    apply hφg
    apply (qf.mem_iff_of_associated hassoc).mp
    change s ∈ qf.under S
    rwa [hqf]
  have : IsLocalization.Away (f * s) T :=
    IsLocalization.Away.mul_of_associated f s (φ g) hassoc
  refine ⟨f * s, (inferInstance : q.IsPrime).mul_notMem hf hs, ?_⟩
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (.powers (f * s)) T (Localization.Away (f * s))).restrictScalars R)

/-- The exact local criterion, with independent universes for the base, the
source algebra, and the chosen model of the base localization. -/
theorem unramifiedGeometricallyUnibranchLocalCriterion :
    UnramifiedGeometricallyUnibranchLocalCriterionStatement.{u, v, w} := by
  apply localCriterion_of_etale_domain_localizations
  intro R A Rp _ _ _ _ _ p _ _ _ _ _ _ hRp
  exact GeometricallyUnibranchEtaleDomain.isDomain_atPrime_of_geometricallyUnibranch
    R A Rp p hRp

end Langlands.AlgebraicGeometry.UnramifiedGeometricallyUnibranchLocalCriterionProof
