import Langlands.Automorphic.CuspidalArithmeticSpectralTransportProof
import Langlands.Automorphic.Unramified.CyclicOrbitInductionComparisonStatement
import Langlands.Automorphic.Unramified.IsobaricArithmeticSpectralTransport
import Langlands.Global.AdelicFunctoriality.GaloisPlaceCount
import Langlands.Global.Arithmetic.CyclicNormKernelUnramifiedOrderProof
import Langlands.Representation.Unramified.EigenvaluesPowerRoots

/-! # Restricting an induced spectrum to the full Galois orbit -/

noncomputable section

set_option autoImplicit false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Langlands.Unramified Global Global.AdelicFunctoriality CuspidalOperatorRealization
open Polynomial Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Pointwise Classical

private theorem nsmul_singleton_eq_replicate (k : ℕ) (z : ℂˣ) :
    k • ({z} : Multiset ℂˣ) = Multiset.replicate k z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_nsmul, ih, add_comm, Multiset.singleton_add, Multiset.replicate_succ]

private theorem power_induced_eigenvalues {J : Type*} [Fintype J] {n m : ℕ}
    (a : Eigenvalues n) (b : J → Eigenvalues m) (f : ℕ) (hf : 0 < f)
    (heq : a.eulerPolynomial = ∏ j, (b j).eulerPolynomial.comp (X ^ f)) :
    ((a.power f : Eigenvalues n) : Multiset ℂˣ) = f • ∑ j, (b j : Multiset ℂˣ) := by
  choose z hz using fun j => Eigenvalues.ofTuple_surjective m (b j)
  let c : J × Fin m → ℂˣ := fun ij => z ij.1 ij.2
  have h : a.eulerPolynomial = ∏ ij : J × Fin m, (1 - C (c ij : ℂ) * X ^ f) := by
    rw [heq, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← hz j, Eigenvalues.eulerPolynomial_ofTuple, Polynomial.prod_comp]
    simp [c]
  rw [Eigenvalues.coe_power_eq_sum_replicate a c (fun _ => f) f (fun _ => hf) (fun _ => dvd_refl _) h,
    Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.div_self hf, pow_one, c, ← nsmul_singleton_eq_replicate, ← Finset.smul_sum]
  congr 1
  rw [← hz j, Finset.sum_eq_multiset_sum]
  change (Multiset.map ((fun x : ℂˣ => ({x} : Multiset ℂˣ)) ∘ z j) Finset.univ.val).sum =
    (List.ofFn (z j) : Multiset ℂˣ)
  rw [← Multiset.map_map, Multiset.sum_map_singleton, Fin.univ_val_map]

section Places

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]

omit [NumberField F] [IsGalois F E] in
private theorem galoisPlace_liesOver {v : Global.FinitePlace F} (w : FinitePlacesAbove E v)
    (σ : E ≃ₐ[F] E) : (finitePlaceEquiv σ.toRingEquiv w.1).asIdeal.LiesOver v.asIdeal := by
  exact HeckeCharacter.liesOver_finitePlaceEquiv_algEquiv σ v w.1

/-- The arithmetic pullback of a finite place stays over the same base place. -/
def placeOrbit {v : Global.FinitePlace F} (w : FinitePlacesAbove E v)
    (σ : E ≃ₐ[F] E) : FinitePlacesAbove E v :=
  ⟨finitePlaceEquiv σ.toRingEquiv w.1, galoisPlace_liesOver w σ⟩

omit [NumberField F] [IsGalois F E] in
private theorem placeOrbit_mul {v : Global.FinitePlace F} (w : FinitePlacesAbove E v)
    (σ τ : E ≃ₐ[F] E) : placeOrbit w (σ * τ) = placeOrbit (placeOrbit w σ) τ := by
  apply Subtype.ext
  change finitePlaceEquiv (τ.toRingEquiv.trans σ.toRingEquiv) w.1 =
    finitePlaceEquiv τ.toRingEquiv (finitePlaceEquiv σ.toRingEquiv w.1)
  rw [finitePlaceEquiv_trans]
  rfl

omit [NumberField F] [IsGalois F E] in
private theorem placeOrbit_one {v : Global.FinitePlace F} (w : FinitePlacesAbove E v) :
    placeOrbit w (1 : E ≃ₐ[F] E) = w := by
  apply Subtype.ext
  change finitePlaceEquiv (RingEquiv.refl E) w.1 = w.1
  rw [finitePlaceEquiv_refl]
  rfl

private theorem placeOrbit_surjective {v : Global.FinitePlace F} (w : FinitePlacesAbove E v) :
    Function.Surjective (placeOrbit w) := by
  intro q
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 F) (𝓞 E) (E ≃ₐ[F] E)
    q.1.asIdeal w.1.asIdeal
    ((Ideal.LiesOver.over (P := q.1.asIdeal) (p := v.asIdeal)).symm.trans
      (Ideal.LiesOver.over (P := w.1.asIdeal) (p := v.asIdeal)))
  refine ⟨σ, Subtype.ext (HeightOneSpectrum.ext ?_)⟩
  change (finitePlaceEquiv σ.toRingEquiv w.1).asIdeal = q.1.asIdeal
  rw [finitePlaceEquiv_asIdeal, hσ]
  ext x
  rw [Ideal.mem_comap]
  exact Ideal.smul_mem_pointwise_smul_iff

private theorem inertiaDeg_eq_of_liesOver {v : Global.FinitePlace F} (w q : FinitePlacesAbove E v) :
    q.1.asIdeal.inertiaDeg (𝓞 F) = w.1.asIdeal.inertiaDeg (𝓞 F) := by
  obtain ⟨σ, rfl⟩ := placeOrbit_surjective w q
  exact HeckeCharacter.inertiaDeg_finitePlaceEquiv_algEquiv σ v w.1

private theorem card_orbit_fibre {v : Global.FinitePlace F} (w q : FinitePlacesAbove E v)
    (he : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.ramificationIdx (𝓞 F) = 1) :
    (Finset.univ.filter fun σ => placeOrbit w σ = q).card = w.1.asIdeal.inertiaDeg (𝓞 F) := by
  have hcard (x y : FinitePlacesAbove E v) :
      (Finset.univ.filter fun σ => placeOrbit w σ = x).card =
        (Finset.univ.filter fun σ => placeOrbit w σ = y).card := by
    obtain ⟨g, hg⟩ := placeOrbit_surjective x y
    refine Finset.card_nbij' (fun σ => σ * g) (fun σ => σ * g⁻¹) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [placeOrbit_mul, hσ]
      exact hg
    · intro σ hσ
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ, true_and] at hσ ⊢
      rw [placeOrbit_mul, hσ, ← hg, ← placeOrbit_mul, mul_inv_cancel]
      exact placeOrbit_one x
    · intro σ _
      simp
    · intro σ _
      simp
  have hsum := Finset.card_eq_sum_card_fiberwise (f := placeOrbit w)
    (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hdegree := finitePlacesAbove_sum_ramification_inertia (L := E) v
  simp only [he, one_mul, fun x => inertiaDeg_eq_of_liesOver w x, Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at hdegree
  simp only [Finset.card_univ, ← Nat.card_eq_fintype_card (α := E ≃ₐ[F] E),
    IsGalois.card_aut_eq_finrank F E, fun x => hcard x q, Finset.sum_const, smul_eq_mul] at hsum
  let : Nonempty (FinitePlacesAbove E v) := ⟨w⟩
  exact Nat.eq_of_mul_eq_mul_left Fintype.card_pos (hsum.symm.trans hdegree.symm)

private theorem sum_orbit_spectra {v : Global.FinitePlace F} (w : FinitePlacesAbove E v)
    (he : ∀ x : FinitePlacesAbove E v, x.1.asIdeal.ramificationIdx (𝓞 F) = 1)
    (a : FinitePlacesAbove E v → Multiset ℂˣ) :
    (∑ σ : E ≃ₐ[F] E, a (placeOrbit w σ)) = w.1.asIdeal.inertiaDeg (𝓞 F) • ∑ q, a q := by
  rw [Finset.smul_sum]
  calc
    (∑ σ : E ≃ₐ[F] E, a (placeOrbit w σ)) =
        ∑ q : FinitePlacesAbove E v,
          ∑ σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a (placeOrbit w σ) :=
      (Finset.sum_fiberwise_of_maps_to (g := placeOrbit w)
        (fun _ _ => Finset.mem_univ _) (fun σ => a (placeOrbit w σ))).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [show (∑ σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a (placeOrbit w σ)) =
        ∑ _σ ∈ Finset.univ.filter (fun σ => placeOrbit w σ = q), a q from
          Finset.sum_congr rfl fun σ hσ => congrArg a (Finset.mem_filter.mp hσ).2,
        Finset.sum_const, card_orbit_fibre w q he]

/-- At an unramified base place, the residue-degree power of the induced
spectrum is the sum of the spectra along the full orbit of any upper place. -/
def WeakInductionOrbitRestrictionStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] (v : Global.FinitePlace F) {n m : ℕ}
    (a : Eigenvalues n) (b : FinitePlacesAbove E v → Eigenvalues m),
    (∀ q : FinitePlacesAbove E v, q.1.asIdeal.ramificationIdx (𝓞 F) = 1) →
    a.eulerPolynomial = ∏ q : FinitePlacesAbove E v,
      (b q).eulerPolynomial.comp (X ^ q.1.asIdeal.inertiaDeg (𝓞 F)) →
    ∀ w : FinitePlacesAbove E v,
      ((a.power (w.1.asIdeal.inertiaDeg (𝓞 F)) : Eigenvalues n) : Multiset ℂˣ) =
        ∑ σ : E ≃ₐ[F] E, (b (placeOrbit w σ) : Multiset ℂˣ)

theorem weakInductionOrbitRestriction : WeakInductionOrbitRestrictionStatement.{uF,uE} := by
  intro F E _ _ _ _ _ _ v n m a b he h w
  simp_rw [fun q => inertiaDeg_eq_of_liesOver w q] at h
  exact (power_induced_eigenvalues a b _ (w.1.asIdeal.inertiaDeg_pos (𝓞 F)) h).trans
    (sum_orbit_spectra w he fun q => b q).symm

end Places

private theorem coe_eigenvalues_rank_cast {J : Type*} {n m : ℕ} (h : n = m)
    (t : SpectralSystem J n) (v : J) (hv : v ∉ (h ▸ t : SpectralSystem J m).exceptional)
    (hv' : v ∉ t.exceptional) :
    ((h ▸ t : SpectralSystem J m).eigenvalues v hv : Multiset ℂˣ) =
      (t.eigenvalues v hv' : Multiset ℂˣ) := by
  subst h
  rfl

set_option maxHeartbeats 1200000 in
/-- Attach the multiset calculation to the actual arithmetic pullbacks of an
upper cuspidal presentation. -/
theorem weakInductionOrbitBaseChange : WeakInductionOrbitBaseChangeStatement.{uF,uE,uV,uW} := by
  intro F E _ _ _ _ _ _ _ _ r m c d ⟨s, t, hs, ht, hst⟩
  obtain ⟨T, P, rfl, rfl⟩ := ht
  let cf := PositiveRankCuspidalClass.ofFixedRank c
  let ce := PositiveRankCuspidalClass.ofFixedRank T.isoClass
  let O := IsobaricData.galoisOrbit F ce
  let k := Fintype.card (E ≃ₐ[F] E)
  let e : Fin k ≃ (E ≃ₐ[F] E) := (Fintype.equivFin _).symm
  let σ (i : Fin k) := ce.galoisConj (e i)
  let b (i : Fin k) := (P.arithmeticComap (e i).toRingEquiv.symm).spectralSystem
  let tSum := SpectralSystem.finiteSum b
  have hEnum : Finset.univ.val.map σ = O := by
    change Finset.univ.val.map ((fun g => ce.galoisConj g) ∘ e) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
    rfl
  have hRt : (∑ _ : Fin k, (m + 1)) = O.rank := by
    simp [O, IsobaricData.rank_galoisOrbit, ce, k]
  let tO : SpectralSystem (Global.FinitePlace E) O.rank := hRt ▸ tSum
  have hR : O.rank = (IsobaricData.ofCuspidal cf).rank := by
    rw [IsobaricData.rank_galoisOrbit_of_isGalois, IsobaricData.rank_ofCuspidal]
    change Module.finrank F E * (m + 1) = r + 1
    rw [mul_comm, ← hst.1]
  have htO : O.HasSpectralSystem.{uE,uW} tO := by
    refine ⟨k, σ, hEnum, b, fun i => ⟨_, P.arithmeticComap (e i).toRingEquiv.symm, rfl, rfl⟩, ?_⟩
    exact Filter.Eventually.of_forall fun q hq hq' =>
      (SpectralSystem.eulerPolynomial_eqRec hRt tSum q hq' hq).symm
  have hsf : (IsobaricData.ofCuspidal cf).HasSpectralSystem.{uF,uV} s :=
    IsobaricData.hasSpectralSystem_ofCuspidal_of (c := cf) hs
      (Filter.Eventually.of_forall fun _ _ _ => rfl)
  refine ⟨hR, s, tO, hsf, htO, ?_⟩
  let U : SpectralSystem (Global.FinitePlace E) (IsobaricData.ofCuspidal cf).rank := hR ▸ tO
  change U.IsArithmeticWeakBaseChangeOf s
  filter_upwards [hst.2, SpectralSystem.eventually_avoidsAbove (F := F) U.exceptional] with v hv hU
  obtain ⟨hvS, hvP, he, hp⟩ := hv
  refine ⟨hvS, hU, he, fun w => ?_⟩
  apply Sym.ext
  have hO : w.1 ∉ tO.exceptional := by
    simpa only [U, SpectralSystem.exceptional_eqRec] using hU w
  have hB : w.1 ∉ tSum.exceptional := by
    simpa only [tO, SpectralSystem.exceptional_eqRec] using hO
  rw [coe_eigenvalues_rank_cast hR _ _ _ hO, coe_eigenvalues_rank_cast hRt _ _ _ hB]
  have hnum := weakInductionOrbitRestriction F E v (s.eigenvalues v hvS)
    (fun q : FinitePlacesAbove E v => P.spectralSystem.eigenvalues q.1 (hvP q)) he hp w
  have hB' : w.1 ∉ SpectralSystem.familyExceptional b := hB
  change (∑ i : Fin k, ((b i).eigenvalues w.1 (SpectralSystem.not_mem_exceptional b _ hB' i) :
    Multiset ℂˣ)) = _
  calc
    (∑ i : Fin k, ((b i).eigenvalues w.1 (SpectralSystem.not_mem_exceptional b _ hB' i) : Multiset ℂˣ)) =
        ∑ i : Fin k, (P.spectralSystem.eigenvalues (placeOrbit w (e i)).1 (hvP (placeOrbit w (e i))) :
          Multiset ℂˣ) := by
      exact Finset.sum_congr rfl fun i _ => rfl
    _ = ∑ g : E ≃ₐ[F] E, (P.spectralSystem.eigenvalues (placeOrbit w g).1 (hvP (placeOrbit w g)) :
        Multiset ℂˣ) := e.sum_comp fun g =>
          (P.spectralSystem.eigenvalues (placeOrbit w g).1 (hvP (placeOrbit w g)) : Multiset ℂˣ)
    _ = _ := hnum.symm

end Langlands.Automorphic.Unramified
