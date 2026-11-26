import Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement
import Langlands.Global.Arithmetic.HarrisProposition48IdentityMackey
import Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.AssociatedPresentationSpectrum

/-! # Weak monomial induction in stages for the identity Mackey constituent -/

noncomputable section

universe uF uV uK uE uM uW uW'

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified.WeakInduction

open IsDedekindDomain Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open scoped NumberField

variable {K : Type uK} {E : Type uE} {M : Type uM} [Field K] [Field E] [Field M]
  [NumberField K] [NumberField E] [NumberField M]
  [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]

/-- The finite places of `M` above a finite place `v` of `K`, indexed in stages
through the places of `E` above `v`. -/
def finitePlacesAboveTower (v : FinitePlace K) :
    (Σ w : FinitePlacesAbove E v, FinitePlacesAbove M w.1) ≃ FinitePlacesAbove M v where
  toFun p := ⟨p.2.1, by
    have := p.1.2
    have := p.2.2
    exact Ideal.LiesOver.trans p.2.1.asIdeal p.1.1.asIdeal v.asIdeal⟩
  invFun u := ⟨⟨u.1.under (𝓞 E), by
      have := u.2
      exact Ideal.LiesOver.tower_bot u.1.asIdeal _ v.asIdeal⟩,
    ⟨u.1, liesOver_under u.1⟩⟩
  left_inv p := Sigma.subtype_ext (Subtype.ext (finitePlacesAbove_under p.1.1 p.2)) rfl
  right_inv _ := rfl

omit [NumberField K] in
/-- A property of almost all finite places of `E` holds, for almost all finite
places `v` of `K`, at every place of `E` above `v`. -/
theorem eventually_forall_finitePlacesAbove {P : FinitePlace E → Prop}
    (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : FinitePlace K in Filter.cofinite, ∀ w : FinitePlacesAbove E v, P w.1 := by
  classical
  have hfin := Filter.eventually_cofinite.mp h
  filter_upwards [SpectralSystem.eventually_avoidsAbove (F := K) hfin.toFinset] with v hv w
  have hw := hv w
  rwa [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hw

/-- **Weak induction in stages.** If `s` over `K` is an arithmetic weak induction of
`t` over `E` and `t` is a weak induction of the Hecke character `χ` of `M`, then `s`
is a weak induction of `χ` for the tower `K ⊆ E ⊆ M`. -/
theorem isWeakInductionOf_of_isArithmeticWeakInductionOf {n m : ℕ}
    {s : SpectralSystem (FinitePlace K) n} {t : SpectralSystem (FinitePlace E) m}
    {χ : HeckeCharacter M}
    (hst : s.IsArithmeticWeakInductionOf t) (ht : t.IsWeakInductionOf χ) :
    s.IsWeakInductionOf χ := by
  classical
  refine ⟨?_, ?_⟩
  · rw [hst.1, ht.1, ← Module.finrank_mul_finrank K E M, mul_comm]
  filter_upwards [hst.2, eventually_forall_finitePlacesAbove (K := K) ht.2] with v hv hw
  intro hvs
  obtain ⟨_, htx, hram, heul⟩ := hv
  refine ⟨fun u => ?_, fun ϖ hϖ => ?_⟩
  · let p := (finitePlacesAboveTower (E := E) v).symm u
    obtain ⟨h1, h2⟩ := (hw p.1 (htx p.1)).1 p.2
    have : u.1.asIdeal.LiesOver p.1.1.asIdeal := p.2.2
    refine ⟨?_, h2⟩
    rw [Ideal.ramificationIdx_tower (R := 𝓞 K) p.1.1.asIdeal u.1.asIdeal, hram p.1, one_mul]
    exact h1
  · let ϖw (w : FinitePlacesAbove E v) (u : FinitePlacesAbove M w.1) :
        (FiniteCompletion M u.1)ˣ :=
      ϖ (finitePlacesAboveTower v ⟨w, u⟩)
    have hϖw (w : FinitePlacesAbove E v) : IsUniformizerFamily w.1 (ϖw w) := fun u =>
      hϖ (finitePlacesAboveTower v ⟨w, u⟩)
    rw [heul, SpectralSystem.inducedEulerPolynomial, inducedEulerPolynomial]
    symm
    rw [← Fintype.prod_equiv (finitePlacesAboveTower (E := E) v) _ _ (fun _ => rfl),
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(hw w (htx w)).2 (ϖw w) (hϖw w), inducedEulerPolynomial, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun u _ => ?_
    have : u.1.asIdeal.LiesOver w.1.asIdeal := u.2
    have : u.1.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans u.1.asIdeal w.1.asIdeal v.asIdeal
    change 1 - C ((χ.finiteComponent u.1 (ϖw w u) : ℂˣ) : ℂ) *
        X ^ (u.1.asIdeal.inertiaDeg (𝓞 K)) =
      (1 - C ((χ.finiteComponent u.1 (ϖw w u) : ℂˣ) : ℂ) *
        X ^ (u.1.asIdeal.inertiaDeg (𝓞 E))).comp (X ^ w.1.asIdeal.inertiaDeg (𝓞 K))
    rw [Ideal.inertiaDeg_tower (R := 𝓞 K) w.1.asIdeal u.1.asIdeal]
    simp only [sub_comp, one_comp, mul_comp, C_comp, X_pow_comp, ← pow_mul]

end Langlands.Automorphic.Unramified.WeakInduction

namespace Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

open Langlands.Global Langlands.Unramified

variable {K : Type uK} {E : Type uE} {M : Type uM} [Field K] [Field E] [Field M]
  [NumberField K] [NumberField E] [NumberField M]
  [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient E)]

/-- Two spectral systems attached to one cuspidal class agree in Euler polynomials
at almost all places, whatever presentations and carrier universes witness them. -/
theorem HasSpectralSystem.sameEulerPolynomials {q : ℕ} {d : IsoClass E q}
    {t t' : SpectralSystem (FinitePlace E) (q + 1)}
    (ht : HasSpectralSystem.{uE, uW} d t) (ht' : HasSpectralSystem.{uE, uW'} d t') :
    t.SameEulerPolynomials t' := by
  obtain ⟨T, P, hT, rfl⟩ := ht
  rw [← hT] at ht'
  obtain ⟨P', rfl⟩ := (hasSpectralSystem_iff T t').mp ht'
  exact P.spectralSystem_sameEulerPolynomials P'

/-- **Weak automorphic induction in stages.** For a tower `K ⊆ E ⊆ M`, a weak
induction to `K` of a weak automorphic induction to `E` of a Hecke character `χ`
of `M` is a weak automorphic induction of `χ`. The two spectral systems of the
intermediate class may come from different presentations. -/
theorem IsWeakInductionOf.isWeakAutomorphicInductionOf {r q : ℕ} {c : IsoClass K r}
    {d : IsoClass E q} {χ : HeckeCharacter M}
    (hcd : IsWeakInductionOf.{uK, uE, uV, uW} c d)
    (hd : d.IsWeakAutomorphicInductionOf.{uE, uM, uW'} χ) :
    c.IsWeakAutomorphicInductionOf.{uK, uM, uV} χ := by
  obtain ⟨s, t, hs, ht, hst⟩ := hcd
  obtain ⟨t', ht', htχ⟩ := hd
  have hst' : s.IsArithmeticWeakInductionOf t' :=
    hst.of_sameEulerPolynomials (SpectralSystem.sameEulerPolynomials_refl s)
      (ht.sameEulerPolynomials ht')
  exact ⟨s, hs, Langlands.Automorphic.Unramified.WeakInduction.isWeakInductionOf_of_isArithmeticWeakInductionOf
    hst' htχ⟩

end Langlands.Automorphic.CuspidalOperatorRealization.IsoClass

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- Weak induction in stages for the trivial double coset of a step with `D ⊆ E'`. -/
theorem proposition48PrimeInductionStages :
    Proposition48PrimeInductionStagesStatement.{uF, uV} := by
  intro Q D hD
  let : CompactSpace (AdeleQuotient D) := compactSpace_adeleQuotient D
  intro r m c d hcd hd
  let M := Q.mackeyField D 1
  let : Algebra D M := (IntermediateField.inclusion (show D ≤ M from le_sup_left)).toAlgebra
  have : IsScalarTower Q.E D M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hcM : c.IsWeakAutomorphicInductionOf.{0, 0, uV} (Q.mackeyCharacter D 1) :=
    hcd.isWeakAutomorphicInductionOf hd
  have h := hcM.arithmeticComap (RingEquiv.refl Q.E) (Q.identityMackeyEquiv D hD).toRingEquiv
    (Q.identityMackeyEquiv_algebraMap D hD)
  rwa [CuspidalOperatorRealization.IsoClass.arithmeticComap_refl,
    Q.identityMackeyEquiv_comap D hD] at h

end Langlands.Global.Harris
