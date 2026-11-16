import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCompleteHet

/-! # The closed-fibre charts are infinitesimally étale

For Step 2a of Murre's induction (Bourbaki exp. 294): if `F` is represented over the punctured
spectrum of the complete local noetherian ring `R`, the element `ξ_y ∈ F(Spec B_y)` of a
closed-fibre chart is infinitesimally étale at every non-closed point of `Spec B_y`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

open Charts EtaleLocus

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Etale

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {L : Type u} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] [Algebra R L]
  [Module.Finite R L] [Algebra.Etale R L]
  {B : Type u} [CommRing B] [IsLocalRing B] [Algebra R B] (π : L →ₐ[R] B)
  (hπ : Function.Surjective π) (ξB : F.obj (op (ovR R B)))

include hπ in
/-- A quotient `B` of a local, finite étale `R`-algebra: if `F` is represented over the
punctured spectrum, a pro-representable monomorphism `ξ ∈ F(Spec B)` is infinitesimally étale
at the non-closed points of `Spec B`. -/
theorem infinitesimallyEtaleAt_chart (hF5 : NilpotentInjective F)
    (hF7 : OneDimensionalLifting F) (hmono : IsMonoElement F ξB) (hPR : ProRep F ξB)
    (hX' : UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F))
    (z : (ovR R B).left) (hz : z ≠ closedPoint B) : InfinitesimallyEtaleAt F ξB z := by
  classical
  let w0 : Spec (CommRingCat.of (L ⧸ RingHom.ker π)) := (chartInv π hπ).left z
  have hw0 : primeOf (RingHom.ker π) w0 = z.asIdeal.comap π := by
    ext l
    exact Iff.rfl
  have hπloc : IsLocalHom π.toRingHom := IsLocalHom.of_surjective _ hπ
  have hπm : (maximalIdeal B).comap π.toRingHom = maximalIdeal L :=
    congrArg PrimeSpectrum.asIdeal (IsLocalRing.comap_closedPoint π.toRingHom)
  have hne : primeOf (RingHom.ker π) w0 ≠ maximalIdeal L := by
    rw [hw0]
    intro h
    apply hz
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective π.toRingHom hπ
    exact h.trans hπm.symm
  -- a maximal non-maximal prime above `w0`
  let S : Set (Ideal L) :=
    {Q | Q.IsPrime ∧ primeOf (RingHom.ker π) w0 ≤ Q ∧ Q ≠ maximalIdeal L}
  obtain ⟨Q₀, ⟨hQ₀p, hQ₀le, hQ₀ne⟩, hQ₀max⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian L L) S
      ⟨_, inferInstance, le_rfl, hne⟩
  have hIQ₀ : RingHom.ker π ≤ Q₀ := (le_primeOf w0).trans hQ₀le
  have hwp : (Ideal.map (Ideal.Quotient.mk (RingHom.ker π)) Q₀).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIQ₀)
  let w : Spec (CommRingCat.of (L ⧸ RingHom.ker π)) := ⟨_, hwp⟩
  have hwQ : primeOf (RingHom.ker π) w = Q₀ := Ideal.comap_map_mk hIQ₀
  have hw1 : primeOf (RingHom.ker π) w ≠ maximalIdeal L := hwQ ▸ hQ₀ne
  have hw2 : ∀ Q : Ideal L, Q.IsPrime → primeOf (RingHom.ker π) w < Q → Q = maximalIdeal L := by
    intro Q hQ hlt
    rw [hwQ] at hlt
    by_contra hQne
    exact hQ₀max Q ⟨hQ, hQ₀le.trans hlt.le, hQne⟩ hlt
  have hle : w0.asIdeal ≤ w.asIdeal := by
    intro x hx
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact Ideal.mem_map_of_mem _ (hQ₀le hx)
  -- the level at `w`, from the representation over the punctured spectrum
  have hrange : Set.range (EtaleLocus.levelMap R (algebraMap L (Ow (RingHom.ker π) w))) ⊆
      Set.range (puncturedSpectrum R).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change _ ≠ closedPoint R
    intro h
    have hx := congrArg PrimeSpectrum.asIdeal h
    change Ideal.comap ((algebraMap L (Ow (RingHom.ker π) w)).comp (algebraMap R L))
      x.asIdeal = maximalIdeal R at hx
    have h1 : x.asIdeal.comap (algebraMap L (Ow (RingHom.ker π) w)) ≤ Q₀ := by
      intro l hl
      have hm : algebraMap L (Ow (RingHom.ker π) w) l ∈ maximalIdeal (Ow (RingHom.ker π) w) :=
        le_maximalIdeal x.isPrime.ne_top hl
      rw [← hwQ]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Ow (RingHom.ker π) w)
        (primeOf (RingHom.ker π) w) l).1 hm
    have h2 : Ideal.comap (algebraMap R L) Q₀ = maximalIdeal R := by
      apply le_antisymm (le_maximalIdeal (Ideal.IsPrime.comap _).ne_top)
      rw [← hx, ← Ideal.comap_comap]
      exact Ideal.comap_mono h1
    have h3 : Ideal.IsMaximal Q₀ := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) Q₀
      (by rw [Ideal.under, h2]; exact maximalIdeal.isMaximal R)
    exact hQ₀ne (IsLocalRing.eq_maximalIdeal h3)
  obtain ⟨Lv⟩ := nonempty_level_of_range (F := F) (algebraMap L (Ow (RingHom.ker π) w))
    (puncturedSpectrum R).ι hX' hrange
  -- infinitesimal étaleness at `w`, then at `w0` by generization
  have hw : InfinitesimallyEtaleAt F (F.map (chartHom π hπ).op ξB) w :=
    infinitesimallyEtaleAt_of_killAt_surjective hF5 _ w Lv
      (fun A _ _ _ δ' hδ' ↦ killAt_chart π hπ ξB hF5 hF7 hmono hPR w hw1 hw2 A δ' hδ')
  have hw0' : InfinitesimallyEtaleAt F (F.map (chartHom π hπ).op ξB) w0 :=
    infinitesimallyEtaleAt_of_le_of_level hF5 _ Lv hw hle
  have h := Charts.infinitesimallyEtaleAt_restrict (chartInv π hπ) (y := z) hw0'
  rwa [← map_comp_op_apply, chartInv_chartHom, op_id, F.map_id, types_id_apply] at h

end Etale

section ChartElem

variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
  {Y : ℕ → Scheme.{u}} {q : ∀ k, Y k ⟶ Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1)))}
  (e : ∀ k, (baseChange (maximalIdealPowQuotientMap R k) F).RepresentableBy (Over.mk (q k)))
  [hfu : ∀ k, FormallyUnramified (q k)] [hlft : ∀ k, LocallyOfFiniteType (q k)]

include hfu hlft in
/-- The element `ξ_y` of a closed-fibre chart is infinitesimally étale at every non-closed
point of `Spec B_y`. -/
theorem chartElem_infinitesimallyEtaleAt (hF : MurreConditions F)
    (hX' : UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F)) (y : Y 0)
    (z : (chartU e y).left) (hz : z ≠ closedPoint (ChartRing e y)) :
    InfinitesimallyEtaleAt F (chartElem e hF.2.2.2.2.1 y) z := by
  obtain ⟨-, -, hF1b, -, hF3, -, hF5, hF6, hF7, -⟩ := id hF
  have : IsLocalHom (algebraMap R (ChartRing e y)) := isLocalHom_of_finite _
  obtain ⟨L, _, _, hL, hLfin, hLet, π, hπ⟩ := exists_etaleCover (R := R) (B := ChartRing e y)
  have : IsNoetherianRing L := Algebra.FiniteType.isNoetherianRing R L
  exact infinitesimallyEtaleAt_chart π hπ _ hF5 hF7 (chartElem_isMonoElement e hF3 y hF1b hF6)
    (fun A1 _ _ _ _ _ _ η σ hσ ↦ chart_lift_complete e hF3 y η σ hσ) hX' z hz

end ChartElem

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
