import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedOrbitFourierPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesOrbitFiniteness
import Langlands.Representation.Aubert.General.InductionCompactVisibility
import Langlands.Representation.Plancherel.NormalizedCompactPicture
import Langlands.Representation.Category.ClassInvariants

/-! # `Θ^H` for one parabolic subgroup and the support of `ψ_f` (Waldspurger, Remark VIII.1.3)

Waldspurger VIII.1 (printed p. 321): for `(O, P) ∈ Θ` and a compact open subgroup `H` of `G`,
`(O, P) ∈ Θ^H` if `I_P^G E` has a nonzero `H`-fixed vector for one (or every) `(ω, E) ∈ O`.
Remark VIII.1.3 states that `Θ^H` is finite if Theorem VIII.1.2 holds for the Levi subgroups, and
that `ψ_f[O, P] ≠ 0` only if `(O, P) ∈ Θ^H` when `f` is bi-invariant under `H`.

For one parabolic `P = M U` this module proves:

* `coefficientFourierTransform_eq_zero_of_fixedVectors_eq_bot`,
  `inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot`: if `f` is right invariant under `H`
  and `I_P^G ω` has no nonzero `H`-fixed vector, then `f̂(ω, P) = 0`;
* `HasInducedFixedVector`: the condition "`I_P^G E` has a nonzero `H`-fixed vector" on classes of
  irreducible representations of `M`, and its independence of the unramified twist
  (`hasInducedFixedVector_twist_iff`, for `H ⊆ K` with `G = P K`);
* `inducedDiscreteSeriesFixedOrbits`: the orbits `O` with `(O, P) ∈ Θ^H`, with the membership
  criterion `mk_mem_inducedDiscreteSeriesFixedOrbits_iff` (one member suffices, every member
  satisfies the condition), and its finiteness `finite_inducedDiscreteSeriesFixedOrbits` from the
  finiteness of the sets `Θ^L_M` of `M` (Theorem VIII.1.2 for `M`);
* on actual rational points, for a standard parabolic `P_I(F)`: vanishing of `f̂(ω, P)` and of
  `ψ_f[O, P]`, the membership `(O, P) ∈ Θ^H` when `ψ_f[O, P] ≠ 0`, the finiteness of `Θ^H`
  for `P_I(F)`, and the finiteness of the orbits with `ψ_f[O, P_I] ≠ 0`
  (`exists_finite_rationalFourierOrbitSection_ne_zero`), given Theorem VIII.1.2 for `M_I(F)`.
-/

noncomputable section

universe u uG uV uI

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section Vanishing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G]
  [Nonempty (CompactOpenSubgroup G)]
  {mu : Measure G} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, uG, uV} ℂ G) (hw : L2Weights mu Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- If `f` is right invariant under `H` and `A` has no nonzero `H`-fixed vector, then
`f̂ = d π(f̌) = 0`: by Lemma VII.1.1 (i), `π(h) T = T` for the endomorphism `T` of `f̂` and
`h ∈ H`, so `T` takes values in the `H`-fixed vectors. -/
theorem coefficientFourierTransform_eq_zero_of_fixedVectors_eq_bot
    (ht : TranslationWeights Ξ σ) (d : ℝ) {H : Subgroup G}
    (hH : fixedVectors A.representation H = ⊥) (f : Space Ξ σ)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    coefficientFourierTransform A hw hA hT hΞ hσ d f = 0 := by
  apply coefficientTensorToEnd_injective A
  rw [map_zero]
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.zero_apply]
  have hmem : coefficientTensorToEnd A (coefficientFourierTransform A hw hA hT hΞ hσ d f) w ∈
      fixedVectors A.representation H := by
    change ∀ k : H, A.representation (k : G) _ = _
    intro k
    have hk : Space.translate ht (k : G) 1 f = f :=
      Space.ext fun x => by
        rw [Space.translate_apply, inv_one, one_mul]
        exact hf k k.2 x
    have h1 := coefficientFourierTransform_translate A hw hA hT hΞ hσ ht d (k : G) 1 f
    rw [hk] at h1
    have h2 := congrArg (fun s => coefficientTensorToEnd A s w) h1
    rw [coefficientTensorToEnd_action, inv_one, map_one, mul_one, Module.End.mul_apply] at h2
    exact h2.symm
  rw [hH] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

end Vanishing

section Induced

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hi : A.representation.IsIrreducible)
  {mu : Measure G} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights mu Ξ σ)
  (hT : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **`f̂(ω, P) = 0` when `I_P^G ω` has no nonzero `H`-fixed vector** and `f` is right invariant
under `H` (Waldspurger, Remark VIII.1.3: "il est clair que `ψ_f[O, P] ≠ 0` seulement si
`(O, P) ∈ Θ^H`"). -/
theorem inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot (ht : TranslationWeights Ξ σ)
    {H : Subgroup G}
    (hH : fixedVectors ((normalizedInductionFunctor h hU).obj A).representation H = ⊥)
    (f : Space Ξ σ) (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f = 0 := by
  have h0 := coefficientFourierTransform_eq_zero_of_fixedVectors_eq_bot
    ((normalizedInductionFunctor h hU).obj A) hw
    (CompactInduction.induced_isAdmissible h hU K hK hPK A hm hsq.1) hT hΞ hσ ht
    (representationFormalDegree C hC μM hcof hsq hi) hH f hf
  rw [inducedFourierTransform, LinearMap.comp_apply]
  erw [h0]
  exact map_zero _

end Induced

section Classes

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))

/-- **The condition defining `Θ^H`** (Waldspurger VIII.1, printed p. 321) on a class `ω` of
irreducible admissible representations of `M`: `I_P^G E` has a nonzero vector fixed by `H`, for
a representative `(ω, E)`. It does not depend on the representative, since normalized induction
carries equivalences to equivalences. -/
def HasInducedFixedVector (H : Subgroup G) :
    SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M) → Prop :=
  Quotient.lift
    (fun A => fixedVectors ((normalizedInductionFunctor h hU).obj A.obj).representation H ≠ ⊥)
    (by
      rintro A B ⟨e⟩
      apply propext
      exact fixedVectors_ne_bot_iff_of_equiv
        (SmoothRep.equivOfIso ((normalizedInductionFunctor h hU).mapIso
          ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso e))) H)

@[simp]
theorem hasInducedFixedVector_mk (H : Subgroup G)
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M)) :
    HasInducedFixedVector.{uG, uV} h hU H (Quotient.mk _ A) ↔
      fixedVectors ((normalizedInductionFunctor h hU).obj A.obj).representation H ≠ ⊥ :=
  Iff.rfl

end Classes

section Restriction

variable {G : Type uG} [Group G] {V : Type*} {W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

/-- For `H ⊆ K`, the `H`-fixed vectors of `ρ` are those of its restriction to `K`. -/
theorem fixedVectors_eq_comap_subtype (ρ : Representation ℂ G V) {K H : Subgroup G}
    (hHK : H ≤ K) :
    fixedVectors ρ H = fixedVectors (ρ.comp K.subtype) (H.comap K.subtype) := by
  ext v
  simp only [fixedVectors, Representation.mem_invariants]
  constructor
  · intro hv k
    exact hv ⟨(k.1 : G), k.2⟩
  · intro hv k
    exact hv ⟨⟨(k : G), hHK k.2⟩, k.2⟩

/-- Two representations of `G` whose restrictions to `K` are equivalent have nonzero
`H`-fixed vectors simultaneously, for `H ⊆ K`. -/
theorem fixedVectors_ne_bot_iff_of_equiv_restrict {ρ : Representation ℂ G V}
    {τ : Representation ℂ G W} {K H : Subgroup G}
    (e : Representation.Equiv (ρ.comp K.subtype) (τ.comp K.subtype)) (hHK : H ≤ K) :
    fixedVectors ρ H ≠ ⊥ ↔ fixedVectors τ H ≠ ⊥ := by
  rw [fixedVectors_eq_comap_subtype ρ hHK, fixedVectors_eq_comap_subtype τ hHK]
  exact fixedVectors_ne_bot_iff_of_equiv e _

end Restriction

section Twist

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)

include hP hK hPK hν hr in
/-- **Independence of the twist** (Waldspurger VIII.1, printed p. 321: "la propriété ne dépend pas
du choix de `(ω, E) ∈ O`"): for `H ⊆ K` with `G = P K` and an unramified character `χ` of `M`,
`I_P^G(A ⊗ χ)` has a nonzero `H`-fixed vector if and only if `I_P^G A` does. Both restrict to
`K` as the same compact picture (`unramifiedNormalizedInductionCompactEquiv`). -/
theorem fixedVectors_normalizedInduction_twist_ne_bot_iff (χ : unramifiedCharacters ν)
    (A : SmoothRep.{0, uG, uV} ℂ M) {H : Subgroup G} (hHK : H ≤ K.toSubgroup) :
    fixedVectors ((normalizedInductionFunctor h hU).obj
        (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ))).representation H ≠ ⊥ ↔
      fixedVectors ((normalizedInductionFunctor h hU).obj A).representation H ≠ ⊥ :=
  fixedVectors_ne_bot_iff_of_equiv_restrict
    ((unramifiedNormalizedInductionCompactEquiv h K hU hP hK hPK ν hν hr χ A).trans
      (normalizedInductionCompactEquiv h K hU hP hK hPK A).symm) hHK

include hP hK hPK hν hr in
/-- The condition `HasInducedFixedVector` is invariant under unramified twists, for `H ⊆ K`. -/
theorem hasInducedFixedVector_twist_iff (χ : unramifiedCharacters ν) {H : Subgroup G}
    (hHK : H ≤ K.toSubgroup) (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) :
    HasInducedFixedVector h hU H
        (SmoothDualClass.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ) ω) ↔
      HasInducedFixedVector h hU H ω := by
  induction ω using Quotient.inductionOn with
  | h A =>
    exact fixedVectors_normalizedInduction_twist_ne_bot_iff h K hU hP hK hPK ν hν hr χ A.obj hHK

end Twist

section Orbits

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure]
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

/-- **Waldspurger's `Θ^H` for one parabolic `P = MU`** (VIII.1, printed p. 321): the orbits `O`
of `Im X(M)` in `E₂(M)` (discrete series of `M` modulo `C`) such that `I_P^G E` has a nonzero
`H`-fixed vector for some `(ω, E) ∈ O`; `(O, P) ∈ Θ^H` exactly when `O` belongs to this set. -/
def inducedDiscreteSeriesFixedOrbits (H : Subgroup G) :
    Set (DiscreteSeriesOrbitClass.{uG, uI, uV} C hC μM ν) :=
  (Quotient.mk (MulAction.orbitRel _ _)) ''
    {ω : DiscreteSeriesClass.{uG, uV} C hC μM | HasInducedFixedVector h hU H ω.val}

/-- The orbit of `π` belongs to `Θ^H` as soon as one representative `A` of a member of the orbit
has `I_P^G A` with a nonzero `H`-fixed vector. -/
theorem mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative {H : Subgroup G}
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
    (hπ : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
    (A : UnitaryOrbitRepresentative ν π)
    (hA : fixedVectors ((normalizedInductionFunctor h hU).obj A.val.obj).representation H ≠ ⊥) :
    Quotient.mk _ (discreteSeriesClass C hC μM π hπ) ∈
      inducedDiscreteSeriesFixedOrbits h hU C hC μM ν H := by
  refine ⟨discreteSeriesClass C hC μM A.val
    (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μM hπ A), hA, ?_⟩
  obtain ⟨χ, hχ⟩ := A.property
  exact Quotient.sound ⟨χ, Subtype.ext hχ⟩

variable (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

include hP hK hPK hν hr in
/-- **Membership in `Θ^H` does not depend on the member of the orbit** (Waldspurger VIII.1,
printed p. 321), for `H ⊆ K` with `G = P K`: the orbit of `ω` is in `Θ^H` if and only if
`I_P^G E` has a nonzero `H`-fixed vector for `(ω, E)` itself. -/
theorem mk_mem_inducedDiscreteSeriesFixedOrbits_iff {H : Subgroup G} (hHK : H ≤ K.toSubgroup)
    (ω : DiscreteSeriesClass.{uG, uV} C hC μM) :
    Quotient.mk _ ω ∈ inducedDiscreteSeriesFixedOrbits h hU C hC μM ν H ↔
      HasInducedFixedVector h hU H ω.val := by
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨χ, rfl⟩ := Quotient.exact he
    exact (hasInducedFixedVector_twist_iff h K hU hP hK hPK ν hν hr
      (unitaryUnramifiedInclusion ν χ) hHK ω.val).mp hw
  · intro hω
    exact ⟨ω, hω, rfl⟩

omit [MeasurableSpace (M ⧸ C)] in
include hP hK hPK hν hr in
/-- If the orbit of `π` is not in `Θ^H` (`H ⊆ K`), then no representative `A` of a member of
the orbit has `I_P^G A` with a nonzero `H`-fixed vector. -/
theorem fixedVectors_unitaryOrbitRepresentative_eq_bot {H : Subgroup G}
    (hHK : H ≤ K.toSubgroup) (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
    (hπ : fixedVectors ((normalizedInductionFunctor h hU).obj π.obj).representation H = ⊥)
    (A : UnitaryOrbitRepresentative ν π) :
    fixedVectors ((normalizedInductionFunctor h hU).obj A.val.obj).representation H = ⊥ := by
  obtain ⟨χ, hχ⟩ := A.property
  have h1 := hasInducedFixedVector_twist_iff h K hU hP hK hPK ν hν hr
    (unitaryUnramifiedInclusion ν χ) hHK (Quotient.mk _ π)
  rw [hχ] at h1
  by_contra hne
  exact (h1.mp hne) hπ

end Orbits

section Finiteness

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hM : IsClosed (M : Set G)) [CompactSpace (Induction.LeftQuotient P)]
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure]
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))

include hM in
/-- **Reduction of `Θ^H` to the Levi subgroup** (proof of Remark VIII.1.3 (i)): there are
finitely many compact open subgroups `L_x` of `M`, independent of the inducing representations,
such that every orbit `O` with `(O, P) ∈ Θ^H` lies in some `Θ^{L_x}_M`. They come from the
Library's `finiteInductionFixedVectorVisibility` (compactness of `P \ G`). -/
theorem exists_inducedDiscreteSeriesFixedOrbits_subset (H : OpenSubgroup G) :
    ∃ (t : Finset G) (L : t → OpenSubgroup M), (∀ x, IsCompact (L x : Set M)) ∧
      (inducedDiscreteSeriesFixedOrbits h hU C hC μM ν H.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{uG, uI, uV} C hC μM ν)) ⊆
        ⋃ x, discreteSeriesFixedOrbits C hC μM ν (L x).toSubgroup := by
  obtain ⟨t, L, hLc, hvis⟩ := finiteInductionFixedVectorVisibility.{uG, uV} h hU hM H
  refine ⟨t, L, hLc, ?_⟩
  rintro _ ⟨ω, hω, rfl⟩
  obtain ⟨A, hA⟩ := Quotient.exists_rep ω.val
  have hω' : fixedVectors ((normalizedInductionFunctor h hU).obj A.obj).representation
      H.toSubgroup ≠ ⊥ := by
    change HasInducedFixedVector h hU H.toSubgroup ω.val at hω
    rw [← hA] at hω
    exact hω
  have hnt := (Submodule.nontrivial_iff_ne_bot).mpr hω'
  obtain ⟨x, hx⟩ := hvis A.obj hnt
  refine Set.mem_iUnion.mpr ⟨x, ω, ?_, rfl⟩
  change SmoothDualClass.HasFixedVector (L x).toSubgroup ω.val
  rw [← hA]
  exact (Submodule.nontrivial_iff_ne_bot).mp hx

include hM in
/-- **Remark VIII.1.3 (i) for one parabolic** (Waldspurger, printed p. 321): if Theorem VIII.1.2
holds for `M` (`Θ^L_M` is finite for every compact open subgroup `L` of `M`), then for every open
subgroup `H` of `G` the set of orbits `O` with `(O, P) ∈ Θ^H` is finite. -/
theorem finite_inducedDiscreteSeriesFixedOrbits (H : OpenSubgroup G)
    (hfin : ∀ L : OpenSubgroup M, IsCompact (L : Set M) →
      (discreteSeriesFixedOrbits C hC μM ν L.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{uG, uI, uV} C hC μM ν)).Finite) :
    (inducedDiscreteSeriesFixedOrbits h hU C hC μM ν H.toSubgroup :
      Set (DiscreteSeriesOrbitClass.{uG, uI, uV} C hC μM ν)).Finite := by
  obtain ⟨t, L, hLc, hsub⟩ := exists_inducedDiscreteSeriesFixedOrbits_subset h hU hM C hC μM ν H
  exact (Set.finite_iUnion fun x => hfin (L x) (hLc x)).subset hsub

end Finiteness

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

-- The decomposition `P_I(F) = M_I(F) ⋉ U_I(F)` and the closedness of `U_I(F)`.
set_option hygiene false in
local notation "𝐡" =>
  isSemidirectDecomposition_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I)

set_option hygiene false in
local notation "𝐡U" => isClosed_standardUnipotentPoints i ν (RationalPointFamily.rootSet i ν I)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
include hG hi hν hPK in
/-- `G(F) = P_I(F) K`, with the factors as elements of the subgroups. -/
theorem exists_standardParabolicPoints_rootSet_subtype_mul (g : rationalPoints G) :
    ∃ p : standardParabolicPoints i ν (RationalPointFamily.rootSet i ν I), ∃ k : K,
      g = (p : rationalPoints G) * (k : rationalPoints G) := by
  obtain ⟨q, hq, k, hk, e⟩ := exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK g
  exact ⟨⟨q, hq⟩, ⟨k, hk⟩, e⟩

include hG hi hν hKc hPK in
/-- **Independence of the member of the orbit on actual points** (Waldspurger VIII.1, printed
p. 321), for `H ⊆ K`: if `I_{P_I}^G π` has no nonzero `H`-fixed vector, neither has
`I_{P_I}^G A` for any representative `A` of a member of the unitary unramified orbit of `π`. -/
theorem fixedVectors_rationalInduction_unitaryOrbitRepresentative_eq_bot
    {H : Subgroup (rationalPoints G)} (hHK : H ≤ K.toSubgroup)
    (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
    (hπ : fixedVectors ((normalizedInductionFunctor 𝐡 𝐡U).obj π.obj).representation H = ⊥)
    (A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π) :
    fixedVectors ((normalizedInductionFunctor 𝐡 𝐡U).obj A.val.obj).representation H = ⊥ :=
  fixedVectors_unitaryOrbitRepresentative_eq_bot (G := rationalPoints G) (h := 𝐡) (hU := 𝐡U)
    (ν := RationalPointFamily.leviRationalNormCharacters i ν I) (K := K)
    (hP := isClosed_standardParabolicPoints_rootSet hG hi hν I) (hK := hKc)
    (hPK := exists_standardParabolicPoints_rootSet_subtype_mul hG hi hν I hPK)
    (hν := RationalPointFamily.continuous_leviRationalNormCharacters i ν I)
    (hr := continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    hHK π hπ A

include hG hi hν hKc hPK in
/-- **Remark VIII.1.3 (i) on actual points, for one standard parabolic** (Waldspurger, printed
p. 321): if Theorem VIII.1.2 holds for `M_I(F)` (`hfin`: the set `Θ^L_{M_I}` of orbits of
discrete series of `M_I(F)` modulo `C` with a nonzero `L`-fixed vector is finite for every
compact open subgroup `L` of `M_I(F)`), then for every open subgroup `H` of `G(F)` the set of
orbits `O` with `(O, P_I(F)) ∈ Θ^H` is finite. -/
theorem finite_rationalInducedDiscreteSeriesFixedOrbits
    (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
    [MeasurableSpace (𝐌 ⧸ C)] (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G))
    (hfin : ∀ L : OpenSubgroup 𝐌, IsCompact (L : Set 𝐌) →
      (discreteSeriesFixedOrbits C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
        L.toSubgroup : Set (DiscreteSeriesOrbitClass.{u, _, uV} C hC μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite) :
    (inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U C hC μM
      (RationalPointFamily.leviRationalNormCharacters i ν I) H.toSubgroup :
        Set (DiscreteSeriesOrbitClass.{u, _, uV} C hC μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite := by
  have := compactSpace_leftQuotient_standardParabolicPoints_rootSet hG hi hν I hKc hPK
  exact finite_inducedDiscreteSeriesFixedOrbits (G := rationalPoints G) 𝐡 𝐡U
    (isClosed_standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) C hC μM _ H hfin

section Representative

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (A : SmoothRep.{0, u, uV} ℂ 𝐌)
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hirr : A.representation.IsIrreducible)
  (hTA : IsRationalLeviTempered hKc ρ hM A)
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **`f̂(ω, P) = 0` on actual points when `I_{P_I}^G ω` has no nonzero `H`-fixed vector** and
`f ∈ C(G)` is right invariant under `H` (Waldspurger, Remark VIII.1.3, printed p. 321). -/
theorem rationalInducedFourierTransform_eq_zero_of_fixedVectors_eq_bot
    {H : Subgroup (rationalPoints G)}
    (hH : fixedVectors ((normalizedInductionFunctor 𝐡 𝐡U).obj A).representation H = ⊥)
    (f : RationalSchwartzSpace hKc hPK ρ) (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    rationalInducedFourierTransform hG hi hν I hKc hPK ρ hρ hKρ hM A C hC μM hsq hirr hTA hsw f =
      0 := by
  have := locallyCompactSpace_standardParabolicPoints_rootSet hG hi hν I
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  have h := inducedFourierTransform_eq_zero_of_fixedVectors_eq_bot (G := rationalPoints G)
    (M := standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) 𝐡 𝐡U
    (isClosed_standardParabolicPoints_rootSet hG hi hν I)
    (continuous_projection_standard hG hi hν (RationalPointFamily.rootSet_subset i ν I) _)
    K hKc (exists_standardParabolicPoints_rootSet_mul hG hi hν I hPK)
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    (modularCharacter_standardParabolicPoints hG hi hν I rfl
      (RationalPointFamily.rootSet_subset i ν I))
    A (compactOpenCofinal_standardLevi I hKc) C hC μM hsq hirr
    (rationalL2Weights K.isOpen hKc hPK ρ hsw)
    (rationalHasTemperedCoefficients_normalizedInduction ρ hG hi hν
      (RationalPointFamily.rootSet_subset i ν I) I rfl K hKc hPK hM hρ hKρ A hsq.1 hTA)
    (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ)
    (rationalTranslationWeights K.isOpen hKc hPK ρ) hH f hf
  unfold rationalInducedFourierTransform
  with_reducible_and_instances exact h

end Representative

section Orbit

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
  (hTA : ∀ A : UnitaryOrbitRepresentative (RationalPointFamily.leviRationalNormCharacters i ν I) π,
    IsRationalLeviTempered hKc ρ hM A.val.obj)
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **`ψ_f[O, P] = 0` when `(O, P) ∉ Θ^H`** (Waldspurger, Remark VIII.1.3, printed p. 321), on
actual points, for `H ⊆ K`: if `f ∈ C(G)` is right invariant under `H` and `I_{P_I}^G π` has no
nonzero `H`-fixed vector, then `ψ_f[O, P_I] = 0` on the whole unitary unramified orbit `O` of
`π`. -/
theorem rationalFourierOrbitSection_eq_zero_of_fixedVectors_eq_bot
    {H : Subgroup (rationalPoints G)} (hHK : H ≤ K.toSubgroup)
    (hπ : fixedVectors ((normalizedInductionFunctor 𝐡 𝐡U).obj π.obj).representation H = ⊥)
    (f : RationalSchwartzSpace hKc hPK ρ) (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g) :
    rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f = 0 := by
  funext A
  rw [rationalFourierOrbitSection_apply]
  exact rationalInducedFourierTransform_eq_zero_of_fixedVectors_eq_bot hG hi hν I hKc hPK ρ hρ
    hKρ hM A.val.obj C hC μM (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A)
    A.val.property.1 (hTA A) hsw
    (fixedVectors_rationalInduction_unitaryOrbitRepresentative_eq_bot hG hi hν I hKc hPK hHK π
      hπ A) f hf

/-- **`ψ_f[O, P] ≠ 0` only if `(O, P) ∈ Θ^H`** (Waldspurger, Remark VIII.1.3, printed p. 321:
"si `f ∈ C(G)` et si `H` est un sous-groupe ouvert compact de `G` tel que `f` soit
bi-invariante par `H`, il est clair que, pour `(O, P) ∈ Θ`, `ψ_f[O, P] ≠ 0` seulement si
`(O, P) ∈ Θ^H`"), on actual points, for every subgroup `H` under which `f` is right invariant. -/
theorem mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero
    {H : Subgroup (rationalPoints G)} (f : RationalSchwartzSpace hKc hPK ρ)
    (hf : ∀ k ∈ H, ∀ g, f (g * k) = f g)
    (hne : rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f ≠
      0) :
    Quotient.mk _ (discreteSeriesClass C hC μM π hsq) ∈ inducedDiscreteSeriesFixedOrbits 𝐡 𝐡U
      C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I) H := by
  by_contra hnot
  apply hne
  funext A
  rw [rationalFourierOrbitSection_apply]
  refine rationalInducedFourierTransform_eq_zero_of_fixedVectors_eq_bot hG hi hν I hKc hPK ρ hρ
    hKρ hM A.val.obj C hC μM (unitaryOrbitRepresentative_isDiscreteSeries _ π C hC μM hsq A)
    A.val.property.1 (hTA A) hsw ?_ f hf
  by_contra hA
  exact hnot (mk_mem_inducedDiscreteSeriesFixedOrbits_of_representative 𝐡 𝐡U C hC μM
    (RationalPointFamily.leviRationalNormCharacters i ν I) π hsq A hA)

end Orbit

section Support

variable {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (hρ : IsClosedSubgroup ρ)
  (hKρ : (K : Subgroup (rationalPoints G)) ≤ rationalHeightSubgroup (F := F) ρ)
  (hM : IsIwasawaPair
    ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    ((K : Subgroup (rationalPoints G)).subgroupOf
      (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I))))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (μM : Measure (𝐌 ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  {mu : Measure (rationalPoints G)} [mu.IsMulLeftInvariant] [mu.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight mu (rationalXi hKc hPK) (rationalHeight (F := F) ρ))

/-- **Remark VIII.1.3 (ii) on actual points, for one standard parabolic** (Waldspurger, printed
p. 321): if Theorem VIII.1.2 holds for `M_I(F)` (`hfin`), then for every `f ∈ C(G)` there is a
finite set `T` of orbits of discrete series of `M_I(F)` modulo `C` containing the orbit of every
`π` with `ψ_f[O, P_I] ≠ 0`. `T` is `Θ^H` for `P_I(F)` and a compact open subgroup `H` under which
`f` is right invariant. -/
theorem exists_finite_rationalFourierOrbitSection_ne_zero
    (hfin : ∀ L : OpenSubgroup 𝐌, IsCompact (L : Set 𝐌) →
      (discreteSeriesFixedOrbits C hC μM (RationalPointFamily.leviRationalNormCharacters i ν I)
        L.toSubgroup : Set (DiscreteSeriesOrbitClass.{u, _, uV} C hC μM
          (RationalPointFamily.leviRationalNormCharacters i ν I))).Finite)
    (f : RationalSchwartzSpace hKc hPK ρ) :
    ∃ T : Set (DiscreteSeriesOrbitClass.{u, _, uV} C hC μM
        (RationalPointFamily.leviRationalNormCharacters i ν I)), T.Finite ∧
      ∀ (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
        (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μM)
        (hTA : ∀ A : UnitaryOrbitRepresentative
          (RationalPointFamily.leviRationalNormCharacters i ν I) π,
            IsRationalLeviTempered hKc ρ hM A.val.obj),
        rationalFourierOrbitSection hG hi hν I hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f ≠ 0 →
          Quotient.mk _ (discreteSeriesClass C hC μM π hsq) ∈ T := by
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  obtain ⟨L, hL⟩ := Space.exists_rightInvariant f
  exact ⟨_, finite_rationalInducedDiscreteSeriesFixedOrbits hG hi hν I hKc hPK C hC μM L.1 hfin,
    fun π hsq hTA hne =>
      mk_mem_inducedDiscreteSeriesFixedOrbits_of_rationalFourierOrbitSection_ne_zero hG hi hν I
        hKc hPK ρ hρ hKρ hM π C hC μM hsq hTA hsw f hL hne⟩

end Support

end Rational

end Langlands.HarishChandraSchwartz
