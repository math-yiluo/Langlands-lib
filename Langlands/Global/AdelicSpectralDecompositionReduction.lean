import Langlands.Global.AdelicSpectralDecompositionStatement
import Langlands.Global.AdelicStandardParabolicFiniteness
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Reduction of Langlands' spectral decomposition to four analytic ingredients

Getz–Hahn Theorem 10.5.1 (`SpectralDecompositionStatement`), split into the following
propositions, all on `[G] = A_G G(F) \ G(𝔸)` for the presented standard parabolics of the target:

* `RelativeWavePacketOrthogonalityStatement` (Lapid 2011, Proposition 2, with `Ω(P, P') = ∅`):
  wave packets of non-associate standard parabolics are orthogonal;
* `RelativeWavePacketAssociationStatement` (functional equation and unitarity of `M(w, λ)` on
  the imaginary axis): if `w M w⁻¹ = M'`, every wave packet of `P` lies in `L²_{P'}([G])`;
* `RelativeWavePacketCompletenessStatement` (Delorme 2023, Theorem 7.9; Arthur 2005,
  Theorem 7.2): a function on `[G]` orthogonal to the wave packets of every standard parabolic
  is zero;
* `GroupParabolicSpectrumStatement` (Getz–Hahn (9.6) and §10.5): `L²_G([G]) = L²_disc([G])`.

The theorem `spectralDecomposition_of_reduction` derives `SpectralDecompositionStatement` from
the four. The finiteness in item 1 comes from the proved theorem
`standardParabolicSpectrumFiniteness` (module `Langlands.Global.AdelicStandardParabolicFiniteness`),
applied to item 3. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct ComplexConjugate

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

section Statements

/-- Orthogonality of the wave packets of non-associate standard parabolics (Lapid 2011,
Proposition 2: the inner product of the wave packets of `P` and `P'` is a sum over
`Ω(P, P')`, which is empty when `P` and `P'` are not associate; Arthur 2005, Theorem 7.2(b)).
For presented standard parabolics `P = MU` and `P' = M'U'` of the target such that no rational
point `w` and no `c : M' → M` satisfy `IsWeylConjugation p l p' l' w c`, every wave packet `Θ`
of `P` and every wave packet `Θ'` of `P'` over `i(𝔞_M^G)^*`, resp. `i(𝔞_{M'}^G)^*`, that are
square integrable on `[G]` satisfy `∫_{[G]} Θ · conj Θ' = 0`. -/
def RelativeWavePacketOrthogonalityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K,
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
        (A' : CommGroupScheme (Spec (CommRingCat.of F)))
        [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
        [IsAffine U'.X.left]
        (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
        (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
        [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
        [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
        (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp),
        haveI : LocallyOfFiniteType P'.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p' →
        LeviSubgroup.IsGeometricUnipotentRadical iU' →
        ∀ hK' : IsIwasawaCompact p' K,
          (¬ ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
              IsWeylConjugation p l p' l' w c) →
          ∀ Θ Θ' : AdelicGroupPoints F G → ℂ,
            IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
            IsRelativeWavePacket hK' rho hsmooth hcalc iU' l' r' hA' hT' Θ' →
            MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => Θ y.out) 2
              (RestrictionSplitCentre.canonicalMeasure F G) →
            MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => Θ' y.out) 2
              (RestrictionSplitCentre.canonicalMeasure F G) →
            ∫ y, Θ y.out * conj (Θ' y.out) ∂(RestrictionSplitCentre.canonicalMeasure F G) = 0

/-- Wave packets of associate parabolics span the same space (Getz–Hahn §10.5; the functional
equation `E(M(w, λ)φ, wλ) = E(φ, λ)` together with the holomorphy and unitarity of `M(w, λ)` on
`i𝔞_P^*`). For presented standard parabolics `P = MU` and `P' = M'U'` of the target, a rational
point `w` and `c : M' → M` with `IsWeylConjugation p l p' l' w c` (that is, `w M w⁻¹ = M'`),
the class in `L²([G])` of every square-integrable wave packet of `P` lies in `L²_{P'}([G])`. -/
def RelativeWavePacketAssociationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K,
      ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
        (A' : CommGroupScheme (Spec (CommRingCat.of F)))
        [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
        [IsAffine U'.X.left]
        (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
        (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
        [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
        [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
        (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp),
        haveI : LocallyOfFiniteType P'.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p' →
        LeviSubgroup.IsGeometricUnipotentRadical iU' →
        ∀ hK' : IsIwasawaCompact p' K,
        ∀ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
          IsWeylConjugation p l p' l' w c →
          ∀ Θ : AdelicGroupPoints F G → ℂ,
            IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
            ∀ f : Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G),
              f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] (fun y => Θ y.out) →
              f ∈ parabolicSpectrum hK' rho hsmooth hcalc iU' l' r' hA' hT'

/-- Completeness of the wave packets of the standard parabolics on `[G]` (Delorme 2023,
Theorem 7.9, the surjectivity half of Arthur 2005, Theorem 7.2(b); Getz–Hahn Theorem 10.5.1).
If a square-integrable function `f` on `[G]` satisfies `∫_{[G]} f · conj Θ = 0` for every
square-integrable wave packet `Θ` over `i(𝔞_M^G)^*` of every presented standard parabolic of the
target, then `f = 0` almost everywhere. -/
def RelativeWavePacketCompletenessStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    ∀ f : RestrictionSplitCentre.CanonicalQuotient F G → ℂ,
      MemLp f 2 (RestrictionSplitCentre.canonicalMeasure F G) →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
        [IsAffine U.X.left]
        (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
        [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
        LeviSubgroup.IsGeometricUnipotentRadical iU →
        ∀ hK : IsIwasawaCompact p K,
        ∀ Θ : AdelicGroupPoints F G → ℂ,
          IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
          MemLp (fun y : RestrictionSplitCentre.CanonicalQuotient F G => Θ y.out) 2
            (RestrictionSplitCentre.canonicalMeasure F G) →
          ∫ y, f y * conj (Θ y.out) ∂(RestrictionSplitCentre.canonicalMeasure F G) = 0) →
      f =ᵐ[RestrictionSplitCentre.canonicalMeasure F G] 0

/-- The space of `G` itself is the discrete spectrum (Getz–Hahn (9.6) and §10.5, where
`L²_G([G]) = L²_disc([G])`; classically, the closed span of the square-integrable automorphic
forms on `[G]` is the discrete part of the right regular representation). For a presented
standard parabolic of the target with `p` an isomorphism, `L²_P([G])` is
`discreteSpectrum F G hG`. -/
def GroupParabolicSpectrumStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K, IsIso p →
        parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT = discreteSpectrum F G hG

end Statements

section Proof

/-- The `L²` inner product computed on representatives: if `u =ᵐ f` and `v =ᵐ g`, then
`⟪v, u⟫ = ∫ f · conj g`. -/
theorem l2_inner_eq_integral_mul_conj {α : Type*} [MeasurableSpace α] {m : Measure α}
    {u v : Lp ℂ 2 m} {f g : α → ℂ} (hu : u =ᵐ[m] f) (hv : v =ᵐ[m] g) :
    inner ℂ v u = ∫ a, f a * conj (g a) ∂m := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, hv] with a ha hb
  rw [RCLike.inner_apply, ha, hb]

/-- Closures of spans of mutually orthogonal sets are orthogonal. -/
theorem isOrtho_topologicalClosure_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {s t : Set E} (h : ∀ u ∈ s, ∀ v ∈ t, inner ℂ u v = 0) :
    (Submodule.span ℂ s).topologicalClosure ⟂ (Submodule.span ℂ t).topologicalClosure := by
  rw [Submodule.isOrtho_iff_le, Submodule.orthogonal_closure]
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
  rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
  exact fun u hu v hv => h u hu v hv

/-- Weyl conjugation is symmetric: if `l(c(m')) = w⁻¹ l'(m') w`, then
`l'(c⁻¹(m)) = w l(m) w⁻¹`. -/
theorem isWeylConjugation_symm {F : Type} [Field F] [NumberField F]
    {G P Q M M' : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G} {l : M ⟶ P}
    {q : Q ⟶ G} {l' : M' ⟶ Q} {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
    {c : M' ⟶ M} (h : IsWeylConjugation p l q l' w c) :
    haveI := h.isIso
    IsWeylConjugation q l' p l w⁻¹ (inv c) := by
  have := h.isIso
  refine ⟨inferInstance, ?_⟩
  have hinv : (G.innerIso w⁻¹).inv = (G.innerIso w).hom := by
    rw [← cancel_mono (G.innerIso w⁻¹).hom, Iso.inv_hom_id, innerIso_inv_hom,
      Iso.hom_inv_id]
  rw [hinv, IsIso.inv_comp_eq, reassoc_of% h.comp_eq, Iso.inv_hom_id, Category.comp_id]

/-- Prove the right conjunct first and use it for the left one. -/
theorem and_of_right_of_imp {a b : Prop} (hb : b) (ha : b → a) : a ∧ b := ⟨ha hb, hb⟩

/-- Langlands' spectral decomposition (Getz–Hahn Theorem 10.5.1) from the four analytic
ingredients, with `standardParabolicSpectrumFiniteness` for the finiteness in item 1. -/
theorem spectralDecomposition_of_reduction
    (hO : RelativeWavePacketOrthogonalityStatement)
    (hAs : RelativeWavePacketAssociationStatement)
    (hC : RelativeWavePacketCompletenessStatement)
    (hD : GroupParabolicSpectrumStatement) :
    SpectralDecompositionStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ _ hP₀ hK₀ S
  refine and_of_right_of_imp ?_ fun H2 => ?_
  · intro P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT h₀ hU hK
    refine ⟨hD F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀ hK₀ P M U A p iU l a r hA hT h₀
      hU hK, ?_⟩
    intro P' M' U' A' _ _ _ _ p' _ iU' l' a' r' _ _ _ hA' hT' h₀' hU' hK'
    refine ⟨?_, ?_⟩
    · rintro ⟨w, c, hwc⟩
      apply le_antisymm
      · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
          (Submodule.isClosed_topologicalClosure _)
        rintro f ⟨Θ, hΘ, hf⟩
        exact hAs F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀ hK₀ P M U A p iU l a r hA hT
          h₀ hU hK P' M' U' A' p' iU' l' a' r' hA' hT' h₀' hU' hK' w c hwc Θ hΘ f hf
      · refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_)
          (Submodule.isClosed_topologicalClosure _)
        rintro f ⟨Θ, hΘ, hf⟩
        have := hwc.isIso
        exact hAs F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀ hK₀ P' M' U' A' p' iU' l' a' r'
          hA' hT' h₀' hU' hK' P M U A p iU l a r hA hT h₀ hU hK w⁻¹ (inv c)
          (isWeylConjugation_symm hwc) Θ hΘ f hf
    · intro hn
      refine isOrtho_topologicalClosure_span ?_
      rintro u ⟨Θ, hΘ, hu⟩ v ⟨Θ', hΘ', hv⟩
      rw [inner_eq_zero_symm, l2_inner_eq_integral_mul_conj hu hv]
      exact hO F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀ hK₀ P M U A p iU l a r hA hT h₀
        hU hK P' M' U' A' p' iU' l' a' r' hA' hT' h₀' hU' hK' hn Θ Θ' hΘ hΘ'
        ((Lp.memLp u).ae_eq hu) ((Lp.memLp v).ae_eq hv)
  refine ⟨?_, ?_⟩
  · -- finiteness: `standardParabolicSpectrumFiniteness`, given item 3 (proved above as `H2`)
    refine standardParabolicSpectrumFiniteness F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀
      hK₀ ?_
    intro P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT h₀ hU hK P' M' U' A' _ _ _ _ p' _ iU' l' a' r'
      _ _ _ hA' hT' h₀' hU' hK' h
    exact ((H2 P M U A p iU l a r hA hT h₀ hU hK).2 P' M' U' A' p' iU' l' a' r' hA' hT' h₀' hU'
      hK').1 h
  · -- density: a function orthogonal to every wave packet vanishes
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal] at hx
    refine Lp.eq_zero_iff_ae_eq_zero.mpr
      (hC F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hP₀ hK₀ x (Lp.memLp x) ?_)
    intro P M U A _ _ _ _ p _ iU l a r _ _ _ hA hT h₀ hU hK Θ hΘ hΘL
    have : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    have hS : parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT ∈ S :=
      ⟨P, M, U, A, inferInstance, inferInstance, inferInstance, inferInstance, p,
        inferInstance, iU, l, a, r, inferInstance, inferInstance, inferInstance, hA, hT, h₀, hU,
        hK, rfl⟩
    have hmem : hΘL.toLp _ ∈ sSup S :=
      le_sSup hS (Submodule.le_topologicalClosure _
        (Submodule.subset_span ⟨Θ, hΘ, hΘL.coeFn_toLp⟩))
    have h0 := hx _ hmem
    rwa [l2_inner_eq_integral_mul_conj (Filter.EventuallyEq.refl _ _) hΘL.coeFn_toLp] at h0

end Proof

end Langlands.Global
