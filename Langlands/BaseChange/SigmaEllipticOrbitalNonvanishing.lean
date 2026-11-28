import Langlands.BaseChange.CyclicNormLemma
import Langlands.BaseChange.RegularCyclicBasis
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.RegularOrbitalProfileExistence
import Langlands.BaseChange.SigmaLiftCharacterIdentity.Parameters
import Langlands.BaseChange.SigmaDiscreteEllipticNonvanishingReduction

/-!
# Nonvanishing of σ-orbital integrals on an open set of σ-elliptic elements

Let `F` be a nonarchimedean local field of characteristic zero and `E` a commutative
`F`-algebra, cyclic of group `⟨σ⟩` of order `l` (for instance a cyclic field extension of
`F` with generator `σ`). The module proves that a test function `φ` on `GL_n(E)` whose σ-orbital
integrals vanish off the σ-elliptic set, and whose integral against a σ-conjugation invariant
function `Θ` on the σ-regular set is nonzero, has σ-orbital integrals that do not vanish on a
nonempty open set of σ-elliptic elements, for every choice of compatible measures. With `Θ`
the twisted character of an irreducible representation this is the argument of
Henniart–Lemaire 2011, II.5.14, Corollaire 2, and Arthur–Clozel 1989, Chapter 1,
Lemma 2.12 (ii).

The proof uses three facts proved in the Library: the integral of an integrable function
whose σ-orbital integrals all vanish is zero (`integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero`),
the normalized σ-orbital integrals of a test function are locally constant on the σ-regular
set (from the regular orbital profiles of `regularOrbitalProfileExistence`), and two compatible
choices of centralizer and quotient measures differ by a positive scalar.
-/

noncomputable section

namespace Langlands.BaseChange

open Set MeasureTheory MeasureTheory.Measure _root_.Topology
open scoped NNReal
open Langlands.HarmonicAnalysis Langlands.JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (IsLocallyProfinite isLocallyProfinite_of_mathlib)
open SigmaLiftCharacterIdentity (coefficients coefficients_associated
  coefficients_cyclicNorm_conj charpoly_eq_of_baseChange_coefficients continuous_coefficients
  continuous_cyclicNorm continuous_entrywiseAut)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section Scaling

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {Θ : Type*} [FunLike Θ G G] [MonoidHomClass Θ G G]

/-- For a continuous twist `θ` of a second countable locally compact group, two compatible
pairs of a right Haar measure on the twisted centralizer of `δ` and a quotient measure give
twisted orbital integrals that differ by one positive scalar, for every function. -/
theorem exists_twistedOrbitalIntegral_eq_smul_of_isCompatible (θ : Θ)
    (hθ : Continuous (fun x : G => θ x)) (δ : G) {μG : Measure G}
    {μ₁ μ₂ : Measure (twistedCentralizer θ δ)} [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant]
    [μ₂.IsHaarMeasure] [μ₂.IsMulRightInvariant]
    {ν₁ ν₂ : Measure (LeftQuotient (twistedCentralizer θ δ))}
    (h₁ : IsCompatible (twistedCentralizer θ δ) μG μ₁ ν₁)
    (h₂ : IsCompatible (twistedCentralizer θ δ) μG μ₂ ν₂) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : G → ℂ,
      twistedOrbitalIntegral θ δ ν₁ f = (c : ℝ) • twistedOrbitalIntegral θ δ ν₂ f := by
  have hclosed := isClosed_twistedCentralizer θ hθ δ
  let : LocallyCompactSpace (twistedCentralizer θ δ) := hclosed.locallyCompactSpace
  let : SecondCountableTopology (twistedCentralizer θ δ) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let c := haarScalarFactor μ₂ μ₁
  have hc : 0 < c := haarScalarFactor_pos_of_isHaarMeasure μ₂ μ₁
  have hscale : μ₂ = c • μ₁ := isMulLeftInvariant_eq_smul μ₂ μ₁
  refine ⟨c, hc, fun f => ?_⟩
  rw [h₁.eq_smul_of_subgroup_smul hclosed h₂ hscale, twistedOrbitalIntegral_smul_measure]

end Scaling

section InvariantCutoff

variable {G B A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [TopologicalSpace B] [TopologicalSpace A] [T2Space A]
  {θ : G →* G} {μ : Measure G} {R : Set G}
  {m : RegularOrbitalMeasures θ μ R} {p : R → B}

/-- Local constancy of normalized twisted orbital integrals on an open regular locus, for
every test function, from the regular orbital profile data and a continuous function `a`
on the group that is constant exactly on the twisted conjugacy classes through the locus:
the test function is cut off to the preimage under `a` of the image of a compact open
neighbourhood, which is open, closed, invariant and contained in the locus. -/
theorem RegularOrbitalProfileData.isLocallyConstant_twistedOrbitalIntegral
    (d : RegularOrbitalProfileData m p) (hG : IsLocallyProfinite G)
    (a : G → A) (ha : Continuous a)
    (hinv : ∀ (x g : G), a (twistedConj θ x g) = a g)
    (hfiber : ∀ (r : R) (g : G), a g = a r → ∃ x : G, twistedConj θ x (r : G) = g)
    (f : SchwartzBruhat G) :
    IsLocallyConstant (fun r : R => twistedOrbitalIntegral θ (r : G) (m.quotient r) f) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro r
  obtain ⟨K, hrK, hKo, hKc, hKR⟩ := hG.2 (r : G) R (d.isOpen.mem_nhds r.property)
  let C := a ⁻¹' (a '' K)
  have hCc : IsClosed C := (hKc.image ha).isClosed.preimage ha
  have hCsat : C = ⋃ x : G, twistedConj θ x '' K := by
    ext g
    constructor
    · rintro ⟨k, hk, hkg⟩
      obtain ⟨x, hx⟩ := hfiber ⟨k, hKR hk⟩ g hkg.symm
      exact mem_iUnion.mpr ⟨x, k, hk, hx⟩
    · intro hg
      obtain ⟨x, k, hk, rfl⟩ := mem_iUnion.mp hg
      exact ⟨k, hk, (hinv x k).symm⟩
  have hCo : IsOpen C := by
    rw [hCsat]
    exact isOpen_iUnion fun x =>
      ((isOpenMap_mul_right (θ x)).comp (isOpenMap_mul_left x⁻¹)) K hKo
  have hCR : C ⊆ R := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := mem_iUnion.mp (hCsat ▸ hg)
    obtain ⟨s, hs, -⟩ := d.orbit ⟨k, hKR hk⟩ x
    exact hs ▸ s.property
  have hrC : (r : G) ∈ C := ⟨r, hrK, rfl⟩
  let fC : G → ℂ := C.indicator f
  have hfl : IsLocallyConstant fC := by
    apply (IsLocallyConstant.iff_eventually_eq _).2
    intro x
    by_cases hx : x ∈ C
    · have hf := (IsLocallyConstant.iff_eventually_eq _).1 f.locallyConstant x
      filter_upwards [hCo.mem_nhds hx, hf] with y hy hfy
      simpa only [fC, Set.indicator_of_mem hy, Set.indicator_of_mem hx] using hfy
    · filter_upwards [hCc.isOpen_compl.mem_nhds hx] with y hy
      simp only [fC, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  have hfs : Function.support fC ⊆ Function.support f := by
    intro x hx
    by_contra hz
    exact hx (Set.indicator_apply_eq_zero.mpr fun _ => by simpa [Function.mem_support] using hz)
  let f' : SchwartzBruhat G := ⟨fC, hfl, f.hasCompactSupport.mono hfs⟩
  have hf' : Function.support f' ⊆ R := fun _ hx => hCR (Set.support_indicator_subset hx)
  have hval (s : R) (hs : (s : G) ∈ C) :
      twistedOrbitalIntegral θ (s : G) (m.quotient s) f' =
      twistedOrbitalIntegral θ (s : G) (m.quotient s) f := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
      have hx : twistedConj θ x (s : G) ∈ C := by
        change a (twistedConj θ x (s : G)) ∈ a '' K
        rwa [hinv]
      exact Set.indicator_of_mem hx _
  obtain ⟨U, hUo, hrU, hU⟩ := (d.locallyConstant f' hf').exists_open r
  refine ⟨U ∩ Subtype.val ⁻¹' C, hUo.inter (hCo.preimage continuous_subtype_val),
    ⟨hrU, hrC⟩, fun s hs => ?_⟩
  rw [← hval s hs.2, ← hval r hrC]
  exact hU s hs.1

end InvariantCutoff

section Fibers

variable {F : Type u} {E : Type v} [Field F] [CommRing E] [Algebra F E]
  {n l : ℕ} {σ : E ≃ₐ[F] E}

/-- Two elements of `GL_n(F)`, the first regular semisimple, with the same characteristic
polynomial coefficients are conjugate. -/
theorem exists_conj_of_coefficients_eq_of_isRegularSemisimple {γ g : GeneralLinear n F}
    (hγ : IsRegularSemisimple γ) (hg : coefficients g = coefficients γ) :
    ∃ x : GeneralLinear n F, x⁻¹ * γ * x = g := by
  have hpoly := Distribution.charpoly_eq_of_coeff_eq
    (g : Matrix (Fin n) (Fin n) F) (γ : Matrix (Fin n) (Fin n) F) (congrFun hg)
  obtain ⟨y, hy⟩ := exists_matrix_conj_of_charpoly_eq_of_separable _ _ hγ hpoly
  refine ⟨y⁻¹, ?_⟩
  simpa only [inv_inv] using (Units.ext hy : y * γ * y⁻¹ = g)

/-- Two elements of `GL_n(E)`, the first σ-regular, whose cyclic norms have the same
characteristic polynomial coefficients are σ-conjugate. -/
theorem exists_twistedConj_of_cyclicNorm_coefficients_eq
    (hσ : IsCyclicAlgebra σ l) {δ g : GeneralLinear n E}
    (hδ : IsSigmaRegular σ l δ) (hg : coefficients (cyclicNorm σ l g) =
      coefficients (cyclicNorm σ l δ)) :
    ∃ x : GeneralLinear n E, x⁻¹ * δ * entrywiseAut σ n x = g := by
  obtain ⟨γ, hδγ, hγ⟩ := hδ
  obtain ⟨γ', hgγ'⟩ := (cyclicNormLemma F E σ l n hσ).1 g
  have hcoeff : coefficients (baseChange F E n γ') = coefficients (baseChange F E n γ) := by
    rw [← coefficients_associated hgγ', ← coefficients_associated hδγ, hg]
  have hpoly := charpoly_eq_of_baseChange_coefficients hσ hcoeff
  have hc : coefficients γ' = coefficients γ :=
    funext fun i => congrArg (fun p : Polynomial F => p.coeff i.val) hpoly
  obtain ⟨b, hb⟩ := exists_conj_of_coefficients_eq_of_isRegularSemisimple hγ hc
  obtain ⟨x, hx⟩ := hδγ
  obtain ⟨y, hy⟩ := hgγ'
  refine (cyclicNormLemma F E σ l n hσ).2.2 δ g ⟨x * baseChange F E n b * y⁻¹, ?_⟩
  calc
    _ = y * ((baseChange F E n b)⁻¹ * (x⁻¹ * cyclicNorm σ l δ * x) *
        baseChange F E n b) * y⁻¹ := by group
    _ = y * baseChange F E n γ' * y⁻¹ := by
      rw [hx, ← map_inv, ← map_mul, ← map_mul, hb]
    _ = cyclicNorm σ l g := by rw [← hy]; group

end Fibers

/-- Let `φ` be a test function on `GL_n(E)` and `Θ` a function invariant under
σ-conjugation at σ-regular elements, with `φ Θ` integrable for the Haar measure `μ` and
`∫ φ Θ dμ ≠ 0`. If the σ-orbital integrals of `φ` vanish at every σ-regular element that is
not σ-elliptic, then there is a nonempty open set `V` of σ-elliptic elements such that at every
`δ ∈ V` the σ-orbital integral of `φ` is nonzero for every right Haar measure on the
σ-centralizer of `δ` and every compatible quotient measure.

Proof: if every σ-orbital integral of `φ` vanished, so would every σ-orbital integral of
`φ Θ` (it is `Θ(δ)` times that of `φ`), and `∫ φ Θ dμ` would be zero. So some σ-regular
`δ₀` has a nonzero σ-orbital integral, and `δ₀` is σ-elliptic. The normalized σ-orbital
integrals of `φ` are locally constant on the open σ-regular set; their constancy set around
`δ₀`, intersected with the open σ-elliptic set, is `V`, and every compatible choice of measures
rescales the normalized value by a positive scalar. -/
theorem exists_isOpen_sigmaElliptic_sigmaOrbitalIntegral_ne_zero
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ}
    (hE : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
    (φ : SchwartzBruhat (GeneralLinear n E)) (Θ : GeneralLinear n E → ℂ)
    (hint : Integrable (fun g => φ g * Θ g) μ) (hne : ∫ g, φ g * Θ g ∂μ ≠ 0)
    (hinv : ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ →
      ∀ x : GeneralLinear n E, Θ (x⁻¹ * δ * entrywiseAut σ n x) = Θ δ)
    (hvan : SigmaOrbitalIntegralsVanishOffElliptic σ l μ ⇑φ) :
    ∃ V : Set (GeneralLinear n E), IsOpen V ∧ V.Nonempty ∧
      (∀ δ ∈ V, IsSigmaElliptic σ l δ) ∧
      ∀ δ ∈ V, ∀ (μδ : Measure (sigmaCentralizer σ n δ)) [μδ.IsHaarMeasure]
        [μδ.IsMulRightInvariant] (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ))),
        IsCompatible (sigmaCentralizer σ n δ) μ μδ νδ → sigmaOrbitalIntegral σ n δ νδ ⇑φ ≠ 0 := by
  classical
  let : Module.Finite F E := hE.1
  let : T2Space F := LocalFieldTopology.t2Space F
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : TotallyDisconnectedSpace F := LocalFieldTopology.totallyDisconnectedSpace F
  let : T2Space E := (finiteAlgebraCoordinates (F := F) (E := E)).symm.t2Space
  have hG : IsLocallyProfinite (GeneralLinear n E) :=
    generalLinear_isLocallyProfinite_of_finiteAlgebra (F := F) n
  let : T2Space (GeneralLinear n E) := hG.t2Space
  let : LocallyCompactSpace (GeneralLinear n E) := hG.locallyCompactSpace
  let : SecondCountableTopology (GeneralLinear n E) :=
    generalLinear_secondCountable_of_finiteAlgebra (F := F) n
  have hθ : Continuous (fun x : GeneralLinear n E => entrywiseAut σ n x) :=
    continuous_entrywiseAut σ n
  -- The σ-orbital integrals of `φ Θ` are `Θ(δ)` times those of `φ`.
  have hfun (δ : GeneralLinear n E) (hδ : IsSigmaRegular σ l δ) :
      twistedOrbitFunction (entrywiseAut σ n) δ (fun g => φ g * Θ g) =
        fun q => Θ δ * twistedOrbitFunction (entrywiseAut σ n) δ (⇑φ) q := by
    funext q
    induction q using Quotient.inductionOn with
    | h x =>
      simp only [twistedOrbitFunction_mk]
      rw [hinv δ hδ x, mul_comm]
  -- Some σ-regular element has a nonzero σ-orbital integral.
  obtain ⟨δ₀, hδ₀, μ₀, _, _, ν₀, hc₀, hne₀⟩ : ∃ δ₀ : GeneralLinear n E,
      IsSigmaRegular σ l δ₀ ∧ ∃ (μδ : Measure (sigmaCentralizer σ n δ₀))
        (_ : μδ.IsHaarMeasure) (_ : μδ.IsMulRightInvariant)
        (νδ : Measure (LeftQuotient (sigmaCentralizer σ n δ₀))),
        IsCompatible (sigmaCentralizer σ n δ₀) μ μδ νδ ∧
          sigmaOrbitalIntegral σ n δ₀ νδ ⇑φ ≠ 0 := by
    by_contra hcon
    apply hne
    refine integral_eq_zero_of_sigmaOrbitalIntegral_eq_zero hE μ hint ?_
    intro δ hδ μδ _ _ νδ hcδ
    have hz : sigmaOrbitalIntegral σ n δ νδ ⇑φ = 0 := by
      by_contra hz
      exact hcon ⟨δ, hδ, μδ, inferInstance, inferInstance, νδ, hcδ, hz⟩
    rw [sigmaOrbitalIntegral, twistedOrbitalIntegral] at hz
    rw [sigmaOrbitalIntegral, twistedOrbitalIntegral, hfun δ hδ, integral_const_mul, hz,
      mul_zero]
  have hell₀ : IsSigmaElliptic σ l δ₀ := by
    by_contra h
    exact hne₀ (hvan δ₀ hδ₀ h μ₀ ν₀ hc₀)
  -- Normalized σ-orbital integrals are locally constant on the σ-regular set.
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : LocallyCompactSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_locallyCompactSpace F n
  obtain ⟨-, mE, -, pE, -, dE, -, -⟩ := regularOrbitalProfileExistence F E σ l n hE
    (Measure.haar : Measure (GeneralLinear n F)) μ
  have hconst := dE.isLocallyConstant_twistedOrbitalIntegral hG
    (coefficients ∘ cyclicNorm σ l) (continuous_coefficients.comp (continuous_cyclicNorm σ l))
    (coefficients_cyclicNorm_conj hE.pow_eq_one)
    (fun r g hg => exists_twistedConj_of_cyclicNorm_coefficients_eq hE r.property hg) φ
  let r₀ : {δ : GeneralLinear n E | IsSigmaRegular σ l δ} := ⟨δ₀, hδ₀⟩
  obtain ⟨U, hUo, hr₀U, hU⟩ := hconst.exists_open r₀
  -- Every compatible choice rescales the normalized value by a positive scalar.
  have hscale (s : {δ : GeneralLinear n E | IsSigmaRegular σ l δ})
      (μδ : Measure (sigmaCentralizer σ n s)) [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
      (νδ : Measure (LeftQuotient (sigmaCentralizer σ n s)))
      (hcδ : IsCompatible (sigmaCentralizer σ n s) μ μδ νδ) :
      ∃ c : ℝ≥0, 0 < c ∧ sigmaOrbitalIntegral σ n s νδ ⇑φ =
        (c : ℝ) • sigmaOrbitalIntegral σ n s (mE.quotient s) ⇑φ := by
    let μs : Measure (sigmaCentralizer σ n s) := mE.centralizer s
    let : μs.IsHaarMeasure := mE.haar s
    let : μs.IsMulRightInvariant := mE.rightInvariant s
    have hcs : IsCompatible (sigmaCentralizer σ n s) μ μs (mE.quotient s) := mE.compatible s
    obtain ⟨c, hc, hcf⟩ := exists_twistedOrbitalIntegral_eq_smul_of_isCompatible
      (entrywiseAut σ n) hθ (s : GeneralLinear n E) hcδ hcs
    exact ⟨c, hc, hcf φ⟩
  have hN₀ : sigmaOrbitalIntegral σ n r₀ (mE.quotient r₀) ⇑φ ≠ 0 := by
    obtain ⟨c, -, hcf⟩ := hscale r₀ μ₀ ν₀ hc₀
    intro h0
    exact hne₀ (hcf.trans (by rw [h0, smul_zero]))
  refine ⟨Subtype.val '' U ∩ {δ | IsSigmaElliptic σ l δ},
    (dE.isOpen.isOpenMap_subtype_val U hUo).inter (isOpen_setOf_isSigmaElliptic hE n),
    ⟨δ₀, ⟨r₀, hr₀U, rfl⟩, hell₀⟩, fun δ hδ => hδ.2, ?_⟩
  rintro δ ⟨⟨s, hsU, rfl⟩, -⟩ μδ _ _ νδ hcδ
  obtain ⟨c, hc, hcf⟩ := hscale s μδ νδ hcδ
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  have hs : sigmaOrbitalIntegral σ n s (mE.quotient s) ⇑φ ≠ 0 := by
    have h := hU s hsU
    intro h0
    exact hN₀ (h.symm.trans h0)
  rw [hcf]
  exact smul_ne_zero hc' hs

end Langlands.BaseChange
