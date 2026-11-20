import Langlands.BaseChange.TwistedCharacter.ConjugationAverage
import Langlands.Representation.OrbitSpan
import Mathlib.MeasureTheory.Integral.Prod

/-! # Local constancy of the twisted operator from compact pushforwards -/

noncomputable section

namespace Langlands.BaseChange

open Filter HarmonicAnalysis HarishChandraSchwartz MeasureTheory
open scoped Topology

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The compact subgroup and the given representatives supply a Cartan covering. -/
def HasCartanCoverage (K : Subgroup G) (M : Set G) : Prop :=
  ∀ g : G, ∃ k : K, ∃ m ∈ M, ∃ j : K, g = (k : G) * m * (j : G)

/-- A compact open subgroup of `P` can be conjugated into any specified open subgroup,
uniformly over the Cartan representatives. -/
def HasUniformCartanContraction (P : Subgroup G) (M : Set G) : Prop :=
  ∀ U : OpenSubgroup G, ∃ L : CompactOpenSubgroup P,
    ∀ m ∈ M, ∀ p : L.toSubgroup, m⁻¹ * ((p : P) : G) * m ∈ U

/-- The map for compact averaging of a twisted conjugacy parameter and a right factor. -/
def twistedConjugationProductMap (σ : G ≃* G) (K : Subgroup G) {P : Subgroup G}
    (L : CompactOpenSubgroup P) (y : G) (q : K × L.toSubgroup) : G :=
  (q.1 : G) * y * (σ (q.1 : G))⁻¹ * σ ((q.2 : P) : G)

variable [IsTopologicalGroup G]

/-- The pushforward of the two probability Haar measures under `twistedConjugationProductMap`,
using the canonical Borel measurable spaces. -/
def twistedConjugationPushforward (σ : G ≃* G) (K : Subgroup G) [CompactSpace K]
    {P : Subgroup G} (L : CompactOpenSubgroup P) (y : G) : @Measure G (borel G) := by
  letI : MeasurableSpace G := borel G
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  letI : MeasurableSpace L.toSubgroup := borel _
  haveI : BorelSpace L.toSubgroup := ⟨rfl⟩
  letI : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
  exact Measure.map (twistedConjugationProductMap σ K L y)
    ((normalizedHaar K).prod (normalizedHaar L.toSubgroup))

/-- For each compact open subgroup of `P` the compact pushforward measure is constant
on some neighborhood of `δ`. -/
def HasLocallyConstantTwistedConjugationPushforward (σ : G ≃* G)
    (K : Subgroup G) [CompactSpace K] (P : Subgroup G) (δ : G) : Prop :=
  ∀ L : CompactOpenSubgroup P, ∀ᶠ y in 𝓝 δ,
    twistedConjugationPushforward σ K L y = twistedConjugationPushforward σ K L δ

section Operators

variable [SecondCountableTopology G]
  (σ : G ≃* G) (K : Subgroup G) [CompactSpace K] {P : Subgroup G}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (A : Module.End ℂ V)

private theorem conjugationAverage_dual_eq_integral (hσ : Continuous σ)
    (hA : ∀ g : G, A ∘ₗ ρ g = ρ (σ g) ∘ₗ A)
    (L : CompactOpenSubgroup P) (w : V) (hw : ∀ p : L.toSubgroup, ρ ((p : P) : G) w = w)
    (ℓ : V →ₗ[ℂ] ℂ) (y : G) :
    letI : MeasurableSpace G := borel G
    letI : MeasurableSpace K := borel K
    haveI : BorelSpace K := ⟨rfl⟩
    ℓ (conjugationAverage ρ hρ K (ρ y ∘ₗ A) w) =
      ∫ x, ℓ (ρ x (A w)) ∂(twistedConjugationPushforward σ K L y) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  let _ : MeasurableSpace K := borel K
  have _ : BorelSpace K := ⟨rfl⟩
  let _ : MeasurableSpace L.toSubgroup := borel _
  have _ : BorelSpace L.toSubgroup := ⟨rfl⟩
  let _ : CompactSpace L.toSubgroup := isCompact_iff_compactSpace.mp L.2
  have _ : SecondCountableTopology K := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let coeff (x : G) : ℂ := ℓ (ρ x (A w))
  have hc : Continuous coeff := ((Hecke.orbitMap_locallyConstant ρ (hρ (A w))).comp ℓ).continuous
  let Φ := twistedConjugationProductMap σ K L y
  have hΦ : Continuous Φ := by
    have hk : Continuous fun q : K × L.toSubgroup => (q.1 : G) :=
      continuous_subtype_val.comp continuous_fst
    have hp : Continuous fun q : K × L.toSubgroup => ((q.2 : P) : G) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact ((hk.mul continuous_const).mul (hσ.comp hk).inv).mul (hσ.comp hp)
  have hA' (x : G) : A (ρ x w) = ρ (σ x) (A w) :=
    LinearMap.congr_fun (hA x) w
  have hpoint (k : K) (p : L.toSubgroup) :
      coeff (Φ (k, p)) = ℓ (ρ (k : G) (ρ y (A (ρ (k : G)⁻¹ w)))) := by
    simp only [Φ, twistedConjugationProductMap, coeff, map_mul, Module.End.mul_apply]
    rw [← hA' ((p : P) : G), hw p, ← map_inv σ, ← hA']
  change ℓ (conjugationAverage ρ hρ K (ρ y ∘ₗ A) w) = _
  rw [conjugationAverage_dual]
  calc
    _ = ∫ k : K, (∫ p : L.toSubgroup, coeff (Φ (k, p)) ∂(normalizedHaar L.toSubgroup))
          ∂(normalizedHaar K) := by
      simp [hpoint]
    _ = ∫ q, coeff (Φ q) ∂((normalizedHaar K).prod (normalizedHaar L.toSubgroup)) :=
      (integral_prod _ ((hc.comp hΦ).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).symm
    _ = _ := (integral_map hΦ.aemeasurable hc.aestronglyMeasurable).symm

/-- Cartan coverage, uniform contraction and equality of compact pushforward measures
give local constancy of the twisted operator average for a smooth irreducible representation. -/
theorem conjugationAverage_eventuallyEq_of_pushforward (hσ : Continuous σ)
    (hA : ∀ g : G, A ∘ₗ ρ g = ρ (σ g) ∘ₗ A)
    (hi : ρ.IsIrreducible) (M : Set G) (hCartan : HasCartanCoverage K M)
    (hContract : HasUniformCartanContraction P M)
    (δ : G) (hPush : HasLocallyConstantTwistedConjugationPushforward σ K P δ) :
    letI : MeasurableSpace K := borel K
    haveI : BorelSpace K := ⟨rfl⟩
    ∀ᶠ y in 𝓝 δ, conjugationAverage ρ hρ K (ρ y ∘ₗ A) =
      conjugationAverage ρ hρ K (ρ δ ∘ₗ A) := by
  let _ : MeasurableSpace G := borel G
  let _ : MeasurableSpace K := borel K
  have _ : BorelSpace K := ⟨rfl⟩
  by_cases hV : Subsingleton V
  · exact Filter.Eventually.of_forall fun _ => LinearMap.ext fun _ => Subsingleton.elim _ _
  have _ : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S := Set.range fun j : K => ρ (j : G) v
  have _ : Finite S := ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous
    (continuous_subtype_val : Continuous fun j : K => (j : G))).range_finite
  have hSmooth : IsSmooth ρ := hρ
  choose U hU using hSmooth
  let J := OpenSubgroup.iInfOfFinite (fun w : S => U (w : V))
  obtain ⟨L, hL⟩ := hContract J
  have hw (m : G) (hm : m ∈ M) (j : K) (p : L.toSubgroup) :
      ρ ((p : P) : G) (ρ m (ρ (j : G) v)) = ρ m (ρ (j : G) v) := by
    let jv : S := ⟨ρ (j : G) v, ⟨j, rfl⟩⟩
    have hu : m⁻¹ * ((p : P) : G) * m ∈ U (jv : V) :=
      OpenSubgroup.iInfOfFinite_le (fun w : S => U (w : V)) jv (hL m hm p)
    have hfix : ρ (m⁻¹ * ((p : P) : G) * m) (ρ (j : G) v) = ρ (j : G) v :=
      hU (jv : V) ⟨_, hu⟩
    have he : ((p : P) : G) * m = m * (m⁻¹ * ((p : P) : G) * m) := by group
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hfix]
  filter_upwards [hPush L] with y hy
  let Ty := conjugationAverage ρ hρ K (ρ y ∘ₗ A)
  let Tδ := conjugationAverage ρ hρ K (ρ δ ∘ₗ A)
  have hsame (w : V) (hw' : ∀ p : L.toSubgroup, ρ ((p : P) : G) w = w) : Ty w = Tδ w := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ℓ
    rw [map_sub, sub_eq_zero]
    calc
      ℓ (Ty w) = ∫ x, ℓ (ρ x (A w)) ∂(twistedConjugationPushforward σ K L y) :=
        conjugationAverage_dual_eq_integral σ K ρ hρ A hσ hA L w hw' ℓ y
      _ = ∫ x, ℓ (ρ x (A w)) ∂(twistedConjugationPushforward σ K L δ) := by rw [hy]
      _ = ℓ (Tδ w) := (conjugationAverage_dual_eq_integral σ K ρ hρ A hσ hA L w hw' ℓ δ).symm
  have horbit (g : G) : Ty (ρ g v) = Tδ (ρ g v) := by
    obtain ⟨k, m, hm, j, rfl⟩ := hCartan g
    simp only [mul_assoc, map_mul, Module.End.mul_apply]
    rw [show Ty (ρ (k : G) (ρ m (ρ (j : G) v))) = ρ (k : G) (Ty (ρ m (ρ (j : G) v))) from
        conjugationAverage_equivariant ρ hρ K (ρ y ∘ₗ A) k _,
      show Tδ (ρ (k : G) (ρ m (ρ (j : G) v))) = ρ (k : G) (Tδ (ρ m (ρ (j : G) v))) from
        conjugationAverage_equivariant ρ hρ K (ρ δ ∘ₗ A) k _,
      hsame _ (hw m hm j)]
  have hker : (⊤ : Submodule ℂ V) ≤ LinearMap.ker (Ty - Tδ) := by
    rw [← span_range_orbit_eq_top hi hv, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr (horbit g))
  apply LinearMap.ext
  intro w
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (hker (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ V))))

end Operators

end Langlands.BaseChange
