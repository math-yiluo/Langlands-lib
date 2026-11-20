import Langlands.BaseChange.TwistedCharacterRegularValuesStatement
import Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof
import Langlands.Representation.Character.ModularConjugationProof

/-! # Ordinary character values on conjugacy saturations and in degree one -/

noncomputable section

namespace Langlands.BaseChange.SigmaLiftCharacterIdentity

open MeasureTheory Langlands.HarmonicAnalysis Langlands.JacquetLanglands

section Saturation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The union of the conjugates of an ordinary character window. -/
def conjugacySaturation (U : Set G) : Set G :=
  ⋃ g : G, Distribution.conjugationHomeomorph g '' U

lemma isOpen_conjugacySaturation {U : Set G} (hU : IsOpen U) :
    IsOpen (conjugacySaturation U) :=
  isOpen_iUnion fun g => (Distribution.conjugationHomeomorph g).isOpenMap _ hU

lemma conj_mem_conjugacySaturation {U : Set G} {g : G} (hg : g ∈ U) (x : G) :
    x * g * x⁻¹ ∈ conjugacySaturation U :=
  Set.mem_iUnion.2 ⟨x, g, hg, Distribution.conjugationHomeomorph_apply x g⟩

variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable {V : Type*} [MeasurableSpace G] [BorelSpace G] [AddCommGroup V] [Module ℂ V]
variable {μ : Measure G} [μ.IsHaarMeasure]
variable {π : Representation ℂ G V} {hπ : IsAdmissible π} {a : ℂ}

private lemma evaluate_conjugate {U : Set G}
    (hvalue : ∀ f : SchwartzBruhat G, Function.support f ⊆ U →
      Character.distribution μ π hπ f = a * ∫ y, f y ∂μ)
    (g : G) (f : SchwartzBruhat G)
    (hf : Function.support f ⊆ Distribution.conjugationHomeomorph g '' U) :
    Character.distribution μ π hπ f = a * ∫ y, f y ∂μ := by
  let e := Distribution.conjugationHomeomorph g
  have hpull : Function.support (Hecke.TestFunction.pullback e f) ⊆ U := by
    intro y hy
    have hy' : e y ∈ Function.support f := hy
    obtain ⟨z, hz, heq⟩ := hf hy'
    exact e.injective heq ▸ hz
  have hcharacter := Character.distribution_conjugation_modular μ π hπ g f
  have hintegral : (∫ y, Hecke.TestFunction.pullback e f y ∂μ) =
      ((Distribution.renardModular g : ℝ) : ℂ) * ∫ y, f y ∂μ := by
    exact (Distribution.RenardModular.translation G μ).2 f g g
  have hfactor : ((Distribution.renardModular g : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.2 (by
      exact_mod_cast ((Distribution.RenardModular.regularity G).1 g).ne')
  have h := hvalue _ hpull
  rw [hcharacter, hintegral, mul_left_comm a] at h
  exact mul_left_cancel₀ hfactor h

/-- The same ordinary value evaluates every test function supported in the conjugacy saturation. -/
lemma evaluate_saturation {U : Set G} (hU : IsOpen U)
    (hvalue : ∀ f : SchwartzBruhat G, Function.support f ⊆ U →
      Character.distribution μ π hπ f = a * ∫ y, f y ∂μ)
    (f : SchwartzBruhat G) (hf : Function.support f ⊆ conjugacySaturation U) :
    Character.distribution μ π hπ f = a * ∫ y, f y ∂μ := by
  classical
  let D := Character.distribution μ π hπ - a • Distribution.ofMeasure μ
  have hD : D ∈ Distribution.supportedOn (conjugacySaturation U)ᶜ := by
    apply Distribution.openRestrictionLocality
    intro y hy
    obtain ⟨g, hgy⟩ := Set.mem_iUnion.1 (not_not.mp hy)
    let U' := Distribution.conjugationHomeomorph g '' U
    have hU' : IsOpen U' := (Distribution.conjugationHomeomorph g).isOpenMap _ hU
    refine ⟨U', hU', hgy, ?_⟩
    apply LinearMap.ext
    intro φ
    rw [Distribution.restrictOpen_apply]
    have hsupp : Function.support (SchwartzBruhat.extendZero hU' φ) ⊆ U' := by
      intro z hz
      by_contra hz'
      exact hz (SchwartzBruhat.extendZero_apply_of_not_mem hU' φ hz')
    have hz := evaluate_conjugate hvalue g _ hsupp
    change Character.distribution μ π hπ _ - a * Distribution.ofMeasure μ _ = 0
    rw [Distribution.ofMeasure_apply, hz, sub_self]
  have h := hD f (fun y hy => by
    by_contra hfy
    exact hy (hf hfy))
  change Character.distribution μ π hπ f - a * Distribution.ofMeasure μ f = 0 at h
  rw [Distribution.ofMeasure_apply, sub_eq_zero] at h
  exact h

end Saturation

section DegreeOne

universe u uV

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ)

/-- The ordinary regular character value follows by using the identity intertwiner in degree one. -/
lemma ordinary_regular_values (hregular : TwistedCharacterRegularValuesStatement.{u, u, uV}) :
    haveI := LocalFieldTopology.generalLinear_t2Space F n
    haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
    haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π), π.IsIrreducible →
      ∀ γ : GeneralLinear n F, IsRegularSemisimple γ → ∃ a : ℂ, HasCharacterValue π hπ γ a := by
  intro V _ _ π hπ hirr γ hγ
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let A : SigmaIntertwiner (1 : F ≃ₐ[F] F) n π :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => by
      ext v
      simp [entrywiseAut_one_apply])
  have hσ : IsSigmaRegular (1 : F ≃ₐ[F] F) 1 γ := by
    refine ⟨γ, ⟨1, ?_⟩, hγ⟩
    have hbase : baseChange F F n γ = γ := by
      apply Units.ext
      ext i j
      simp [baseChange_apply_apply]
    rw [cyclicNorm_succ, cyclicNorm_zero, pow_zero, entrywiseAut_one_apply, hbase]
    simp
  obtain ⟨a, ha⟩ := hregular F F 1 1 n (isCyclicAlgebra_one (F := F)) π hπ hirr A γ hσ
  exact ⟨a, (hasTwistedCharacterValue_one_iff π hπ γ a).1 ha⟩

end DegreeOne

end Langlands.BaseChange.SigmaLiftCharacterIdentity
