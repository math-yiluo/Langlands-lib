import Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.Representation.Induction.SplitKernelCharacter
import Langlands.Representation.Derivative.MinusVanishing
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
import Langlands.Group.GL.MirabolicModulusProof

/-!
# The source-rank-one boundary of BZ77 Proposition 4.13(c)
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MeasureTheory MeasureTheory.Measure
open scoped TensorProduct NNReal

namespace Langlands.Derivative.MirabolicProductMinus

open GeneralLinear GeneralLinear.Mirabolic GeneralLinear.Mirabolic.MixedProduct
  HarmonicAnalysis

universe uF uV

/-! ## Transport along equal subgroups and trivial localizations -/

section Transport

variable {G : Type*} [Group G]

/-- Character relations only depend on the subgroup and the character values. -/
theorem relations_congr {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) {U U' : Subgroup G} (h : U = U') (θ : U →* ℂˣ)
    (θ' : U' →* ℂˣ) (hθ : ∀ u : U, θ' (Subgroup.inclusion h.le u) = θ u) :
    Jacquet.Localization.relations ρ U θ = Jacquet.Localization.relations ρ U' θ' := by
  subst h
  obtain rfl : θ' = θ := MonoidHom.ext fun u => hθ u
  rfl

/-- A compact open subgroup basis at the identity transports along equal subgroups. -/
theorem compactOpenBasis_congr [TopologicalSpace G] {U U' : Subgroup G} (h : U = U')
    (hU : ∀ O : Set U, IsOpen O → (1 : U) ∈ O →
      ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ (K : Set U) ⊆ O) :
    ∀ O : Set U', IsOpen O → (1 : U') ∈ O →
      ∃ K : OpenSubgroup U', IsCompact (K : Set U') ∧ (K : Set U') ⊆ O := by
  subst h
  exact hU

/-- A cover by compact open subgroups transports along equal subgroups. -/
theorem compactOpenCover_congr [TopologicalSpace G] {U U' : Subgroup G} (h : U = U')
    (hU : ∀ g : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ g ∈ K) :
    ∀ g : U', ∃ K : OpenSubgroup U', IsCompact (K : Set U') ∧ g ∈ K := by
  subst h
  exact hU

/-- The Haar modulus of a conjugation transports along equal subgroups. -/
theorem mulEquivHaarChar_normalizerConj_congr [TopologicalSpace G] [IsTopologicalGroup G]
    {U U' : Subgroup G} (h : U = U') [m : MeasurableSpace U] [b : BorelSpace U]
    [LocallyCompactSpace U] [m' : MeasurableSpace U'] [b' : BorelSpace U']
    [LocallyCompactSpace U'] (g : G) (hg : g ∈ Subgroup.normalizer (U : Set G))
    (hg' : g ∈ Subgroup.normalizer (U' : Set G)) :
    mulEquivHaarChar (HaarModulus.normalizerConj U ⟨g, hg⟩) =
      mulEquivHaarChar (HaarModulus.normalizerConj U' ⟨g, hg'⟩) := by
  subst h
  obtain rfl : m = m' := b.measurable_eq.trans b'.measurable_eq.symm
  rfl

/-- On a subsingleton group every topological automorphism has Haar modulus one. -/
theorem mulEquivHaarChar_of_subsingleton {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
    [Subsingleton K] (φ : K ≃ₜ* K) : mulEquivHaarChar φ = 1 := by
  obtain rfl : φ = ContinuousMulEquiv.refl K := by
    ext x
    exact Subsingleton.elim _ _
  exact mulEquivHaarChar_refl

/-- If the subgroup acts through the character, the localized quotient is the
whole carrier. -/
def localizationTrivialEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (h : ∀ (u : U) (v : V), ρ u v = (θ u : ℂ) • v) :
    Jacquet.Localization.Coinvariants ρ U θ ≃ₗ[ℂ] V :=
  Submodule.quotEquivOfEqBot _ (by
    rw [eq_bot_iff]
    apply Submodule.span_le.2
    rintro _ ⟨⟨u, v⟩, rfl⟩
    change ρ u v - (θ u : ℂ) • v ∈ (⊥ : Submodule ℂ V)
    rw [h, sub_self]
    exact Submodule.zero_mem _)

@[simp] theorem localizationTrivialEquiv_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (U : Subgroup G) (θ : U →* ℂˣ)
    (h : ∀ (u : U) (v : V), ρ u v = (θ u : ℂ) • v) (v : V) :
    localizationTrivialEquiv ρ U θ h (Jacquet.Localization.mk ρ U θ v) = v := rfl

/-- If every group element acts trivially, the coinvariants are the whole carrier. -/
def coinvariantsTrivialEquiv {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ∀ (g : G) (v : V), ρ g v = v) :
    Representation.Coinvariants ρ ≃ₗ[ℂ] V :=
  Submodule.quotEquivOfEqBot _ (by
    rw [eq_bot_iff]
    apply Submodule.span_le.2
    rintro _ ⟨⟨g, v⟩, rfl⟩
    change ρ g v - v ∈ (⊥ : Submodule ℂ V)
    rw [h, sub_self]
    exact Submodule.zero_mem _)

@[simp] theorem coinvariantsTrivialEquiv_mk {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ∀ (g : G) (v : V), ρ g v = v) (v : V) :
    coinvariantsTrivialEquiv ρ h (Representation.Coinvariants.mk ρ v) = v := rfl

/-- The trivial-coinvariant identification commutes with coinvariant maps. -/
theorem coinvariantsTrivialEquiv_map {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (hρ : ∀ (g : G) (v : V), ρ g v = v) (hτ : ∀ (g : G) (w : W), τ g w = w)
    (f : ρ.IntertwiningMap τ) (z : Representation.Coinvariants ρ) :
    coinvariantsTrivialEquiv τ hτ (Representation.Coinvariants.map ρ τ f z) =
      f (coinvariantsTrivialEquiv ρ hρ z) := by
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective ρ z
  rfl

/-- Two linear identifications with one model space, which turn both actions into
the same operators, give an equivalence of representations. -/
def equivOfCommonModel {U V W : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (φ : G → U →ₗ[ℂ] U) (eV : V ≃ₗ[ℂ] U) (eW : W ≃ₗ[ℂ] U)
    (hV : ∀ g v, eV (ρ g v) = φ g (eV v)) (hW : ∀ g w, eW (σ g w) = φ g (eW w)) :
    ρ.Equiv σ :=
  Representation.Equiv.mk (eV.trans eW.symm) fun g => LinearMap.ext fun v => by
    apply eW.injective
    change eW (eW.symm (eV (ρ g v))) = eW (σ g (eW.symm (eV v)))
    rw [hW, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hV]

theorem equivOfCommonModel_apply {U V W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (φ : G → U →ₗ[ℂ] U) (eV : V ≃ₗ[ℂ] U) (eW : W ≃ₗ[ℂ] U)
    (hV : ∀ g v, eV (ρ g v) = φ g (eV v)) (hW : ∀ g w, eW (σ g w) = φ g (eW w)) (v : V) :
    equivOfCommonModel φ eV eW hV hW v = eW.symm (eV v) := rfl

/-- Composites `eW⁻¹ ∘ eV` commute with maps that both identifications turn into
the same model map. -/
theorem symm_comp_natural {U U' V V' W W' : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
    [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (eV : V ≃ₗ[ℂ] U) (eW : W ≃ₗ[ℂ] U) (eV' : V' ≃ₗ[ℂ] U') (eW' : W' ≃ₗ[ℂ] U')
    (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W') (m : U →ₗ[ℂ] U')
    (hf : ∀ v, eV' (f v) = m (eV v)) (hg : ∀ w, eW' (g w) = m (eW w)) (v : V) :
    eW'.symm (eV' (f v)) = g (eW.symm (eV v)) := by
  apply eW'.injective
  rw [LinearEquiv.apply_symm_apply, hg, LinearEquiv.apply_symm_apply, hf]

end Transport

/-- The three normalizing scalars `ν^(-1/2)`, `(ν⁻¹)⁻¹` and `ν^(-1/2)` multiply to `1`. -/
theorem half_mul_inv_inv_mul_half (d : ℝ≥0ˣ) :
    ((((d : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (((((d : ℝ≥0)⁻¹)⁻¹ : ℝ≥0) : ℝ) : ℂ) *
      ((((d : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
  have hd : 0 < ((d : ℝ≥0) : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 d.ne_zero)
  have h : ((d : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) * ((d : ℝ≥0) : ℝ) *
      ((d : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [mul_comm (((d : ℝ≥0) : ℝ) ^ _) ((d : ℝ≥0) : ℝ), mul_assoc, ← Real.rpow_add hd,
      show (-(1 / 2 : ℝ) + -(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one,
      mul_inv_cancel₀ hd.ne']
  rw [inv_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h, Complex.ofReal_one]

/-- Three scalars with product `1` act trivially in succession. -/
theorem smul_smul_smul_of_mul_eq_one {M : Type*} [AddCommGroup M] [Module ℂ M] (a b c : ℂ)
    (y : M) (h : a * b * c = 1) : a • b • c • y = y := by
  rw [smul_smul, smul_smul, h, one_smul]

/-! ## Split kernels with trivial intersection -/

section TrivialIntersection

open Induction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]
variable {L : Type*} [Group L] [TopologicalSpace L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ) (θ : SmoothCharacter ℂ r.ker)
variable (hI : ∀ i : H.comap r.ker.subtype, i = 1)

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TopologicalSpace L] in
include hI in
/-- A character is trivial on a trivial kernel intersection. -/
theorem character_trivial_of_trivial :
    ∀ i : H.comap r.ker.subtype, θ.toMonoidHom i = 1 := fun i => by
  rw [hI i, OneMemClass.coe_one, map_one]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [TopologicalSpace L] in
include hI in
/-- The restricted inducing representation of a trivial intersection is trivial. -/
theorem inducing_trivial_of_trivial :
    ∀ (i : H.comap r.ker.subtype) (v : V), σ.comp (r.ker.subtype.subgroupComap H) i v = v :=
  fun i v => by rw [hI i, map_one, Module.End.one_apply]

variable [MeasurableSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype))]
  [BorelSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype))]
variable (ν : Measure (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)))
  [IsFiniteMeasureOnCompacts ν]
variable [LocallyCompactSpace r.ker] [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
  ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
variable (μN : Measure r.ker) (μI : Measure (H.comap r.ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : QuotientIntegration.IsCompatible (H.comap r.ker.subtype) μN μI ν)

/-- With trivial kernel intersection, the `θ`-localized quotient of compact
induction is the inducing space itself, through the twisted relative integral. -/
def trivialSplitKernelEquiv :
    Jacquet.Localization.Coinvariants (compactInduced H σ) r.ker θ.toMonoidHom ≃ₗ[ℂ] V :=
  (splitKernelCharacterEquiv r s hrs hr hs H hH hsH σ hσ θ
      (character_trivial_of_trivial r H θ hI) ν hBasis μN μI hCompatible).trans
    (coinvariantsTrivialEquiv _ (inducing_trivial_of_trivial r H σ hI))

theorem trivialSplitKernelEquiv_mk (f : CompactFunctions H σ) :
    trivialSplitKernelEquiv r s hrs hr hs H hH hsH σ hσ θ hI ν hBasis μN μI hCompatible
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f) =
      coinvariantsTrivialEquiv _ (inducing_trivial_of_trivial r H σ hI)
        (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ
          (character_trivial_of_trivial r H θ hI) ν f) := rfl

/-- Section translation: a section value whose inverse conjugation fixes `θ`
acts through the inducing representation, scaled by the inverse Haar modulus of
its inverse conjugation on the kernel. -/
theorem trivialSplitKernelEquiv_section (l : L)
    (hθl : ∀ n : r.ker, θ.toMonoidHom (splitKernelConjugation r s l n) = θ.toMonoidHom n)
    (f : CompactFunctions H σ) :
    trivialSplitKernelEquiv r s hrs hr hs H hH hsH σ hσ θ hI ν hBasis μN μI hCompatible
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom
          (compactInduced H σ (s l) f)) =
      ((((mulEquivHaarChar (splitKernelConjugation r s l))⁻¹ : ℝ≥0) : ℝ) : ℂ) •
        σ ⟨s l, hsH l⟩
          (trivialSplitKernelEquiv r s hrs hr hs H hH hsH σ hσ θ hI ν hBasis μN μI hCompatible
            (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f)) := by
  have : LocallyCompactSpace (H.comap r.ker.subtype) :=
    (isClosed_splitKernelIntersection r H hH).locallyCompactSpace
  have : Subsingleton (H.comap r.ker.subtype) := ⟨fun a b => (hI a).trans (hI b).symm⟩
  rw [trivialSplitKernelEquiv_mk, trivialSplitKernelEquiv_mk,
    splitKernelCharacterIntegral_section r s hrs hr hs H hH hsH σ hσ θ _ ν hCompatible l hθl f,
    mulEquivHaarChar_of_subsingleton, one_div, map_smul]
  obtain ⟨v, hv⟩ := Representation.Coinvariants.mk_surjective _
    (splitKernelCharacterIntegral r s hrs hr hs H hH hsH σ hσ θ
      (character_trivial_of_trivial r H θ hI) ν f)
  rw [← hv]
  rfl

/-- The identification commutes with every coefficient intertwiner. -/
theorem trivialSplitKernelEquiv_natural {W : Type*} [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ H W} (hτ : IsSmooth τ) (T : σ.IntertwiningMap τ)
    (f : CompactFunctions H σ) :
    trivialSplitKernelEquiv r s hrs hr hs H hH hsH τ hτ θ hI ν hBasis μN μI hCompatible
        (Jacquet.Localization.mk (compactInduced H τ) r.ker θ.toMonoidHom
          (compactInducedMap H T f)) =
      T (trivialSplitKernelEquiv r s hrs hr hs H hH hsH σ hσ θ hI ν hBasis μN μI hCompatible
        (Jacquet.Localization.mk (compactInduced H σ) r.ker θ.toMonoidHom f)) := by
  rw [trivialSplitKernelEquiv_mk, trivialSplitKernelEquiv_mk,
    splitKernelCharacterIntegral_natural r s hrs hr hs H hH hsH σ hσ θ _ ν hτ T f]
  exact coinvariantsTrivialEquiv_map _ _ (splitKernelInducingMap r H T) _

end TrivialIntersection

/-! ## The explicit rank cast of the mirabolic group -/

section RankCast

variable {R : Type*} [CommRing R]

/-- The identity `P_(b+1) → P_(a+1)` along a rank equality `a = b`. -/
def mirabolicCastHom {a b : ℕ} (h : a = b) : mirabolic b R →* mirabolic a R := by
  subst h
  exact MonoidHom.id _

theorem mirabolicCastHom_apply {a b : ℕ} (h : a = b) (x : mirabolic b R) (i j : Fin (a + 1)) :
    (mirabolicCastHom h x).val.val i j =
      x.val.val (Fin.cast (by rw [h]) i) (Fin.cast (by rw [h]) j) := by
  subst h
  rfl

theorem continuous_mirabolicCastHom [TopologicalSpace R] {a b : ℕ} (h : a = b) :
    Continuous (mirabolicCastHom (R := R) h) := by
  subst h
  exact continuous_id

/-- For `k = 0`, the mirabolic block of the case (II) projection undoes the rank cast. -/
theorem leftUnitProjection_mirabolicCastHom (k : ℕ) (x : mirabolic (k + 0) R) :
    leftUnitProjection k (mirabolicCastHom (Nat.add_comm 0 k) x) = x := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e : ∀ m : Fin (k + 1),
      Fin.cast (show 0 + k + 1 = k + 0 + 1 by omega) (leftIndex 0 k (Sum.inr m)) = m :=
    fun m => Fin.ext (by simp)
  rw [leftUnitProjection_apply, mirabolicCastHom_apply, e, e]

end RankCast

/-! ## The case (III) subgroup for `r = 0` -/

section RightZero

variable {R : Type*} [CommRing R] {m : ℕ}

theorem rightIndex_zero_inr (i : Fin m) :
    rightIndex m 0 (Sum.inr i) = (i : Fin (m + 0)).castSucc :=
  Fin.ext (by simp)

/-- For `r = 0`, the Levi element `diag(l, 1)` lies in the case (III) subgroup. -/
theorem levi_mem_rightSubgroup_zero (l : GeneralLinear (m + 0) R) :
    levi l ∈ rightSubgroup m 0 R := by
  rw [mem_rightSubgroup_iff_entry]
  intro i j
  obtain rfl : j = Fin.last 0 := Fin.ext (by omega)
  rw [rightIndex_last, rightIndex_zero_inr]
  exact levi_last l i

/-- For `r = 0`, the case (III) projection of `diag(l, 1)` is `(1, l)`. -/
theorem rightProjection_levi_zero (l : GeneralLinear (m + 0) R) :
    rightProjection (k := m) (r := 0) (R := R)
        (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup m 0 R) =
      (1, l) := by
  refine Prod.ext (rankOne_eq_one _) ?_
  apply Units.ext
  ext i j
  rw [rightProjection_gl_apply, rightIndex_zero_inr, rightIndex_zero_inr]
  exact levi_first l i j

/-- For `r = 0`, the case (III) subgroup meets the radical only in the identity. -/
theorem eq_one_of_mem_rightSubgroup_zero {g : mirabolic (m + 0) R}
    (hg : g ∈ rightSubgroup m 0 R) (hp : g ∈ (projection (n := m + 0) (F := R)).ker) :
    g = 1 := by
  rw [ker_projection] at hp
  have hc : radicalCoordinates (⟨g, hp⟩ : radical (m + 0) R) = 0 := by
    funext i
    have h := (mem_rightSubgroup_iff_entry (k := m) (r := 0) (R := R) g).1 hg i (Fin.last 0)
    rw [rightIndex_last, rightIndex_zero_inr] at h
    exact h
  have h := radicalElement_coordinates (⟨g, hp⟩ : radical (m + 0) R)
  rw [hc, radicalElement_zero] at h
  exact (congrArg Subtype.val h).symm

end RightZero

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-! ## Radical boxes and the Levi Haar modulus -/

section Padic

/-- Radical boxes form a basis of compact open subgroups at the identity. -/
theorem radical_compactOpenBasis (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ O : Set (radical (m + 1) F.Carrier), IsOpen O → (1 : radical (m + 1) F.Carrier) ∈ O →
      ∃ K : OpenSubgroup (radical (m + 1) F.Carrier),
        IsCompact (K : Set (radical (m + 1) F.Carrier)) ∧
          (K : Set (radical (m + 1) F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro O hO h1
  have h0 : radicalElement ⁻¹' O ∈ nhds (0 : Fin (m + 1) → F.Carrier) := by
    apply (hO.preimage continuous_radicalElement).mem_nhds
    rw [Set.mem_preimage, radicalElement_zero]
    exact h1
  obtain ⟨N, hN⟩ := Mirabolic.exists_latticeBox_subset T h0
  refine ⟨Mirabolic.radicalBox T m N, Mirabolic.isCompact_radicalBox T m N, fun u hu => ?_⟩
  have h := hN ((Mirabolic.mem_radicalBox T).mp hu)
  rwa [Set.mem_preimage, radicalElement_coordinates] at h

/-- Every radical element lies in a compact open radical box. -/
theorem radical_compactOpenCover (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ u : radical (m + 1) F.Carrier, ∃ K : OpenSubgroup (radical (m + 1) F.Carrier),
      IsCompact (K : Set (radical (m + 1) F.Carrier)) ∧ u ∈ K := by
  let := T.topology
  intro u
  obtain ⟨M, hM⟩ := Mirabolic.exists_mem_latticeBox T (radicalCoordinates u)
  exact ⟨Mirabolic.radicalBox T m M, Mirabolic.isCompact_radicalBox T m M, hM⟩

/-- Conjugation `u ↦ diag(l,1)⁻¹ u diag(l,1)` scales Haar measure on the radical
by `|det l|⁻¹`. -/
theorem mulEquivHaarChar_conj_levi_inv (T : F.TopologicalData) (n : ℕ)
    (l : GeneralLinear n F.Carrier)
    (hl : (levi l)⁻¹ ∈ Subgroup.normalizer (radical n F.Carrier : Set (mirabolic n F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
    letI : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
    letI : MeasurableSpace (radical n F.Carrier) := borel _
    haveI : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
    mulEquivHaarChar (HaarModulus.normalizerConj (radical n F.Carrier) ⟨(levi l)⁻¹, hl⟩) =
      (T.determinantNorm n l : ℝ≥0)⁻¹ := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
  let : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical n F.Carrier) := borel _
  have : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  have e : (⟨(levi l)⁻¹, hl⟩ :
      Subgroup.normalizer (radical n F.Carrier : Set (mirabolic n F.Carrier))) =
      Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv l⁻¹) :=
    Subtype.ext (map_inv levi l).symm
  have h := congrArg (fun χ : GeneralLinear n F.Carrier →* ℝ≥0ˣ => ((χ l⁻¹ : ℝ≥0ˣ) : ℝ≥0))
    (leviRadical_haarCharacter F T n)
  rw [e]
  refine h.trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val]

/-- For `r = 0`, the normalized case (III) inducing action of `diag(l, 1)` is
`|det l|^(-1/2) (1 ⊗ ρ(l))`. -/
theorem twist_rightInducing_levi_zero (T : F.TopologicalData) (k : ℕ) {W V : Type*}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (mirabolic 0 F.Carrier) W)
    (ρ : Representation ℂ (GeneralLinear k F.Carrier) V) (l : GeneralLinear (k + 0) F.Carrier)
    (w : W ⊗[ℂ] V) :
    letI := T.topology
    twist (T.rightCharacter k 0).toMonoidHom (rightInducingRepresentation τ ρ)
        ⟨levi l, levi_mem_rightSubgroup_zero l⟩ w =
      ((((T.determinantNorm k l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        TensorProduct.map LinearMap.id (ρ l) w := by
  let := T.topology
  have h : twist (T.rightCharacter k 0).toMonoidHom (rightInducingRepresentation τ ρ)
      ⟨levi l, levi_mem_rightSubgroup_zero l⟩ w =
      (T.rightLeviCharacter k 0 (rightProjection (k := k) (r := 0) (R := F.Carrier)
          (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)) : ℂ) •
        TensorProduct.map (τ (rightProjection (k := k) (r := 0) (R := F.Carrier)
            (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)).1)
          (ρ (rightProjection (k := k) (r := 0) (R := F.Carrier)
            (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)).2) w := rfl
  rw [h, rightProjection_levi_zero, T.rightLeviCharacter_zero_right_apply]
  dsimp only
  rw [map_one]
  rfl

end Padic

/-! ## The target side: `(Ψ⁻τ) × (ρ|P)` at `r = 0` -/

section Target

/-- The target functor with its rank cast replaced by the explicit pullback. -/
abbrev rightBoundaryQuotient (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + 0) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T 0).prod (generalLinearRestriction T k) ⋙
    T.leftMixedProductFunctor 0 k ⋙
      Mirabolic.continuousPullbackFunctor (mirabolicCastHom (Nat.add_comm 0 k))
        (continuous_mirabolicCastHom (Nat.add_comm 0 k))

theorem psiMinus_zero_trivial (T : F.TopologicalData)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier))
    (u : radical 0 F.Carrier) (v : A) :
    letI := T.topology
    A.representation (u : mirabolic 0 F.Carrier) v =
      (((1 : radical 0 F.Carrier →* ℂˣ) u : ℂˣ) : ℂ) • v := by
  let := T.topology
  rw [Subsingleton.elim u 1, OneMemClass.coe_one, map_one, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- Evaluation at `1` on `(Ψ⁻τ) × (ρ|P)` at `r = 0`, where the inducing
subgroup is the whole group. -/
def rightBoundaryTopEquiv (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + k + 1)
  Induction.compactInducedTopEquiv (leftSubgroup 0 k F.Carrier) mem_leftSubgroup_zero
    (twist (T.leftCharacter 0 k).toMonoidHom
      (leftInducingRepresentation ((Mirabolic.psiMinus T 0).obj X.1).representation
        ((generalLinearRestriction T k).obj X.2).representation))
    ((isSmooth_twist_iff _ _ (T.leftCharacter 0 k).isOpen_ker).mpr
      (isSmooth_leftInducingRepresentation ((Mirabolic.psiMinus T 0).obj X.1).isSmooth
        ((generalLinearRestriction T k).obj X.2).isSmooth))

/-- The carrier of `(Ψ⁻τ) × (ρ|P)` at `r = 0`: evaluation at `1`, followed by the
trivial `V_1`-quotient of `τ`. -/
def rightBoundaryQuotientEquiv (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    (rightBoundaryQuotient.{uF, uV} T k).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  (rightBoundaryTopEquiv T k X).toLinearEquiv.trans
    (TensorProduct.congr
      (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
        (psiMinus_zero_trivial T X.1))
      (LinearEquiv.refl ℂ X.2))

theorem rightBoundaryQuotientEquiv_apply (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (x : letI := T.topology; (rightBoundaryQuotient.{uF, uV} T k).obj X) :
    letI := T.topology
    rightBoundaryQuotientEquiv T k X x =
      TensorProduct.congr
        (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
          (psiMinus_zero_trivial T X.1))
        (LinearEquiv.refl ℂ X.2) ((rightBoundaryTopEquiv T k X).toLinearEquiv x) := rfl

/-- The identification turns the action of `g ∈ P_(k+1)` into `1 ⊗ ρ(g)`. -/
theorem rightBoundaryQuotientEquiv_action (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (g : mirabolic (k + 0) F.Carrier)
    (x : letI := T.topology; (rightBoundaryQuotient.{uF, uV} T k).obj X) :
    letI := T.topology
    rightBoundaryQuotientEquiv T k X
        (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) =
      TensorProduct.map LinearMap.id (X.2.representation g.val)
        (rightBoundaryQuotientEquiv T k X x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (0 + k + 1)
  let X' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic k F.Carrier) :=
    ((Mirabolic.psiMinus T 0).obj X.1, (generalLinearRestriction T k).obj X.2)
  let g' : leftSubgroup 0 k F.Carrier :=
    Induction.topHom (leftSubgroup 0 k F.Carrier) mem_leftSubgroup_zero
      (mirabolicCastHom (Nat.add_comm 0 k) g)
  let eX := TensorProduct.congr
    (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
      (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)
  have hB : T.leftMixedEval X' (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) 1 =
      T.leftMixedEval X' x (mirabolicCastHom (Nat.add_comm 0 k) g) :=
    (T.leftMixedProductFunctor_action X' (mirabolicCastHom (Nat.add_comm 0 k) g) x 1).trans
      (congrArg _ (one_mul _))
  have hc0 : T.leftLeviCharacter 0 k (leftProjection g') = 1 := by
    rw [T.leftLeviCharacter_zero_left k]
    rfl
  have hC : T.leftMixedEval X' x (mirabolicCastHom (Nat.add_comm 0 k) g) =
      leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1) := by
    have := T.leftMixedEval_covariant X' x g' 1
    rw [mul_one, hc0, Units.val_one, one_smul] at this
    exact this
  have e₁ : (leftProjection g').1 = 1 := Units.ext (Matrix.ext fun i => Fin.elim0 i)
  have e₂ : (leftProjection g').2 = g := leftUnitProjection_mirabolicCastHom k g
  have key : eX.toLinearMap ∘ₗ
        leftInducingRepresentation X'.1.representation X'.2.representation g' =
      TensorProduct.map LinearMap.id (X.2.representation g.val) ∘ₗ eX.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change TensorProduct.congr _ _ (X'.1.representation (leftProjection g').1 a ⊗ₜ[ℂ]
        X'.2.representation (leftProjection g').2 b) = _
    rewrite [e₁, e₂, map_one X'.1.representation]
    rfl
  have h1 : ∀ y : (rightBoundaryQuotient.{uF, uV} T k).obj X,
      rightBoundaryQuotientEquiv T k X y = eX (T.leftMixedEval X' y 1) := fun y => rfl
  have h2 : eX (T.leftMixedEval X'
        (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) 1) =
      eX (leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1)) := congrArg eX (hB.trans hC)
  have h3 : eX (leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1)) =
      TensorProduct.map LinearMap.id (X.2.representation g.val)
        (eX (T.leftMixedEval X' x 1)) :=
    LinearMap.congr_fun key (T.leftMixedEval X' x 1)
  exact ((h1 _).trans h2).trans (h3.trans (congrArg _ (h1 x).symm))

/-- The identification is natural in both inputs. -/
theorem rightBoundaryQuotientEquiv_natural (T : F.TopologicalData) (k : ℕ)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y)
    (x : letI := T.topology; (rightBoundaryQuotient.{uF, uV} T k).obj X) :
    letI := T.topology
    rightBoundaryQuotientEquiv T k Y
        (SmoothRep.hom ((rightBoundaryQuotient.{uF, uV} T k).map φ) x) =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
        (rightBoundaryQuotientEquiv T k X x) := by
  let := T.topology
  have h : (rightBoundaryTopEquiv T k Y).toLinearEquiv
      (SmoothRep.hom ((rightBoundaryQuotient.{uF, uV} T k).map φ) x) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T 0).map φ.1)).toLinearMap
        (SmoothRep.hom φ.2).toLinearMap ((rightBoundaryTopEquiv T k X).toLinearEquiv x) := rfl
  have key : (TensorProduct.congr
        (localizationTrivialEquiv Y.1.representation (radical 0 F.Carrier) 1
          (psiMinus_zero_trivial T Y.1)) (LinearEquiv.refl ℂ Y.2)).toLinearMap ∘ₗ
        TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T 0).map φ.1)).toLinearMap
          (SmoothRep.hom φ.2).toLinearMap =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap ∘ₗ
        (TensorProduct.congr
          (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
            (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ a
    rfl
  exact (congrArg (TensorProduct.congr
    (localizationTrivialEquiv Y.1.representation (radical 0 F.Carrier) 1
      (psiMinus_zero_trivial T Y.1)) (LinearEquiv.refl ℂ Y.2)) h).trans
    (LinearMap.congr_fun key _)

end Target

/-- The actual rank transport is pullback along the explicit cast homomorphism. -/
def mirabolicRankCastIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ≅
      Mirabolic.continuousPullbackFunctor (mirabolicCastHom h)
        (continuous_mirabolicCastHom h) := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-! ## The boundary clause -/

section Boundary

open Induction

set_option maxHeartbeats 400000 in
/-- BZ77 4.13(c) at source rank one: `Φ⁻(τ × ρ) ≅ (Ψ⁻τ) × (ρ|P)` naturally,
for `τ` on `P_1` and `ρ` on `GL_(k+1)`. -/
theorem rightPhiBoundary (T : F.TopologicalData) : RightPhiBoundary.{uF, uV} F T := by
  let := T.topology
  intro ψ k
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + 1 + 0 + 1)
  let := T.generalLinearLocallyCompactSpace (k + 1 + 0 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + 1 + 0) (F := F.Carrier)
  -- The split group data: `G = P_(k+2)`, `r = projection`, `s = levi`, `H` of case (III).
  let r := projection (n := k + 1 + 0) (F := F.Carrier)
  let s := levi (n := k + 1 + 0) (F := F.Carrier)
  let H := rightSubgroup (k + 1) 0 F.Carrier
  have hrs : ∀ l, r (s l) = l := projection_levi
  have hr : Continuous r := GeneralLinear.Mirabolic.continuous_projection
  have hs : Continuous s := continuous_levi
  have hH : IsClosed (H : Set (mirabolic (k + 1 + 0) F.Carrier)) := rightSubgroup_isClosed
  have hsH : ∀ l, s l ∈ H := levi_mem_rightSubgroup_zero
  have hNr : r.ker = radical (k + 1 + 0) F.Carrier := ker_projection
  let θ : SmoothCharacter ℂ r.ker :=
    { toMonoidHom := (T.mirabolicTheta ψ (k + 0)).comp (Subgroup.inclusion hNr.le)
      isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ (k + 0)).preimage
        (continuous_inclusion hNr.le) }
  have hI : ∀ i : H.comap r.ker.subtype, i = 1 := fun i =>
    Subtype.ext (Subtype.ext (eq_one_of_mem_rightSubgroup_zero (m := k + 1) i.2 i.1.2))
  -- Measures on the kernel, the trivial intersection and the quotient.
  have hNc : IsClosed (r.ker : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  let : LocallyCompactSpace r.ker := hNc.locallyCompactSpace
  have hIc : IsClosed ((H.comap r.ker.subtype : Subgroup r.ker) : Set r.ker) :=
    hH.preimage continuous_subtype_val
  let : LocallyCompactSpace (H.comap r.ker.subtype) := hIc.locallyCompactSpace
  let : MeasurableSpace r.ker := borel _
  have : BorelSpace r.ker := ⟨rfl⟩
  let : MeasurableSpace (H.comap r.ker.subtype) := borel _
  have : BorelSpace (H.comap r.ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := ⟨rfl⟩
  have hBasis := compactOpenBasis_congr hNr.symm (radical_compactOpenBasis T (k + 0))
  have hCover := compactOpenCover_congr hNr.symm (radical_compactOpenCover T (k + 0))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure r.ker := haar
  let μI : Measure (H.comap r.ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The Levi Haar modulus and the invariance of `θ`.
  have hHaar : ∀ l : GeneralLinear (k + 1 + 0) F.Carrier,
      mulEquivHaarChar (splitKernelConjugation r s l) =
        (T.determinantNorm (k + 1 + 0) l : ℝ≥0)⁻¹ := by
    intro l
    let : LocallyCompactSpace (radical (k + 1 + 0) F.Carrier) :=
      radical_isClosed.locallyCompactSpace
    let : MeasurableSpace (radical (k + 1 + 0) F.Carrier) := borel _
    have : BorelSpace (radical (k + 1 + 0) F.Carrier) := ⟨rfl⟩
    have hl : (levi l)⁻¹ ∈ Subgroup.normalizer
        (radical (k + 1 + 0) F.Carrier : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
      rw [← hNr]
      simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
    exact (mulEquivHaarChar_normalizerConj_congr hNr ((levi l)⁻¹)
      (by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]) hl).trans
      (mulEquivHaarChar_conj_levi_inv T (k + 1 + 0) l hl)
  have hθl : ∀ (h : mirabolic (k + 0) F.Carrier) (n : r.ker),
      θ.toMonoidHom (splitKernelConjugation r s h.val n) = θ.toMonoidHom n := by
    intro h n
    have hn : (n : mirabolic (k + 1 + 0) F.Carrier) ∈ radical (k + 0 + 1) F.Carrier :=
      hNr ▸ n.2
    have := Derivative.Mirabolic.theta_isInvariant ψ (k + 0) (successorEquiv h⁻¹) ⟨n.1, hn⟩
    refine (congrArg (Derivative.Mirabolic.theta ψ (k + 0)) (Subtype.ext ?_)).trans this
    change (levi h.val)⁻¹ * (n : mirabolic (k + 1 + 0) F.Carrier) * levi h.val =
      successor h⁻¹ * (n : mirabolic (k + 1 + 0) F.Carrier) * (successor h⁻¹)⁻¹
    rw [map_inv, inv_inv]
    rfl
  -- The source identification.
  let σ := fun X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) =>
    twist (T.rightCharacter (k + 1) 0).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)
  have hσ : ∀ X, IsSmooth (σ X) := fun X =>
    (isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) 0).isOpen_ker).mpr
      (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth)
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      (rightPhiProduct.{uF, uV} T ψ k 0).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 := fun X =>
    (Submodule.quotEquivOfEq _ _ (relations_congr (compactInduced H (σ X)) hNr.symm
      (T.mirabolicTheta ψ (k + 0)) θ.toMonoidHom fun _ => rfl)).trans
      (trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν)
  have hE : ∀ X (h : mirabolic (k + 0) F.Carrier)
      (v : (rightPhiProduct.{uF, uV} T ψ k 0).obj X),
      E X (((rightPhiProduct.{uF, uV} T ψ k 0).obj X).representation h v) =
        TensorProduct.map LinearMap.id (X.2.representation h.val) (E X v) := by
    intro X h v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.phiMinusQuotient_surjective T ψ (k + 0) A v
    let l : GeneralLinear (k + 1 + 0) F.Carrier := h.val
    let w := trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
      (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom f)
    have h1 : E X (((rightPhiProduct.{uF, uV} T ψ k 0).obj X).representation h
          (Mirabolic.phiMinusQuotient T ψ (k + 0) A f)) =
        ((realPowerCharacter ((T.determinantNorm (k + 0 + 1)).comp
          (mirabolic (k + 0) F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ)) •
          trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
            (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom
              (compactInduced H (σ X) (s l) f)) :=
      map_smul (E X) _ _
    have h2 := trivialSplitKernelEquiv_section r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν
      hBasis μN μI hν l (hθl h) f
    have h3 : σ X ⟨s l, hsH l⟩ w =
        ((((T.determinantNorm (k + 1) l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
          TensorProduct.map LinearMap.id (X.2.representation h.val) w :=
      twist_rightInducing_levi_zero T (k + 1) X.1.representation X.2.representation l w
    have hc : ((realPowerCharacter ((T.determinantNorm (k + 0 + 1)).comp
          (mirabolic (k + 0) F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ)) *
        ((((mulEquivHaarChar (splitKernelConjugation r s l))⁻¹ : ℝ≥0) : ℝ) : ℂ) *
          ((((T.determinantNorm (k + 1) l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [hHaar l, coe_realPowerCharacter]
      exact half_mul_inv_inv_mul_half (T.determinantNorm (k + 1) l)
    have hw : E X (Mirabolic.phiMinusQuotient T ψ (k + 0) A f) = w := rfl
    refine h1.trans ?_
    rw [h2, h3, hw]
    exact smul_smul_smul_of_mul_eq_one _ _ _ _ hc
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (v : (rightPhiProduct.{uF, uV} T ψ k 0).obj X),
      E Y (SmoothRep.hom ((rightPhiProduct.{uF, uV} T ψ k 0).map φ) v) =
        TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
          (E X v) := by
    intro X Y φ v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.phiMinusQuotient_surjective T ψ (k + 0) A v
    exact trivialSplitKernelEquiv_natural r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis
      μN μI hν (hσ Y) (twistIntertwining (T.rightCharacter (k + 1) 0).toMonoidHom
        (MixedProductTensor.pullbackMap rightProjection
          (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))) f
  -- Assemble the natural isomorphism.
  let iso0 : rightPhiProduct.{uF, uV} T ψ k 0 ≅ rightBoundaryQuotient.{uF, uV} T k :=
    NatIso.ofComponents
      (fun X => SmoothRep.mkIso (equivOfCommonModel
        (fun g => TensorProduct.map LinearMap.id (X.2.representation g.val)) (E X)
        (rightBoundaryQuotientEquiv T k X) (hE X) (rightBoundaryQuotientEquiv_action T k X)))
      (fun φ => MixedProductTensor.smoothRep_hom_ext fun v =>
        symm_comp_natural _ _ _ _ _ _ _ (hEnat φ) (rightBoundaryQuotientEquiv_natural T k φ) v)
  exact ⟨iso0 ≪≫ Functor.isoWhiskerLeft
    ((Mirabolic.psiMinus T 0).prod (generalLinearRestriction T k) ⋙
      T.leftMixedProductFunctor.{uF, uV} 0 k)
      (mirabolicRankCastIso.{uF, max uF uV} T (Nat.add_comm 0 k)).symm⟩

end Boundary

end Langlands.Derivative.MirabolicProductMinus
