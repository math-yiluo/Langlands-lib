import Langlands.BushnellKutzko.CuspidalMatrixIntertwining
import Langlands.BushnellKutzko.SupercuspidalConductorDepthZeroReduction
import Langlands.BushnellKutzko.FiniteMatrixGaussInjectivityStatement
import Langlands.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Category.Contragredient

/-! # The extreme determinant shell at depth zero

Let `K` be a `p`-adic field with ring of integers `𝔬_K`, uniformizer `ϖ` and residue field `k`,
let `ψ` be a unitary additive character of conductor `𝔬_K`, and let `Φ` be the indicator of the
first unit group `1 + ϖ M_{n+1}(𝔬_K)` of the standard lattice chain (`stratumTest` with matrix
parameter `0`). Let `σ` be a smooth representation of `GL_{n+1}(K)` and `w` a nonzero vector
fixed by that first unit group. Assuming finite matrix Gauss injectivity, there is a smooth
functional `ℓ` with

`∫_{ord(det g) = -(n+1)} Φ̂(g) ℓ(σ(g^{-T}) w) dg ≠ 0`

(`standardDepthZeroShellNonzero_of_finiteMatrixGaussInjectivity`).

On that shell `Φ̂` vanishes outside `ϖ⁻¹ GL_{n+1}(𝔬_K)` and equals
`vol(ϖ M_{n+1}(𝔬_K)) ψ(tr g)` on it. Translating by the scalar matrix `ϖ · 1` and averaging
over `GL_{n+1}(𝔬_K)`, the integral becomes `|GL_{n+1}(k)|⁻¹ vol ℓ(σ(ϖ · 1) T w)`. Here `T` is
the Gauss operator `∑_ḡ ψ̄(tr ḡ) ρ(ḡ)` of the representation `ρ(k̄) = σ(k^{-T})` of `GL_{n+1}(k)`
on the vectors fixed by the kernel of reduction, and `ψ̄(x̄) = ψ(ϖ⁻¹ x)`. Injectivity of `T` and
smooth duality supply `ℓ`. This is the depth-zero case of the shell calculation of
Bushnell–Fröhlich (1985), (3.3.10)–(3.3.15).
-/

noncomputable section

namespace Langlands.BushnellKutzko

open ValuativeRel

universe uK uV

section Residue

variable {R : Type*} [CommRing R] [IsLocalRing R] {n : ℕ}

omit [IsLocalRing R] in
/-- Change of coefficients commutes with the inverse transpose. -/
theorem generalLinear_map_inverseTranspose {S : Type*} [CommRing S] (f : R →+* S)
    (g : GeneralLinear n R) :
    Matrix.GeneralLinearGroup.map f (GeneralLinear.inverseTranspose n R g) =
      GeneralLinear.inverseTranspose n S (Matrix.GeneralLinearGroup.map f g) := by
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply, GeneralLinear.inverseTranspose_entry,
    GeneralLinear.inverseTranspose_entry, ← Matrix.GeneralLinearGroup.map_inv,
    Matrix.GeneralLinearGroup.map_apply]

/-- An additive character takes equal values at elements with equal residues, if it is trivial
on the maximal ideal. -/
theorem addChar_eq_of_residue_eq (χ : AddChar R ℂ)
    (hχ : ∀ x ∈ IsLocalRing.maximalIdeal R, χ x = 1) {x y : R}
    (h : IsLocalRing.residue R x = IsLocalRing.residue R y) : χ x = χ y := by
  have hxy : x - y ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  rw [show x = (x - y) + y by abel, AddChar.map_add_eq_mul, hχ _ hxy, one_mul]

/-- An additive character of `R` trivial on the maximal ideal, as a character of the residue
field. -/
def residueCharacter (χ : AddChar R ℂ) (hχ : ∀ x ∈ IsLocalRing.maximalIdeal R, χ x = 1) :
    AddChar (IsLocalRing.ResidueField R) ℂ where
  toFun y := χ (Function.surjInv IsLocalRing.residue_surjective y)
  map_zero_eq_one' := by
    rw [addChar_eq_of_residue_eq χ hχ (y := 0) (by
      rw [Function.surjInv_eq IsLocalRing.residue_surjective, map_zero]), AddChar.map_zero_eq_one]
  map_add_eq_mul' a b := by
    rw [← AddChar.map_add_eq_mul]
    apply addChar_eq_of_residue_eq χ hχ
    rw [map_add, Function.surjInv_eq IsLocalRing.residue_surjective,
      Function.surjInv_eq IsLocalRing.residue_surjective,
      Function.surjInv_eq IsLocalRing.residue_surjective]

theorem residueCharacter_residue (χ : AddChar R ℂ)
    (hχ : ∀ x ∈ IsLocalRing.maximalIdeal R, χ x = 1) (x : R) :
    residueCharacter χ hχ (IsLocalRing.residue R x) = χ x :=
  addChar_eq_of_residue_eq χ hχ (Function.surjInv_eq IsLocalRing.residue_surjective _)

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The vectors fixed by the image under `ι` of the kernel of reduction modulo the maximal
ideal. -/
def reductionKernelFixedVectors (ι : GeneralLinear n R →* G) (σ : Representation ℂ G V) :
    Submodule ℂ V where
  carrier := {v | ∀ k : GeneralLinear n R,
    Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) k = 1 → σ (ι k) v = v}
  add_mem' {v w} hv hw k hk := by
    rw [map_add, hv k hk, hw k hk]
  zero_mem' k _ := map_zero _
  smul_mem' c v hv k hk := by
    rw [map_smul, hv k hk]

theorem mem_reductionKernelFixedVectors (ι : GeneralLinear n R →* G)
    (σ : Representation ℂ G V) (v : V) :
    v ∈ reductionKernelFixedVectors ι σ ↔ ∀ k : GeneralLinear n R,
      Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) k = 1 → σ (ι k) v = v :=
  Iff.rfl

theorem inverseTranspose_mem_reductionKernelFixedVectors (ι : GeneralLinear n R →* G)
    (σ : Representation ℂ G V) (h : GeneralLinear n R) {v : V}
    (hv : v ∈ reductionKernelFixedVectors ι σ) :
    σ (ι h) v ∈ reductionKernelFixedVectors ι σ := by
  intro k hk
  have hconj : Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) (h⁻¹ * k * h) = 1 := by
    rw [map_mul, map_mul, hk, mul_one, map_inv, inv_mul_cancel]
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul,
    show k * h = h * (h⁻¹ * k * h) by group, map_mul, map_mul, Module.End.mul_apply,
    hv _ hconj]

/-- The action `k ↦ σ(ι(k^{-T}))` of `GL_n(R)` on the reduction-kernel fixed vectors. -/
def reductionKernelAction (ι : GeneralLinear n R →* G) (σ : Representation ℂ G V) :
    GeneralLinear n R →* Module.End ℂ (reductionKernelFixedVectors ι σ) where
  toFun k := (σ (ι (GeneralLinear.inverseTranspose n R k))).restrict
    fun _ hv => inverseTranspose_mem_reductionKernelFixedVectors ι σ _ hv
  map_one' := by
    ext v
    simp
  map_mul' k h := by
    ext v
    simp

theorem reductionKernelAction_apply (ι : GeneralLinear n R →* G) (σ : Representation ℂ G V)
    (k : GeneralLinear n R) (v : reductionKernelFixedVectors ι σ) :
    (reductionKernelAction ι σ k v : V) =
      σ (ι (GeneralLinear.inverseTranspose n R k)) (v : V) :=
  rfl

/-- The representation of `GL_n` of the residue field on the reduction-kernel fixed vectors,
`ρ(k̄) v = σ(ι(k^{-T})) v` for any lift `k`. -/
def reductionRepresentation (ι : GeneralLinear n R →* G) (σ : Representation ℂ G V) :
    Representation ℂ (GeneralLinear n (IsLocalRing.ResidueField R))
      (reductionKernelFixedVectors ι σ) :=
  (Units.coeHom _).comp
    ((Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue R)).liftOfSurjective
      IntegralMatrices.map_residue_surjective
      ⟨(reductionKernelAction ι σ).toHomUnits, fun k hk => by
        rw [MonoidHom.mem_ker] at hk ⊢
        apply Units.ext
        ext v
        rw [MonoidHom.coe_toHomUnits, Units.val_one, reductionKernelAction_apply,
          Module.End.one_apply]
        apply v.2
        rw [generalLinear_map_inverseTranspose, hk, map_one]⟩)

theorem reductionRepresentation_map (ι : GeneralLinear n R →* G) (σ : Representation ℂ G V)
    (k : GeneralLinear n R) (v : reductionKernelFixedVectors ι σ) :
    (reductionRepresentation ι σ
        (Matrix.GeneralLinearGroup.map (IsLocalRing.residue R) k) v : V) =
      σ (ι (GeneralLinear.inverseTranspose n R k)) (v : V) := by
  simp only [reductionRepresentation, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.liftOfRightInverse_comp_apply, Units.coeHom_apply, MonoidHom.coe_toHomUnits]
  rfl

end Residue

section StandardChain

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {n : ℕ}

include hϖ in
/-- For the standard chain, a matrix with every entry in `ϖ^d 𝔬_F` lies in `𝔓^d`. -/
theorem toLin'_mem_standard_endFiltration (d : ℤ) (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hX : ∀ a b, (((LatticeChain.uniformizerAsUnit hϖ ^ d)⁻¹ : Fˣ) : F) * X a b ∈ 𝒪[F]) :
    Matrix.toLin' X ∈ (LatticeChain.standard hϖ (Fin (n + 1))).endFiltration d := by
  intro i v hv
  rw [LatticeChain.mem_standard_lattice] at hv ⊢
  intro a
  set u := LatticeChain.uniformizerAsUnit hϖ
  have hsplit : (((u ^ (i + d))⁻¹ : Fˣ) : F) =
      (((u ^ d)⁻¹ : Fˣ) : F) * (((u ^ i)⁻¹ : Fˣ) : F) := by
    rw [zpow_add, mul_inv, mul_comm, Units.val_mul]
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine sum_mem fun b _ => ?_
  rw [hsplit, show (((u ^ d)⁻¹ : Fˣ) : F) * (((u ^ i)⁻¹ : Fˣ) : F) * (X a b * v b) =
    ((((u ^ d)⁻¹ : Fˣ) : F) * X a b) * ((((u ^ i)⁻¹ : Fˣ) : F) * v b) by ring]
  exact mul_mem (hX a b) (hv b)

/-- For the standard chain, every entry of a matrix in `𝔓^d` lies in `ϖ^d 𝔬_F`. -/
theorem entry_mem_of_toLin'_mem_standard_endFiltration (d : ℤ)
    (X : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hX : Matrix.toLin' X ∈ (LatticeChain.standard hϖ (Fin (n + 1))).endFiltration d)
    (a b : Fin (n + 1)) :
    (((LatticeChain.uniformizerAsUnit hϖ ^ d)⁻¹ : Fˣ) : F) * X a b ∈ 𝒪[F] := by
  classical
  have h := hX 0 (Pi.single b 1) (by
    rw [LatticeChain.mem_standard_lattice]
    intro k
    rw [zpow_zero, inv_one, Units.val_one, one_mul, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  rw [zero_add, LatticeChain.mem_standard_lattice] at h
  have h' := h a
  rwa [Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply] at h'

end StandardChain

section Padic

local instance dzTopologicalSpace {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance dzValuativeRel {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel

local instance dzLocalField {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField

local instance dzMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) :
    MeasurableSpace K.Carrier :=
  borel _

local instance dzBorel {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) : BorelSpace K.Carrier :=
  ⟨rfl⟩

local instance dzGLMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ) :
    MeasurableSpace (GeneralLinear n K.Carrier) :=
  borel _

local instance dzGLBorel {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) (n : ℕ) :
    BorelSpace (GeneralLinear n K.Carrier) :=
  ⟨rfl⟩

open MeasureTheory HarmonicAnalysis ValuativeRel

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p) {n : ℕ}

/-- The inclusion `GL_{n+1}(𝔬_K) → GL_{n+1}(K)`. -/
abbrev integralInclusion (K : PadicField.{uK} p) (n : ℕ) :
    GeneralLinear (n + 1) 𝒪[K.Carrier] →* GeneralLinear (n + 1) K.Carrier :=
  Matrix.GeneralLinearGroup.map 𝒪[K.Carrier].subtype

/-- An integral matrix congruent to the identity modulo the maximal ideal lies in the first unit
group of the standard lattice chain. -/
theorem integralInclusion_mem_unitSubgroup_one {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)
    (k : GeneralLinear (n + 1) 𝒪[K.Carrier])
    (hk : Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[K.Carrier]) k = 1) :
    integralInclusion K n k ∈ unitSubgroup K (LatticeChain.standard hϖ (Fin (n + 1))) 1 := by
  rw [mem_unitSubgroup_iff_sub_one_mem K _ le_rfl, LatticeChain.mem_matrixFiltration]
  apply toLin'_mem_standard_endFiltration hϖ 1
  intro a b
  have hsub : ((integralInclusion K n k).val - 1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) =
      (k.val - 1).map 𝒪[K.Carrier].subtype := by
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hmem : (k.val - 1) a b ∈ IsLocalRing.maximalIdeal 𝒪[K.Carrier] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h := congrArg (fun g : GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier]) =>
      g a b) hk
    simp only [Matrix.GeneralLinearGroup.map_apply] at h
    rw [Matrix.sub_apply, map_sub, h, Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [hsub, Matrix.map_apply, ← hc]
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have : (((LatticeChain.uniformizerAsUnit hϖ ^ (1 : ℤ))⁻¹ : K.Carrierˣ) : K.Carrier) *
      𝒪[K.Carrier].subtype (c * ϖ) = c := by
    rw [zpow_one, Units.val_inv_eq_inv_val, LatticeChain.coe_uniformizerAsUnit, map_mul,
      Subring.coe_subtype, mul_comm, mul_assoc, mul_inv_cancel₀ hϖ0, mul_one]
  rw [this]
  exact c.2

/-- Over a group with a left-invariant measure, integrating over `{g | z g ∈ S}` is integrating
`g ↦ H(z⁻¹ g)` over `S`. -/
theorem setIntegral_preimage_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G} (hS : MeasurableSet S) (z : G)
    (hS' : MeasurableSet {g | z * g ∈ S}) (H : G → ℂ) :
    ∫ g in {g | z * g ∈ S}, H g ∂μ = ∫ k in S, H (z⁻¹ * k) ∂μ := by
  rw [← integral_indicator hS', ← integral_indicator hS,
    ← integral_mul_left_eq_self ({g | z * g ∈ S}.indicator H) z⁻¹]
  congr 1
  funext k
  have key : z⁻¹ * k ∈ {g | z * g ∈ S} ↔ k ∈ S := by
    show z * (z⁻¹ * k) ∈ S ↔ k ∈ S
    rw [mul_inv_cancel_left]
  simp only [Set.indicator]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

/-- Left translation by an element of a subgroup preserves the integral over the subgroup. -/
theorem setIntegral_subgroup_mul_left {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (H : Subgroup G) (hH : MeasurableSet (H : Set G))
    {h : G} (hh : h ∈ H) (F : G → ℂ) :
    ∫ x in (H : Set G), F (h * x) ∂μ = ∫ x in (H : Set G), F x ∂μ := by
  rw [← integral_indicator hH, ← integral_indicator hH,
    ← integral_mul_left_eq_self ((H : Set G).indicator F) h]
  congr 1
  funext x
  have key : h * x ∈ (H : Set G) ↔ x ∈ (H : Set G) := H.mul_mem_cancel_left hh
  simp only [Set.indicator]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.2 h1) h2
  · exact absurd (key.1 h2) h1
  · rfl

theorem isOpen_integralSubgroup_padic :
    IsOpen (Conductor.integralSubgroup 𝒪[K.Carrier] n :
      Set (GeneralLinear (n + 1) K.Carrier)) := by
  rw [← Conductor.levelSubgroup_zero]
  exact (Conductor.levelOpenSubgroup K.Carrier n 0).isOpen

theorem isCompact_integralSubgroup_padic :
    IsCompact (Conductor.integralSubgroup 𝒪[K.Carrier] n :
      Set (GeneralLinear (n + 1) K.Carrier)) := by
  rw [← Conductor.levelSubgroup_zero]
  exact Conductor.isCompact_levelOpenSubgroup K.Carrier n 0

/-- **Averaging over `GL_{n+1}(𝔬_K)`.** If `F` is continuous on `GL_{n+1}(K)` and its value at
an integral matrix depends only on the reduction `k̄` modulo the maximal ideal, through a
function `Θ` on `GL_{n+1}` of the residue field, then the integral of `F` over `GL_{n+1}(𝔬_K)`
(of measure one) is the average of `Θ`. -/
theorem setIntegral_integralSubgroup_eq_average
    [Fintype (GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier]))]
    (F : GeneralLinear (n + 1) K.Carrier → ℂ) (hF : Continuous F)
    (Θ : GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier]) → ℂ)
    (hΘ : ∀ k, F (integralInclusion K n k) =
      Θ (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[K.Carrier]) k)) :
    ∫ g in (Conductor.integralSubgroup 𝒪[K.Carrier] n : Set (GeneralLinear (n + 1) K.Carrier)),
        F g ∂(RankinSelberg.generalLinearHaar K.Carrier n) =
      (Fintype.card (GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier])) : ℂ)⁻¹ *
        ∑ g, Θ g := by
  set μ := RankinSelberg.generalLinearHaar K.Carrier n
  set K₀ := Conductor.integralSubgroup 𝒪[K.Carrier] n
  set red := Matrix.GeneralLinearGroup.map (n := Fin (n + 1)) (IsLocalRing.residue 𝒪[K.Carrier])
  have hK₀m : MeasurableSet (K₀ : Set (GeneralLinear (n + 1) K.Carrier)) :=
    (isOpen_integralSubgroup_padic K).measurableSet
  have hK₀c := isCompact_integralSubgroup_padic (K := K) (n := n)
  have hsurj : Function.Surjective red := IntegralMatrices.map_residue_surjective
  let s : GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier]) →
      GeneralLinear (n + 1) K.Carrier := fun g => integralInclusion K n (Function.surjInv hsurj g)
  have hs (g) : s g ∈ K₀ := ⟨Function.surjInv hsurj g, rfl⟩
  have hint (g) : IntegrableOn (fun x => F (s g * x)) (K₀ : Set _) μ :=
    (hF.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_compact' hK₀c hK₀m
  have hsum : ∑ g, ∫ x in (K₀ : Set _), F (s g * x) ∂μ =
      (Fintype.card (GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier])) : ℂ) *
        ∫ x in (K₀ : Set _), F x ∂μ := by
    rw [Finset.sum_congr rfl fun g _ => setIntegral_subgroup_mul_left μ K₀ hK₀m (hs g) F,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hconst : ∫ x in (K₀ : Set _), ∑ g, F (s g * x) ∂μ =
      ∫ _ in (K₀ : Set (GeneralLinear (n + 1) K.Carrier)), ∑ g, Θ g ∂μ := by
    refine setIntegral_congr_fun hK₀m fun x hx => ?_
    obtain ⟨k, rfl⟩ := hx
    simp only [s]
    rw [Finset.sum_congr rfl fun g _ => by rw [← map_mul, hΘ, map_mul,
      Function.surjInv_eq hsurj]]
    exact Fintype.sum_equiv (Equiv.mulRight (red k)) _ _ fun _ => rfl
  have hμ : μ.real (K₀ : Set (GeneralLinear (n + 1) K.Carrier)) = 1 := by
    rw [Measure.real, RankinSelberg.generalLinearHaar_integralSubgroup, ENNReal.toReal_one]
  rw [← integral_finsetSum _ fun g _ => hint g, hconst, setIntegral_const, hμ, one_smul] at hsum
  have hcard : (Fintype.card (GeneralLinear (n + 1) (IsLocalRing.ResidueField 𝒪[K.Carrier])) :
      ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, inv_mul_cancel_left₀ hcard]

/-! ### The scalar matrix `ϖ · 1` -/

section Scalar

/-- The scalar matrix `ϖ · 1` in `GL_{n+1}(K)`. -/
abbrev uniformizerScalar (n : ℕ) {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ) :
    GeneralLinear (n + 1) K.Carrier :=
  Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (LatticeChain.uniformizerAsUnit hϖ)

variable {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)

theorem uniformizerScalar_mul_apply (g : GeneralLinear (n + 1) K.Carrier) (a b : Fin (n + 1)) :
    (uniformizerScalar K n hϖ * g) a b = (ϖ : K.Carrier) * g a b := by
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul]
  rfl

theorem uniformizerScalar_inv_mul_apply (g : GeneralLinear (n + 1) K.Carrier)
    (a b : Fin (n + 1)) :
    ((uniformizerScalar K n hϖ)⁻¹ * g) a b = (ϖ : K.Carrier)⁻¹ * g a b := by
  rw [← map_inv, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul, Units.val_inv_eq_inv_val, LatticeChain.coe_uniformizerAsUnit]

theorem inverseTranspose_uniformizerScalar_inv :
    GeneralLinear.inverseTranspose (n + 1) K.Carrier (uniformizerScalar K n hϖ)⁻¹ =
      uniformizerScalar K n hϖ := by
  ext a b
  rw [GeneralLinear.inverseTranspose_entry, inv_inv, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  simp only [eq_comm]

theorem det_uniformizerScalar_mul (g : GeneralLinear (n + 1) K.Carrier) :
    (uniformizerScalar K n hϖ * g).val.det = (ϖ : K.Carrier) ^ (n + 1) * g.val.det := by
  rw [Units.val_mul, Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem ord_uniformizerScalar_mul (g : GeneralLinear (n + 1) K.Carrier) :
    K.canonicalTopologicalData.ord (uniformizerScalar K n hϖ * g).val.det =
      (n + 1 : ℤ) + K.canonicalTopologicalData.ord g.val.det := by
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  rw [det_uniformizerScalar_mul, K.canonicalTopologicalData.ord_mul (pow_ne_zero _ hϖ0)
    g.det_ne_zero, ← zpow_natCast, K.canonicalTopologicalData.ord_zpow,
    ord_coe_of_irreducible K hϖ, mul_one]
  push_cast
  ring

/-- If `ϖ g` lies in `GL_{n+1}(𝔬_K)`, then `ord(det g) = -(n+1)`. -/
theorem ord_det_eq_of_uniformizerScalar_mul_mem {g : GeneralLinear (n + 1) K.Carrier}
    (hg : uniformizerScalar K n hϖ * g ∈ Conductor.integralSubgroup 𝒪[K.Carrier] n) :
    K.canonicalTopologicalData.ord g.val.det = -(n + 1 : ℤ) := by
  obtain ⟨k, hk⟩ := hg
  have hdet : (uniformizerScalar K n hϖ * g).val.det =
      ((Matrix.GeneralLinearGroup.det k : 𝒪[K.Carrier]ˣ) : 𝒪[K.Carrier]) := by
    rw [← hk]
    exact (RingHom.map_det 𝒪[K.Carrier].subtype k.val).symm
  have h0 := ord_coe_unit K (Matrix.GeneralLinearGroup.det k)
  rw [← hdet, ord_uniformizerScalar_mul] at h0
  omega

/-- If every entry of `ϖ g` is integral and `ord(det g) = -(n+1)`, then `ϖ g` lies in
`GL_{n+1}(𝔬_K)`. -/
theorem uniformizerScalar_mul_mem_of_entries {g : GeneralLinear (n + 1) K.Carrier}
    (hent : ∀ a b, (ϖ : K.Carrier) * g a b ∈ 𝒪[K.Carrier])
    (hdet : K.canonicalTopologicalData.ord g.val.det = -(n + 1 : ℤ)) :
    uniformizerScalar K n hϖ * g ∈ Conductor.integralSubgroup 𝒪[K.Carrier] n := by
  set T := K.canonicalTopologicalData
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝒪[K.Carrier] := fun a b => ⟨_, hent a b⟩
  have hA : A.map 𝒪[K.Carrier].subtype = (uniformizerScalar K n hϖ * g).val := by
    ext a b
    rw [Matrix.map_apply, uniformizerScalar_mul_apply]
    rfl
  have hcoe : ((A.det : 𝒪[K.Carrier]) : K.Carrier) = (uniformizerScalar K n hϖ * g).val.det := by
    rw [← hA]
    exact RingHom.map_det 𝒪[K.Carrier].subtype A
  have hne : ((A.det : 𝒪[K.Carrier]) : K.Carrier) ≠ 0 := by
    rw [hcoe]
    exact (uniformizerScalar K n hϖ * g).det_ne_zero
  have hord : T.ord ((A.det : 𝒪[K.Carrier]) : K.Carrier) = 0 := by
    rw [hcoe, ord_uniformizerScalar_mul, hdet]
    ring
  have hinv : ((A.det : 𝒪[K.Carrier]) : K.Carrier)⁻¹ ∈ 𝒪[K.Carrier] :=
    (RankinSelberg.UnramifiedUnitary.mem_integers_iff_ord K T (inv_ne_zero hne)).2
      (by rw [T.ord_inv, hord, neg_zero])
  have hunit : IsUnit A.det :=
    IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hne))
  exact ⟨Matrix.GeneralLinearGroup.mk'' A hunit, Units.ext hA⟩

end Scalar

/-! ### The residue character and the Fourier transform of the standard test function -/

section Fourier

variable (ψ : UnitaryAdditiveCharacter K.Carrier) (hψ : Conductor.HasIntegerConductor ψ)
  {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)

/-- `x̄ ↦ ψ(ϖ⁻¹ x)` on the residue field of `𝔬_K`, for `ψ` of conductor `𝔬_K`. -/
def residueScaledCharacter : AddChar (IsLocalRing.ResidueField 𝒪[K.Carrier]) ℂ :=
  residueCharacter
    ((scaledCharacter K ψ (ϖ : K.Carrier)⁻¹).compAddMonoidHom
      𝒪[K.Carrier].subtype.toAddMonoidHom)
    (scaledCharacter_eq_one_of_mem_maximalIdeal K hψ hϖ)

theorem residueScaledCharacter_residue (x : 𝒪[K.Carrier]) :
    residueScaledCharacter K ψ hψ hϖ (IsLocalRing.residue 𝒪[K.Carrier] x) =
      ψ.complex ((ϖ : K.Carrier)⁻¹ * x) :=
  residueCharacter_residue _ _ x

theorem residueScaledCharacter_ne_one : residueScaledCharacter K ψ hψ hϖ ≠ 1 := by
  obtain ⟨c, hc⟩ := exists_scaledCharacter_ne_one K hψ hϖ
  intro h
  apply hc
  have h' := residueScaledCharacter_residue K ψ hψ hϖ c
  rw [h, AddChar.one_apply] at h'
  rw [scaledCharacter_apply]
  exact h'.symm

theorem measurableSet_standard_matrixFiltration_one :
    MeasurableSet ((LatticeChain.standard hϖ (Fin (n + 1))).matrixFiltration 1 :
      Set (Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)) := by
  set c : K.Carrier := (((LatticeChain.uniformizerAsUnit hϖ ^ (1 : ℤ))⁻¹ : K.Carrierˣ) : K.Carrier)
  have hset : ((LatticeChain.standard hϖ (Fin (n + 1))).matrixFiltration 1 :
      Set (Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier)) =
      ⋂ (a : Fin (n + 1)) (b : Fin (n + 1)),
        (fun y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier => c * y a b) ⁻¹'
          (𝒪[K.Carrier] : Set K.Carrier) := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun hy a b => entry_mem_of_toLin'_mem_standard_endFiltration hϖ 1 y hy a b,
      fun h => toLin'_mem_standard_endFiltration hϖ 1 y h⟩
  rw [hset]
  have hO : MeasurableSet (𝒪[K.Carrier] : Set K.Carrier) :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation K.Carrier)).measurableSet
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => hO.preimage ?_
  exact (measurable_const_mul c).comp
    (((measurable_pi_apply b).comp (measurable_pi_apply a) :
      Measurable fun y : Fin (n + 1) → Fin (n + 1) → K.Carrier => y a b))

include hψ in
/-- On the shell `ord(det g) = -(n+1)`, the Fourier transform of the standard first-unit
indicator vanishes outside `ϖ⁻¹ GL_{n+1}(𝔬_K)`. -/
theorem uniformizerScalar_mul_mem_of_fourier_ne_zero (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure] {g : GeneralLinear (n + 1) K.Carrier}
    (hg : rectangularFourierIntegral ψ ν
      (stratumTest K (LatticeChain.standard hϖ (Fin (n + 1))) le_rfl ψ 0) g.val ≠ 0)
    (hdet : K.canonicalTopologicalData.ord g.val.det = -(n + 1 : ℤ)) :
    uniformizerScalar K n hϖ * g ∈ Conductor.integralSubgroup 𝒪[K.Carrier] n := by
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have hmem := toLin'_inv_smul_transpose_mem_of_fourier_ne_zero K ψ ν
    (LatticeChain.standard hϖ (Fin (n + 1))) (k := 1) le_rfl 0 (inv_ne_zero hϖ0)
    (exists_scaledCharacter_ne_one K hψ hϖ) (j := 0) (by norm_num) (by simp) g.val hg
  refine uniformizerScalar_mul_mem_of_entries K hϖ (fun a b => ?_) hdet
  have h := entry_mem_of_toLin'_mem_standard_endFiltration hϖ 0 _ hmem b a
  simpa [Matrix.smul_apply, Matrix.transpose_apply, inv_inv] using h

include hψ in
/-- On `ϖ⁻¹ GL_{n+1}(𝔬_K)` the Fourier transform of the standard first-unit indicator is
`vol(𝔓) ψ(tr g)`. -/
theorem rectangularFourierIntegral_stratumTest_of_mem (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure] {g : GeneralLinear (n + 1) K.Carrier}
    (hg : uniformizerScalar K n hϖ * g ∈ Conductor.integralSubgroup 𝒪[K.Carrier] n) :
    rectangularFourierIntegral ψ ν
        (stratumTest K (LatticeChain.standard hϖ (Fin (n + 1))) le_rfl ψ 0) g.val =
      ((RankinSelberg.rectangularMeasure ν (n + 1) (n + 1)).real
          ((LatticeChain.standard hϖ (Fin (n + 1))).matrixFiltration 1 : Set _) : ℂ) *
        ψ.complex g.val.trace := by
  have hϖ0 : (ϖ : K.Carrier) ≠ 0 := coe_uniformizer_ne_zero hϖ
  have hent : ∀ a b, (ϖ : K.Carrier) * g a b ∈ 𝒪[K.Carrier] := fun a b => by
    have h := ((Conductor.mem_integralSubgroup _ n _).1 hg).1 a b
    rwa [uniformizerScalar_mul_apply] at h
  refine rectangularFourierIntegral_twistedIndicator_of_trace_eq_one ψ ν _
    (measurableSet_standard_matrixFiltration_one K hϖ) 0 g.val fun y hy => ?_
  have hy' : ∀ a b, (ϖ : K.Carrier)⁻¹ * y a b ∈ 𝒪[K.Carrier] := fun a b => by
    have h := entry_mem_of_toLin'_mem_standard_endFiltration hϖ 1 y hy a b
    simpa [zpow_one, Units.val_inv_eq_inv_val] using h
  have htr : (y * (g.val.transpose - 0)).trace =
      ∑ a, ∑ b, ((ϖ : K.Carrier)⁻¹ * y a b) * ((ϖ : K.Carrier) * g a b) := by
    rw [sub_zero]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_mul_mul_comm, inv_mul_cancel₀ hϖ0, one_mul]
  have hmem : (y * (g.val.transpose - 0)).trace ∈ 𝒪[K.Carrier] := by
    rw [htr]
    exact sum_mem fun a _ => sum_mem fun b _ => mul_mem (hy' a b) (hent a b)
  rw [UnitaryAdditiveCharacter.complex_apply, hψ.1 _ hmem]
  rfl

/-- The volume of `𝔓 = ϖ M_{n+1}(𝔬_K)` for the product Haar measure is nonzero. -/
theorem standard_matrixFiltration_one_volume_ne_zero (ν : AdditiveHaarMeasure K.Carrier)
    [SigmaFinite ν.measure] :
    ((RankinSelberg.rectangularMeasure ν (n + 1) (n + 1)).real
      ((LatticeChain.standard hϖ (Fin (n + 1))).matrixFiltration 1 : Set _) : ℂ) ≠ 0 := by
  set 𝓢 := LatticeChain.standard hϖ (Fin (n + 1))
  set P : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier) := ↑(𝓢.matrixFiltration 1)
  have hopen : IsOpen P := by
    have h := isOpen_one_add_matrixFiltration K 𝓢 (k := 1) le_rfl
    have hP : P = (fun x => x + 1) ⁻¹'
        {y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier | y - 1 ∈ 𝓢.matrixFiltration 1} := by
      ext x
      simp [P]
    rw [hP]
    exact h.preimage (continuous_id.add continuous_const)
  have hcpt : IsCompact P := by
    have h := isCompact_one_add_matrixFiltration K 𝓢 (k := 1) le_rfl
    have hP : P = (fun x => x - 1) ''
        {y : Matrix (Fin (n + 1)) (Fin (n + 1)) K.Carrier | y - 1 ∈ 𝓢.matrixFiltration 1} := by
      ext x
      constructor
      · intro hx
        refine ⟨x + 1, ?_, by simp⟩
        change x + 1 - 1 ∈ 𝓢.matrixFiltration 1
        rwa [add_sub_cancel_right]
      · rintro ⟨y, hy, rfl⟩
        exact hy
    rw [hP]
    exact h.image (continuous_id.sub continuous_const)
  have hne : P.Nonempty := ⟨0, zero_mem (𝓢.matrixFiltration 1)⟩
  have : (RankinSelberg.rectangularMeasure ν (n + 1) (n + 1)).IsOpenPosMeasure :=
    inferInstanceAs
      (Measure.pi (fun _ : Fin (n + 1) => Measure.pi (fun _ : Fin (n + 1) => ν.measure))).IsOpenPosMeasure
  have : IsFiniteMeasureOnCompacts (RankinSelberg.rectangularMeasure ν (n + 1) (n + 1)) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts
      (Measure.pi (fun _ : Fin (n + 1) => Measure.pi (fun _ : Fin (n + 1) => ν.measure))))
  rw [Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]
  exact ⟨(hopen.measure_pos _ hne).ne', hcpt.measure_lt_top.ne⟩

end Fourier

/-! ### The extreme shell and the finite Gauss operator -/

section Gauss

variable {ϖ : 𝒪[K.Carrier]} (hϖ : Irreducible ϖ)

theorem trace_uniformizerScalar_inv_mul (g : GeneralLinear (n + 1) K.Carrier) :
    ((uniformizerScalar K n hϖ)⁻¹ * g).val.trace = (ϖ : K.Carrier)⁻¹ * g.val.trace := by
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => uniformizerScalar_inv_mul_apply K hϖ g a a

theorem trace_integralInclusion (k : GeneralLinear (n + 1) 𝒪[K.Carrier]) :
    (integralInclusion K n k).val.trace = ((k.val.trace : 𝒪[K.Carrier]) : K.Carrier) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.GeneralLinearGroup.map_apply,
    Subring.coe_subtype]
  push_cast
  rfl

theorem trace_map_residue (k : GeneralLinear (n + 1) 𝒪[K.Carrier]) :
    (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[K.Carrier]) k).val.trace =
      IsLocalRing.residue 𝒪[K.Carrier] k.val.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.GeneralLinearGroup.map_apply, map_sum]

/-- **The extreme shell from finite Gauss injectivity.** Finite matrix Gauss injectivity gives,
for every nonzero vector fixed by the first unit group of the standard chain, a smooth functional
for which the integral over the shell `ord(det g) = -(n+1)` of the standard depth-zero test is
nonzero. -/
theorem standardDepthZeroShellNonzero_of_finiteMatrixGaussInjectivity
    (hGauss : FiniteMatrixGaussInjectivityStatement.{uK, uV}) :
    StandardDepthZeroShellNonzero.{uK, uV} := by
  intro p _ K n ψ hψ ν _ V _ _ σ hσ ϖ hϖ w hw0 𝓢 hfix
  classical
  set T := K.canonicalTopologicalData
  set μ := RankinSelberg.generalLinearHaar K.Carrier n
  set z := uniformizerScalar K n hϖ
  set K₀ := Conductor.integralSubgroup 𝒪[K.Carrier] n
  -- the finite Gauss operator on the reduction-kernel fixed vectors
  have hw' : w.val ∈ reductionKernelFixedVectors (integralInclusion K n) σ :=
    fun k hk => hfix _ (integralInclusion_mem_unitSubgroup_one K hϖ k hk)
  let kres := IsLocalRing.ResidueField 𝒪[K.Carrier]
  let : Fintype kres := Fintype.ofFinite kres
  let ψr := residueScaledCharacter K ψ hψ hϖ
  let ρ := reductionRepresentation (integralInclusion K n) σ
  let w' : reductionKernelFixedVectors (integralInclusion K n) σ := ⟨w.val, hw'⟩
  have hinj := hGauss kres (n + 1) ψr (residueScaledCharacter_ne_one K ψ hψ hϖ)
    (reductionKernelFixedVectors (integralInclusion K n) σ) ρ
  let : Fintype (GeneralLinear (n + 1) kres) := Fintype.ofFinite _
  set Tw : reductionKernelFixedVectors (integralInclusion K n) σ :=
    ∑ g : GeneralLinear (n + 1) kres, ψr g.val.trace • ρ g w' with hTw_def
  have hTw : Tw ≠ 0 := by
    intro h
    apply hw0
    have h0 : (fun v => ∑ g : GeneralLinear (n + 1) kres, ψr g.val.trace • ρ g v) w' =
        (fun v => ∑ g : GeneralLinear (n + 1) kres, ψr g.val.trace • ρ g v) 0 := by
      simp only [map_zero, smul_zero, Finset.sum_const_zero]
      exact h
    exact congrArg Subtype.val (hinj h0)
  -- the functional
  set u : V := σ z (Tw : V)
  have hu : u ≠ 0 := by
    intro h
    apply hTw
    apply Subtype.ext
    have h' := congrArg (σ z⁻¹) h
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] at h'
    exact h'
  obtain ⟨ℓ, hℓ⟩ := exists_smoothDual_apply_ne_zero_of_compact_cofinal
    (GeneralLinear.compactOpen_cofinal K T (n + 1)) σ hσ hu
  refine ⟨ℓ, ?_⟩
  -- the integral
  set f := stratumCoefficient K σ ℓ w
  set vol : ℂ := ((RankinSelberg.rectangularMeasure ν (n + 1) (n + 1)).real
    (𝓢.matrixFiltration 1 : Set _) : ℂ)
  have hf (g : GeneralLinear (n + 1) K.Carrier) : f.val g = ℓ.1 (σ g w.val) := rfl
  set I : GeneralLinear (n + 1) K.Carrier → ℂ := fun g =>
    rectangularFourierIntegral ψ ν (stratumTest K 𝓢 le_rfl ψ 0) g.val *
      GodementJacquet.coefficientIota f.val g
  have hK₀m : MeasurableSet (K₀ : Set (GeneralLinear (n + 1) K.Carrier)) :=
    (isOpen_integralSubgroup_padic K).measurableSet
  have hsm : MeasurableSet {g : GeneralLinear (n + 1) K.Carrier |
      z * g ∈ (K₀ : Set (GeneralLinear (n + 1) K.Carrier))} :=
    hK₀m.preimage (continuous_const.mul continuous_id).measurable
  have h1 : ∫ g in {g : GeneralLinear (n + 1) K.Carrier | T.ord (Matrix.det g.val) =
        -(n + 1 : ℤ)}, I g ∂μ =
        ∫ g in {g | z * g ∈ (K₀ : Set (GeneralLinear (n + 1) K.Carrier))}, I g ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_ord_det_eq K _)
      (fun g hg => ord_det_eq_of_uniformizerScalar_mul_mem K hϖ hg) fun g hg => ?_
    by_contra hI
    apply hg.2
    have hΦ : rectangularFourierIntegral ψ ν (stratumTest K 𝓢 le_rfl ψ 0) g.val ≠ 0 :=
      left_ne_zero_of_mul hI
    exact uniformizerScalar_mul_mem_of_fourier_ne_zero K ψ hψ hϖ ν hΦ hg.1
  have h2 := setIntegral_preimage_mul_left μ hK₀m z hsm I
  set F : GeneralLinear (n + 1) K.Carrier → ℂ := fun g =>
    vol * ψ.complex ((z⁻¹ * g).val.trace) * GodementJacquet.coefficientIota f.val (z⁻¹ * g)
  have h3 : ∫ k in (K₀ : Set (GeneralLinear (n + 1) K.Carrier)), I (z⁻¹ * k) ∂μ =
      ∫ k in (K₀ : Set (GeneralLinear (n + 1) K.Carrier)), F k ∂μ := by
    refine setIntegral_congr_fun hK₀m fun k hk => ?_
    have hk' : z * (z⁻¹ * k) ∈ K₀ := by rwa [mul_inv_cancel_left]
    simp only [I, F]
    rw [rectangularFourierIntegral_stratumTest_of_mem K ψ hψ hϖ ν hk']
  have hFc : Continuous F := by
    have hmul : Continuous fun g : GeneralLinear (n + 1) K.Carrier => z⁻¹ * g :=
      continuous_const.mul continuous_id
    refine (continuous_const.mul (ψ.continuous_complex.comp
      (Units.continuous_val.comp hmul).matrix_trace)).mul ?_
    exact ((GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients σ f).continuous.comp
      (GeneralLinear.continuous_inverseTranspose _ _)).comp hmul
  let Θ : GeneralLinear (n + 1) kres → ℂ := fun g =>
    vol * ψr g.val.trace * ℓ.1 (σ z (ρ g w' : V))
  have hΘ (k : GeneralLinear (n + 1) 𝒪[K.Carrier]) :
      F (integralInclusion K n k) =
        Θ (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[K.Carrier]) k) := by
    simp only [F, Θ]
    rw [trace_uniformizerScalar_inv_mul K hϖ, trace_integralInclusion K, trace_map_residue K,
      residueScaledCharacter_residue K ψ hψ hϖ, reductionRepresentation_map]
    congr 1
    change ℓ.1 (σ (GeneralLinear.inverseTranspose (n + 1) K.Carrier
      (z⁻¹ * integralInclusion K n k)) w.val) = _
    rw [map_mul, inverseTranspose_uniformizerScalar_inv K hϖ,
      ← generalLinear_map_inverseTranspose, map_mul, Module.End.mul_apply]
  have h4 := setIntegral_integralSubgroup_eq_average K F hFc Θ hΘ
  have hΘsum : ∑ g, Θ g = vol * ℓ.1 u := by
    simp only [Θ, u, hTw_def, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  change ∫ g in {g : GeneralLinear (n + 1) K.Carrier | T.ord (Matrix.det g.val) =
    -(n + 1 : ℤ)}, I g ∂μ ≠ 0
  rw [h1, h2, h3, h4, hΘsum]
  have hcard : (Fintype.card (GeneralLinear (n + 1) kres) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact mul_ne_zero (inv_ne_zero hcard)
    (mul_ne_zero (standard_matrixFiltration_one_volume_ne_zero K hϖ ν) hℓ)

end Gauss

end Padic

end Langlands.BushnellKutzko
