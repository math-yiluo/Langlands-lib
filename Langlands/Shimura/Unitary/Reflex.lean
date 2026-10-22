import Langlands.Shimura.Unitary.Positivity
import Langlands.Shimura.Unitary.HarrisLevels
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Data.Fintype.Fin
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Pi

/-! # Kottwitz's Hodge-type function and the reflex field of the Harris datum -/

noncomputable section

universe u v w t

namespace Langlands.Shimura

open NumberField Algebra Matrix
open scoped Classical

section HodgeNumber

variable {n : ℕ}

/-- Kottwitz's subspace `V₁` of the simple module `ℂⁿ`: the vectors on which
`z ⊗ 1 ∈ ℂ ⊗_ℝ ℂ`, acting through `h`, is multiplication by `z`. -/
def hodgeSubspace (h : ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {v | ∀ z : ℂ, h z *ᵥ v = z • v}
  add_mem' {v w} hv hw z := by
    rw [Matrix.mulVec_add, hv z, hw z, smul_add]
  zero_mem' z := by rw [Matrix.mulVec_zero, smul_zero]
  smul_mem' c v hv z := by
    rw [Matrix.mulVec_smul, hv z, smul_comm]

theorem mem_hodgeSubspace (h : ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    v ∈ hodgeSubspace h ↔ ∀ z : ℂ, h z *ᵥ v = z • v := Iff.rfl

/-- Kottwitz's number `n(i) = dim_ℂ V₁` for one complex factor. -/
def hodgeNumber (h : ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) : ℕ :=
  Module.finrank ℂ (hodgeSubspace h)

/-- For a diagonal homomorphism, `V₁` is spanned by the coordinates on which
`z` acts by `z` rather than by `z̄`. -/
theorem hodgeSubspace_eq_of_diagonal (h : ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (p : Fin n → Prop) [DecidablePred p]
    (hh : ∀ z, h z = Matrix.diagonal fun j => if p j then z else star z) :
    hodgeSubspace h =
      ⨅ j ∈ {j | ¬ p j}, LinearMap.ker (LinearMap.proj j : (Fin n → ℂ) →ₗ[ℂ] ℂ) := by
  ext v
  simp only [mem_hodgeSubspace, hh, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.proj_apply]
  constructor
  · intro hv j hj
    have hj' : ¬ p j := hj
    have hI := congrFun (hv Complex.I) j
    simp only [Matrix.mulVec_diagonal, hj', ite_false, Pi.smul_apply, smul_eq_mul,
      Complex.star_def, Complex.conj_I] at hI
    have h2 : (2 * Complex.I) * v j = 0 := by linear_combination -hI
    exact (mul_eq_zero.mp h2).resolve_left (by simp)
  · intro hv z
    funext j
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hj : p j
    · simp [hj]
    · simp [hv j hj]

theorem hodgeNumber_of_diagonal (h : ℂ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (p : Fin n → Prop) [DecidablePred p]
    (hh : ∀ z, h z = Matrix.diagonal fun j => if p j then z else star z) :
    hodgeNumber h = (Finset.univ.filter p).card := by
  have hd : Disjoint {j | p j} {j | ¬ p j} :=
    Set.disjoint_left.mpr fun _ hj hj' => hj' hj
  have hu : Set.univ ⊆ {j | p j} ∪ {j | ¬ p j} := fun j _ => em (p j)
  rw [hodgeNumber, hodgeSubspace_eq_of_diagonal h p hh,
    (LinearMap.iInfKerProjEquiv ℂ (fun _ : Fin n => ℂ) hd hu).finrank_eq,
    Module.finrank_fintype_fun_eq_card, ← Fintype.card_subtype]
  rfl

/-- The Kottwitz homomorphism at a factor of signature `(r, n-r)`: on the
first `r` coordinates `z` acts by `z`, on the others by `z̄`. -/
theorem hodgeNumber_correctedComplexHom_conj (r : ℕ) (hr : r ≤ n) :
    hodgeNumber ((correctedComplexHom n r).comp Complex.conjAe.toAlgHom) = r := by
  rw [hodgeNumber_of_diagonal _ (fun j : Fin n => j.val < r), Fin.card_filter_val_lt,
    min_eq_right hr]
  intro z
  change correctedComplexHom n r (star z) = _
  rw [correctedComplexHom_apply]
  apply congrArg Matrix.diagonal
  funext j
  split_ifs <;> simp

/-- The conjugate factor of the same homomorphism has the complementary number. -/
theorem hodgeNumber_correctedComplexHom (r : ℕ) (hr : r ≤ n) :
    hodgeNumber ((matrixConj n).toAlgHom.comp
      ((correctedComplexHom n r).comp Complex.conjAe.toAlgHom)) = n - r := by
  rw [hodgeNumber_of_diagonal _ (fun j : Fin n => ¬ j.val < r), Finset.filter_not,
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Fin.card_filter_val_lt,
    min_eq_right hr, Finset.card_univ, Fintype.card_fin]
  intro z
  ext i j
  change matrixConj n (correctedComplexHom n r (star z)) i j = _
  rw [matrixConj_apply, correctedComplexHom_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  split_ifs <;> simp

end HodgeNumber

section RealPlace

variable (E : Type u) {K : Type v} [Field E] [IsTotallyReal E]
variable [Field K] [Algebra E K]

/-- The real embedding of the totally real field below a complex embedding. -/
def realPlaceBelow (i : K →+* ℂ) : E →+* ℝ :=
  (IsTotallyReal.complexEmbedding_isReal (i.comp (algebraMap E K))).embedding

theorem ofReal_realPlaceBelow (i : K →+* ℂ) (x : E) :
    (realPlaceBelow E i x : ℂ) = i (algebraMap E K x) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

theorem realPlaceBelow_eq_iff (i : K →+* ℂ) (τ : E →+* ℝ) :
    realPlaceBelow E i = τ ↔ i.comp (algebraMap E K) = Complex.ofRealHom.comp τ := by
  constructor
  · rintro rfl
    ext x
    exact (ofReal_realPlaceBelow E i x).symm
  · intro h
    ext x
    apply Complex.ofReal_injective
    rw [ofReal_realPlaceBelow]
    exact RingHom.congr_fun h x

theorem comp_realPlaceBelow (i : K →+* ℂ) :
    i.comp (algebraMap E K) = Complex.ofRealHom.comp (realPlaceBelow E i) :=
  (realPlaceBelow_eq_iff E i _).mp rfl

theorem realPlaceBelow_conjugate (i : K →+* ℂ) :
    realPlaceBelow E (ComplexEmbedding.conjugate i) = realPlaceBelow E i := by
  rw [realPlaceBelow_eq_iff, ComplexEmbedding.conjugate_comp, comp_realPlaceBelow]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

theorem realPlaceBelow_of_isCMSection {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (hΦ : IsCMSection E K Φ) (τ : E →+* ℝ) : realPlaceBelow E (Φ τ) = τ :=
  (realPlaceBelow_eq_iff E _ τ).mpr (hΦ τ)

end RealPlace

section HodgeFunction

variable {E : Type u} {K : Type v} {A : Type w}
variable [Field E] [NumberField E] [IsTotallyReal E] [Field K] [Algebra E K]

/-- Kottwitz's function `i ↦ n(i)` for an `ℝ`-algebra homomorphism `h` into the
standard archimedean model `∏_τ M_n(ℂ)`, whose factor at `τ` carries the CM
field through `Φ τ`. Complexifying that factor gives the two factors at `Φ τ`
and at its conjugate; on the second one the action is entrywise conjugated. -/
def standardHodgeFunction (Φ : (E →+* ℝ) → (K →+* ℂ)) {n : ℕ}
    (h : ℂ →ₐ[ℝ] ((E →+* ℝ) → Matrix (Fin n) (Fin n) ℂ)) (i : K →+* ℂ) : ℕ :=
  if i = Φ (realPlaceBelow E i) then
    hodgeNumber ((Pi.evalAlgHom ℝ _ (realPlaceBelow E i)).comp h)
  else
    hodgeNumber ((matrixConj n).toAlgHom.comp
      ((Pi.evalAlgHom ℝ _ (realPlaceBelow E i)).comp h))

/-- The stabilizer in `Aut(ℂ/ℚ)` of a function on the complex embeddings. -/
def hodgeStabilizer (f : (K →+* ℂ) → ℕ) : Subgroup (ℂ ≃ₐ[ℚ] ℂ) where
  carrier := {s | ∀ i, f ((s : ℂ →+* ℂ).comp i) = f i}
  mul_mem' {s t} hs ht i := by
    have : ((s * t : ℂ ≃ₐ[ℚ] ℂ) : ℂ →+* ℂ).comp i =
        (s : ℂ →+* ℂ).comp ((t : ℂ →+* ℂ).comp i) := RingHom.ext fun _ => rfl
    rw [this, hs, ht]
  one_mem' i := by
    have : ((1 : ℂ ≃ₐ[ℚ] ℂ) : ℂ →+* ℂ).comp i = i := RingHom.ext fun _ => rfl
    rw [this]
  inv_mem' {s} hs i := by
    have : (s : ℂ →+* ℂ).comp (((s⁻¹ : ℂ ≃ₐ[ℚ] ℂ) : ℂ →+* ℂ).comp i) = i :=
      RingHom.ext fun x => s.apply_symm_apply (i x)
    rw [← hs, this]

theorem mem_hodgeStabilizer (f : (K →+* ℂ) → ℕ) (s : ℂ ≃ₐ[ℚ] ℂ) :
    s ∈ hodgeStabilizer f ↔ ∀ i, f ((s : ℂ →+* ℂ).comp i) = f i := Iff.rfl

/-- Composition with an automorphism of `ℂ` is injective on ring homomorphisms. -/
theorem autComp_eq_iff {X : Type t} [NonAssocSemiring X] (s : ℂ ≃ₐ[ℚ] ℂ) (j j' : X →+* ℂ) :
    (s : ℂ →+* ℂ).comp j = (s : ℂ →+* ℂ).comp j' ↔ j = j' :=
  ⟨fun h => RingHom.ext fun x => s.injective (by simpa using RingHom.congr_fun h x),
    fun h => h ▸ rfl⟩

/-- Kottwitz's reflex field: the fixed field of the stabilizer of `i ↦ n(i)`. -/
def reflexField (f : (K →+* ℂ) → ℕ) : IntermediateField ℚ ℂ :=
  IntermediateField.fixedField (hodgeStabilizer f)

variable [NumberField K] [IsTotallyComplex K] [IsQuadraticExtension E K]
variable [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower E K A]

namespace HarrisSignatureCharts

variable {σ : SecondKindInvolution E K A} {n : ℕ} {Φ : (E →+* ℝ) → (K →+* ℂ)}
variable (C : HarrisSignatureCharts σ n Φ)

/-- Kottwitz's function `i ↦ n(i)` of the Harris datum: the Kottwitz
homomorphism `h₀` in the standard model of the charts. -/
def hodgeFunction : (K →+* ℂ) → ℕ :=
  standardHodgeFunction Φ (kottwitzHom n (E →+* ℝ) C.distinguished).hom

/-- The reflex field of the Harris datum. -/
def reflexField : IntermediateField ℚ ℂ :=
  Shimura.reflexField C.hodgeFunction

omit [NumberField E] [IsScalarTower E K A] in
theorem evalAlgHom_comp_kottwitzHom (τ : E →+* ℝ) :
    (Pi.evalAlgHom ℝ _ τ).comp (kottwitzHom n (E →+* ℝ) C.distinguished).hom =
      (correctedComplexHom n (if τ = C.distinguished then n - 1 else n)).comp
        Complex.conjAe.toAlgHom :=
  AlgHom.ext fun _ => rfl

omit [NumberField E] [IsScalarTower E K A] in
/-- The Hodge numbers of the Harris datum: `n(Φ τ)` is the number `r_τ` of
positive entries of the signature and `n(Φ τ)′ = n - r_τ`. -/
theorem hodgeFunction_apply (i : K →+* ℂ) :
    C.hodgeFunction i =
      if i = Φ (realPlaceBelow E i) then
        (if realPlaceBelow E i = C.distinguished then n - 1 else n)
      else (if realPlaceBelow E i = C.distinguished then 1 else 0) := by
  have hn := C.rank_gt_one
  rw [hodgeFunction, standardHodgeFunction, evalAlgHom_comp_kottwitzHom]
  split_ifs with h1 h2 h2
  · exact hodgeNumber_correctedComplexHom_conj _ (Nat.sub_le n 1)
  · exact hodgeNumber_correctedComplexHom_conj _ le_rfl
  · rw [hodgeNumber_correctedComplexHom _ (Nat.sub_le n 1)]
    omega
  · rw [hodgeNumber_correctedComplexHom _ le_rfl, Nat.sub_self]

/-- The embedding `Φ τ₁` of the CM field at the distinguished real place. -/
def distinguishedEmbedding : K →+* ℂ :=
  Φ C.distinguished

/-- The image `Φ τ₁ (K) ⊂ ℂ` of the CM field at the distinguished place. -/
def distinguishedImage : IntermediateField ℚ ℂ :=
  C.distinguishedEmbedding.toRatAlgHom.fieldRange

omit [NumberField E] [IsScalarTower E K A] in
theorem mem_fixingSubgroup_distinguishedImage_iff (s : ℂ ≃ₐ[ℚ] ℂ) :
    s ∈ IntermediateField.fixingSubgroup C.distinguishedImage ↔
      (s : ℂ →+* ℂ).comp C.distinguishedEmbedding = C.distinguishedEmbedding := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    ext x
    exact h _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  · intro h y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact RingHom.congr_fun h x

omit [IsScalarTower E K A] in
/-- The Hodge numbers of the Harris datum, sorted by embeddings: `n - 1` at
`Φ τ₁`, `1` at its conjugate, `n` at the other members of `Φ` and `0` at their
conjugates. -/
theorem hodgeFunction_eq (hΦ : IsCMSection E K Φ) (i : K →+* ℂ) :
    C.hodgeFunction i =
      if i = C.distinguishedEmbedding then n - 1
      else if i = ComplexEmbedding.conjugate C.distinguishedEmbedding then 1
      else if i = Φ (realPlaceBelow E i) then n else 0 := by
  have hrp : realPlaceBelow E C.distinguishedEmbedding = C.distinguished :=
    realPlaceBelow_of_isCMSection E hΦ _
  have hd : C.distinguishedEmbedding = Φ C.distinguished := rfl
  rw [C.hodgeFunction_apply]
  by_cases h1 : i = C.distinguishedEmbedding
  · rw [ite_eq_left h1, h1, hrp, ite_eq_left hd, ite_eq_left rfl]
  rw [ite_eq_right h1]
  by_cases h2 : i = ComplexEmbedding.conjugate C.distinguishedEmbedding
  · have h2' : realPlaceBelow E i = C.distinguished := by
      rw [h2, realPlaceBelow_conjugate, hrp]
    rw [ite_eq_left h2, h2', ← hd, ite_eq_right h1, ite_eq_left rfl]
  rw [ite_eq_right h2]
  have h3 : realPlaceBelow E i ≠ C.distinguished := by
    intro h
    have hc : i.comp (algebraMap E K) = C.distinguishedEmbedding.comp (algebraMap E K) := by
      rw [comp_realPlaceBelow, h, hd, hΦ]
    rcases eq_or_eq_conjugate_of_comp_eq C.distinguishedEmbedding i hc with h' | h'
    · exact h1 h'
    · exact h2 h'
  rw [ite_eq_right h3, ite_eq_right h3]

omit [NumberField E] [IsScalarTower E K A] in
/-- With `n = 2` and a single real place the function is constant, so its
stabilizer is all of `Aut(ℂ/ℚ)`. -/
theorem hodgeFunction_eq_one (h2 : n = 2) [Subsingleton (E →+* ℝ)] (i : K →+* ℂ) :
    C.hodgeFunction i = 1 := by
  rw [C.hodgeFunction_apply, Subsingleton.elim (realPlaceBelow E i) C.distinguished]
  subst h2
  simp

omit [NumberField E] [IsScalarTower E K A] in
theorem hodgeStabilizer_eq_top (h2 : n = 2) [Subsingleton (E →+* ℝ)] :
    hodgeStabilizer C.hodgeFunction = ⊤ :=
  eq_top_iff.mpr fun _ _ i => by
    rw [C.hodgeFunction_eq_one h2, C.hodgeFunction_eq_one h2]

end HarrisSignatureCharts

section HarrisCMType

variable {F : Type t} [Field F] [NumberField F] [IsCMField F] [IsQuadraticExtension ℚ F]
variable {σ : SecondKindInvolution E K A} {n : ℕ} {ι : F →+* K} {τ₀ : F →+* ℂ}

omit [IsScalarTower E K A] in
/-- For Harris's CM type, an embedding is the selected one above its real place
exactly when it induces `τ₀` on the imaginary quadratic subfield. -/
theorem eq_harrisCMSection_realPlaceBelow_iff (i : K →+* ℂ) :
    i = harrisCMSection E ι τ₀ (realPlaceBelow E i) ↔ i.comp ι = τ₀ := by
  constructor
  · intro h
    rw [h]
    exact harrisCMSection_comp E ι τ₀ _
  · intro h
    exact eq_harrisCMSection E ι τ₀ _ h (comp_realPlaceBelow E i)

namespace HarrisSignatureCharts

variable (C : HarrisSignatureCharts σ n (harrisCMSection E ι τ₀))

omit [IsScalarTower E K A] in
/-- Kottwitz's function for Harris's datum, in Harris's terms: `n - 1` at
`Φ τ₁`, `1` at its conjugate, `n` at the other embeddings inducing `τ₀` on the
imaginary quadratic subfield and `0` at the remaining ones. -/
theorem hodgeFunction_eq_harris (i : K →+* ℂ) :
    C.hodgeFunction i =
      if i = C.distinguishedEmbedding then n - 1
      else if i = ComplexEmbedding.conjugate C.distinguishedEmbedding then 1
      else if i.comp ι = τ₀ then n else 0 := by
  rw [C.hodgeFunction_eq (isCMSection_harrisCMSection E ι τ₀)]
  simp only [eq_harrisCMSection_realPlaceBelow_iff]

omit [IsScalarTower E K A] in
theorem distinguishedEmbedding_comp : C.distinguishedEmbedding.comp ι = τ₀ :=
  harrisCMSection_comp E ι τ₀ C.distinguished

omit [IsScalarTower E K A] in
/-- Every automorphism of `ℂ` fixing `Φ τ₁ (K)` stabilizes Kottwitz's function. -/
theorem fixingSubgroup_le_hodgeStabilizer :
    IntermediateField.fixingSubgroup C.distinguishedImage ≤
      hodgeStabilizer C.hodgeFunction := by
  intro s hs
  rw [mem_fixingSubgroup_distinguishedImage_iff] at hs
  have hconj : (s : ℂ →+* ℂ).comp (ComplexEmbedding.conjugate C.distinguishedEmbedding) =
      ComplexEmbedding.conjugate C.distinguishedEmbedding :=
    RingHom.ext fun k => by
      have hk := RingHom.congr_fun hs (cmConjugation E K k)
      rw [RingHom.comp_apply, embedding_cmConjugation] at hk
      rw [RingHom.comp_apply, ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply, hk]
  have hτ₀ : (s : ℂ →+* ℂ).comp τ₀ = τ₀ := by
    rw [← C.distinguishedEmbedding_comp, ← RingHom.comp_assoc, hs]
  have e1 : ∀ i : K →+* ℂ, (s : ℂ →+* ℂ).comp i = C.distinguishedEmbedding ↔
      i = C.distinguishedEmbedding := fun i => by
    rw [← autComp_eq_iff s i C.distinguishedEmbedding, hs]
  have e2 : ∀ i : K →+* ℂ,
      (s : ℂ →+* ℂ).comp i = ComplexEmbedding.conjugate C.distinguishedEmbedding ↔
        i = ComplexEmbedding.conjugate C.distinguishedEmbedding := fun i => by
    rw [← autComp_eq_iff s i (ComplexEmbedding.conjugate C.distinguishedEmbedding), hconj]
  have e3 : ∀ i : K →+* ℂ, ((s : ℂ →+* ℂ).comp i).comp ι = τ₀ ↔ i.comp ι = τ₀ :=
    fun i => by
      rw [RingHom.comp_assoc, ← autComp_eq_iff s (i.comp ι) τ₀, hτ₀]
  intro i
  rw [C.hodgeFunction_eq_harris, C.hodgeFunction_eq_harris]
  simp only [e1, e2, e3]

omit [IsScalarTower E K A] in
/-- Conversely, if `n ≥ 3` or the totally real field has a second real place,
every automorphism stabilizing Kottwitz's function fixes `Φ τ₁ (K)`. -/
theorem hodgeStabilizer_le_fixingSubgroup (h : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished) :
    hodgeStabilizer C.hodgeFunction ≤
      IntermediateField.fixingSubgroup C.distinguishedImage := by
  intro s hs
  rw [mem_fixingSubgroup_distinguishedImage_iff]
  rw [mem_hodgeStabilizer] at hs
  have hn := C.rank_gt_one
  have hval : C.hodgeFunction C.distinguishedEmbedding = n - 1 := by
    rw [C.hodgeFunction_eq_harris, ite_eq_left rfl]
  by_contra hne
  have h1 := hs C.distinguishedEmbedding
  rw [hval, C.hodgeFunction_eq_harris, ite_eq_right hne] at h1
  have h2 : (s : ℂ →+* ℂ).comp C.distinguishedEmbedding =
      ComplexEmbedding.conjugate C.distinguishedEmbedding := by
    by_contra h2
    rw [ite_eq_right h2] at h1
    split_ifs at h1 <;> omega
  rw [ite_eq_left h2] at h1
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ≠ C.distinguished := h.resolve_left (by omega)
  have hrp : realPlaceBelow E (harrisCMSection E ι τ₀ τ) = τ :=
    realPlaceBelow_of_isCMSection E (isCMSection_harrisCMSection E ι τ₀) τ
  have hψ : C.hodgeFunction (harrisCMSection E ι τ₀ τ) = n := by
    rw [C.hodgeFunction_apply, hrp, ite_eq_left rfl, ite_eq_right hτ]
  have h4 := hs (harrisCMSection E ι τ₀ τ)
  rw [hψ] at h4
  have h5 : ((s : ℂ →+* ℂ).comp (harrisCMSection E ι τ₀ τ)).comp ι = τ₀ := by
    by_contra h5
    rw [C.hodgeFunction_eq_harris] at h4
    split_ifs at h4 <;> omega
  have hsτ : (s : ℂ →+* ℂ).comp τ₀ = τ₀ := by
    rw [RingHom.comp_assoc, harrisCMSection_comp] at h5
    exact h5
  apply IsTotallyComplex.complexEmbedding_not_isReal τ₀
  rw [ComplexEmbedding.isReal_iff]
  calc ComplexEmbedding.conjugate τ₀
      = (ComplexEmbedding.conjugate C.distinguishedEmbedding).comp ι := by
        rw [ComplexEmbedding.conjugate_comp, C.distinguishedEmbedding_comp]
    _ = ((s : ℂ →+* ℂ).comp C.distinguishedEmbedding).comp ι := by rw [h2]
    _ = τ₀ := by rw [RingHom.comp_assoc, C.distinguishedEmbedding_comp, hsτ]

omit [IsScalarTower E K A] in
/-- The reflex field contains `Φ τ₁ (K)` if `n ≥ 3` or the totally real field
has a second real place. -/
theorem distinguishedImage_le_reflexField (h : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished) :
    C.distinguishedImage ≤ C.reflexField :=
  (IntermediateField.le_iff_le _ _).mpr (C.hodgeStabilizer_le_fixingSubgroup h)

omit [IsScalarTower E K A] in
/-- The reflex field is contained in the fixed field of the automorphisms fixing
`Φ τ₁ (K)`. -/
theorem reflexField_le_fixedField :
    C.reflexField ≤
      IntermediateField.fixedField (IntermediateField.fixingSubgroup C.distinguishedImage) :=
  IntermediateField.fixedField_le C.fixingSubgroup_le_hodgeStabilizer

omit [IsScalarTower E K A] in
/-- Hence the reflex field is `Φ τ₁ (K)` as soon as `Φ τ₁ (K)` is the fixed field
of its own fixing group. -/
theorem reflexField_eq_distinguishedImage (h : 3 ≤ n ∨ ∃ τ, τ ≠ C.distinguished)
    (hgal : IntermediateField.fixedField
      (IntermediateField.fixingSubgroup C.distinguishedImage) = C.distinguishedImage) :
    C.reflexField = C.distinguishedImage :=
  le_antisymm (hgal ▸ C.reflexField_le_fixedField) (C.distinguishedImage_le_reflexField h)

end HarrisSignatureCharts

end HarrisCMType

end HodgeFunction

end Langlands.Shimura
