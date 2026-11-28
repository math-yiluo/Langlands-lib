import Langlands.BaseChange.TwistedSupercuspidalCuspFormMatchingStatement
import Langlands.BaseChange.CuspFormOrbitalVanishingStatement
import Langlands.BaseChange.SigmaStableSupercuspidalDescentStatement
import Langlands.BaseChange.SupercuspidalCoefficientEllipticMatchingStatement
import Langlands.BaseChange.SigmaLiftCharacterIdentityStatement
import Langlands.BaseChange.LeviClassSystem
import Langlands.BaseChange.EllipticLocusClopen

/-!
# Matching cusp forms for a σ-stable supercuspidal: a reduction

`twistedSupercuspidalCuspFormMatchingReduction` proves
`TwistedSupercuspidalCuspFormMatchingReductionStatement`: the implication to
`TwistedSupercuspidalCuspFormMatchingStatement` from the vanishing of orbital integrals of cusp
forms off the elliptic set, the descent of σ-stable supercuspidal representations, the character
identity of σ-lifts and the elliptic matching of supercuspidal matrix coefficients. See the
paired Markdown.
-/

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.HarmonicAnalysis Langlands.TraceFormula

universe u v uV uW

section Lemmas

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]

/-- The inverse of a generator of a cyclic algebra generates it too. -/
theorem IsCyclicAlgebra.symm {σ : E ≃ₐ[F] E} {l : ℕ} (h : IsCyclicAlgebra σ l) :
    IsCyclicAlgebra σ.symm l := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, ?_, fun x hx => h5 x ?_⟩
  · rw [← AlgEquiv.aut_inv, orderOf_inv, h4]
  · have := congrArg σ hx
    rwa [AlgEquiv.apply_symm_apply, eq_comm] at this

/-- `δ · N_k(δ)^σ = N_{k+1}(δ)`. -/
theorem mul_entrywiseAut_cyclicNorm (σ : E ≃ₐ[F] E) (k : ℕ) {n : ℕ} (δ : GeneralLinear n E) :
    δ * entrywiseAut σ n (cyclicNorm σ k δ) = cyclicNorm σ (k + 1) δ := by
  induction k with
  | zero => simp [cyclicNorm_succ, entrywiseAut_one_apply]
  | succ k ih =>
    calc δ * entrywiseAut σ n (cyclicNorm σ (k + 1) δ)
        = δ * entrywiseAut σ n (cyclicNorm σ k δ * entrywiseAut (σ ^ k) n δ) := by
          rw [cyclicNorm_succ]
      _ = (δ * entrywiseAut σ n (cyclicNorm σ k δ)) *
            entrywiseAut σ n (entrywiseAut (σ ^ k) n δ) := by
          rw [map_mul, mul_assoc]
      _ = cyclicNorm σ (k + 1) δ * entrywiseAut (σ ^ (k + 1)) n δ := by
          rw [ih, pow_succ', entrywiseAut_mul_apply]
      _ = cyclicNorm σ (k + 1 + 1) δ := (cyclicNorm_succ σ (k + 1) δ).symm

/-- The twisted norm of `δ⁻¹` for the inverse generator, transported by `σ^k`:
`(N_{σ⁻¹,k}(δ⁻¹))^{σ^k} = (N_{σ,k}(δ)^σ)⁻¹`. -/
theorem entrywiseAut_pow_cyclicNorm_symm_inv (σ : E ≃ₐ[F] E) (k : ℕ) {n : ℕ}
    (δ : GeneralLinear n E) :
    entrywiseAut (σ ^ k) n (cyclicNorm σ.symm k δ⁻¹) =
      (entrywiseAut σ n (cyclicNorm σ k δ))⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hcancel : ∀ x : GeneralLinear n E,
        entrywiseAut (σ ^ k) n (entrywiseAut (σ.symm ^ k) n x) = x := by
      intro x
      rw [← entrywiseAut_mul_apply, ← AlgEquiv.aut_inv, inv_pow, mul_inv_cancel,
        entrywiseAut_one_apply]
    rw [cyclicNorm_succ, map_mul, pow_succ', entrywiseAut_mul_apply, entrywiseAut_mul_apply, ih,
      hcancel, ← map_mul, ← mul_inv_rev, mul_entrywiseAut_cyclicNorm, map_inv]

/-- For `σ ^ l = 1`: `N_{σ⁻¹}(δ⁻¹) = δ⁻¹ N_σ(δ)⁻¹ δ`. -/
theorem cyclicNorm_symm_inv {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : σ ^ l = 1) {n : ℕ}
    (δ : GeneralLinear n E) :
    cyclicNorm σ.symm l δ⁻¹ = δ⁻¹ * (cyclicNorm σ l δ)⁻¹ * δ := by
  have h := entrywiseAut_pow_cyclicNorm_symm_inv σ l δ
  rw [hσ, entrywiseAut_one_apply, entrywiseAut_cyclicNorm, hσ, entrywiseAut_one_apply] at h
  rw [h]
  group

/-- If `δ` and `γ` are associated for `σ` (with `σ ^ l = 1`), then `δ⁻¹` and `γ⁻¹` are
associated for `σ⁻¹`. -/
theorem IsNormAssociated.symm_inv {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : σ ^ l = 1) {n : ℕ}
    {δ : GeneralLinear n E} {γ : GeneralLinear n F} (h : IsNormAssociated σ l δ γ) :
    IsNormAssociated σ.symm l δ⁻¹ γ⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨δ⁻¹ * g, ?_⟩
  rw [cyclicNorm_symm_inv hσ, map_inv, ← hg]
  group

end Lemmas

section Field

variable {F : Type u} [Field F] {n : ℕ}

open _root_.Polynomial in
/-- The mirror of a squarefree polynomial over a field is squarefree. -/
theorem squarefree_mirror {p : F[X]} (h : Squarefree p) : Squarefree p.mirror := by
  intro x hx
  obtain ⟨y, hy⟩ := hx
  have hp : p = x.mirror * x.mirror * y.mirror := by
    rw [← mirror_mirror p, hy, mirror_mul_of_domain, mirror_mul_of_domain]
  obtain ⟨r, hr, hrx⟩ := Polynomial.isUnit_iff.mp (h _ ⟨_, hp⟩)
  have hx' : x = C r := by rw [← mirror_mirror x, ← hrx, mirror_C]
  rw [hx']
  exact Polynomial.isUnit_C.mpr hr

open _root_.Polynomial in
/-- In characteristic zero, the inverse of a regular semisimple element is regular semisimple:
its characteristic polynomial is a unit times the reverse of that of `γ`. -/
theorem isRegularSemisimple_inv [CharZero F] {γ : GeneralLinear n F}
    (h : IsRegularSemisimple γ) : IsRegularSemisimple γ⁻¹ := by
  unfold IsRegularSemisimple at h ⊢
  have hu : IsUnit (γ : Matrix (Fin n) (Fin n) F) := Units.isUnit γ
  rw [Matrix.coe_units_inv, Matrix.charpoly_inv _ hu, ← Matrix.reverse_charpoly]
  rw [PerfectField.separable_iff_squarefree] at h ⊢
  have hrev : Squarefree (γ : Matrix (Fin n) (Fin n) F).charpoly.reverse :=
    (squarefree_mirror h).of_mul_left
  have hdet : IsUnit (γ : Matrix (Fin n) (Fin n) F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hunit : IsUnit ((-1 : F[X]) ^ Fintype.card (Fin n) *
      C (Ring.inverse (γ : Matrix (Fin n) (Fin n) F).det)) :=
    (isUnit_neg_one.pow _).mul (Polynomial.isUnit_C.mpr hdet.ringInverse)
  exact (associated_unit_mul_left _ _ hunit).squarefree_iff.mpr hrev

variable {E : Type v} [Field E] [Algebra F E]

/-- Two elements of `GL_n(F)` associated with the same `δ` have the same characteristic
polynomial. -/
theorem IsNormAssociated.charpoly_eq {σ : E ≃ₐ[F] E} {l : ℕ} {δ : GeneralLinear n E}
    {γ γ' : GeneralLinear n F} (h : IsNormAssociated σ l δ γ)
    (h' : IsNormAssociated σ l δ γ') :
    (γ : Matrix (Fin n) (Fin n) F).charpoly = (γ' : Matrix (Fin n) (Fin n) F).charpoly := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  have hconj : baseChange F E n γ' = (g⁻¹ * g')⁻¹ * baseChange F E n γ * (g⁻¹ * g') := by
    rw [← hg, ← hg']
    group
  have hE : ((baseChange F E n γ : GeneralLinear n E) : Matrix (Fin n) (Fin n) E).charpoly =
      ((baseChange F E n γ' : GeneralLinear n E) : Matrix (Fin n) (Fin n) E).charpoly := by
    rw [hconj, charpoly_conj]
  have hmap : ∀ t : GeneralLinear n F,
      ((baseChange F E n t : GeneralLinear n E) : Matrix (Fin n) (Fin n) E).charpoly =
        (t : Matrix (Fin n) (Fin n) F).charpoly.map (algebraMap F E) := by
    intro t
    change ((t : Matrix (Fin n) (Fin n) F).map (algebraMap F E)).charpoly = _
    rw [Matrix.charpoly_map]
  rw [hmap, hmap] at hE
  exact Polynomial.map_injective _ (algebraMap F E).injective hE

/-- Association with a fixed `δ` does not change regular ellipticity. -/
theorem IsNormAssociated.isRegularElliptic_iff {σ : E ≃ₐ[F] E} {l : ℕ}
    {δ : GeneralLinear n E} {γ γ' : GeneralLinear n F} (h : IsNormAssociated σ l δ γ)
    (h' : IsNormAssociated σ l δ γ') : IsRegularElliptic γ ↔ IsRegularElliptic γ' := by
  unfold IsRegularElliptic IsRegularSemisimple
  rw [h.charpoly_eq h']

/-- Being a norm is invariant under conjugation. -/
theorem IsNorm.of_conj {σ : E ≃ₐ[F] E} {l : ℕ} {x γ : GeneralLinear n F}
    (h : IsNorm σ l (x⁻¹ * γ * x)) : IsNorm σ l γ := by
  obtain ⟨δ, g, hg⟩ := h
  refine ⟨δ, g * baseChange F E n x⁻¹, ?_⟩
  calc (g * baseChange F E n x⁻¹)⁻¹ * cyclicNorm σ l δ * (g * baseChange F E n x⁻¹)
      = baseChange F E n x * (g⁻¹ * cyclicNorm σ l δ * g) * (baseChange F E n x)⁻¹ := by
        rw [map_inv]
        group
    _ = baseChange F E n x * baseChange F E n (x⁻¹ * γ * x) * (baseChange F E n x)⁻¹ := by
        rw [hg]
    _ = baseChange F E n γ := by
        rw [map_mul, map_mul, map_inv]
        group

end Field


/-- `TwistedSupercuspidalCuspFormMatchingStatement` follows from the vanishing of orbital and
σ-orbital integrals of cusp forms off the elliptic sets, the descent of σ-stable supercuspidal
representations, the character identity of σ-lifts and the elliptic matching of supercuspidal
matrix coefficients. The representation of `GL_n(F)` produced by the descent lies in
`Type uV`, for an arbitrary universe `uV`. -/
def TwistedSupercuspidalCuspFormMatchingReductionStatement : Prop :=
  CuspFormOrbitalVanishingStatement.{u} →
    CuspFormSigmaOrbitalVanishingStatement.{u, v} →
    SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW} →
    SigmaLiftCharacterIdentityStatement.{u, v, uV, uW} →
    SupercuspidalCoefficientEllipticMatchingStatement.{u, v, uV, uW} →
    TwistedSupercuspidalCuspFormMatchingStatement.{u, v, uW}

/-- The descent and the character identity are applied to the inverse generator `σ⁻¹` and the
intertwiner `A⁻¹`; the elliptic matching supplies the cusp forms, and the vanishing of
non-elliptic (σ-)orbital integrals and the pointwise vanishing at elliptic non-norms give the
remaining clauses of concordance. -/
theorem twistedSupercuspidalCuspFormMatchingReduction :
    TwistedSupercuspidalCuspFormMatchingReductionStatement.{u, v, uV, uW} := by
  intro hvan hσvan hdesc hchar hmatch F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn W _ _ τ hτ hirr A
    μF _ μE _
  have hσl : σ ^ l = 1 := hE.pow_eq_one
  have : Module.Finite F E := hE.1
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  -- the inverse intertwiner, for the inverse generator
  have hg : ∀ g : GeneralLinear n E, entrywiseAut σ n (entrywiseAut σ.symm n g) = g := by
    intro g
    rw [← entrywiseAut_mul_apply, ← AlgEquiv.aut_inv, mul_inv_cancel, entrywiseAut_one_apply]
  have he : ∀ g : GeneralLinear n E, (A.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ
      (τ.comp (entrywiseAut σ.symm n).toMonoidHom) g = τ g ∘ₗ A.toLinearEquiv := by
    intro g
    have h := A.isIntertwining' (entrywiseAut σ.symm n g)
    change (A.toLinearEquiv : W →ₗ[ℂ] W) ∘ₗ τ (entrywiseAut σ.symm n g) =
      τ (entrywiseAut σ n (entrywiseAut σ.symm n g)) ∘ₗ A.toLinearEquiv at h
    rw [hg] at h
    exact h
  let A' : SigmaIntertwiner σ.symm n τ :=
    Representation.Equiv.mk A.toLinearEquiv.symm
      (fun g => A.toLinearEquiv.isIntertwining_symm_isIntertwining he g)
  obtain ⟨V, _, _, π, hπ, c, hπirr, hlift⟩ := hdesc F E σ.symm l n hE.symm hn τ hτ hirr A'
  obtain ⟨hc, hval⟩ :=
    (hchar F E σ.symm l n hE.symm π hπ.1 τ hτ.1 hπirr hirr A' c).mp hlift
  have hconj : ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F), IsNormAssociated σ l δ γ →
      IsRegularElliptic γ → ∃ a : ℂ, HasCharacterValue π hπ.1 γ⁻¹ a ∧
        HasTwistedCharacterValue τ hτ.1 A.symm.toLinearMap δ⁻¹ (c * a) :=
    fun δ γ hδγ hell => hval δ⁻¹ γ⁻¹ (hδγ.symm_inv hσl) (isRegularSemisimple_inv hell.1)
  obtain ⟨φ, f, hφ, hf, hfnorm, hconc, htr⟩ :=
    hmatch F E σ l n hE hn τ hτ hirr A π hπ hπirr c hc hconj μF μE
  refine ⟨φ, f, hφ, hf, ⟨?_, ?_⟩, htr⟩
  · intro γ hγ hnorm μγ _ _ νγ hν
    by_cases hell : IsRegularElliptic γ
    · have h0 : twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ
          (f : GeneralLinear n F → ℂ) = fun _ => 0 := by
        funext q
        induction q using Quotient.inductionOn with
        | h x =>
          rw [twistedOrbitFunction_mk, MonoidHom.id_apply]
          exact hfnorm _ ((isRegularElliptic_conj_iff x γ).mpr hell)
            (fun h => hnorm h.of_conj)
      change ∫ q, twistedOrbitFunction (MonoidHom.id (GeneralLinear n F)) γ
        (f : GeneralLinear n F → ℂ) q ∂νγ = 0
      rw [h0, integral_zero]
    · exact hvan F n hn μF f hf γ hγ hell μγ νγ hν
  · intro δ γ hδγ hγ
    by_cases hell : IsRegularElliptic γ
    · exact hconc δ γ hδγ hell
    · intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ _
      have hnotell : ¬ IsSigmaElliptic σ l δ := fun ⟨γ', h', hell'⟩ =>
        hell ((hδγ.isRegularElliptic_iff h').mpr hell')
      rw [hσvan F E σ l n hE hn μE φ hφ δ ⟨γ, hδγ, hγ⟩ hnotell μδ νδ hνδ,
        hvan F n hn μF f hf γ hγ hell μγ νγ hνγ]

end Langlands.BaseChange
