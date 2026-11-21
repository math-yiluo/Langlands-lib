import Langlands.BaseChange.CommonShintaniLiftNonvanishing
import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.PseudoCoefficient
import Langlands.Representation.Hecke.IntegratedConvolution

/-! # Central characters on scalar norms in Shintani lifts -/

noncomputable section

universe uG uF uE uV uV' uW

set_option autoImplicit false

namespace Langlands.BaseChange

open HarmonicAnalysis JacquetLanglands MeasureTheory
open scoped _root_.Polynomial

section CharacterValues

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {hρ : IsAdmissible ρ}

/-- Left translation by an element acting as a scalar scales the local
value of the twisted distribution by that scalar. -/
theorem HasTwistedCharacterValue.leftTranslate_of_scalar
    {A : Module.End ℂ V} {g a : G} {b d : ℂ}
    (hb : HasTwistedCharacterValue ρ hρ A g b) (ha : ∀ v : V, ρ a v = d • v) :
    HasTwistedCharacterValue ρ hρ A (a * g) (d * b) := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  intro μ _
  have hdist (f : SchwartzBruhat G) :
      twistedDistribution μ ρ hρ A (Hecke.TestFunction.leftTranslate a f) =
        d * twistedDistribution μ ρ hρ A f := by
    rw [twistedDistribution_apply, twistedDistribution_apply, ← smul_eq_mul, ← map_smul]
    apply congrArg FiniteRankEnd.trace
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change Hecke.integratedAction μ ρ hρ.1 (Hecke.TestFunction.leftTranslate a f) (A v) =
      d • Hecke.integratedAction μ ρ hρ.1 f (A v)
    rw [Hecke.integratedAction_leftTranslate, ha]
  obtain ⟨U, hU, hg, hval⟩ := hb μ
  refine ⟨(a⁻¹ * ·) ⁻¹' U, hU.preimage (continuous_const.mul continuous_id),
    by simpa using hg, ?_⟩
  intro f hf
  let f' := Hecke.TestFunction.leftTranslate a⁻¹ f
  have hf' : Function.support f' ⊆ U := by
    intro y hy
    have hy' : a * y ∈ Function.support f := by simpa [f', Function.mem_support] using hy
    simpa using hf hy'
  have htranslate : Hecke.TestFunction.leftTranslate a f' = f := by
    simp [f', ← Hecke.TestFunction.leftTranslate_mul]
  have hintegral : (∫ y, f' y ∂μ) = ∫ y, f y ∂μ := by
    simpa [f'] using (integral_mul_left_eq_self (f : G → ℂ) a)
  calc
    _ = d * twistedDistribution μ ρ hρ A f' :=
      (congrArg (twistedDistribution μ ρ hρ A) htranslate).symm.trans (hdist f')
    _ = _ := by rw [hval f' hf', hintegral, mul_assoc]

private theorem hasCharacterValue_leftTranslate_of_scalar {g a : G} {b d : ℂ}
    (hb : HasCharacterValue ρ hρ g b) (ha : ∀ v : V, ρ a v = d • v) :
    HasCharacterValue ρ hρ (a * g) (d * b) :=
  (hasTwistedCharacterValue_one_iff ρ hρ _ _).mp
    (((hasTwistedCharacterValue_one_iff ρ hρ _ _).mpr hb).leftTranslate_of_scalar ha)

end CharacterValues

section Norm

variable {F : Type uF} [Field F] {E : Type uE} [Field E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}

private theorem cyclicNorm_scalar_mul_product (σ : E ≃ₐ[F] E) (l : ℕ)
    (z : Eˣ) (δ : GeneralLinear n E) :
    cyclicNorm σ l (GeneralLinear.scalar z * δ) =
      GeneralLinear.scalar (∏ i : Fin l, Units.map ((σ ^ (i : ℕ)).toRingHom) z) *
        cyclicNorm σ l δ := by
  induction l with
  | zero => simp
  | succ k ih =>
    have hmap : entrywiseAut (σ ^ k) n (GeneralLinear.scalar z) =
        GeneralLinear.scalar (Units.map ((σ ^ k).toRingHom) z) :=
      Matrix.GeneralLinearGroup.map_scalar ((σ ^ k).toRingHom) z
    rw [cyclicNorm_succ, cyclicNorm_succ, ih, map_mul, hmap, Fin.prod_univ_castSucc, map_mul]
    simp only [Fin.val_castSucc, Fin.val_last, mul_assoc]
    rw [← mul_assoc (cyclicNorm σ k δ),
      ← Matrix.GeneralLinearGroup.scalar_commute _ (cyclicNorm σ k δ), mul_assoc]

/-- Scaling an upstairs matrix by a unit scales its associated matrix by the
field norm of the unit. -/
theorem IsNormAssociated.scalar_mul {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (hδγ : IsNormAssociated σ l δ γ) (hE : IsCyclicAlgebra σ l) (z : Eˣ) :
    IsNormAssociated σ l (GeneralLinear.scalar z * δ)
      (GeneralLinear.scalar (Units.map (Algebra.norm F : E →* F) z) * γ) := by
  have hone : cyclicNorm σ l (1 : GeneralLinear 1 E) = 1 := by
    clear hδγ hE
    induction l with
    | zero => rfl
    | succ k ih => simp [cyclicNorm_succ, ih]
  have hdet := hE.determinant_cyclicNorm (GeneralLinear.scalar z : GeneralLinear 1 E)
  have hnormOne : cyclicNorm σ l (GeneralLinear.scalar z : GeneralLinear 1 E) =
      GeneralLinear.scalar (∏ i : Fin l, Units.map ((σ ^ (i : ℕ)).toRingHom) z) := by
    simpa only [mul_one, hone] using (cyclicNorm_scalar_mul_product σ l z (1 : GeneralLinear 1 E))
  rw [hnormOne] at hdet
  simp only [GeneralLinear.determinant, GeneralLinear.scalar, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin, pow_one] at hdet
  let zF := Units.map (Algebra.norm F : E →* F) z
  have hnorm : (∏ i : Fin l, Units.map ((σ ^ (i : ℕ)).toRingHom) z) =
      Units.map (algebraMap F E).toMonoidHom zF := by
    apply Units.ext
    change _ = algebraMap F E (Algebra.norm F (z : E))
    exact hdet
  obtain ⟨g, hg⟩ := hδγ
  have hbase : baseChange F E n (GeneralLinear.scalar zF) =
      GeneralLinear.scalar (Units.map (algebraMap F E).toMonoidHom zF) :=
    Matrix.GeneralLinearGroup.map_scalar (algebraMap F E) zF
  refine ⟨g, ?_⟩
  change g⁻¹ * cyclicNorm σ l (GeneralLinear.scalar z * δ) * g =
    baseChange F E n (GeneralLinear.scalar zF * γ)
  rw [cyclicNorm_scalar_mul_product, hnorm, map_mul, hbase, ← hg,
    ← mul_assoc g⁻¹, ← Matrix.GeneralLinearGroup.scalar_commute _ g⁻¹]
  simp only [GeneralLinear.scalar, mul_assoc]

/-- Multiplying by a scalar unit preserves regular semisimplicity. -/
theorem isRegularSemisimple_scalar_mul {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ)
    (z : Fˣ) : IsRegularSemisimple (GeneralLinear.scalar z * γ) := by
  let M : Matrix (Fin n) (Fin n) F := γ
  let zInv : F := (↑(z⁻¹) : F)
  let q : F[X] := Polynomial.C zInv * Polynomial.X
  let e : F[X] →+* F[X] := (Polynomial.aeval q).toRingHom
  have hz : (z : F) * zInv = 1 := z.val_inv
  have heX : e Polynomial.X = q := Polynomial.aeval_X q
  have heC (a : F) : e (Polynomial.C a) = Polynomial.C a :=
    Polynomial.aeval_C q a
  have hCq : Polynomial.C (z : F) * q = Polynomial.X := by
    dsimp only [q]
    rw [← mul_assoc, ← map_mul, hz, map_one, one_mul]
  have hmatrix : ((z : F) • M).charmatrix =
      Polynomial.C (z : F) • e.mapMatrix M.charmatrix := by
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.charmatrix_apply_eq, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply,
        smul_eq_mul, map_sub, heX, heC, mul_sub, hCq, map_mul]
    · simp only [Matrix.charmatrix_apply_ne _ _ _ hij, RingHom.mapMatrix_apply, Matrix.map_apply,
        Matrix.smul_apply, smul_eq_mul, map_neg, heC, mul_neg, map_mul]
  have hpoly : ((z : F) • M).charpoly = Polynomial.C ((z : F) ^ n) * M.charpoly.comp q := by
    rw [Matrix.charpoly, hmatrix, Matrix.det_smul, ← e.map_det, Fintype.card_fin, ← map_pow]
    rfl
  change (M.charpoly).Separable at hγ
  change (((Matrix.scalar (Fin n) (z : F)) * M).charpoly).Separable
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, hpoly, Polynomial.separable_def,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.derivative_comp]
  have hq : Polynomial.derivative q = Polynomial.C zInv := by simp [q, Polynomial.derivative_mul]
  rw [hq]
  have hunitPow := ((z.isUnit).pow n).map Polynomial.C
  have hunitInv := (Units.isUnit z⁻¹).map Polynomial.C
  rw [isCoprime_mul_unit_left_left hunitPow, isCoprime_mul_unit_left_right hunitPow,
    isCoprime_mul_unit_left_right hunitInv]
  exact IsCoprime.map hγ e

end Norm

section CentralCharacter

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {E : Type uE} [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}
  [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
  [TotallyDisconnectedSpace (GeneralLinear n F)]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (GeneralLinear n F) V} {hπ : IsAdmissible π}
  {π' : Representation ℂ (GeneralLinear n F) V'} {hπ' : IsAdmissible π'}
  {τ : Representation ℂ (GeneralLinear n E) W} {hτ : IsAdmissible τ}
  {A A' : SigmaIntertwiner σ n τ} {c c' : ℂ}
  {χ : Subgroup.center (GeneralLinear n F) →* ℂˣ}
  {χ' : Subgroup.center (GeneralLinear n F) →* ℂˣ}
  {ξ : Subgroup.center (GeneralLinear n E) →* ℂˣ}

/-- With one nonzero regular norm value, the central character of a
Shintani lift equals that downstairs composed with the scalar field norm. -/
theorem IsShintaniLift.centralCharacter_eq_norm
    (hLift : IsShintaniLift σ l π hπ τ hτ A c) (hE : IsCyclicAlgebra σ l)
    (hχ : HasCentralCharacterRep π χ) (hξ : HasCentralCharacterRep τ ξ)
    {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (hδγ : IsNormAssociated σ l δ γ) (hγ : IsRegularSemisimple γ)
    {b : ℂ} (hb : b ≠ 0) (hval : HasCharacterValue π hπ γ b) (z : Eˣ) :
    ξ (GeneralLinear.scalarToCenter z) =
      χ (GeneralLinear.scalarToCenter (Units.map (Algebra.norm F : E →* F) z)) := by
  let zF := Units.map (Algebra.norm F : E →* F) z
  obtain ⟨a, ha, hat⟩ := hLift.2 δ γ hδγ hγ
  rw [ha.unique hval] at hat
  obtain ⟨a', ha', hat'⟩ := hLift.2 _ _ (hδγ.scalar_mul hE z)
    (isRegularSemisimple_scalar_mul hγ zF)
  have hvalF := hasCharacterValue_leftTranslate_of_scalar hval (hχ (GeneralLinear.scalarToCenter zF))
  have hvalE := hat.leftTranslate_of_scalar (hξ (GeneralLinear.scalarToCenter z))
  rw [ha'.unique hvalF] at hat'
  apply Units.ext
  apply mul_right_cancel₀ (mul_ne_zero hLift.1 hb)
  calc
    _ = c * ((χ (GeneralLinear.scalarToCenter zF) : ℂ) * b) := hvalE.unique hat'
    _ = _ := by ring

/-- The central characters of two representations sharing an irreducible
Shintani lift agree on all scalar norms when a reference value is nonzero. -/
theorem IsShintaniLift.centralCharacters_agree_on_norms
    (hLift : IsShintaniLift σ l π hπ τ hτ A c)
    (hLift' : IsShintaniLift σ l π' hπ' τ hτ A' c') (hE : IsCyclicAlgebra σ l)
    (hI : τ.IsIrreducible) (hχ : HasCentralCharacterRep π χ) (hχ' : HasCentralCharacterRep π' χ')
    {δ : GeneralLinear n E} {γ : GeneralLinear n F}
    (hδγ : IsNormAssociated σ l δ γ) (hγ : IsRegularSemisimple γ)
    (hval : ∃ b : ℂ, b ≠ 0 ∧ HasCharacterValue π hπ γ b) (z : Eˣ) :
    χ (GeneralLinear.scalarToCenter (Units.map (Algebra.norm F : E →* F) z)) =
      χ' (GeneralLinear.scalarToCenter (Units.map (Algebra.norm F : E →* F) z)) := by
  obtain ⟨ξ, ⟨_, hξ⟩, _⟩ := admissibleSchur_centralCharacter τ hτ hI
  obtain ⟨b', hb', hval'⟩ := commonShintaniLiftNonvanishing F E σ l n V V' W
    π hπ π' hπ' τ hτ hI A A' c c' hLift hLift' δ γ hδγ hγ hval
  obtain ⟨b, hb, hval⟩ := hval
  exact (hLift.centralCharacter_eq_norm hE hχ hξ hδγ hγ hb hval z).symm.trans
    (hLift'.centralCharacter_eq_norm hE hχ' hξ hδγ hγ hb' hval' z)

end CentralCharacter

/-- A Shintani lift with a nonzero regular norm value has central
character given on scalars by the downstairs central character and field norm. -/
def ShintaniCentralCharacterOnNormsStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (E : Type uE) [Field E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
    (σ : E ≃ₐ[F] E) (l n : ℕ)
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π)
    (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ)
    (A : SigmaIntertwiner σ n τ) (c : ℂ)
    (χ : Subgroup.center (GeneralLinear n F) →* ℂˣ)
    (ξ : Subgroup.center (GeneralLinear n E) →* ℂˣ),
    IsCyclicAlgebra σ l → IsShintaniLift σ l π hπ τ hτ A c →
    HasCentralCharacterRep π χ → HasCentralCharacterRep τ ξ →
    ∀ (δ : GeneralLinear n E) (γ : GeneralLinear n F),
      IsNormAssociated σ l δ γ → IsRegularSemisimple γ →
      (∃ b : ℂ, b ≠ 0 ∧ HasCharacterValue π hπ γ b) →
      ∀ z : Eˣ, ξ (GeneralLinear.scalarToCenter z) =
        χ (GeneralLinear.scalarToCenter (Units.map (Algebra.norm F : E →* F) z))

theorem shintaniCentralCharacterOnNorms : ShintaniCentralCharacterOnNormsStatement := by
  intro F _ _ _ E _ _ _ _ σ l n _ _ _ _ _ _ V _ _ W _ _
    π hπ τ hτ A c χ ξ hE hLift hχ hξ δ γ hAssoc hReg
  rintro ⟨b, hb, hValue⟩ z
  exact hLift.centralCharacter_eq_norm hE hχ hξ hAssoc hReg hb hValue z

end Langlands.BaseChange
