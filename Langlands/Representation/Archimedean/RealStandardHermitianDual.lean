import Langlands.Global.RankinSelberg.RealStandardDualPairingProof
import Langlands.Representation.Archimedean.RealStandardConjugation
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible
import Langlands.Representation.Archimedean.RealStandardParameterUnitary
import Langlands.Representation.Archimedean.UnitaryGenericPairRegularityStatement

/-! # The Hermitian-dual parameter of a unitarizable real standard module -/

noncomputable section

open scoped ComplexConjugate TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.KFiniteDual Langlands.LocalFactor.Archimedean RealContragredient
open Langlands.Global.RankinSelbergGlobal Langlands.Global.RankinSelbergGlobal.RealLocalJacquet

universe uV

private abbrev KF (n : ℕ) (ds : List RealBlock) :=
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

private theorem standardIntertwiner_of_maps {n : ℕ} {ds : List RealBlock} {W : Type*}
    [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W}
    {ψ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W}
    {T : KF n ds →ₗ[ℂ] W}
    (hK : ∀ k f, T (realStandardRep n ds k f) = σ k (T f))
    (hL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) f,
      T (realStandardLie n ds (1 ⊗ₜ X) f) = ψ (1 ⊗ₜ X) (T f)) :
    IsRealStandardIntertwiner n σ ψ ds T := by
  constructor
  · intro k f
    let k' : Matrix.unitaryGroup (Fin n) ℝ := ⟨k.val.val, k.2⟩
    have hk : Unitary.toUnits k' = k.val := by ext; rfl
    refine ⟨rightTranslation_mem_kFiniteFunctions_realStandardModule n ds f.2 k.2, ?_⟩
    have he : realStandardRep n ds k' f = ⟨_, rightTranslation_mem_kFiniteFunctions_realStandardModule
        n ds f.2 k.2⟩ := Subtype.ext (by rw [realStandardRep_apply_coe, hk])
    simpa only [he] using hK k' f
  · intro X f
    refine ⟨rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X, ?_⟩
    have he : realStandardLie n ds (1 ⊗ₜ X) f =
        ⟨_, rightDerivative_mem_kFiniteFunctions_realStandardModule n ds f.2 X⟩ :=
      Subtype.ext (realStandardLie_one_tmul_apply_coe n ds X f)
    simpa only [he] using hL X f

/-- The bilinear pairing identifies the standard module of the dual blocks with the finite
contragredient of the given irreducible standard module. -/
theorem exists_realStandardDualFiniteDualEquiv {n : ℕ} {ds : List RealBlock}
    (hrank : realRank ds = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds)) :
    ∃ e : KF n (ds.map dualBlock) ≃ₗ[ℂ] kDual (realStandardRep n ds),
      IsRealStandardIntertwiner n (kDualRep (realStandardRep n ds))
        (dualLie (isRealGKModule_realStandardModule n ds)) (ds.map dualBlock) e.toLinearMap := by
  obtain ⟨Q, ⟨hQK, hQL⟩, hQsep⟩ := realStandardDualPairing n ds hrank hirr
  let ρ := realStandardRep n ds
  let hgk := isRealGKModule_realStandardModule n ds
  have hK (k : Matrix.unitaryGroup (Fin n) ℝ) (h : KF n (ds.map dualBlock)) :
      Q.flip (realStandardRep n (ds.map dualBlock) k h) = ρ.dual k (Q.flip h) := by
    ext f
    change Q f (realStandardRep n (ds.map dualBlock) k h) = Q (ρ k⁻¹ f) h
    have hpair := hQK k (ρ k⁻¹ f) h
    change Q (ρ k (ρ k⁻¹ f)) (realStandardRep n (ds.map dualBlock) k h) = _ at hpair
    rwa [Representation.self_inv_apply] at hpair
  let S := Q.flip.intertwiningMap_of_isIntertwiningMap _ _ hK
  let T : KF n (ds.map dualBlock) →ₗ[ℂ] kDual ρ :=
    Q.flip.codRestrict (kDual ρ) fun h => (FiniteVectors.IsFiniteVector.map S
      ((isRealGKModule_realStandardModule n (ds.map dualBlock)).1 h))
  have hT : IsRealStandardIntertwiner n (kDualRep ρ) (dualLie hgk) (ds.map dualBlock) T := by
    apply standardIntertwiner_of_maps
    · intro k h
      exact Subtype.ext (hK k h)
    · intro X h
      apply Subtype.ext
      ext f
      rw [dualLie_apply_apply]
      exact eq_neg_of_add_eq_zero_right (hQL X f h)
  have hTi : Function.Injective T := (injective_iff_map_eq_zero _).2 fun h hh => by
    by_contra! hn
    obtain ⟨f, hf⟩ := hQsep h hn
    exact hf (congrArg (fun w : kDual ρ => (w : Module.Dual ℂ (KF n ds)) f) hh)
  have hT0 : T ≠ 0 := by
    let hnt := realStandardNontrivial n (ds.map dualBlock) ((realRank_map_dualBlock ds).trans hrank)
    obtain ⟨h, hh⟩ := exists_ne (0 : KF n (ds.map dualBlock))
    intro he
    exact hh (hTi (by simp [he]))
  let e := LinearEquiv.ofBijective T ⟨hTi, hT.surjective
    (isIrreducible_kDual hgk hirr (realStandardAdmissible n ds)) hT0⟩
  exact ⟨e, hT⟩

/-- The block obtained by taking its inverse inducing character and then conjugating its
standard-module exponent. -/
def realHermitianDualBlock (x : RealBlock) : RealBlock := realBlockConjExponent (dualBlock x)

/-- Hermitian duality negates the real exponent. -/
theorem realBlockExponent_hermitianDual (x : RealBlock) :
    realBlockExponent (realHermitianDualBlock x) = -realBlockExponent x := by
  cases x <;> simp [realHermitianDualBlock, realBlockConjExponent, dualBlock,
    RealCharacterData.inverse, ComplexCharacterData.inverse, RealJacquetFrobenius.charData,
    realBlockExponent]

private theorem conjExponent_involutive : Function.Involutive realBlockConjExponent := by
  intro x
  cases x with
  | character c =>
    cases c with
    | mk χ p t hχ =>
      simp only [realBlockConjExponent, RealJacquetFrobenius.charData, Complex.conj_conj,
        RealBlock.character.injEq, RealCharacterData.mk.injEq, and_true]
      ext1 z
      apply Units.ext
      exact (hχ z).symm
  | induced d =>
    cases d with
    | mk χ m t hχ =>
      simp only [realBlockConjExponent, characterOfParams, Complex.conj_conj, RealBlock.induced.injEq,
        ComplexCharacterData.mk.injEq, and_true]
      ext1 z
      apply Units.ext
      change borelFactor m (2 * t) (z : ℂ) = (χ z : ℂ)
      rw [borelFactor_eq_cpow m (2 * t) z.ne_zero]
      exact (hχ z).symm

private theorem realRank_map_conj (ds : List RealBlock) :
    realRank (ds.map realBlockConjExponent) = realRank ds := by
  induction ds with
  | nil => rfl
  | cons x ds ih => cases x <;> simp [realBlockConjExponent, RealBlock.rank, ih]

/-- Hermitian duality preserves the sum of the block sizes. -/
theorem realRank_map_hermitianDual (ds : List RealBlock) :
    realRank (ds.map realHermitianDualBlock) = realRank ds := by
  change realRank (ds.map (realBlockConjExponent ∘ dualBlock)) = realRank ds
  rw [← List.map_map, realRank_map_conj, realRank_map_dualBlock]

/-- Pointwise conjugation is onto the standard module with conjugated exponents. -/
theorem realStandardConjugation_surjective (n : ℕ) (ds : List RealBlock) :
    Function.Surjective (realStandardConjugation n ds) := by
  intro f
  have hcomp : realBlockConjExponent ∘ realBlockConjExponent = id :=
    funext conjExponent_involutive
  have hd : (ds.map realBlockConjExponent).map realBlockConjExponent = ds := by
    rw [List.map_map, hcomp, List.map_id]
  obtain ⟨e, he⟩ := exists_linearEquiv_coe_eq (congrArg (KF n) hd)
  refine ⟨e (realStandardConjugation n (ds.map realBlockConjExponent) f), Subtype.ext ?_⟩
  rw [realStandardConjugation_apply_coe, he, realStandardConjugation_apply_coe]
  exact funext fun g => Complex.conj_conj (f.val g)

/-- The Hermitian-dual blocks give another standard parameter of an infinitesimally
unitary irreducible real standard module. -/
theorem realStandard_hermitianDual_parameter {n : ℕ} {ds : List RealBlock}
    (hrank : realRank ds = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds)) :
    HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds)
      (ds.map realHermitianDualBlock) := by
  change HasRealStandardParameter n _ _ (ds.map (realBlockConjExponent ∘ dualBlock))
  rw [← List.map_map]
  obtain ⟨e, he⟩ := exists_realStandardDualFiniteDualEquiv hrank hirr
  obtain ⟨b, hb⟩ := hunit
  let hgk := isRealGKModule_realStandardModule n ds
  let es := ds.map dualBlock
  let cs := es.map realBlockConjExponent
  let C := LinearEquiv.ofBijective (realStandardConjugation n es)
    ⟨realStandardConjugation_injective n es, realStandardConjugation_surjective n es⟩
  let U := LinearEquiv.ofBijective (b.toKFiniteDual hgk.1)
    ⟨b.toKFiniteDual_injective hgk.1, realGK_toKFiniteDual_surjective hgk b hb hirr
      (realStandardAdmissible n ds)⟩
  let A : KF n cs ≃ₗ[ℂ] KF n ds := C.symm.trans (e.trans U.symm)
  refine ⟨(realRank_map_conj es).trans ((realRank_map_dualBlock ds).trans hrank),
    A.toLinearMap, A.injective, standardIntertwiner_of_maps ?_ ?_⟩
  · intro k f
    have hC : C.symm (realStandardRep n cs k f) = realStandardRep n es k (C.symm f) := by
      apply C.injective
      rw [C.apply_symm_apply]
      have h := realStandardConjugation_compact n es k (C.symm f)
      change C (realStandardRep n es k (C.symm f)) = realStandardRep n cs k (C (C.symm f)) at h
      rw [C.apply_symm_apply] at h
      exact h.symm
    apply U.injective
    change U (U.symm (e (C.symm (realStandardRep n cs k f)))) =
      b.toKFiniteDual hgk.1 (realStandardRep n ds k (U.symm (e (C.symm f))))
    rw [U.apply_symm_apply, hC, b.toKFiniteDual_compact]
    change e.toLinearMap (realStandardRep n es k (C.symm f)) =
      kDualRep (realStandardRep n ds) k (U (U.symm (e (C.symm f))))
    rw [U.apply_symm_apply, he.map_realStandardRep]
    rfl
  · intro X f
    have hC : C.symm (realStandardLie n cs (1 ⊗ₜ X) f) =
        realStandardLie n es (1 ⊗ₜ X) (C.symm f) := by
      apply C.injective
      rw [C.apply_symm_apply]
      have h := realStandardConjugation_lie n es X (C.symm f)
      change C (realStandardLie n es (1 ⊗ₜ X) (C.symm f)) =
        realStandardLie n cs (1 ⊗ₜ X) (C (C.symm f)) at h
      rw [C.apply_symm_apply] at h
      exact h.symm
    apply U.injective
    change U (U.symm (e (C.symm (realStandardLie n cs (1 ⊗ₜ X) f)))) =
      b.toKFiniteDual hgk.1 (realStandardLie n ds (1 ⊗ₜ X) (U.symm (e (C.symm f))))
    rw [U.apply_symm_apply, hC, realGK_toKFiniteDual_lie hgk b hb]
    change e.toLinearMap (realStandardLie n es (1 ⊗ₜ X) (C.symm f)) =
      dualLie hgk (1 ⊗ₜ X) (U (U.symm (e (C.symm f))))
    rw [U.apply_symm_apply, he.map_realStandardLie]
    rfl

/-- A uniform lower exponent estimate for the canonical modules also gives the upper
estimate, by applying it to the Hermitian-dual presentation. -/
theorem realUnitaryGenericExponentBound_of_standard_lower
    (hlower : ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
      IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
      IsRealGenericGKModule n (realStandardLie n ds) →
      IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
      ∀ x ∈ ds, -(1 / 2 : ℝ) < realBlockExponent x) :
    RealUnitaryGenericExponentBoundStatement.{uV} := by
  apply realUnitaryGenericExponentBound_of_standard
  intro n ds hrank hirr hgen hunit x hx
  obtain ⟨hrank', hirr', hgen', hunit'⟩ := realStandardParameter_model hirr hgen hunit
    (realStandard_hermitianDual_parameter hrank hirr hunit)
  have h := hlower n (ds.map realHermitianDualBlock) hrank' hirr' hgen' hunit'
    (realHermitianDualBlock x) (List.mem_map_of_mem hx)
  rw [realBlockExponent_hermitianDual] at h
  exact abs_lt.mpr ⟨hlower n ds hrank hirr hgen hunit x hx, by linarith⟩

end Langlands.Archimedean
