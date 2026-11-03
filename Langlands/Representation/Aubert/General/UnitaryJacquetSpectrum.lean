import Langlands.Representation.Aubert.General.UnitaryJacquet
import Langlands.Representation.Exponents.Central

/-! # Conjugation of central exponents on actual unitary Jacquet modules -/

noncomputable section

namespace Langlands

universe uG uV uW

section Characters

variable {H : Type uG} [Group H]

/-- Complex conjugation of a character, with the same domain. -/
def conjugateComplexCharacter (χ : H →* ℂˣ) : H →* ℂˣ :=
  (Units.map (starRingEnd ℂ).toMonoidHom).comp χ

@[simp]
theorem conjugateComplexCharacter_apply (χ : H →* ℂˣ) (h : H) :
    (conjugateComplexCharacter χ h : ℂ) = starRingEnd ℂ (χ h : ℂ) := rfl

@[simp]
theorem conjugateComplexCharacter_ker (χ : H →* ℂˣ) :
    (conjugateComplexCharacter χ).ker = χ.ker := by
  ext h
  simp only [MonoidHom.mem_ker, Units.ext_iff, conjugateComplexCharacter_apply,
    Units.val_one]
  constructor
  · intro h
    have h' := congrArg (starRingEnd ℂ) h
    simpa using h'
  · intro h
    rw [h, map_one]

@[simp]
theorem conjugateComplexCharacter_norm (χ : H →* ℂˣ) (h : H) :
    ‖(conjugateComplexCharacter χ h : ℂ)‖ = ‖(χ h : ℂ)‖ := by
  simp

end Characters

section CentralSpaces

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An equivariant conjugate-linear map transports every power of a shifted
action operator, conjugating its scalar. -/
theorem conjugateLinearMap_action_sub_pow
    (f : V →ₗ⋆[ℂ] W) (hf : ∀ g v, f (ρ g v) = σ g (f v))
    (g : G) (c : ℂ) (n : ℕ) (v : V) :
    f (((ρ g - c • 1) ^ n) v) =
      ((σ g - (starRingEnd ℂ c) • 1) ^ n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smulₛₗ, hf, ih]

/-- A conjugate-linear equivariant equivalence preserves the finite uniform
central-character condition, conjugating the character. -/
theorem mem_centralCharacterSpace_conjugate_iff
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (χ : Subgroup.center G →* ℂˣ) (n : ℕ) (v : V) :
    e v ∈ centralCharacterSpace σ (conjugateComplexCharacter χ) n ↔
      v ∈ centralCharacterSpace ρ χ n := by
  simp only [mem_centralCharacterSpace, conjugateComplexCharacter_apply]
  constructor
  · intro h z
    apply e.injective
    exact (conjugateLinearMap_action_sub_pow e.toLinearMap he z (χ z) n v).trans
      ((h z).trans (map_zero e).symm)
  · intro h z
    exact (conjugateLinearMap_action_sub_pow e.toLinearMap he z (χ z) n v).symm.trans
      (by rw [h z, map_zero])

/-- The same equivalence preserves the increasing union of the uniform
central-character spaces, keeping the exponent for each vector. -/
theorem mem_generalizedCentralCharacterSpace_conjugate_iff
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (χ : Subgroup.center G →* ℂˣ) (v : V) :
    e v ∈ generalizedCentralCharacterSpace σ (conjugateComplexCharacter χ) ↔
      v ∈ generalizedCentralCharacterSpace ρ χ := by
  change (e v ∈ ⨆ n : ℕ,
    (centralCharacterSpace σ (conjugateComplexCharacter χ) n).toSubmodule) ↔
      v ∈ ⨆ n : ℕ, (centralCharacterSpace ρ χ n).toSubmodule
  rw [Submodule.mem_iSup_of_directed _
    (centralCharacterSpace_mono σ (conjugateComplexCharacter χ)).directed_le,
    Submodule.mem_iSup_of_directed _ (centralCharacterSpace_mono ρ χ).directed_le]
  exact exists_congr fun n => mem_centralCharacterSpace_conjugate_iff e he χ n v

/-- Restrict the actual conjugate-linear equivalence to the generalized
central-character spaces, rather than just comparing their supports. -/
def conjugateGeneralizedCentralCharacterEquiv
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (χ : Subgroup.center G →* ℂˣ) :
    (generalizedCentralCharacterSpace ρ χ).toSubmodule ≃ₗ⋆[ℂ]
      (generalizedCentralCharacterSpace σ (conjugateComplexCharacter χ)).toSubmodule where
  toFun v := ⟨e v, (mem_generalizedCentralCharacterSpace_conjugate_iff e he χ v).mpr
    v.property⟩
  invFun w := ⟨e.symm w,
    (mem_generalizedCentralCharacterSpace_conjugate_iff e he χ (e.symm w)).mp
      (by simp)⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv w := Subtype.ext (e.apply_symm_apply w)
  map_add' v w := Subtype.ext (e.map_add v w)
  map_smul' c v := Subtype.ext (e.map_smulₛₗ c v)

/-- In particular the full generalized space vanishes on one side precisely
when the corresponding conjugated space vanishes on the other. -/
theorem generalizedCentralCharacterSpace_conjugate_eq_bot_iff
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (χ : Subgroup.center G →* ℂˣ) :
    generalizedCentralCharacterSpace σ (conjugateComplexCharacter χ) = ⊥ ↔
      generalizedCentralCharacterSpace ρ χ = ⊥ := by
  constructor
  · intro h
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    have hw := (mem_generalizedCentralCharacterSpace_conjugate_iff e he χ v).mpr hv
    rw [h] at hw
    change e v = 0 at hw
    change v = 0
    exact e.injective (by simpa only [map_zero] using hw)
  · intro h
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    have hv := (mem_generalizedCentralCharacterSpace_conjugate_iff e he χ v).mp hw
    rw [h] at hv
    change v = 0 at hv
    change e v = 0
    rw [hv, map_zero]

/-- Equivariant conjugate-linear equivalence conjugates every central exponent,
including the open-kernel condition. -/
theorem isCentralExponent_conjugate_iff [TopologicalSpace G]
    (e : V ≃ₗ⋆[ℂ] W) (he : ∀ g v, e (ρ g v) = σ g (e v))
    (χ : Subgroup.center G →* ℂˣ) :
    IsCentralExponent σ (conjugateComplexCharacter χ) ↔ IsCentralExponent ρ χ := by
  simp only [IsCentralExponent, conjugateComplexCharacter_ker]
  exact and_congr Iff.rfl
    (not_congr (generalizedCentralCharacterSpace_conjugate_eq_bot_iff e he χ))

end CentralSpaces

end Langlands

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The actual inverse half modulus is real, hence is fixed by conjugation. -/
theorem star_closedInverseHalfCharacter
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G)) (m : M) :
    starRingEnd ℂ (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) =
      (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) := by
  simp [HaarModulus.closedInverseHalfCharacter, Jacquet.inverseHalfCharacter_apply]

/-- The Hermitian Jacquet equivalence intertwines the actual normalized Levi
actions: conjugation fixes the real inverse-half-modulus factor. -/
theorem unitaryJacquetConjugateEquiv_apply_action
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (b : InvariantPositiveForm A.representation)
    (m : M) (q : (normalizedJacquetFunctor U M hU hMU).obj A) :
    unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b
        (((normalizedJacquetFunctor U M hU hMU).obj A).representation m q) =
      ((normalizedJacquetFunctor U M hU hMU).obj A.contragredient).representation m
        (unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b q) := by
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation U 1 q
  let e : Jacquet.Localization.Coinvariants A.representation U 1 ≃ₗ⋆[ℂ]
      Jacquet.Localization.Coinvariants (smoothContragredient A.representation) U 1 :=
    unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b
  change e ((HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) •
      Jacquet.Localization.mk A.representation U 1 (A.representation m v)) =
    (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) •
      Jacquet.Localization.mk (smoothContragredient A.representation) U 1
        (smoothContragredient A.representation m (b.toSmoothDual hA.1 v))
  rw [e.map_smulₛₗ, star_closedInverseHalfCharacter]
  change (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) •
      Jacquet.Localization.mk (smoothContragredient A.representation) U 1
        (b.toSmoothDual hA.1 (A.representation m v)) = _
  rw [b.toSmoothDual_apply_action hA.1]

/-- The Hermitian equivalence on actual normalized Jacquet modules restricts
to their generalized central-character spaces with conjugated characters. -/
def unitaryJacquetCentralCharacterEquiv
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (b : InvariantPositiveForm A.representation)
    (χ : Subgroup.center M →* ℂˣ) :
    (generalizedCentralCharacterSpace
      ((normalizedJacquetFunctor U M hU hMU).obj A).representation χ).toSubmodule ≃ₗ⋆[ℂ]
    (generalizedCentralCharacterSpace
      ((normalizedJacquetFunctor U M hU hMU).obj A.contragredient).representation
      (conjugateComplexCharacter χ)).toSubmodule :=
  conjugateGeneralizedCentralCharacterEquiv
    (unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b)
    (unitaryJacquetConjugateEquiv_apply_action U M hU hMU hcofinal A hA b) χ

/-- Same-subgroup normalized Jacquet central exponents of an admissible
unitarizable representation and of its smooth dual correspond by conjugation. -/
theorem unitaryJacquet_isCentralExponent_conjugate_iff
    (U M : Subgroup G) (hU : IsClosed (U : Set G))
    (hMU : M ≤ Subgroup.normalizer (U : Set G))
    (hcofinal : CompactOpenCofinal G) (A : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (hunitary : IsUnitarizable A.representation)
    (χ : Subgroup.center M →* ℂˣ) :
    IsCentralExponent
        ((normalizedJacquetFunctor U M hU hMU).obj A.contragredient).representation
        (conjugateComplexCharacter χ) ↔
      IsCentralExponent
        ((normalizedJacquetFunctor U M hU hMU).obj A).representation χ := by
  obtain ⟨b⟩ := hunitary
  exact isCentralExponent_conjugate_iff
    (unitaryJacquetConjugateEquiv U M hU hMU hcofinal A hA b)
    (unitaryJacquetConjugateEquiv_apply_action U M hU hMU hcofinal A hA b) χ

end Langlands.Aubert.General
