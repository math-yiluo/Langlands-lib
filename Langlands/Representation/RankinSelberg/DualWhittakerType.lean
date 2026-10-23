import Langlands.Representation.Whittaker.DualTransform
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.CuspidalSupport.GroupTransport

/-!
# Inverse transpose preserves Whittaker type

Weyl translation gives an actual equivalence of functional spaces. Finite
generation and admissibility are transported through the group automorphism.
No identification with the smooth contragredient is used.
-/

noncomputable section

namespace Langlands

universe uR uG uH uF uV

/-- Finite generation over the group algebra is preserved by pullback through
an actual group equivalence. -/
theorem finite_asModule_comp_mulEquiv
    {R : Type uR} [CommRing R] {G : Type uG} [Group G]
    {H : Type uH} [Group H] {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (e : H ≃* G)
    (hρ : Module.Finite (MonoidAlgebra R G) ρ.asModule) :
    Module.Finite (MonoidAlgebra R H) (Representation.asModule (ρ.comp e.toMonoidHom)) := by
  let := hρ
  have heq : (Representation.asAlgebraHom (ρ.comp e.toMonoidHom)).comp
      (MonoidAlgebra.domCongr R R e.symm).toAlgHom = ρ.asAlgebraHom := by
    ext g
    simp [MonoidAlgebra.domCongr_single,
      Representation.asAlgebraHom_single]
  let f : ρ.asModule →ₛₗ[(MonoidAlgebra.domCongr R R e.symm).toRingEquiv.toRingHom]
      Representation.asModule (ρ.comp e.toMonoidHom) :=
    { toFun := fun v => v
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a v
        exact congrArg (fun T : Module.End R V => T v) (DFunLike.congr_fun heq a).symm }
  exact Module.Finite.of_surjective f (fun v => ⟨v, rfl⟩)

namespace Whittaker

open GeneralLinear HarmonicAnalysis

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

omit [TopologicalSpace F] in
/-- Pulling back twice recovers the original representation. -/
@[simp] theorem inverseTransposePullback_involutive :
    inverseTransposePullback (inverseTransposePullback π) = π := by
  ext g v
  change π (inverseTranspose (n + 1) F (inverseTranspose (n + 1) F g)) v = π g v
  rw [inverseTranspose_involutive]

/-- Weyl translation transports functionals for any two characters exchanged
by the reflected unipotent map. Both directions are explicit. -/
def reflectedFunctionalEquiv
    (θ θ' : upperUnipotent (n + 1) F →* ℂˣ)
    (hθ : ∀ u, θ (reflectedUnipotent u) = θ' u)
    (hθ' : ∀ u, θ' (reflectedUnipotent u) = θ u) :
    functionals (upperUnipotent (n + 1) F) θ π ≃ₗ[ℂ]
      functionals (upperUnipotent (n + 1) F) θ' (inverseTransposePullback π) where
  toFun ℓ := ⟨ℓ.val.comp (π (weylLong (n + 1) F)), by
    intro u v
    change ℓ.val (π (weylLong (n + 1) F)
      (π (inverseTranspose (n + 1) F u.val) v)) =
        (θ' u : ℂ) * ℓ.val (π (weylLong (n + 1) F) v)
    have he : weylLong (n + 1) F * inverseTranspose (n + 1) F u.val =
        (reflectedUnipotent u).val * weylLong (n + 1) F := by
      simp only [reflectedUnipotent_val, mul_assoc, weylLong_mul_self, mul_one]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply,
      ℓ.property, hθ]⟩
  invFun ℓ := ⟨ℓ.val.comp (π (weylLong (n + 1) F)), by
    intro u v
    change ℓ.val (π (weylLong (n + 1) F) (π u.val v)) =
      (θ u : ℂ) * ℓ.val (π (weylLong (n + 1) F) v)
    have he : weylLong (n + 1) F * u.val =
        inverseTranspose (n + 1) F (reflectedUnipotent u).val *
          weylLong (n + 1) F := by
      simp only [reflectedUnipotent_val, map_mul, inverseTranspose_weylLong,
        inverseTranspose_involutive, mul_assoc, weylLong_mul_self, mul_one]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
    change ℓ.val (inverseTransposePullback π (reflectedUnipotent u).val
      (π (weylLong (n + 1) F) v)) = _
    rw [ℓ.property, hθ']⟩
  left_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (weylLong (n + 1) F) (π (weylLong (n + 1) F) v)) = ℓ.val v
    rw [← Module.End.mul_apply, ← map_mul, weylLong_mul_self, map_one,
      Module.End.one_apply]
  right_inv ℓ := by
    apply Subtype.ext
    ext v
    change ℓ.val (π (weylLong (n + 1) F) (π (weylLong (n + 1) F) v)) = ℓ.val v
    rw [← Module.End.mul_apply, ← map_mul, weylLong_mul_self, map_one,
      Module.End.one_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Standard functionals correspond to inverse-character functionals on the
inverse-transpose pullback, by the existing actual dual-functional formula. -/
def dualFunctionalEquiv (ψ : UnitaryAdditiveCharacter F) :
    glFunctionals ψ n π ≃ₗ[ℂ] glInverseFunctionals ψ n (inverseTransposePullback π) :=
  reflectedFunctionalEquiv π _ _ (standardCharacter_reflected ψ)
    (inverseStandardCharacter_reflected ψ)

@[simp] theorem dualFunctionalEquiv_apply (ψ : UnitaryAdditiveCharacter F)
    (ℓ : glFunctionals ψ n π) : dualFunctionalEquiv π ψ ℓ = dualFunctional ψ π ℓ := rfl

/-- The inverse-character case reverses in the same manner. -/
def dualInverseFunctionalEquiv (ψ : UnitaryAdditiveCharacter F) :
    glInverseFunctionals ψ n π ≃ₗ[ℂ] glFunctionals ψ n (inverseTransposePullback π) :=
  reflectedFunctionalEquiv π _ _ (inverseStandardCharacter_reflected ψ)
    (standardCharacter_reflected ψ)

@[simp] theorem dualInverseFunctionalEquiv_apply (ψ : UnitaryAdditiveCharacter F)
    (ℓ : glInverseFunctionals ψ n π) (v : V) :
    (dualInverseFunctionalEquiv π ψ ℓ).val v = ℓ.val (π (weylLong (n + 1) F) v) := rfl

end Whittaker

namespace RankinSelberg

open GeneralLinear HarmonicAnalysis Whittaker

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Inverse transpose preserves Whittaker type, reversing the standard character. -/
theorem isOfWhittakerType_inverseTransposePullback
    (hπ : IsOfWhittakerType n (standardCharacter ψ n) π) :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) (inverseTransposePullback π) := by
  refine ⟨isAdmissible_comp_continuousMulEquiv π
    (inverseTransposeContinuous (n + 1) F) hπ.1,
    finite_asModule_comp_mulEquiv π (inverseTranspose (n + 1) F) hπ.2.1, ?_⟩
  obtain ⟨e⟩ := hπ.2.2
  exact ⟨(dualFunctionalEquiv π ψ).symm.trans e⟩

/-- The inverse-character version also preserves Whittaker type. -/
theorem isOfWhittakerType_inverseTransposePullback_inverse
    (hπ : IsOfWhittakerType n (inverseStandardCharacter ψ n) π) :
    IsOfWhittakerType n (standardCharacter ψ n) (inverseTransposePullback π) := by
  refine ⟨isAdmissible_comp_continuousMulEquiv π
    (inverseTransposeContinuous (n + 1) F) hπ.1,
    finite_asModule_comp_mulEquiv π (inverseTranspose (n + 1) F) hπ.2.1, ?_⟩
  obtain ⟨e⟩ := hπ.2.2
  exact ⟨(dualInverseFunctionalEquiv π ψ).symm.trans e⟩

/-- Whittaker type for the transformed model is equivalent to that for the source. -/
theorem isOfWhittakerType_inverseTransposePullback_iff :
    IsOfWhittakerType n (inverseStandardCharacter ψ n) (inverseTransposePullback π) ↔
      IsOfWhittakerType n (standardCharacter ψ n) π := by
  constructor
  · intro h
    simpa only [inverseTransposePullback_involutive] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ (inverseTransposePullback π) h
  · exact isOfWhittakerType_inverseTransposePullback ψ π

end RankinSelberg
end Langlands
