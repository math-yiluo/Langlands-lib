import Langlands.BaseChange.Norm
import Langlands.Representation.Twist.AlgebraProof
import Langlands.Representation.Classification.Segments
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Mathlib.RingTheory.Norm.Defs

/-!
# The σ-lift of a supercuspidal representation: definitions

For a field `F` and a commutative `F`-algebra `E`: the characters of `Fˣ` trivial on the
norms `N_{E/F}(Eˣ)` (Henniart–Lemaire's group `K(E/F)`, II.1.3) and the stabilizer in it
of the isomorphism class of a representation `π` of `GL_n(F)` (II.4.12). For a
nonarchimedean local field `E` and `σ : E ≃ₐ[F] E`: the normalized parabolically induced
representation `P × P^σ × ⋯ × P^{σ^{s-1}}` of `GL_{s n₁}(E)` (II.4.12). See the paired
Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

universe u v uV uW

section NormTrivial

variable {F : Type u} [Field F] (E : Type v) [CommRing E] [Algebra F E]

/-- A character `κ` of `Fˣ` is trivial on the norms `N_{E/F}(Eˣ)`. These characters form
Henniart–Lemaire's group `K(E/F)` (II.1.3). -/
def IsNormTrivial (κ : Fˣ →* ℂˣ) : Prop :=
  ∀ x : Eˣ, κ (Units.map (Algebra.norm F : E →* F) x) = 1

/-- The trivial character is trivial on the norms. -/
theorem isNormTrivial_one : IsNormTrivial E (1 : Fˣ →* ℂˣ) :=
  fun _ => rfl

variable {E}

/-- Characters trivial on the norms are closed under products. -/
theorem IsNormTrivial.mul {κ η : Fˣ →* ℂˣ} (hκ : IsNormTrivial E κ)
    (hη : IsNormTrivial E η) : IsNormTrivial E (κ * η) := by
  intro x
  rw [MonoidHom.mul_apply, hκ x, hη x, one_mul]

/-- Characters trivial on the norms are closed under inverses. -/
theorem IsNormTrivial.inv {κ : Fˣ →* ℂˣ} (hκ : IsNormTrivial E κ) :
    IsNormTrivial E κ⁻¹ := by
  intro x
  rw [MonoidHom.inv_apply, hκ x, inv_one]

variable (E)

/-- The stabilizer of the isomorphism class of `π` in `K(E/F)`: the characters `κ` of `Fˣ`
trivial on `N_{E/F}(Eˣ)` with `π ≅ (κ ∘ det) ⊗ π` (Henniart–Lemaire, II.4.12). -/
def normTwistStabilizer {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) : Subgroup (Fˣ →* ℂˣ) where
  carrier := {κ | IsNormTrivial E κ ∧
    Nonempty (π.Equiv (twist (κ.comp GeneralLinear.determinant) π))}
  one_mem' := by
    refine ⟨isNormTrivial_one E, ?_⟩
    have h : ((1 : Fˣ →* ℂˣ).comp
        (GeneralLinear.determinant : GeneralLinear n F →* Fˣ)) = 1 := by
      ext
      rfl
    rw [h, twist_one]
    exact ⟨Representation.Equiv.refl π⟩
  mul_mem' := by
    rintro κ η ⟨hκ, ⟨eκ⟩⟩ ⟨hη, ⟨eη⟩⟩
    refine ⟨hκ.mul hη, ⟨?_⟩⟩
    rw [MonoidHom.mul_comp, ← twist_twist]
    exact eκ.trans (twistEquiv _ eη)
  inv_mem' := by
    rintro κ ⟨hκ, ⟨eκ⟩⟩
    refine ⟨hκ.inv, ⟨?_⟩⟩
    have e := twistEquiv ((κ.comp GeneralLinear.determinant)⁻¹) eκ
    rw [twist_inv_twist, ← MonoidHom.inv_comp] at e
    exact e.symm

/-- Membership in `normTwistStabilizer`. -/
theorem mem_normTwistStabilizer {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear n F) V) (κ : Fˣ →* ℂˣ) :
    κ ∈ normTwistStabilizer E π ↔
      IsNormTrivial E κ ∧ Nonempty (π.Equiv (twist (κ.comp GeneralLinear.determinant) π)) :=
  Iff.rfl

end NormTrivial

section OrbitProduct

variable {F : Type u} [Field F] {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E]

/-- The product `P × P^σ × ⋯ × P^{σ^{s-1}}` (Henniart–Lemaire, II.4.12): normalized parabolic
induction to `GL_{s n₁}(E)`, from the standard block upper triangular parabolic subgroup with
`s` diagonal blocks of size `n₁`, of the tensor product whose `i`-th factor is
`P^{σ^i} : g ↦ P(g^{σ^i})`. -/
def sigmaOrbitProduct (σ : E ≃ₐ[F] E) (s : ℕ) {n₁ : ℕ} (hn₁ : 0 < n₁) {W : Type uW}
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GeneralLinear n₁ E) W) :=
  (LocalFieldData.ofInstances E).normalizedProductInduced
    (GeneralLinear.BlockShape.uniform s n₁ hn₁)
    (fun i => P.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom)

/-- For `s = 1` the product is `P` itself, after the rank transport `1 * n₁ = n₁`. -/
theorem sigmaOrbitProduct_one_equiv (σ : E ≃ₐ[F] E) {n₁ : ℕ} (hn₁ : 0 < n₁) {W : Type uW}
    [AddCommGroup W] [Module ℂ W] (P : Representation ℂ (GeneralLinear n₁ E) W)
    (hP : IsSmooth P) :
    Nonempty ((sigmaOrbitProduct σ 1 hn₁ P).Equiv
      (P.comp (GeneralLinear.reindex (R := E)
        (finCongr (Nat.one_mul n₁).symm)).symm.toMonoidHom)) := by
  have h1 : ∀ g : GeneralLinear n₁ E, entrywiseAut (σ ^ 0) n₁ g = g := by
    intro g
    rw [pow_zero]
    exact entrywiseAut_one_apply g
  have hτ : ∀ i : Fin (GeneralLinear.BlockShape.uniform 1 n₁ hn₁).length,
      IsSmooth (P.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom) := by
    intro i
    have hi : (i : ℕ) = 0 := by
      have := i.2
      simp only [GeneralLinear.BlockShape.uniform_length] at this
      omega
    have hP' : P.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom = P := by
      ext g : 1
      rw [hi]
      exact congrArg P (h1 g)
    rw [hP']
    exact hP
  have e := (LocalFieldData.ofInstances E).singleBlockNormalizedProductEquiv
    (GeneralLinear.BlockShape.uniform 1 n₁ hn₁) rfl
    (fun i => P.comp (entrywiseAut (σ ^ (i : ℕ)) n₁).toMonoidHom) hτ ⟨0, Nat.one_pos⟩
  refine ⟨e.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ W) ?_)⟩
  intro g
  apply LinearMap.ext
  intro w
  change P (entrywiseAut (σ ^ 0) n₁ _) w = P _ w
  exact congrArg (fun x => P x w) (h1 _)

end OrbitProduct

end Langlands.BaseChange
