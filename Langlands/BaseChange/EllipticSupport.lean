import Langlands.BaseChange.Norm
import Langlands.BaseChange.OrbitalIntegral
import Langlands.JacquetLanglands.RegularElliptic

/-!
# Test functions supported in the regular elliptic set

Henniart–Lemaire (2011), II.6.3, II.6.4 and II.6.6 (printed pp. 120, 121 and 123), use test
functions that vanish off the regular elliptic (respectively σ-elliptic) elements at one
place (the support clauses of their conditions `c_{v₁}(f)` and `c^σ_{v₁}(φ)`). This module
defines:

* `IsEllipticSupported f`: `f : GL_n(F) → ℂ` vanishes off the regular elliptic elements
  (the Library's `JacquetLanglands.IsRegularElliptic`);
* `IsSigmaEllipticSupported σ l φ`: `φ : GL_n(E) → ℂ` vanishes off the σ-elliptic elements
  (`IsSigmaElliptic σ l`).

The lemmas show that these supports are contained in the regular and σ-regular sets (so the
predicates refine `IsRegularSupported` and `IsSigmaRegularSupported`), and that both
predicates hold for `0` and are preserved by sums and by multiplication by constants.
See the paired Markdown.
-/

namespace Langlands.BaseChange

open Langlands.JacquetLanglands

universe u v

section Elliptic

variable {F : Type u} [Field F] {n : ℕ}

/-- `f : GL_n(F) → ℂ` is supported in the regular elliptic set `G(F)_e`: every `g` with
`f g ≠ 0` is regular elliptic. -/
def IsEllipticSupported (f : GeneralLinear n F → ℂ) : Prop :=
  ∀ g : GeneralLinear n F, f g ≠ 0 → IsRegularElliptic g

/-- A function supported in the regular elliptic set is supported in the regular semisimple
set. -/
theorem IsEllipticSupported.isRegularSupported {f : GeneralLinear n F → ℂ}
    (hf : IsEllipticSupported f) : IsRegularSupported f :=
  fun g hg => (hf g hg).isRegularSemisimple

theorem isEllipticSupported_zero : IsEllipticSupported (0 : GeneralLinear n F → ℂ) :=
  fun _ hg => absurd rfl hg

theorem IsEllipticSupported.add {f f' : GeneralLinear n F → ℂ} (hf : IsEllipticSupported f)
    (hf' : IsEllipticSupported f') : IsEllipticSupported (f + f') := by
  intro g hg
  by_cases h : f g = 0
  · refine hf' g fun h' => hg ?_
    rw [Pi.add_apply, h, h', add_zero]
  · exact hf g h

theorem IsEllipticSupported.const_mul {f : GeneralLinear n F → ℂ} (hf : IsEllipticSupported f)
    (c : ℂ) : IsEllipticSupported fun g => c * f g :=
  fun g hg => hf g (right_ne_zero_of_mul hg)

end Elliptic

section SigmaElliptic

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

/-- `φ : GL_n(E) → ℂ` is supported in the σ-elliptic set: every `δ` with `φ δ ≠ 0` is
σ-elliptic, that is associated with a regular elliptic element of `GL_n(F)`. -/
def IsSigmaEllipticSupported (σ : E ≃ₐ[F] E) (l : ℕ) (φ : GeneralLinear n E → ℂ) : Prop :=
  ∀ δ : GeneralLinear n E, φ δ ≠ 0 → IsSigmaElliptic σ l δ

/-- A function supported in the σ-elliptic set is supported in the σ-regular set. -/
theorem IsSigmaEllipticSupported.isSigmaRegularSupported {σ : E ≃ₐ[F] E} {l : ℕ}
    {φ : GeneralLinear n E → ℂ} (hφ : IsSigmaEllipticSupported σ l φ) :
    IsSigmaRegularSupported σ l φ := by
  intro δ hδ
  obtain ⟨γ, hδγ, hγ⟩ := hφ δ hδ
  exact ⟨γ, hδγ, hγ.isRegularSemisimple⟩

theorem isSigmaEllipticSupported_zero (σ : E ≃ₐ[F] E) (l : ℕ) :
    IsSigmaEllipticSupported σ l (0 : GeneralLinear n E → ℂ) :=
  fun _ hδ => absurd rfl hδ

theorem IsSigmaEllipticSupported.add {σ : E ≃ₐ[F] E} {l : ℕ} {φ φ' : GeneralLinear n E → ℂ}
    (hφ : IsSigmaEllipticSupported σ l φ) (hφ' : IsSigmaEllipticSupported σ l φ') :
    IsSigmaEllipticSupported σ l (φ + φ') := by
  intro δ hδ
  by_cases h : φ δ = 0
  · refine hφ' δ fun h' => hδ ?_
    rw [Pi.add_apply, h, h', add_zero]
  · exact hφ δ h

theorem IsSigmaEllipticSupported.const_mul {σ : E ≃ₐ[F] E} {l : ℕ}
    {φ : GeneralLinear n E → ℂ} (hφ : IsSigmaEllipticSupported σ l φ) (c : ℂ) :
    IsSigmaEllipticSupported σ l fun δ => c * φ δ :=
  fun δ hδ => hφ δ (right_ne_zero_of_mul hδ)

end SigmaElliptic

end Langlands.BaseChange
