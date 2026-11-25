import Langlands.AlgebraicGeometry.Modules.MonoidalTensorComparison
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowSection_smul_monoidalV2
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Scalar gauges of sections from trivialized tensor powers -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules.TensorPowerGauge

variable {X : Scheme.{u}}

/-- The monoidal tensor powers of a module sheaf agree with the right-associated explicit
sheafified tensor powers. -/
def tensorPowComparison (L : X.Modules) : (n : ℕ) →
    L.tensorPowFLT n ≅ Langlands.Scheme.Modules.tensorPow L n
  | 0 => Iso.refl _
  | n + 1 => β_ (L.tensorPowFLT n) L ≪≫ monoidalTensorIso L (L.tensorPowFLT n) ≪≫
      (Langlands.Scheme.Modules.tensorFunctor X).mapIso
        ((Iso.refl L).prod (tensorPowComparison L n))

variable {L : X.Modules} {n : ℕ} (τ : L.tensorPowFLT n ≅ 𝟙_ X.Modules)

/-- The scalar function obtained by sending the `n`-th tensor power of a local section through
a trivialization of the `n`-th tensor power. -/
def gauge {U : X.Opens} (s : Γ(L, U)) : Γ(X, U) :=
  τ.hom.app U (Scheme.Modules.tensorPowSectionFLT s n)

lemma gauge_restrict {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) :
    X.presheaf.map i.op (gauge τ s) = gauge τ (L.presheaf.map i.op s) := by
  unfold gauge
  rw [← Scheme.Modules.map_tensorPowSection]
  have h := congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
    (τ.hom.mapPresheaf.naturality i.op)) (Scheme.Modules.tensorPowSectionFLT s n)
  exact h.symm

lemma gauge_smul {U : X.Opens} (g : Γ(X, U)) (s : Γ(L, U)) :
    gauge τ (g • s) = g ^ n * gauge τ s := by
  unfold gauge
  rw [Scheme.Modules.tensorPowSection_smul_monoidalV2, Scheme.Modules.Hom.app_smul]
  rfl

lemma isUnit_gauge {U : X.Opens} {s : Γ(L, U)} (hs : Scheme.Modules.IsFrameOn s U) :
    IsUnit (gauge τ s) := by
  have h := (hs.tensorPowSection_monoidalV2 n).map_iso τ
  obtain ⟨g, hg⟩ := (h (le_refl U) (le_refl U)).2 (Scheme.Modules.unitSection U)
  have hid : (homOfLE (le_refl U)).op = 𝟙 (Opposite.op U) := rfl
  simp only [hid, CategoryTheory.Functor.map_id] at hg
  have hg' : g * gauge τ s = 1 := hg
  exact IsUnit.of_mul_eq_one_right g hg'

end Langlands.AlgebraicGeometry.Modules.TensorPowerGauge
