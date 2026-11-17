import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleTensor
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # Tensor powers of line bundles glued from unit cocycles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.CocycleGluing

variable {X : Scheme.{u}} {ι : Type u} {T : ι → X.Opens}

theorem IsCocycle.pow {g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ}
    (hg : IsCocycle g) (n : ℕ) : IsCocycle (g ^ n) := by
  intro i j k
  simpa only [Pi.pow_apply, Units.val_pow_eq_pow_val, map_pow, ← mul_pow] using
    congrArg (fun x => x ^ n) (hg i j k)

/-- The constant unit cocycle glues to the actual structure module. -/
def oneIso (hT : (⨆ i, T i) = ⊤) :
    structureSheaf X ≅ glued (1 : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) := by
  let e : ∀ i, Γ(structureSheaf X, T i) := fun i => (1 : Γ(X, T i))
  have he : ∀ i, Scheme.Modules.IsFrameOn (e i) (T i) := by
    intro i W hW _
    change Function.Bijective (fun r : Γ(X, W) =>
      r * X.presheaf.map (homOfLE hW).op (1 : Γ(X, T i)))
    simp only [map_one, mul_one]
    exact ⟨fun _ _ h => h, fun r => ⟨r, rfl⟩⟩
  have htrans : IsTransition e (1 : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ) := by
    intro i j
    change X.presheaf.map _ (1 : Γ(X, T j)) =
      (1 : Γ(X, T i ⊓ T j)) * X.presheaf.map _ (1 : Γ(X, T i))
    simp only [map_one, one_mul]
  exact frameIso he htrans hT

/-- The actual tensor power of a glued cocycle line is isomorphic to the line
glued from the corresponding power cocycle. -/
def powerIso (g : ∀ i j : ι, (Γ(X, T i ⊓ T j))ˣ)
    (hg : IsCocycle g) (hT : (⨆ i, T i) = ⊤) :
    (n : ℕ) → tensorPow (glued g) n ≅ glued (g ^ n)
  | 0 => oneIso hT ≪≫ eqToIso (congrArg glued (pow_zero g).symm)
  | n + 1 =>
    (tensorFunctor X).mapIso ((Iso.refl _).prod (powerIso g hg hT n)) ≪≫
      tensorIso hg (hg.pow n) hT ≪≫
        eqToIso (congrArg glued (pow_succ' g n).symm)

end Langlands.AlgebraicGeometry.Picard.CocycleGluing
