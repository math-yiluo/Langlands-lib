import Langlands.AlgebraicGeometry.Modules.AffinePushforwardEulerCharacteristicProof
import Langlands.AlgebraicGeometry.Modules.CechResolution.Acyclic
import Langlands.AlgebraicGeometry.Modules.PullbackQuasicoherent
import Mathlib.CategoryTheory.Retract

/-! # Cohomology retraction from a trace along an affine morphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- The `R`-module cohomology functors `Hⁿ(X, -)` are additive. -/
instance DerivedSections.relativeCohomology_additive {X : Scheme.{u}} {R : CommRingCat.{u}}
    (g : X ⟶ Spec R) (n : ℕ) : (DerivedSections.relativeCohomology g n).Additive :=
  inferInstanceAs ((DerivedSections.relativeGlobalSections g).rightDerived n).Additive

/-- Over a field `K`, if `i ≫ r = d • 𝟙` with `(d : K) ≠ 0`, then `A` is a retract of `B`. -/
def retractOfCompEqNsmul {K : Type u} [Field K] {A B : ModuleCat.{u} K} (i : A ⟶ B)
    (r : B ⟶ A) (d : ℕ) (hd : (d : K) ≠ 0) (h : i ≫ r = d • 𝟙 A) : Retract A B where
  i := i
  r := (d : K)⁻¹ • r
  retract := by
    rw [Linear.comp_smul, h, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hd,
      one_smul]

open DerivedSections in
/-- Let `h : X ⟶ Y` be affine, `g : Y ⟶ Spec K` and `M` quasi-coherent on `Y`. A morphism
`t : h_* h^* M ⟶ M` with `η ≫ t = d • 𝟙` and `(d : K) ≠ 0` exhibits `Hⁿ(Y, M)` as a retract
of `Hⁿ(X, h^* M)`. -/
def cohomologyRetractOfTrace {K : Type u} [Field K] {X Y : Scheme.{u}} (h : X ⟶ Y)
    [IsAffineHom h] (g : Y ⟶ Spec (CommRingCat.of K)) (M : Y.Modules) [M.IsQuasicoherent]
    (d : ℕ) (hd : (d : K) ≠ 0)
    (t : (Scheme.Modules.pushforward h).obj ((Scheme.Modules.pullback h).obj M) ⟶ M)
    (ht : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M ≫ t = d • 𝟙 M)
    (n : ℕ) :
    Retract ((relativeCohomology g n).obj M)
      ((relativeCohomology (h ≫ g) n).obj ((Scheme.Modules.pullback h).obj M)) :=
  let e := affinePushforwardCohomologyIso h g ((Scheme.Modules.pullback h).obj M) n
  retractOfCompEqNsmul
    ((relativeCohomology g n).map ((Scheme.Modules.pullbackPushforwardAdjunction h).unit.app M)
      ≫ e.inv)
    (e.hom ≫ (relativeCohomology g n).map t) d hd (by
      have : (relativeCohomology g n).Additive := DerivedSections.relativeCohomology_additive g n
      rw [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, ht, Functor.map_nsmul,
        CategoryTheory.Functor.map_id])

/-- Over a field `K`, let `f : X ⟶ Y` be an affine morphism of `K`-schemes and `M` a
quasi-coherent module on `Y`. A morphism `t : f_* f^* M ⟶ M` whose composite with the unit
`M ⟶ f_* f^* M` is `d • 𝟙` with `(d : K) ≠ 0` makes `Hⁿ(Y, M)` a retract of `Hⁿ(X, f^* M)`. -/
theorem finiteFlatCohomologyRetract_of_trace {K : Type u} [Field K]
    {X Y : Over (Spec (CommRingCat.of K))} (f : X ⟶ Y) [IsAffineHom f.left]
    (M : Y.left.Modules) [M.IsQuasicoherent] (d : ℕ) (hd : (d : K) ≠ 0)
    (t : (Scheme.Modules.pushforward f.left).obj ((Scheme.Modules.pullback f.left).obj M) ⟶ M)
    (ht : (Scheme.Modules.pullbackPushforwardAdjunction f.left).unit.app M ≫ t = d • 𝟙 M)
    (n : ℕ) :
    Nonempty (Retract ((DerivedSections.relativeCohomology Y.hom n).obj M)
      ((DerivedSections.relativeCohomology X.hom n).obj
        ((Scheme.Modules.pullback f.left).obj M))) := by
  rw [← Over.w f]
  exact ⟨cohomologyRetractOfTrace f.left Y.hom M d hd t ht n⟩

end Langlands.AlgebraicGeometry.Modules
