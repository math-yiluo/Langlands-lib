import Langlands.AbelianScheme.Tate.RationalPrimeHom

/-! # Actual prime rational Tate maps and rational isomorphisms -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj ModuleCat.Algebra

namespace Langlands.AbelianScheme.Tate.PrimeAdic

universe u
variable {S : Scheme.{u}} (T : Over S) (p : ℕ) [Fact p.Prime]
  {A B C : AbelianScheme S}

/-- The published rational Hom map extends the actual group-scheme Tate map. -/
theorem rationalHomMap_ofHom_groupHom (f : A ⟶ B) :
    rationalHomMap T p (Rationalization.ofHom f) =
      GroupScheme.Tate.PrimeAdic.rationalMap T p (AbelianScheme.groupHom f) :=
  rationalHomMap_ofHom T p f

/-- Rational scalar multiplication in the existing Hom space scales its Tate map. -/
theorem rationalHomMap_smul (q : ℚ) (f : Rationalization.Hom A B) :
    rationalHomMap T p (q • f) = q • rationalHomMap T p f :=
  map_smul (rationalHomMap T p) q f

/-- Evaluation of the rational extension on an integral homomorphism and a pure tensor. -/
@[simp] theorem rationalHomMap_ofHom_tmul (f : A ⟶ B) (a : ℚ_[p])
    (x : Integral A T p) :
    rationalHomMap T p (Rationalization.ofHom f) (a ⊗ₜ[ℤ_[p]] x) =
      a ⊗ₜ[ℤ_[p]] map T p f x := by
  rw [rationalHomMap_ofHom, rationalMap_tmul]

/-- Evaluation on a rational multiple of an integral homomorphism. -/
theorem rationalHomMap_tmul_apply (q : ℚ) (f : A ⟶ B) (x : Rational A T p) :
    rationalHomMap T p (q ⊗ₜ[ℤ] f) x = q • rationalMap T p f x := rfl

/-- The actual endomorphism action extends the published integral Tate map. -/
@[simp] theorem rationalEndAction_ofEnd (A : AbelianScheme S)
    (f : CategoryTheory.End A) :
    rationalEndAction T p A (Rationalization.ofEnd A f) = rationalMap T p f := by
  change rationalHomMap T p (Rationalization.ofHom f) = _
  exact rationalHomMap_ofHom T p f

/-- A rational isomorphism induces an equivalence of the actual prime Tate modules. -/
def rationalIso (e : Rationalization.of A ≅ Rationalization.of B) :
    Rational A T p ≃ₗ[ℚ_[p]] Rational B T p :=
  ((rationalizedFunctor T p).mapIso e).toLinearEquiv

@[simp] theorem rationalIso_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (x : Rational A T p) :
    rationalIso T p e x = rationalHomMap T p e.hom x := rfl

@[simp] theorem rationalIso_refl :
    rationalIso T p (Iso.refl (Rationalization.of A)) =
      LinearEquiv.refl ℚ_[p] (Rational A T p) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T p) x

theorem rationalIso_trans (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C) :
    rationalIso T p (e.trans f) = (rationalIso T p e).trans (rationalIso T p f) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T p e.hom f.hom) x

@[simp] theorem rationalIso_symm (e : Rationalization.of A ≅ Rationalization.of B) :
    rationalIso T p e.symm = (rationalIso T p e).symm := by
  apply LinearEquiv.ext
  intro x
  rfl

end Langlands.AbelianScheme.Tate.PrimeAdic
