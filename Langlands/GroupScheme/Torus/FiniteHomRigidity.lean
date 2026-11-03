import Langlands.GroupScheme.Torus.Integral
import Langlands.GroupScheme.Rational.LeviFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Ideal.GoingUp

/-! # Finite-map rigidity for closed tori -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An integral map into a domain reflects injectivity through any following ring map. -/
theorem injective_of_integral_comp_injective
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [Nontrivial A] [IsDomain B]
    (f : A →+* B) (g : B →+* C) (hf : f.IsIntegral)
    (hfg : Function.Injective (g.comp f)) : Function.Injective g := by
  let : Algebra A B := f.toAlgebra
  let : Algebra.IsIntegral A B := ⟨hf⟩
  apply (RingHom.injective_iff_ker_eq_bot g).mpr
  apply Ideal.eq_bot_of_under_eq_bot (R := A)
  change (RingHom.ker g).comap f = ⊥
  rw [RingHom.comap_ker]
  exact (RingHom.injective_iff_ker_eq_bot _).mp hfg

/-- A closed subscheme of an integral affine finite cover is the whole cover when its
restriction is schematically dominant over the affine base. -/
theorem isIso_of_closedImmersion_finite_comp_schematic
    {X Y Z : Scheme.{u}} [IsAffine Y] [IsAffine Z] [IsIntegral Y] [Nonempty Z]
    (a : X ⟶ Y) (q : Y ⟶ Z) [IsClosedImmersion a] [IsFinite q]
    [IsSchemeTheoreticallyDominant (a ≫ q)] : IsIso a := by
  let : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  have hcomp : Function.Injective (a.appTop.hom.comp q.appTop.hom) := by
    have h : Function.Injective (a ≫ q).appTop := (a ≫ q).app_injective ⊤
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using h
  exact injective_of_integral_comp_injective q.appTop.hom a.appTop.hom
    q.finite_appTop.to_isIntegral hcomp

end Langlands.GroupScheme
