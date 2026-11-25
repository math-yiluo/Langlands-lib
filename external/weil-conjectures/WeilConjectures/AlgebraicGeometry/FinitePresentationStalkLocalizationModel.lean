/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.FinitePresentation

/-! # Finite presentation models for affine morphism stalks

Source: Stacks Project, Tags 00R7 and 00RH, the essentially finitely presented stalk algebras.
(blueprint: lem-sbc-finite-presentation-stalk-localization-model)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- A stalk of an affine morphism of finite presentation is essentially finitely presented
over the corresponding base stalk.

Proof: let A = Gamma(Y), B = Gamma(X), and phi = g.appTop. The affine stalks
are R = A_p and S = B_q, where p is the contraction of q under phi. Put
M = phi(A minus p) and P = M inverse B. Localization of the finitely presented
map phi gives a finitely presented map R to P. Since M is contained in B minus q,
localization transitivity makes S a localization of P at the image of B minus q.
The localization universal property defines both algebra structures. Check their
composite against the original stalk map on germs from A; localization extensionality
and the germ-stalk-map equation give the required scalar tower.
Source: Stacks Project, Tag 00RH, application of Tag 00R7 to localized affine algebras.
(blueprint: lem-sbc-finite-presentation-stalk-localization-model) -/
theorem exists_finitePresentation_stalk_localization_model
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X ⟶ Y)
    [LocallyOfFinitePresentation g] (x : X) :
    let R := Y.presheaf.stalk (g x)
    let S := X.presheaf.stalk x
    letI : Algebra R S := (g.stalkMap x).hom.toAlgebra
    ∃ (P : CommRingCat.{u}) (_ : Algebra R P) (_ : Algebra P S),
      IsScalarTower R P S ∧ Algebra.FinitePresentation R P ∧
        ∃ W : Submonoid P, IsLocalization W S := by
  let R := Y.presheaf.stalk (g x)
  let S := X.presheaf.stalk x
  let : Algebra R S := (g.stalkMap x).hom.toAlgebra
  let A := Γ(Y, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A R := Y.presheaf.algebra_section_stalk ⟨g x, by simp⟩
  let : Algebra B S := X.presheaf.algebra_section_stalk ⟨x, by simp⟩
  let p := (isAffineOpen_top Y).primeIdealOf ⟨g x, by simp⟩
  let q := (isAffineOpen_top X).primeIdealOf ⟨x, by simp⟩
  have : IsLocalization.AtPrime R p.asIdeal :=
    (isAffineOpen_top Y).isLocalization_stalk ⟨g x, by simp⟩
  have : IsLocalization.AtPrime S q.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, by simp⟩
  let φ : A →+* B := g.appTop.hom
  let M := p.asIdeal.primeCompl.map φ
  have hM : M ≤ q.asIdeal.primeCompl := by
    rintro b ⟨a, ha, rfl⟩
    change φ a ∉ q.asIdeal
    change a ∉ p.asIdeal at ha
    have heq := IsAffineOpen.comap_primeIdealOf_appLE ⊤ (isAffineOpen_top Y)
      ⊤ (isAffineOpen_top X) (show ⊤ ≤ g ⁻¹ᵁ ⊤ by simp) (show x ∈ (⊤ : X.Opens) by simp)
    have heq' : Ideal.comap φ q.asIdeal = p.asIdeal := by
      simpa [p, q, φ, Scheme.Hom.appLE] using congrArg PrimeSpectrum.asIdeal heq
    exact fun hb ↦ ha (heq' ▸ hb)
  let P := Localization M
  let ψ : R →+* P := IsLocalization.map P φ (Submonoid.le_comap_map p.asIdeal.primeCompl)
  let : Algebra R P := ψ.toAlgebra
  let : Algebra P S := IsLocalization.localizationAlgebraOfSubmonoidLe P S M
    q.asIdeal.primeCompl hM
  have : IsScalarTower B P S :=
    IsLocalization.localization_isScalarTower_of_submonoid_le P S M q.asIdeal.primeCompl hM
  have ht : IsScalarTower R P S := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext p.asIdeal.primeCompl
    ext a
    change (g.stalkMap x).hom (algebraMap A R a) =
      algebraMap P S (ψ (algebraMap A R a))
    rw [show ψ (algebraMap A R a) = algebraMap B P (φ a) from
      IsLocalization.map_eq (Submonoid.le_comap_map p.asIdeal.primeCompl) a]
    rw [← IsScalarTower.algebraMap_apply B P S]
    exact g.germ_stalkMap_apply ⊤ x (by simp) a
  have hfp : Algebra.FinitePresentation R P :=
    RingHom.finitePresentation_localizationPreserves φ p.asIdeal.primeCompl R P
      g.finitePresentation_appTop
  exact ⟨CommRingCat.of P, inferInstance, inferInstance, ht, hfp,
    q.asIdeal.primeCompl.map (algebraMap B P),
    IsLocalization.isLocalization_of_submonoid_le P S M q.asIdeal.primeCompl hM⟩

end AlgebraicGeometry

