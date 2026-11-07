import Langlands.GroupScheme.Rational.SplitSteinbergQuotientStatement

/-! # Actual restriction of regular class functions to Steinberg's product -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme

namespace ClassFunctions

variable {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    {A : Type u} [CommRing A] [Algebra k A]

/-- Restriction of actual invariant coordinates along an affine test morphism. -/
def restriction (f : Lie.AffinePoints G A) : algebra G →ₐ[k] A :=
  (Lie.pointCoordinates G f).comp (inclusion G)

/-- The spectrum of restriction is the given morphism followed by the canonical rho. -/
theorem restriction_spec (f : Lie.AffinePoints G A) :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (restriction G f)).op =
      f ≫ rho G := by
  have h := (quotientPointCoordinates G).symm_apply_apply (f ≫ rho G)
  rw [quotientPointCoordinates_rho] at h
  exact h

/-- The canonical quotient is an isomorphism on an affine parametrization precisely
when restriction of all its invariant functions is bijective. -/
theorem isIso_comp_rho_iff_restriction_bijective (f : Lie.AffinePoints G A) :
    IsIso (f ≫ rho G) ↔ Function.Bijective (restriction G f) := by
  have : (algSpec (CommRingCat.of k)).ReflectsIsomorphisms :=
    algSpec.fullyFaithful.reflectsIsomorphisms
  rw [← restriction_spec,
    isIso_iff_of_reflects_iso _ (algSpec (CommRingCat.of k)), isIso_op_iff]
  constructor
  · intro h
    exact ConcreteCategory.bijective_of_isIso
      (CommAlgCat.ofHom (R := CommRingCat.of k) (restriction G f))
  · intro h
    let e := AlgEquiv.ofBijective (restriction G f) h
    exact (CommAlgCat.isoMk (R := CommRingCat.of k) e).isIso_hom

end ClassFunctions

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G} {r : ℕ}
    (e : Fin r ≃ p.base.support)
    (x : p.NormalizedSimpleRootParametrizations)
    (n : p.SimpleReflectionRepresentatives)

/-- The actual restriction to the polynomial coordinate algebra of the supplied
ordered Steinberg product. -/
def steinbergRestriction : ClassFunctions.algebra G →ₐ[k] MvPolynomial (Fin r) k :=
  ClassFunctions.restriction G (steinbergProduct e x n)

/-- This polynomial restriction defines exactly the canonical quotient composite. -/
theorem steinbergRestriction_spec :
    (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom (steinbergRestriction e x n)).op =
      steinbergProduct e x n ≫ ClassFunctions.rho G :=
  ClassFunctions.restriction_spec G _

/-- An algebraic criterion for the exact supplied-product quotient morphism. -/
theorem steinbergProduct_rho_isIso_iff :
    IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) ↔
      Function.Bijective (steinbergRestriction e x n) :=
  ClassFunctions.isIso_comp_rho_iff_restriction_bijective G _

/-- Polynomial generators of the invariant algebra and an invertible polynomial
restriction together imply the exact quotient isomorphism. -/
theorem steinbergProduct_rho_isIso_of_polynomial_generators
    (c : Fin r → ClassFunctions.algebra G)
    (hc : Function.Bijective
      (MvPolynomial.aeval c : MvPolynomial (Fin r) k →ₐ[k] ClassFunctions.algebra G))
    (hs : Function.Bijective ((steinbergRestriction e x n).comp (MvPolynomial.aeval c))) :
    IsIso (steinbergProduct e x n ≫ ClassFunctions.rho G) := by
  apply (steinbergProduct_rho_isIso_iff e x n).mpr
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := hc.2 a
    obtain ⟨b', rfl⟩ := hc.2 b
    exact congrArg (MvPolynomial.aeval c) (hs.1 hab)
  · intro a
    obtain ⟨b, hb⟩ := hs.2 a
    exact ⟨MvPolynomial.aeval c b, hb⟩

end SplitPinning

end Langlands.GroupScheme
