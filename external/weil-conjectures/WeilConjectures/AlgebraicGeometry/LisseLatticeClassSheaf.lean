/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
public import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport

/-!
# Locally inhabited lattice-class sheaves

Source: Bhatt--Scholze, Proposition 6.8.4(6).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

/-- Lattice classes form a locally constant, locally inhabited sheaf, and every
section has a representative lattice on the localized pro-etale site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), construction of the lattice sheaf.
(auxiliary; not a blueprint node)

Proof: identify the spectral-norm coefficient field with its `WithAbs` presentation
and transport the module along the continuous coefficient-ring isomorphism. Apply
`integralLatticeSheaf_locallyConstant`. Its quotient presentation gives representatives.
For a trivialization of rank n the resulting sheaf is the constant coset sheaf
GL_n(E)/GL_n(A). The identity matrix supplies a section on each trivializing member,
including rank zero. Localization identifies these slice constant sheaves with
constant sheaves on the members' small sites. The sets of classes are small: send a
class to its embedded integral submodule, recorded as a subset on each object of the
slice. The presentation's restriction criterion at the identity shows this assignment
is injective. Shrink each set along this injection and transport all restriction maps
and the sheaf axiom through the bijections. This yields the stated universe for F.
On the empty scheme the empty trivializing cover suffices. -/
theorem exists_lisse_lattice_class_sheaf (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (L : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l E X)))
    (hL : L.IsFiniteLocallyFree) :
    ∃ F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1)),
      Scheme.IsProEtaleLocallyConstant X F ∧
      (∃ (I : Type (u + 1)) (U : I → X.ProEt),
        (Scheme.ProEt.topology X).CoversTop U ∧
          ∀ i : I, Nonempty (F.obj.obj (op (U i)))) ∧
      ∀ U : X.ProEt, Nonempty (F.obj.obj (op U)) →
        Nonempty (IntegralLatticePair (lisseIntegerToField l E X) L U) := by
  obtain ⟨eA, eE, hsquare, hfree⟩ := lisse_coefficient_normalization l E X L hL
  let L' := (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eE.hom)).obj L
  have : L'.IsFiniteLocallyFree := hfree
  obtain ⟨F, c, hpresentation, hcosets⟩ :=
    integralLatticeSheaf_locallyConstant X l (ULift.{u} E) L'
  apply small_lattice_sheaf_of_coset_presentation (lisseIntegerToField l E X)
    (integralLatticeCoefficientMap X l (ULift.{u} E)) eA eE hsquare L L'
    (Iso.refl _) hfree F c hpresentation
  intro U n e
  obtain ⟨k, hk⟩ := hcosets U n e
  exact ⟨integralMatrixCosets (latticeCoefficientIntegers l (ULift.{u} E)) n,
    inferInstance, ⟨k⟩⟩

end AlgebraicGeometry.ProEtale
