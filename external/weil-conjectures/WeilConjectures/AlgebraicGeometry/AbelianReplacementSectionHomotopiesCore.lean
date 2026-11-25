/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AbelianCounitResolutionCalculation
import WeilConjectures.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts
import WeilConjectures.Algebra.Homology.MappingCylinderSplitFactorization
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Mathlib.Algebra.Homology.ModelCategory.Injective
/-! # Constructing the section homotopies before acyclicity

Source: Stacks Project, Tags 013P, 013S and 01FB.
(blueprint: new-abelian-replacement-section-homotopies-core)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
/-- Construction of the comparison map and its two homotopies; the quasi-isomorphism
property is supplied separately. No injectivity of the replacement K is required.

Proof: Forget module structures, write R for the standard abelian resolution of F,
and r for the explicit identity lift from the forgotten I. Exact inverse image is
left adjoint to abelian direct image, so direct image preserves injectives. Thus
f_*R is a nonnegative complex of injectives. Forgetting preserves the given
quasi-isomorphism l. Apply 013P(1) to lift f_*r across the forgotten l up to
homotopy, obtaining k from the forgotten K to f_*R. For a concrete construction,
extend complexes by zero to integer degrees, factor l through its mapping
cylinder, use the injective lifting property on the monic cylinder inclusion,
and compose with the cylinder section; then restrict to nonnegative degrees.
The augmentation equation for beta and the identity-lift equation for r imply
that beta followed by k and counitResolutionAdjoint become homotopic after
precomposition with the forgotten augmentation of J. The adjunction unit and
counit identities identify the two augmented maps. That augmentation is a
quasi-isomorphism, so 013S gives a homotopy of the maps themselves. Apply abelian
sections and compose with abelianPushforwardSectionsIso to obtain the first
homotopy and define q. Applying sections to the lifting homotopy gives the
second after the prescribed equation for a.inv; composing with a.hom cancels
this inverse. These are existential choices of maps only. There is no arbitrary
witness used in a definition. The argument also applies to the zero complex,
zero coefficient modules and empty schemes.

Source: Stacks Project, Tags 013P, 013S, 01FB.
(blueprint: new-abelian-replacement-section-homotopies-core) -/
theorem abelian_replacement_section_homotopies_core {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F)
    (J : InjectiveResolution ((pushforward f).obj F)) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l) (β : J.cocomplex ⟶ K)
    (hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) :
    ∃ q : ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj K ⟶
        ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
          (standardAbelianResolution X F).cocomplex,
      Nonempty (Homotopy
        (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map β ≫ q)
        (counitSectionMap f F J)) ∧
      Nonempty (Homotopy
        ((a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) ≫ q)
        (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
          (forgottenResolutionMap X I))) := by
  obtain ⟨q, hq, hr⟩ := second_section_homotopy_of_counit f I J K l hl β hβ
  exact ⟨q, hq, hr a ha⟩
end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
