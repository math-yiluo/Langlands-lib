/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ResolutionOpenRestrictionCore
import WeilConjectures.AlgebraicGeometry.ResolutionOpenScalarCore
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionSectionsExist

/-! # Untwisted comparison of resolution sections

Source: Stacks Project, Tags 01E1 and 01E4.
(blueprint: lem-pc-resolution-open-scalar-comparison).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Raw resolution sections agree with untwisted open cohomology, naturally for
restriction to a pulled-back principal open and for multiplication by a function.

Source: Stacks Project, Tag 01E4, Lemma 20.7.3, and Tag 01E1, Lemma 20.7.1.
(blueprint: lem-pc-resolution-open-scalar-comparison).

Proof: Restrict I to Y using exact open restriction, which preserves injectives
because extension by zero is an exact left adjoint. Apply the equivalence from
modules on the over-site to modules on Y. The restricted augmentation and complex
are an injective resolution of G. Its sections on any open of Y are identified
with the original resolution's sections on the corresponding open of X by
restrictAppIso. In particular sections on Y and the inverse image of D(a) are
exactly the evaluation of f_*I on W and D(a). Use isoRightDerivedObj to compute
open cohomology by this restricted resolution. Evaluation and forgetting scalars
are exact and commute with homology, giving c and d. At each degree all comparison
maps commute with restriction of the same sections. The naturality of
isoRightDerivedObj and mapHomologyIso therefore gives the restriction equation.
The tensor-unit section s is b times its standard generator. Its nonvanishing
locus is the basic open of b: the stalk generator identifies the maximal-ideal
multiple of the module with the maximal ideal of the local ring, so its fibre
value is nonzero exactly when the germ of b is a unit. Pullback of basic opens
identifies this open with the inverse image of D(a), inside Y. Finally each
section comparison is semilinear for the pullback Γ(T,W) to Γ(Y,top). On the
restricted section complex, the endomorphism induced by G.smulHom(b^n) is
multiplication by b^n in each degree. The semilinear comparison takes this to
multiplication by a^n on the evaluated complex. Applying homology and the
naturality of the resolution comparison yields the scalar equation. This is
valid for n=0 and q=0, empty W, zero F, a=0 and invertible a, since the same
section maps, local-ring test, and exact functors cover all these cases. -/
theorem resolution_open_scalar_comparison {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let b := ((f.app W) ≫ (f ⁻¹ᵁ W).topIso.inv).hom a
    let s : Γ(𝟙_ Y.Modules, ⊤) := unitSectionsEquiv ⊤ b
    ∃ c : P.obj (op W) ≃+
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).obj G,
      (∀ (U : Y.Opens), (U : Set Y) = nonvanishingLocus (𝟙_ Y.Modules) s →
        ∃ d : P.obj (op (T.basicOpen a)) ≃+
          (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
          ∀ x : P.obj (op W),
            (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
              (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
                d ((P.map (homOfLE (T.basicOpen_le a)).op).hom x)) ∧
      (∀ (n : ℕ) (x : P.obj (op W)),
        (RingedSpace.openModuleCohomology Y.toRingedSpace q ⊤).map
          (G.smulHom (b ^ n)) (c x) = c (a ^ n • x)) := by
  dsimp
  obtain ⟨R⟩ := restrictedResolutionSections_exists I (f ⁻¹ᵁ W)
  refine ⟨resolutionOpenComparison f F I q W R, ?_, ?_⟩
  · exact resolution_open_restriction_core f F I q W a R
  · exact resolution_open_scalar_core f F I q W a R

end AlgebraicGeometry.Scheme.Modules
