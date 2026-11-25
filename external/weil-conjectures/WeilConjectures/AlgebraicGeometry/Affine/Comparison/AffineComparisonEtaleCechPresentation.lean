/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineComparisonEtaleCechSystem
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
import WeilConjectures.AlgebraicGeometry.Affine.Comparison.AffineComparisonEtaleCoverPresentation

/-!
# Geometric étale presentations of finite affine pro-étale coverings

Source: Stacks Project, Tag 099U, the two finite Čech limit reductions.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- A finite affine pro-étale covering and all of its repeated intersections admit
compatible affine étale covering approximations. This is purely geometric; it does
not involve sections, coefficients, cochain complexes, or cocycles.
Source: Stacks Project, Tag 099U, the two finite Čech limit reductions, using
Tags 01ZM, 01ZN and 07RP for affine étale finite-presentation descent.
(blueprint: lem-cbc-affine-etale-cech-presentation).

Proof: The one-factor nerve is isomorphic to the corresponding member U_i.
Transport pro-affine-étaleness through this isomorphism. Apply the finite-family
presentation theorem, whose proof factors the finite disjoint union through one
surjection, presents that surjection, and descends its finite affine open cover.
This provides a common small cofiltered index, affine étale covering families,
and scheme limit cones for the base and every original member.
Construct repeated intersections and their structure maps using the wide-pullback
universal property. The base and member limit properties identify each repeated
intersection as the scheme limit of its stages. Projection equations prove the
transition, cone and face identities. Each stage intersection is affine because
it is a finite limit of affine schemes. No nonemptiness assumption is introduced;
the empty family, repetitions, and empty schemes use the same construction. -/
theorem exists_affine_etale_cech_system
    (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n),
      proAffineEtale (Presheaf.cechNerveObj U y).left.hom)
    (hcover : Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
      Scheme.ProEt.topology Y V) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsCofiltered I)
      (S : AffineEtaleCechSystem Y V U I),
      ∀ k y, Nonempty (IsLimit
        ((Scheme.ProEt.forget Y ⋙ Over.forget Y).mapCone (S.nerveCone k y))) := by
  have hUi (a : Fin n) : proAffineEtale (U a).left.hom := by
    let e := (Over.forget V).mapIso (productUniqueIso (fun _ : Fin 1 ↦ U a))
    have : IsIso e.inv.left := by
      change IsIso ((Scheme.ProEt.forget Y ⋙ Over.forget Y).map e.inv)
      infer_instance
    have hw := MorphismProperty.Over.w e.inv
    change e.inv.left ≫ (Presheaf.cechNerveObj U (fun _ : Fin 1 ↦ a)).left.hom =
      (U a).left.hom at hw
    rw [← hw, proAffineEtale.cancel_left_of_respectsIso]
    exact hU 0 (fun _ ↦ a)
  obtain ⟨I, _, _, P, hcov, hAff, hAff₀, hB, hA⟩ :=
    exists_affine_etale_cover_presentation Y V hV U hUi hcover
  refine ⟨I, inferInstance, inferInstance, systemOfPresentation U P hcov hAff hAff₀, ?_⟩
  intro k y
  exact ⟨presentedNerveIsLimit U P hB.some (fun a ↦ (hA a).some) k y⟩

end AlgebraicGeometry.ProEtale
