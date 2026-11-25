/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalOpenToOpenCycle

/-!
# Open-to-open restriction of normalized resolution comparisons

Source: Stacks Project, Tags 03F3 (2) and 0A50, expanded on Hom cocycles.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

/-- Open-to-open restriction identity for a normalized comparison.
Source: Stacks Project, Tag 03F3 (2), and Tag 0A50, proof;
the Hom-cocycle expansion of the parent restriction argument.
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-open-to-open)

Proof: Represent the class by a cycle z in the resolution evaluated at B,
using surjectivity of homologyπ in abelian groups. The free-sheaf sections
adjunction identifies the section iCycles q z with a morphism f from the
free sheaf on B to I.cocomplex.X q. Naturality in the coefficient sheaf
and the cycle equation show that f composed with the differential is zero.
Let a be the image of the inclusion A to B under etaleOpenFreeSheaf X.
Naturality of the free-sheaf adjunction identifies a composed with f with
the restriction of the original section. Naturality of homologyπ identifies
the resulting cycle class with the homology map of etaleSectionMap.
Apply c.open_cocycle at A and B. The formula I.mk₀_comp_extMk expresses
the class at A as precomposition of I.extMk f by a. Expand the two
etaleOpenObjectCohomologyMap expressions. Pulling back a along A.ι and
precomposing with the identity generator at A equals pulling back the
identity generator at B along X.homOfLE h, with the constant-sheaf and
inverse-image composition comparisons inserted. This generator equality is already proved by
`etaleOpenFreeSheafUnit_coherence B A h`: its left side contains the
direct pullback followed by the composition comparison, and its right
side contains the constant comparison followed by the pulled-back unit.
Use Ext.mapExactFunctor_comp and Ext.mapExactFunctor_mk₀ to move
precomposition through inverse image. Substitute the generator equality.
Then `Ext.exactFunctorCompositionComparison` for the two inverse-image
functors and upperStarComp replaces the successive Ext pullbacks by the
direct one. Ext associativity and cancellation of the composition
isomorphism give cohomologyMap along X.homOfLE h followed by the inverse
composition comparison, exactly openCohomologyRestriction. Surjectivity
of homologyπ finishes for every class. This argument includes q = 0,
A = B, empty opens, and the zero sheaf. -/
theorem resolutionSection_canonical_open_to_open {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (I : InjectiveResolution G)
    (c : ResolutionSectionCanonicalComparison G I) :
    ∀ (A B : X.Opens) (h : A ≤ B) q x,
      c.openEquiv A q (HomologicalComplex.homologyMap (etaleSectionMap
        (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
          Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex) q x) =
        openCohomologyRestriction h G q (c.openEquiv B q x) := by
  intro A B h q x
  let K := (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let L := (((etaleSectionFunctor (Scheme.Etale.mk A.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let φ := etaleSectionMap
    (MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤)
      (X := X) (A := Scheme.Etale.mk A.ι) (B := Scheme.Etale.mk B.ι)
      (X.homOfLE h) (X.homOfLE_ι h) trivial) I.cocomplex
  have hs : Function.Surjective (K.homologyπ q) :=
    (AddCommGrpCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance
  obtain ⟨z, rfl⟩ := hs x
  have hmap : HomologicalComplex.homologyMap φ q (K.homologyπ q z) =
      L.homologyπ q ((HomologicalComplex.cyclesMap φ q) z) := by
    have hn := HomologicalComplex.homologyπ_naturality φ q
    exact congrArg (fun f => f z) hn
  rw [hmap]
  exact resolutionSection_canonical_open_to_open_cycle G I c A B h q z
end AlgebraicGeometry.Etale
