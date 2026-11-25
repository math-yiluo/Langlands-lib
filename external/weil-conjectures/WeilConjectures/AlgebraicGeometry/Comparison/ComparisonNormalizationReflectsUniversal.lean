/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedLocalIsomorphismSheaf
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Reflection of universal scalar arrows through etale comparison

Source: Stacks Project, Tags 06YS, 0G7E, 0D6D and 09B1.
(blueprint: lem-weil-pbc-comparison-normalization-reflects-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem reflects_universal_of_invertible_mate
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {L' : D ⥤ E} {U' : E ⥤ D}
    (a : L ⊣ U) (b : L' ⊣ U') (F : A ⥤ D) (G : B ⥤ E)
    [G.ReflectsIsomorphisms] (β : U ⋙ F ≅ G ⋙ U')
    [IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom)))]
    {X : A} {Y : B} (d : X ⟶ U.obj Y)
    (h : StructuredArrow.IsUniversal
      (StructuredArrow.mk (F.map d ≫ β.hom.app Y) : StructuredArrow _ U')) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk d : StructuredArrow _ U)) := by
  let t := (a.homEquiv X Y).symm d
  let m := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom))
  have ht : a.unit.app X ≫ U.map t = d := by
    simpa only [Adjunction.homEquiv_unit] using (a.homEquiv X Y).apply_symm_apply d
  have hw : b.unit.app (F.obj X) ≫ U'.map (m.app X ≫ G.map t) =
      F.map d ≫ β.hom.app Y := by
    have hu := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β.hom) X
    change F.map (a.unit.app X) ≫ β.hom.app (L.obj X) =
      b.unit.app (F.obj X) ≫ U'.map (m.app X) at hu
    rw [Functor.map_comp, ← Category.assoc, ← hu]
    have hn := β.hom.naturality t
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← F.map_comp, ht]
  let f : (StructuredArrow.mk (b.unit.app (F.obj X)) : StructuredArrow _ U') ⟶
      StructuredArrow.mk (F.map d ≫ β.hom.app Y) :=
    StructuredArrow.homMk (m.app X ≫ G.map t) hw
  have : IsIso f := isIso_of_isInitial (mkInitialOfLeftAdjoint _ b _) h f
  have hi : IsIso (m.app X ≫ G.map t) :=
    inferInstanceAs (IsIso ((StructuredArrow.proj _ U').map f))
  have : IsIso (G.map t) := IsIso.of_isIso_comp_left (m.app X) (G.map t)
  have : IsIso t := isIso_of_reflects_iso t G
  exact ⟨(mkInitialOfLeftAdjoint _ a X).ofIso (StructuredArrow.isoMk (asIso t) ht)⟩

private theorem comparison_reflects_isomorphisms (Z : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] :
    Functor.ReflectsIsomorphisms
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory where
  reflects {X Y} f _ := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).map
        ((DerivedCategory.homologyFunctor _ n).map f)) :=
      (NatIso.isIso_map_iff
        (Functor.mapDerivedCategoryHomologyFunctorIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z) n) f).2 (by
        change IsIso ((DerivedCategory.homologyFunctor _ n).map
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory.map f))
        infer_instance)
    exact isIso_of_reflects_iso _ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z)

private theorem comparison_coefficients_eq (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    localIsomorphismComparisonCoefficients (X := Z) q =
      (ProEtale.pbcDerivedComparisonRestrict Z q).symm := by
  have he : normalizationPullbackIso Z.smallEtaleTopology (toProEt Z)
      (ProEt.topology Z) q = (ProEtale.pbcComparisonRestrict Z q).symm := by
    apply Iso.ext
    change normalizationPullbackMate Z.smallEtaleTopology (toProEt Z)
      (ProEt.topology Z) q = (ProEtale.pbcComparisonRestrict Z q).inv
    have hm := ProEtale.comparison_restrict_mate Z q
    have hs := congrArg
      (fun z ↦ ((mateEquiv (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) Z)
        (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) Z)).symm z))
      (congrArg (fun z ↦ TwoSquare.mk _ _ _ _ z) hm)
    simpa only [Equiv.symm_apply_apply, normalizationPullbackMate,
      ProEtale.comparisonAdjunction, ProEtale.comparisonLowerStar,
      ProEtale.comparisonUpperStar, Sheaf.restrictScalars,
      TwoSquare.mk] using hs.symm
  apply Iso.ext
  simp only [localIsomorphismComparisonCoefficients, he,
    ProEtale.pbcDerivedComparisonRestrict, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
    Sheaf.restrictScalars, Category.assoc]

/-- Comparison reflects universality of a coefficient arrow between bounded complexes.

Source: `sites-cohomology.tex`, K-flat resolutions (06YS), their pullback (0G7E),
and composition of derived pullbacks (0D6D); `proetale.tex`, comparison (09B1).
(blueprint: lem-weil-pbc-comparison-normalization-reflects-universal).

Proof: realize fixed-ring sheaves as modules over the constant ring sheaf. Derived
extension of coefficients is left adjoint to the exact restriction functor in this
presentation. Resolve the source by a K-flat complex with flat terms. Comparison
inverse image preserves such complexes. Its scalar-extension comparison is the
canonical isomorphism between the two sheafified balanced tensor products; the
unit in both orders sends x to 1 tensor x. Therefore the adjunct of the displayed
compared arrow is the comparison image of the original scalar adjunct, after this
isomorphism. The assumed initiality says the compared adjunct is invertible.
Comparison inverse image is exact and conservative on sheaves: its sheaf unit is
invertible. Hence it reflects acyclic cones, so it reflects isomorphisms in the
derived category. The original adjunct is consequently invertible. Transporting
the initial adjunction unit along that isomorphism proves the stated initiality.
This argument uses K-flat resolutions without a Tor bound, also for zero rings and
on the empty scheme; the boundedness assumptions on the given objects are harmless.
-/
theorem comparisonNormalization_reflects_universal (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] [Finite R] [Finite S]
    (q : R →+* S)
    {C : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {C' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (_hC : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C))
    (_hC' : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj C'))
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology q).obj C')
    (h : Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory.map δ ≫
          (localIsomorphismComparisonCoefficients q).hom.app C') :
        StructuredArrow _ (normalizationRestrict (ProEt.topology Z) q)))) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk δ : StructuredArrow _
        (normalizationRestrict Z.smallEtaleTopology q))) := by
  obtain ⟨h⟩ := h
  rw [comparison_coefficients_eq Z q] at h
  have := comparison_reflects_isomorphisms Z S
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology q)
  let b := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (ProEt.topology Z) q)
  have : IsIso (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _
      (ProEtale.pbcDerivedComparisonRestrict Z q).symm.hom))) := by
    change IsIso (ProEtale.pbcComparisonReductionMap Z q)
    exact ProEtale.pbcComparisonReductionMap_isIso Z q
  exact reflects_universal_of_invertible_mate a b
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} R) Z).mapDerivedCategory
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) Z).mapDerivedCategory
    (ProEtale.pbcDerivedComparisonRestrict Z q).symm δ h

end AlgebraicGeometry.Scheme
