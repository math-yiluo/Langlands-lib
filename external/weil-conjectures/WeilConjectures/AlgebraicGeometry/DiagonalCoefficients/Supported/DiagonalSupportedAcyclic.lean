/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization

/-! # Acyclicity of a closed diagonal source under a retraction

Source: Stacks, proetale.tex, lemma-closed-immersion-complement-retrocompact-exact,
and the supported-source computation in the diagonal tower trace.
(blueprint: lem-sfb-diagonal-supported-acyclic).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a v w
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section Retract

variable {C D : Type a} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
  (G : D ⥤ C) (F : C ⥤ D) [G.Additive] [F.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [G.PreservesKInjectiveComplexes] (e : G ⋙ F ≅ 𝟭 D)

include e in
private theorem unit_on_image (K : CochainComplex D ℤ) :
    IsIso (F.rightDerivedFunctorUnitQ ((G.mapHomologicalComplex (.up ℤ)).obj K)) := by
  obtain ⟨J, hJ, z, _, hz⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
  let I : K.KInjectiveResolution := ⟨J, z, hz, hJ⟩
  let v := (G.mapHomologicalComplex (.up ℤ)).map I.ι
  have : QuasiIso v := by dsimp only [v]; infer_instance
  have : PreservesFiniteLimits (G ⋙ F) := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits (G ⋙ F) := preservesFiniteColimits_of_natIso e.symm
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map v) := by
    change QuasiIso (((G ⋙ F).mapHomologicalComplex (.up ℤ)).map I.ι)
    infer_instance
  have hI : IsIso (F.rightDerivedFunctorUnitQ
      ((G.mapHomologicalComplex (.up ℤ)).obj I.I)) := by
    rw [F.rightDerivedFunctorUnitQ_eq]
    infer_instance
  have hn := F.rightDerivedFunctorUnitQ_naturality v
  have : IsIso (F.rightDerivedFunctorUnitQ
      ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map v)) := by
    erw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map (DerivedCategory.Q.map v))

include e in
private theorem single_on_image (M : D) :
    IsIso (diagonalTraceRightSingle F (canonicalDiagonalRightDerived F) (G.obj M)) := by
  let K := (HomologicalComplex.single D (.up ℤ) 0).obj M
  let c := (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).inv.app M
  have : IsIso (F.rightDerivedFunctorUnitQ
      ((HomologicalComplex.single D (.up ℤ) 0 ⋙ G.mapHomologicalComplex (.up ℤ)).obj M)) :=
    unit_on_image G F e K
  have hn := F.rightDerivedFunctorUnitQ_naturality c
  have : IsIso (F.rightDerivedFunctorUnitQ
      ((HomologicalComplex.single C (.up ℤ) 0).obj (G.obj M)) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map c)) := by
    erw [← hn]
    infer_instance
  have : IsIso (F.rightDerivedFunctorUnitQ
      ((HomologicalComplex.single C (.up ℤ) 0).obj (G.obj M))) :=
    IsIso.of_isIso_comp_right _ (F.rightDerivedFunctor.map (DerivedCategory.Q.map c))
  unfold diagonalTraceRightSingle
  change IsIso (_ ≫ _ ≫ F.rightDerivedFunctorUnitQ _ ≫ _)
  infer_instance

end Retract

/-- The supported regular module is acyclic for every retraction of the diagonal.

Source: Stacks, proetale.tex, lemma-closed-immersion-complement-retrocompact-exact;
diagonal tower trace, supported-source identification.
(blueprint: lem-sfb-diagonal-supported-acyclic).

Proof: The Noetherian surface has quasi-compact open complement of its closed diagonal.
Closed localization makes diagonal direct image exact. Its inverse image is exact,
so diagonal direct image preserves K-injective complexes. Resolve the regular module
on the diagonal by a K-injective resolution and push that resolution forward. It
remains a resolution because diagonal direct image is exact. Applying the retraction
pushforward gives the original resolution, through the ordinary direct-image
composition isomorphism and Delta f = id. The full derived unit is invertible on the
pushed resolution by K-injective computation, hence also on the original single
supported module by naturality and the two quasi-isomorphisms. No condition on the
coefficient ring beyond commutativity is used, including for the zero ring or empty Y. -/
theorem diagonal_supported_acyclic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    [IsNoetherian (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (h : diagonalImmersion Y ≫ f = 𝟙 (ProjectiveLine Y)) :
    IsIso (diagonalTraceRightSingle (CondensedRing.lowerStar Λ f)
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f)) (source Λ Y)) := by
  let i := diagonalImmersion Y
  have hloc : PreservesFiniteColimits
      (ringSheafDirectImage i (condensedRingObj Λ (diagonalSurface Y))) :=
    (ringSheaf_closed_localization i i.openComplement.ι
      (by
        classical
        ext x
        have hx := Set.ext_iff.mp i.range_eq_compl_range_openComplement_ι x
        change x ∈ Set.range i ↔ x ∉ Set.range i.openComplement.ι at hx
        change x ∈ Set.range i.openComplement.ι ↔ x ∉ Set.range i
        tauto)
      (condensedRingObj Λ (diagonalSurface Y))).1
  have : PreservesFiniteColimits (CondensedRing.linearLowerStar Λ i) := hloc
  have : PreservesFiniteColimits (CondensedRing.lowerStar Λ i) :=
    preservesFiniteColimits_of_natIso (CondensedRing.comapPullbackHomCompIso Λ i)
  have : (CondensedRing.lowerStar Λ i).PreservesKInjectiveComplexes :=
    (CondensedRing.upperStarLowerStarAdjunction Λ i).preservesKInjectiveComplexes
  exact single_on_image (CondensedRing.lowerStar Λ i) (CondensedRing.lowerStar Λ f)
    (CondensedRing.lowerStarComp Λ i f ≪≫ CondensedRing.lowerStarCongr Λ h ≪≫
      CondensedRing.lowerStarId Λ (ProjectiveLine Y))
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
