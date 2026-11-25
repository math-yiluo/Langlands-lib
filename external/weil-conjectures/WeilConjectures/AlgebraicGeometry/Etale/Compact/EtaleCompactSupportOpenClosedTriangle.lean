/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.Open.OpenClosedRecollement

/-!
# Open-closed localization for relative etale compact support

Source: Stacks Project, Tag 0GKP, `lemma-relative-triangle-associated-to-open`
(blueprint: lem-weil-pbc-etale-compact-support-open-closed-triangle).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Relative compact support has an open-closed distinguished triangle and the associated
long exact sequence of cohomology sheaves. The three isomorphisms identify the vertices
with the specified compactification-dependent bounded-below pushforwards, viewed in the
ambient derived category. Since `D⁺` is strictly full and triangulated, this also specifies
its triangle in `D⁺`.

Source: Stacks Project, Tag 0GKP
(blueprint: lem-weil-pbc-etale-compact-support-open-closed-triangle).

Proof plan: (1) The quasi-compact open `U` and closed complement `Z` are qcqs, by the
quasi-separated affine-cover criterion and qcqs permanence. The open immersion is separated
of finite type; the closed immersion is finite and proper, so its composite with `f` is
separated of finite type as well. No finite presentation of the closed ideal is required.
(2) Apply `proposition-extension-zero-restriction-closed-subscheme--8` to obtain the absolute
triangle with terms `j_! j⁻¹ K`, `K`, `i_* i⁻¹ K`; the closed direct image is exact.
(3) Apply `Rp_* j_f!` from `c_f`. Extension by zero is exact; derived direct image is
triangulated, using enough injectives and the additive left exact module direct image.
(4) Compactify `j` by `(j, id)` and `i` by `(id, i)`. Their compact-support functors are
respectively `j_!` and `Ri_* = i_*`. The qcqs composition theorem identifies the outer
terms after applying `Rf_!` with those for the independently specified `c_g` and `c_h`.
Transport the arrows along these isomorphisms; invariance under triangle isomorphisms
preserves distinguishedness.
(5) The module-sheaf category is abelian. Apply the derived homology long exact sequence
at every integer degree. Its connecting map is induced by the third arrow followed by
the cohomology-shift isomorphism; exactness holds at all three positions. -/
theorem exists_compactSupport_openClosed_triangle
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {U Z X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (c_f : Compactification f) (c_g : Compactification (j ≫ f))
    (c_h : Compactification (i ≫ f)) :
    ∃ T : Triangle (DerivedCategory
        (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      Nonempty (T.obj₁ ≅
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c_g).obj
          (((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus).obj K)).obj) ∧
      Nonempty (T.obj₂ ≅
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c_f).obj
          K).obj) ∧
      Nonempty (T.obj₃ ≅
        ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c_h).obj
          (((upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus).obj K)).obj) ∧
      T ∈ distTriang _ ∧
      ∀ q : ℤ,
        ∃ (z₂ : (DerivedCategory.homologyFunctor _ q).map T.mor₁ ≫
            (DerivedCategory.homologyFunctor _ q).map T.mor₂ = 0)
          (z₃ : (DerivedCategory.homologyFunctor _ q).map T.mor₂ ≫
            DerivedCategory.HomologySequence.δ T q (q + 1) = 0)
          (z₁ : DerivedCategory.HomologySequence.δ T q (q + 1) ≫
            (DerivedCategory.homologyFunctor _ (q + 1)).map T.mor₁ = 0),
          (ShortComplex.mk _ _ z₂).Exact ∧
          (ShortComplex.mk _ _ z₃).Exact ∧
          (ShortComplex.mk _ _ z₁).Exact := by
  classical
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated j
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace i
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated i
  have : (𝟭 (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).Additive := ⟨by intros; rfl⟩
  let dU := Compactification.ofIsOpenImmersion j
  let dZ := Compactification.ofIsProper i
  let F := rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) c_f
  let JU := (upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K
  let IZ := (upperStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus.obj K
  let eU : rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) dU ≅
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus :=
    Functor.isoWhiskerLeft _
      (Functor.rightDerivedFunctorPlusNatIso (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.rightDerivedFunctorPlusIdIso _) ≪≫ Functor.rightUnitor _
  let eId : openImmersionLowerShriek (ModuleCat.{u + 1} Λ) (𝟙 Z) ≅
      𝟭 (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 Z)).leftAdjointUniq
      ((Adjunction.id).ofNatIsoRight (upperStarId (ModuleCat.{u + 1} Λ) Z).symm)
  let eZ : rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) dZ ≅
      (lowerStar (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlus :=
    Functor.isoWhiskerRight
        (Functor.mapDerivedCategoryPlusNatIso eId ≪≫ Functor.mapDerivedCategoryPlusIdIso _)
        _ ≪≫
      Functor.leftUnitor _ ≪≫
        (lowerStar (ModuleCat.{u + 1} Λ) i).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
  obtain ⟨compU⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ j f dU c_f c_g
  obtain ⟨compZ⟩ := nonempty_iso_etaleShriek_qcqs_compactification_comp Λ i f dZ c_f c_h
  obtain ⟨δ, hδ, _⟩ := exists_functorial_distTriang_openClosed Λ j i hij
  let S := Triangle.mk
    ((derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).counit.app K)
    ((upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} Λ) i).mapDerivedCategoryPlusAdjunction.unit.app K)
    (δ K)
  let G := F ⋙ DerivedCategory.Plus.ι
  let T := G.mapTriangle.obj S
  have hT : T ∈ distTriang _ := G.map_distinguished S (hδ K)
  refine ⟨T, ?_, ?_, ?_, hT, ?_⟩
  · exact ⟨DerivedCategory.Plus.ι.mapIso
      (F.mapIso ((eU.app JU).symm) ≪≫ compU.app JU)⟩
  · exact ⟨Iso.refl _⟩
  · exact ⟨DerivedCategory.Plus.ι.mapIso
      (F.mapIso ((eZ.app IZ).symm) ≪≫ compZ.app IZ)⟩
  · intro q
    have z₂ : (DerivedCategory.homologyFunctor _ q).map T.mor₁ ≫
        (DerivedCategory.homologyFunctor _ q).map T.mor₂ = 0 := by
      simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero]
    refine ⟨z₂, DerivedCategory.HomologySequence.comp_δ T hT q (q + 1),
      DerivedCategory.HomologySequence.δ_comp T hT q (q + 1), ?_, ?_, ?_⟩
    · exact DerivedCategory.HomologySequence.exact₂ T hT q
    · exact DerivedCategory.HomologySequence.exact₃ T hT q (q + 1)
    · exact DerivedCategory.HomologySequence.exact₁ T hT q (q + 1)

end AlgebraicGeometry.Etale
