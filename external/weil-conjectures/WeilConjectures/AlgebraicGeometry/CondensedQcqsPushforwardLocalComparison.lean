/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.CondensedHypercoverComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianEvaluationColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineAcyclicHypercover
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# The sectionwise pushforward continuity comparison

Source: Hemo--Richarz--Scholbach, Constructible sheaves, Lemma 5.3(1).
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_isIso_of_total
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory A]
    {I : Type*} [Category* I] [HasColimitsOfShape I A] [HasColimitsOfShape I B]
    [HasColimitsOfShape I C]
    (F : DerivedCategory A ⥤ B) (ev : B ⥤ C) [PreservesColimitsOfShape I ev]
    (T : CochainComplex A ℤ ⥤ CochainComplex C ℤ) [PreservesColimitsOfShape I T]
    (q : ℤ) [PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor C (.up ℤ) q)]
    (e : (CochainComplex.Plus.ι A ⋙ DerivedCategory.Q ⋙ F ⋙ ev) ≅
      (CochainComplex.Plus.ι A ⋙ T ⋙ HomologicalComplex.homologyFunctor C (.up ℤ) q))
    (D : I ⥤ CochainComplex A ℤ) (a : ℤ)
    (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n)) :
    IsIso (ev.map (colimit.desc (D ⋙ (DerivedCategory.Q ⋙ F))
      ((DerivedCategory.Q ⋙ F).mapCocone
        ((Cocone.precompose (Functor.whiskerLeft D
          ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A))).obj
            (colimit.cocone (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A)))))) := by
  let S := DerivedCategory.Q ⋙ F
  let H := HomologicalComplex.homologyFunctor C (.up ℤ) q
  let E : I ⥤ CochainComplex A ℤ := D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor A
  have hE (i : I) : CochainComplex.IsStrictlyGE (E.obj i) a := by
    change ((D.obj i).truncGE a).IsStrictlyGE a
    infer_instance
  have hL : CochainComplex.IsStrictlyGE (colimit E) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [IsZero.iff_id_eq_zero]
    apply (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n)
      (colimit.isColimit E)).hom_ext
    intro i
    have := hE i
    exact ((E.obj i).isZero_of_isStrictlyGE a n hn).eq_of_src _ _
  let P : I ⥤ CochainComplex.Plus A :=
    ObjectProperty.lift _ E (fun i ↦ ⟨a, hE i⟩)
  let L : CochainComplex.Plus A := ⟨colimit E, a, hL⟩
  let c : Cocone P :=
    { pt := L
      ι :=
        { app i := ObjectProperty.homMk (colimit.ι E i)
          naturality i j g := by
            apply ObjectProperty.hom_ext
            exact (colimit.cocone E).ι.naturality g } }
  have ht : IsColimit ((CochainComplex.Plus.ι A ⋙ T ⋙ H).mapCocone c) :=
    isColimitOfPreserves (T ⋙ H) (colimit.isColimit E)
  have hs := IsColimit.mapCoconeEquiv e.symm ht
  change IsColimit ((S ⋙ ev).mapCocone (colimit.cocone E)) at hs
  let α : D ⟶ E := Functor.whiskerLeft D
    ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans A)
  have hα (i : I) : IsIso ((Functor.whiskerRight α (S ⋙ ev)).app i) := by
    have : (D.obj i).IsGE a := by
      rw [CochainComplex.isGE_iff]
      intro n hn
      exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ha i n hn)
    have : QuasiIso ((D.obj i).πTruncGE a) := inferInstance
    change IsIso ((S ⋙ ev).map ((D.obj i).πTruncGE a))
    dsimp [S]
    infer_instance
  have : IsIso (Functor.whiskerRight α (S ⋙ ev)) :=
    NatIso.isIso_of_isIso_app _
  have hd := (IsColimit.precomposeHomEquiv
    (asIso (Functor.whiskerRight α (S ⋙ ev))) _).symm hs
  let cD := (Cocone.precompose α).obj (colimit.cocone E)
  have hd : IsColimit (ev.mapCocone (S.mapCocone cD)) :=
    hd.ofIsoColimit (Cocone.ext (Iso.refl _) (fun i ↦ by
      simp [cD, Functor.map_comp]))
  change IsIso (ev.map (colimit.desc (D ⋙ S) (S.mapCocone cD)))
  let φ : ev.mapCocone (colimit.cocone (D ⋙ S)) ⟶ ev.mapCocone (S.mapCocone cD) :=
    { hom := ev.map (colimit.desc (D ⋙ S) (S.mapCocone cD))
      w i := by
        change ev.map (colimit.ι (D ⋙ S) i) ≫ ev.map _ = _
        rw [← ev.map_comp, colimit.ι_desc]
        rfl }
  have : IsIso φ :=
    (isColimitOfPreserves ev (colimit.isColimit (D ⋙ S))).hom_isIso hd φ
  change IsIso ((Cocone.forget (D ⋙ S ⋙ ev)).map φ)
  infer_instance

noncomputable local instance
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] (X : Scheme.{u}) :
    HasZeroMorphisms (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj Λ X)) := inferInstance

set_option backward.isDefEq.respectTransparency false in
-- The proof compares explicit composed cocones in internal module categories.
set_option synthInstance.maxHeartbeats 100000 in
-- Colimit inference for internal module objects needs a larger search budget.
set_option synthInstance.maxSize 4096 in
/-- The canonical pushforward continuity comparison is invertible after evaluation
at one affine weakly contractible target object.

Source: Hemo--Richarz--Scholbach, Lemma 5.3(1), sectionwise hypercover calculation.
(auxiliary; not a blueprint node).

Proof: the good truncation projection is a quasi-isomorphism because cohomology
vanishes below the common bound a. Its target has zero terms below a. The inverse
image W of V is qcqs: base change preserves quasi-compactness and quasi-separatedness
of f, and V is affine. Choose an affine weakly contractible hypercover of W. On each
term, evaluation of module sheaves is exact and commutes with filtered colimits.
Form the alternating section bicomplex and its signed total. In degree r its
nonzero diagonal has indices 0 through r-a, so only finite products occur. The
hypercover resolution identifies this total with derived sections on W, naturally
in the coefficient complex and its maps. Exact filtered colimits identify the
homology of the total colimit with the colimit of total homology. On K-injective
resolutions, pushforward evaluated at V is evaluation at W. Evaluation at the
weakly contractible V is exact, so it commutes with pushforward cohomology. These
identifications send each original cocone leg to its sectionwise hypercover leg;
the colimit universal property therefore identifies the asserted map with the
invertible hypercover comparison. The finite diagonal remains empty below a,
and the argument also applies to an empty W. -/
theorem condensed_qcqs_pushforward_local_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ X)) ℤ)
    (a : ℤ) (ha : ∀ (i : I) (n : ℤ), n < a → IsZero ((D.obj i).homology n))
    (q : ℤ) (V : Y.ProEt) (hV : IsAffine V.left)
    (hweak : ∀ (F G : Sheaf (Scheme.ProEt.topology Y) (Type (u + 1))) (g : F ⟶ G),
      Epi g → Function.Surjective (g.hom.app (op V))) :
    IsIso (((Mod.forget (condensedRingObj Λ Y)).map
      (colimit.desc
        (D ⋙ (DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q))
        ((DerivedCategory.Q ⋙ (CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙
          DerivedCategory.homologyFunctor _ q).mapCocone
          ((Cocone.precompose (Functor.whiskerLeft D
            ((ComplexShape.embeddingUpIntGE a).πTruncGENatTrans _))).obj
              (colimit.cocone
                (D ⋙ (ComplexShape.embeddingUpIntGE a).truncGEFunctor _)))))).hom.app
                  (op V)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (condensedRingObj Λ X)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1})
    (condensedRingObj Λ Y)
  let ev : B ⥤ AddCommGrpCat.{u + 1} := Mod.forget (condensedRingObj Λ Y) ⋙
    (sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)
  let : IsAffine V.left := hV
  have hev := Scheme.ProEt.affine_weaklyContractible_abelian_evaluation_colimits
    Y V hweak
  let : PreservesColimitsOfSize.{u + 1, u + 1}
      ((sheafSections (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj (op V)) := hev.2
  have : PreservesColimitsOfShape I ev := by dsimp [ev]; infer_instance
  let W := (Scheme.proEtaleBaseChange f).obj V
  have : CompactSpace ((𝟭 Scheme).obj V.left) := Scheme.compactSpace_of_isAffine V.left
  have : QuasiSeparatedSpace ((𝟭 Scheme).obj V.left) :=
    quasiSeparatedSpace_of_isAffine V.left
  have : CompactSpace W.left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst V.hom f)
  have : QuasiSeparatedSpace W.left :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst V.hom f)
  obtain ⟨U, haff, hUweak, hzero, hone, hhigher⟩ :=
    Scheme.ProEt.exists_affine_weaklyContractible_hypercover X W
  let T := (Mod.forget (condensedRingObj Λ X)).mapHomologicalComplex (.up ℤ) ⋙
    Scheme.ProEt.abelianHypercoverTotal X W U
  have : PreservesColimitsOfSize.{u + 1, u + 1}
      (Scheme.ProEt.abelianHypercoverTotal X W U) :=
    Scheme.ProEt.abelianHypercoverTotal_preservesColimits X W U haff hUweak
  have : PreservesColimitsOfShape I T := by dsimp [T]; infer_instance
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (.up ℤ) q
  have : PreservesColimitsOfShape I H := by dsimp [H]; infer_instance
  obtain ⟨e⟩ := condensedHypercover_comparison Λ f q V hV hweak U haff hUweak
    hzero hone hhigher
  exact comparison_isIso_of_total
    ((CondensedRing.lowerStar Λ f).rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ q)
    ev T q e D a ha

end AlgebraicGeometry.ProEtale
