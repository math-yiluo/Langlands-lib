/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Torsion.TorsionCohomologicalDimensionAffineLimit
import WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SixFunctors.HigherDirectImageAffineEtaleBound
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Uniform classical pro-étale cohomological bounds
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

@[expose] public section

namespace AlgebraicGeometry.ProEtale

/-- Uniform cohomological bounds for a morphism `f : S ⟶ R` and an étale sheaf `F` on `S`:
with `d` the topological Krull dimension of `S` (zero if `S` is empty), the pro-étale
cohomology of `F` on pro-affine-étale objects over `S` and over `R` (after base change), and
the derived étale pushforward `R f_* F`, vanish in degrees above `2 * d + 1`. -/
def HasClassicalUniformBounds {S R : Scheme.{u}} (f : S ⟶ R)
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  let dS : ℕ := (topologicalKrullDim S).unbotD 0 |>.toNat
  let eS : ℕ := 2 * dS + 1
  (∀ (U : S.ProEt), proAffineEtale U.hom → ∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} U.left).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar AddCommGrpCat.{u + 1} U.hom).obj
              ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F)))))) ∧
    (∀ (V : R.ProEt), proAffineEtale V.hom → ∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} (pullback f V.hom)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ProEtale.upperStar AddCommGrpCat.{u + 1} (pullback.fst f V.hom)).obj
              ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj F)))))) ∧
    (∀ q : ℤ, (eS : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
        ((Etale.lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))

private theorem finite_dimension_bound {k : Type u} [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] :
    topologicalKrullDim X ≤
      (((topologicalKrullDim X).unbotD 0).toNat : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  generalize topologicalKrullDim X = n at *
  induction n using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe n =>
    induction n using ENat.recTopCoe with
    | top => exact False.elim ((ENat.natCast_ne_top d)
        (top_le_iff.mp (WithBot.coe_le_coe.mp hd)))
    | coe n => simp

private theorem finiteType_cd {k : Type u} [Field k] (c d : ℕ)
    (hk : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c)
    {W : Scheme.{u}} (aW : W ⟶ Spec (.of k))
    [LocallyOfFiniteType aW] [QuasiCompact aW]
    (hd : topologicalKrullDim W ≤ (d : WithBot ℕ∞)) :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE W (2 * d + c) := by
  intro F hF q hq
  have hfield (G : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (hG : G.IsTorsion) (n : ℕ) (hn : c < n) : Subsingleton (Sheaf.H G n) := by
    obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of k)) n
    have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
        Etale.cohomology AddCommGrpCat.{u + 1} (Spec (.of k)) (n : ℤ)).obj G) :=
      hk G hG n hn
    exact (e.app G).addCommGroupIsoToAddEquiv.injective.subsingleton
  have hH := Scheme.subsingleton_H_of_two_mul_add_lt c d hfield aW hd F hF q hq
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso W q
  have : Subsingleton ((Sheaf.functorH W.smallEtaleTopology q).obj F) := hH
  exact (e.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

private theorem etaleStage_cd {k : Type u} [Field k] (c d : ℕ)
    (hk : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) c)
    {X W : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (w : W ⟶ X) [Etale w] [CompactSpace W] :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE W (2 * d + c) := by
  have : QuasiCompact (w ≫ aX) := quasiCompact_of_compactSpace _
  exact finiteType_cd c d hk (w ≫ aX)
    (w.topologicalKrullDim_le_of_etale.trans hd)

private theorem comparison_vanishing {X W : Scheme.{u}} (w : W ⟶ X)
    (c : ℕ) (hc : Scheme.HasTorsionEtaleCohomologicalDimensionLE W c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℤ) (hq : (c : ℤ) < q) :
    IsZero ((DerivedCategory.homologyFunctor _ q).obj
      ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} W).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((ProEtale.upperStar AddCommGrpCat.{u + 1} w).obj
            ((comparisonUpperStar AddCommGrpCat.{u + 1} X).obj F))))) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  let G := (Etale.upperStar AddCommGrpCat.{u + 1} w).obj F
  have hG : G.IsTorsion := Etale.isTorsion_upperStar w hF
  have hz : IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} W n).obj
      ((DerivedCategory.singleFunctor _ 0).obj G)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (hc G hG n (by exact_mod_cast hq))
  let Γe := Sheaf.Γ W.smallEtaleTopology AddCommGrpCat.{u + 1}
  let Γp := Sheaf.Γ (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}
  let ee := Sheaf.ΓNatIsoSheafSections W.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale W)
  let ep := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}
    (Scheme.ProEt.isTerminalMkId W)
  have : ((sheafSections W.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (Opposite.op (MorphismProperty.Over.mk ⊤ (𝟙 W) (by infer_instance)))).Additive :=
    { map_add := rfl }
  have : ((sheafSections (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).obj
      (Opposite.op (Scheme.ProEt.mk (𝟙 W)))).Additive := { map_add := rfl }
  have he := hz.of_iso (Γe.homologyRightDerivedFunctorObjSingleFunctorIso G n).symm
  have he' := he.of_iso ((NatIso.rightDerived ee n).app G).symm
  have hp := isZero_rightDerived_globalSectionsFunctor_comparisonUpperStar_obj
    AddCommGrpCat.{u + 1} W G n he'
  have hp' := hp.of_iso ((NatIso.rightDerived ep n).app
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj G))
  have hp'' := hp'.of_iso (Γp.homologyRightDerivedFunctorObjSingleFunctorIso
    ((comparisonUpperStar AddCommGrpCat.{u + 1} W).obj G) n)
  exact hp''.of_iso ((DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
    ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} W).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso
        ((comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} w).app F))))

private theorem proAffine_cd {X V : Scheme.{u}} (v : V ⟶ X)
    (hv : proAffineEtale v) (c : ℕ)
    (hstage : ∀ {W : Scheme.{u}} (w : W ⟶ X) [Etale w] [IsAffine W],
      Scheme.HasTorsionEtaleCohomologicalDimensionLE W c) :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE V c := by
  obtain ⟨I, _, _, D, t, s, hs, ht⟩ := hv
  have (i : I) : IsAffine (D.obj i) := (ht i).1.2.1
  have (i : I) : Etale (t.app i) := (ht i).1.1
  exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit D
    (Cone.mk V s) hs c (fun i ↦ hstage (t.app i))

private theorem proAffine_pullback_cd {X Y V : Scheme.{u}} (g : X ⟶ Y) (v : V ⟶ Y)
    (hv : proAffineEtale v) (c : ℕ)
    (hstage : ∀ {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W],
      Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback w g) c)
    (hqc : ∀ {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W],
      CompactSpace ↑(pullback w g))
    (hqs : ∀ {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W],
      QuasiSeparatedSpace ↑(pullback w g)) :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback g v) c := by
  obtain ⟨I, _, _, D, t, s, hs, ht⟩ := hv
  have (i : I) : IsAffine (D.obj i) := (ht i).1.2.1
  have (i : I) : Etale (t.app i) := (ht i).1.1
  have : Nonempty I := IsCofiltered.nonempty
  let E := Over.lift D t
  let b := Over.liftCone D t (Cone.mk V s) v (fun i ↦ (ht i).2)
  have hb : IsLimit b := Over.isLimitLiftCone D t (Cone.mk V s) v
    (fun i ↦ (ht i).2) hs
  let P := Over.pullback g ⋙ Over.forget X
  let b' := P.mapCone b
  have hb' : IsLimit b' := isLimitOfPreserves P hb
  have (i : I) : CompactSpace ((E ⋙ P).obj i) := hqc (t.app i)
  have (i : I) : QuasiSeparatedSpace ((E ⋙ P).obj i) := hqs (t.app i)
  have {i j : I} (f : i ⟶ j) : IsAffineHom ((E ⋙ P).map f) := by
    have hn : D.map f ≫ t.app j = t.app i := by simp
    have hf : (E ⋙ P).map f ≫ pullback.fst (t.app j) g =
        pullback.fst (t.app i) g ≫ D.map f := by
      change pullback.lift _ _ _ ≫ _ = _
      exact pullback.lift_fst _ _ _
    have hsnd : (E ⋙ P).map f ≫ pullback.snd (t.app j) g =
        pullback.snd (t.app i) g := by
      change pullback.lift _ _ _ ≫ _ = _
      exact pullback.lift_snd _ _ _
    have hout : IsPullback (pullback.fst (t.app i) g)
        ((E ⋙ P).map f ≫ pullback.snd (t.app j) g) (D.map f ≫ t.app j) g := by
      rw [hsnd, hn]
      exact IsPullback.of_hasPullback _ _
    have hpb := hout.of_bot hf.symm (IsPullback.of_hasPullback (t.app j) g)
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) hpb inferInstance
  let e := pullbackSymmetry g v
  exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isLimit (E ⋙ P)
    (b'.extend e.hom) (IsLimit.extendIso (s := b') e.hom hb') c (fun i ↦ hstage (t.app i))

private theorem uniform_bounds_of_field_cd {k : Type u} [Field k]
    (hcd : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) 1)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    HasClassicalUniformBounds g G := by
  let d := (topologicalKrullDim X).unbotD 0 |>.toNat
  let c := 2 * d + 1
  have hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞) := finite_dimension_bound aX
  have stages {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W] :
      Scheme.HasTorsionEtaleCohomologicalDimensionLE (pullback w g) c := by
    have : QuasiCompact (w ≫ aY) := quasiCompact_of_compactSpace _
    exact finiteType_cd 1 d hcd (pullback.fst w g ≫ w ≫ aY)
      ((pullback.snd w g).topologicalKrullDim_le_of_etale.trans hd)
  have qc {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W] :
      CompactSpace ↑(pullback w g) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst w g)
  have qs {W : Scheme.{u}} (w : W ⟶ Y) [Etale w] [IsAffine W] :
      QuasiSeparatedSpace ↑(pullback w g) := by
    have : IsLocallyNoetherian (pullback w g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst w g ≫ w ≫ aY)
    infer_instance
  refine ⟨?_, ?_, ?_⟩
  · intro U hU q hq
    apply comparison_vanishing U.hom c _ G hG q hq
    exact proAffine_cd U.hom hU c (fun w ↦ etaleStage_cd 1 d hcd aX hd w)
  · intro V hV q hq
    exact comparison_vanishing (pullback.fst g V.hom) c
      (proAffine_pullback_cd g V.hom hV c (fun w ↦ stages w)
        (fun w ↦ qc w) (fun w ↦ qs w)) G hG q hq
  · exact Etale.isZero_higherDirectImage_of_affineEtale_cd g c (fun w ↦ stages w) G hG

/-- Uniform vanishing for torsion étale sheaves over finite-type schemes over a finite or
algebraically closed field: `HasClassicalUniformBounds g G` holds, and likewise for every
torsion sheaf on `Y` and every finite-type map from `Y` to a finite-type `k`-scheme. -/
theorem hasClassicalUniformBounds {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (g : X ⟶ Y) [LocallyOfFiniteType g] [QuasiCompact g]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hG : G.IsTorsion) :
    HasClassicalUniformBounds g G ∧
      ∀ {Z : Scheme.{u}} (aZ : Z ⟶ Spec (.of k))
        [LocallyOfFiniteType aZ] [QuasiCompact aZ]
        (h : Y ⟶ Z) [LocallyOfFiniteType h] [QuasiCompact h]
        (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}),
        H.IsTorsion → HasClassicalUniformBounds h H := by
  have hcd : Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of k)) 1 := by
    rcases hk with hfinite | hclosed
    · have : Finite k := hfinite
      exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField k
    · have : IsAlgClosed k := hclosed
      intro F hF q hq
      exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed k
        F hF q (by omega)
  refine ⟨uniform_bounds_of_field_cd hcd aX aY g G hG, ?_⟩
  intro Z aZ _ _ h _ _ H hH
  exact uniform_bounds_of_field_cd hcd aY aZ h H hH

end AlgebraicGeometry.ProEtale

end
