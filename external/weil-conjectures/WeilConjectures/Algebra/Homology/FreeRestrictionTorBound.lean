/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Tor bounds for restricted free modules

Source: Stacks Project, Tags 066H, 066K and 0655.
(blueprint: lem-pc-free-restriction-tor-bound).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Exact colimits commute with homology of short complexes. The proof follows the
functor-category comparison used by `FiniteEtaleCechFilteredColimit`. -/
private theorem shortComplexHomologyColimit
    (C : Type*) [Category* C] [Abelian C]
    (I : Type u) [SmallCategory I] [HasColimitsOfShape I C]
    [HasExactColimitsOfShape I C] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor C) := by
  let L := colim (J := I) (C := C)
  have : L.PreservesHomology := inferInstance
  refine ⟨fun {D} ↦ ?_⟩
  let S := (ShortComplex.functorEquivalence I C).inverse.obj D
  let c : Cocone D :=
    { pt := S.map L
      ι :=
        { app := fun i ↦ S.mapNatTrans (colim.ι i)
          naturality := by
            intro i j f
            apply ShortComplex.Hom.ext
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₁) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₂) f
            · simpa [S, L, ShortComplex.functorEquivalence,
                ShortComplex.FunctorEquivalence.inverse, ShortComplex.mapNatTrans]
                using colimit.w (D ⋙ ShortComplex.π₃) f } }
  have hc : IsColimit c := ShortComplex.isColimitOfIsColimitπ c
    (colimit.isColimit _) (colimit.isColimit _) (colimit.isColimit _)
  apply preservesColimit_of_preserves_colimit_cocone hc
  let e : D ⋙ ShortComplex.homologyFunctor _ ≅ S.homology :=
    NatIso.ofComponents (fun i ↦ S.mapHomologyIso ((CategoryTheory.evaluation _ _).obj i)) (by
      intro i j f
      change ShortComplex.homologyMap
        (S.mapNatTrans ((CategoryTheory.evaluation _ _).map f)) ≫ _ = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp)
  have h : IsColimit ((Cocone.precompose e.hom).obj (colimit.cocone S.homology)) :=
    (IsColimit.precomposeInvEquiv e.symm _).symm (colimit.isColimit _)
  apply IsColimit.ofIsoColimit h
  refine Cocone.ext (S.mapHomologyIso L).symm ?_
  intro i
  dsimp only [Functor.mapCocone, c, Cocone.precompose, colimit.cocone,
    Cocone.functoriality, NatTrans.comp_app, Iso.symm_hom, ShortComplex.homologyFunctor_map]
  rw [Category.assoc]
  change e.hom.app i ≫ colimit.ι S.homology i ≫ (S.mapHomologyIso L).inv =
    ShortComplex.homologyMap (S.mapNatTrans (colim.ι i))
  rw [ShortComplex.homologyMap_mapNatTrans]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Reduce complex homology to the three-term short complex in the given degree. -/
private theorem complexHomologyColimit
    (C : Type*) [Category* C] [Abelian C]
    (I : Type u) [SmallCategory I] [HasColimitsOfShape I C]
    (h : PreservesColimitsOfShape I (ShortComplex.homologyFunctor C))
    (p : ℕ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) p) := by
  let H := HomologicalComplex.shortComplexFunctor C
    (ComplexShape.down ℕ) p
  have : PreservesColimitsOfShape I H :=
    ⟨fun {D} ↦ ⟨fun {c} hc ↦ ⟨ShortComplex.isColimitOfIsColimitπ (H.mapCocone c)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.down ℕ) ((ComplexShape.down ℕ).prev p)) hc)
      (isColimitOfPreserves (HomologicalComplex.eval _ (ComplexShape.down ℕ) p) hc)
      (isColimitOfPreserves
        (HomologicalComplex.eval _ (ComplexShape.down ℕ) ((ComplexShape.down ℕ).next p)) hc)⟩⟩⟩
  have := h
  change PreservesColimitsOfShape I (H ⋙ ShortComplex.homologyFunctor _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Tensor a fixed projective resolution with a varying module. -/
private noncomputable def tensorResolutionFunctor
    {A : Type u} [CommRing A] {M : ModuleCat.{u} A} (P : ProjectiveResolution M) :
    ModuleCat.{u} A ⥤ ChainComplex (ModuleCat.{u} A) ℕ where
  obj N := ((MonoidalCategory.tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex
  map g := (NatTrans.mapHomologicalComplex
    ((MonoidalCategory.tensoringRight (ModuleCat.{u} A)).map g) (.down ℕ)).app P.complex
  map_id N := by ext n; simp
  map_comp f g := by ext n; simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Tor preserves coproducts: resolve the fixed module, use exactness of coproducts
for homology, then apply Tor symmetry to exchange the arguments. -/
private theorem tor'_preserves_coproducts (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (j : ℕ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I) ((Tor' (ModuleCat.{u} A) j).flip.obj M) := by
  let P := projectiveResolution M
  let T := tensorResolutionFunctor P
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) j
  have : PreservesColimitsOfShape (Discrete I) T :=
    HomologicalComplex.preservesColimitsOfShape_of_eval T (fun n ↦ by
      change PreservesColimitsOfShape (Discrete I)
        (MonoidalCategory.tensorLeft (P.complex.X n))
      infer_instance)
  have hH := shortComplexHomologyColimit (ModuleCat.{u} A) (Discrete I)
  have : PreservesColimitsOfShape (Discrete I) H :=
    complexHomologyColimit (ModuleCat.{u} A) (Discrete I) hH j
  let e : (Tor' (ModuleCat.{u} A) j).obj M ≅ T ⋙ H :=
    NatIso.ofComponents
      (fun N ↦ P.isoLeftDerivedObj (MonoidalCategory.tensorRight N) j) (by
        intro N N' g
        change (NatTrans.leftDerived
          ((MonoidalCategory.tensoringRight (ModuleCat.{u} A)).map g) j).app M ≫ _ = _
        rw [P.leftDerived_app_eq]
        simp [T, H, tensorResolutionFunctor])
  have : PreservesColimitsOfShape (Discrete I) ((Tor' (ModuleCat.{u} A) j).obj M) :=
    preservesColimitsOfShape_of_natIso e.symm
  obtain ⟨σ⟩ := nonempty_tor'_flip_iso A j
  exact preservesColimitsOfShape_of_natIso (σ.app M)

/-- A free B-module inherits the Tor bound of the restricted regular B-module.

Source: Stacks Project, Tags 066H, 066K and 0655.
(blueprint: lem-pc-free-restriction-tor-bound).

Proof: restricted finitely supported B-valued functions on I are the direct sum,
indexed by I, of restricted copies of B. Use the natural symmetry of Tor to
resolve the test module M instead of the first argument. Tensoring that resolution
with the direct sum commutes with the sum in each degree. Direct sums of modules
are exact, so homology commutes with this sum. Its degree-j homology is therefore
the direct sum of Tor_j(B,M), zero by hypothesis. Transport back through
Tor symmetry. Empty and infinite index sets are both allowed; no finite generation
is needed. For the zero ring all terms are zero, including j=0. -/
theorem free_restriction_tor_isZero
    {A B : Type u} [CommRing A] [CommRing B] (ρ : A →+* B)
    (I : Type u) (M : ModuleCat.{u} A) (j : ℕ)
    (hTor :
      IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj (of B B))).obj M)) :
    IsZero (((Tor' (ModuleCat.{u} A) j).obj
        ((restrictScalars ρ).obj ((free B).obj I))).obj M) := by
  classical
  let R := restrictScalars ρ
  let F := (Tor' (ModuleCat.{u} A) j).flip.obj M
  have : PreservesColimitsOfShape (Discrete I) F := tor'_preserves_coproducts A M j I
  let Z : I → ModuleCat.{u} B := fun _ ↦ of B B
  let e : (free B).obj I ≅ of B (DirectSum I (fun _ ↦ B)) :=
    (finsuppLEquivDirectSum B B I).toModuleIso
  have hc := isColimitOfPreserves (R ⋙ F) (coproductCoconeIsColimit Z)
  have hz : IsZero ((R ⋙ F).obj (of B (DirectSum I (fun _ ↦ B)))) :=
    hc.isZero_pt ((Functor.isZero_iff _).2 (fun _ ↦ hTor))
  exact hz.of_iso ((R ⋙ F).mapIso e)

end ModuleCat
