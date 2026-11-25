/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive

/-! # Boundedness below of finite twisted inverse image

Source: Stacks Project, Duality for Schemes, Tag 0A9I (finite case, Tag 0AX2)
(blueprint: lem-sc-finite-twisted-inverse-bounded-below).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

-- A zero sheaf has the presentation free(PUnit) --id--> free(PUnit) --> 0.
private lemma qcOfZero {X : Scheme.{u}}
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : Limits.IsZero M) :
    M.IsQuasicoherent := by
  let F := SheafOfModules.free (R := moduleRings X.toRingedSpace) PUnit.{u + 1}
  exact (SheafOfModules.presentationOfIsCokernelFree (𝟙 F) (0 : F ⟶ M) (by simp)
    (Limits.CokernelCofork.IsColimit.ofEpiOfIsZero _ inferInstance hM)).isQuasicoherent

-- Below the cutoff, the truncation triangle gives a cohomology isomorphism;
-- above it, cohomology is zero. Both cases preserve quasi-coherence.
private lemma qcTruncLE {X : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) (n : ℤ) :
    schemeDerivedQCohProperty X ((DerivedCategory.TStructure.t.truncLE n).obj E.obj) := by
  intro i
  by_cases hi : n < i
  · exact qcOfZero _ (DerivedCategory.isZero_of_isLE _ n i hi)
  · have hi' : i ≤ n := le_of_not_gt hi
    let t := DerivedCategory.TStructure.t (C :=
      SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let T := (t.triangleLEGT n).obj E.obj
    have hT := t.triangleLEGT_distinguished n E.obj
    have : T.obj₃.IsGE (n + 1) := by
      change t.IsGE ((t.truncGT n).obj E.obj) (n + 1)
      exact t.isGE_truncGT_obj E.obj n (n + 1)
    have hz : Limits.IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj T.obj₃) :=
      DerivedCategory.isZero_of_isGE _ (n + 1) i (by lia)
    have hz' : Limits.IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (i - 1)).obj T.obj₃) :=
      DerivedCategory.isZero_of_isGE _ (n + 1) (i - 1) (by lia)
    have hepi : Epi ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2
        (hz.eq_of_tgt _ _)
    have hmono : Mono ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).map T.mor₁) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i
        (by lia)).2 (hz'.eq_of_src _ _)
    have hiso : IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).map T.mor₁) :=
      isIso_of_mono_of_epi _
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      (asIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).map T.mor₁)).symm
      (E.property i)

/-- The right adjoint of derived direct image on quasi-coherent complexes preserves
boundedness below for a finite morphism of Noetherian schemes. `comparison` identifies `R`
with the restriction of the shared derived direct image; `adj` specifies its right adjoint.
Quasi-coherence of the image is included in the codomain of `a`.

Source: Stacks Project, Tag 0A9I, specialized to the finite case of Tag 0AX2
(blueprint: lem-sc-finite-twisted-inverse-bounded-below).
Proof:
1. Finite morphisms of Noetherian schemes are quasi-compact and quasi-separated, with
quasi-compact target. Apply lem-pc-derived-direct-image-uniform-truncation-bound to shifted
complexes to obtain a uniform integer N with Rf_* D^{≤r} contained in D^{≤r+N}.
2. Choose c with H^i(K) = 0 for i ≤ c. Set A = τ_{≤c-N} a(K). The bound gives
Rf_* A in D^{≤c}, while K is in D^{≥c+1}. Adjunction identifies Hom(A,a(K)) with
Hom(Rf_* A,K), which vanishes by lem-pc-derived-tstructure-orthogonality.
3. The truncation map A → a(K) is consequently zero, but induces an isomorphism on
cohomology in degrees ≤c-N. These cohomology sheaves vanish, proving boundedness below.
The codomain of the right adjoint already ensures quasi-coherent cohomology. -/
theorem finiteTwistedInverse_boundedBelow
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsNoetherian X] [IsNoetherian Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y)
    (comparison : R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : R ⊣ a) (K : schemeDerivedQCohCategory Y)
    (hK : ∃ n : ℤ, K.obj.IsGE n) :
    ∃ n : ℤ, (a.obj K).obj.IsGE n := by
  -- Finite morphisms are affine, so the cohomological-amplitude bound is zero.
  obtain ⟨n, hn⟩ := hK
  have hcomp : (R ⋙ (schemeDerivedQCohProperty Y).ι).Additive :=
    Functor.additive_of_iso comparison.symm
  have hR : R.Additive := Functor.additive_of_comp_faithful R
    (schemeDerivedQCohProperty Y).ι
  let t := DerivedCategory.TStructure.t (C :=
    SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let A : schemeDerivedQCohCategory X :=
    ⟨(t.truncLE (n - 1)).obj (a.obj K).obj, qcTruncLE (a.obj K) (n - 1)⟩
  have hA : A.obj.IsLE (n - 1) := by dsimp [A]; infer_instance
  have hd : ((schemeDerivedDirectImage f).obj A.obj).IsLE (n - 1) :=
    ((schemeDerivedDirectImage_tExact_and_conservative_of_affine f).1
      A.obj A.property).2 (n - 1) |>.1 |>.mp hA
  have : DerivedCategory.TStructure.t.IsLE
      (((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f).obj A) (n - 1) := hd
  have hRA : (R.obj A).obj.IsLE (n - 1) :=
    DerivedCategory.TStructure.t.isLE_of_iso (comparison.app A).symm (n - 1)
  let g : A ⟶ a.obj K := ObjectProperty.homMk ((t.truncLEι (n - 1)).app (a.obj K).obj)
  have hg : (adj.homEquiv A K).symm g = 0 := by
    apply (schemeDerivedQCohProperty Y).ι.map_injective
    exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ (n - 1) n (by lia) hRA hn
  have hg0 : g = 0 := by
    apply (adj.homEquiv A K).symm.injective
    simpa using hg
  have hι : (t.truncLEι (n - 1)).app (a.obj K).obj = 0 :=
    congrArg InducedCategory.Hom.hom hg0
  have hz : Limits.IsZero A.obj := by
    apply (Limits.IsZero.iff_id_eq_zero _).2
    apply t.to_truncLE_obj_ext
    simp [hι]
  refine ⟨n, ?_⟩
  exact (t.isGE_iff_isZero_truncLE_obj (n - 1) n (by lia) (a.obj K).obj).2 hz

end AlgebraicGeometry
