/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLineFactor

import WeilConjectures.AlgebraicGeometry.Sp.SpRationalRootDiagramBasis
import WeilConjectures.AlgebraicGeometry.Sp.SpSliceNormalizedScalarExtensionBasis
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Sites.LocalProperties

/-! # Invertibility of a normalized ordinary closure-line factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u c v i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor MonObj
attribute [local instance 20000] HasLimitsOfShape.has_limit HasColimitsOfShape.has_colimit
attribute [local instance 20000] Sheaf.instHasLimitsOfShape AddCommGrpCat.hasLimitsOfShape

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- A compatible diagram of linear bases induces a basis on its colimit, retaining
all leg equations. The tensor of the coefficient colimit detects linearity. -/
private theorem normalizedColimitBasis
    {C : Type c} [Category.{v} C] [MonoidalCategory C]
    {I : Type i} [Category.{j} I] [IsSifted I]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt] [ModObj cA.pt cM.pt]
    [PreservesColimit₂ A A (curriedTensor C)]
    (hcoeff : ∀ i, (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) =
      MonObj.mul (X := A.obj i) ≫ cA.ι.app i)
    (hact : ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt =
      Mod.act (M.obj i) ≫ cM.ι.app i)
    (b : A ≅ M)
    (hb : ∀ i, MonObj.mul ≫ b.hom.app i =
      A.obj i ◁ b.hom.app i ≫ Mod.act (M.obj i)) :
    ∃ q : Mod.regular cA.pt ≅ ({ X := cM.pt, mod := inferInstance } : Mod C cA.pt),
      ∀ i, cA.ι.app i ≫ q.hom.hom = b.hom.app i ≫ cM.ι.app i := by
  let c := (Cocone.precompose b.hom).obj cM
  have hc : IsColimit c := (IsColimit.precomposeHomEquiv b cM).symm hM
  let e := hA.coconePointUniqueUpToIso hc
  have he (i : I) : cA.ι.app i ≫ e.hom = b.hom.app i ≫ cM.ι.app i :=
    hA.comp_coconePointUniqueUpToIso_hom hc i
  have hlin : MonObj.mul (X := cA.pt) ≫ e.hom =
      cA.pt ◁ e.hom ≫ Mod.act (A := cA.pt) cM.pt := by
    apply (hA.tensor hA).hom_ext
    intro i
    change (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) ≫ e.hom =
      (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ cA.pt ◁ e.hom ≫ Mod.act (A := cA.pt) cM.pt
    rw [reassoc_of% hcoeff i, he]
    calc
      MonObj.mul (X := A.obj i) ≫ b.hom.app i ≫ cM.ι.app i =
          A.obj i ◁ b.hom.app i ≫ Mod.act (M.obj i) ≫ cM.ι.app i := by
            rw [reassoc_of% hb i]
      _ = A.obj i ◁ b.hom.app i ≫
          (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt := by rw [hact]
      _ = _ := by
        simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp, he]
        simp
  exact ⟨Mod.isoMk e hlin, he⟩

/-- The same construction after a colimit-preserving lax monoidal functor. -/
private theorem mappedColimitBasis
    {C : Type c} [Category.{v} C] [MonoidalCategory C]
    {D : Type*} [Category D] [MonoidalCategory D]
    {I : Type i} [Category.{j} I] [IsSifted I]
    (F : C ⥤ D) [F.LaxMonoidal] [PreservesColimitsOfShape I F]
    (A M : I ⥤ C) [∀ i, MonObj (A.obj i)] [∀ i, ModObj (A.obj i) (M.obj i)]
    (cA : Cocone A) (cM : Cocone M) (hA : IsColimit cA) (hM : IsColimit cM)
    [MonObj cA.pt] [ModObj cA.pt cM.pt]
    [PreservesColimit₂ (A ⋙ F) (A ⋙ F) (curriedTensor D)]
    (hcoeff : ∀ i, (cA.ι.app i ⊗ₘ cA.ι.app i) ≫ MonObj.mul (X := cA.pt) =
      MonObj.mul (X := A.obj i) ≫ cA.ι.app i)
    (hact : ∀ i, (cA.ι.app i ⊗ₘ cM.ι.app i) ≫ Mod.act (A := cA.pt) cM.pt =
      Mod.act (M.obj i) ≫ cM.ι.app i)
    (b : A ⋙ F ≅ M ⋙ F)
    (hb : ∀ i, Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
      F.map (MonObj.mul (X := A.obj i)) ≫ b.hom.app i =
      F.obj (A.obj i) ◁ b.hom.app i ≫
        Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫ F.map (Mod.act (M.obj i))) :
    ∃ q : Mod.regular (F.obj cA.pt) ≅
        (F.mapMod cA.pt).obj ({ X := cM.pt, mod := inferInstance } : Mod C cA.pt),
      ∀ i, F.map (cA.ι.app i) ≫ q.hom.hom = b.hom.app i ≫ F.map (cM.ι.app i) := by
  let : ∀ i, MonObj ((A ⋙ F).obj i) := fun i ↦ F.monObjObj (A.obj i)
  let : ∀ i, ModObj ((A ⋙ F).obj i) ((M ⋙ F).obj i) :=
    fun i ↦ F.modObjObj (A := A.obj i) (M.obj i)
  let : MonObj (F.mapCocone cA).pt := F.monObjObj cA.pt
  let : ModObj (F.mapCocone cA).pt (F.mapCocone cM).pt :=
    F.modObjObj (A := cA.pt) cM.pt
  refine normalizedColimitBasis (A ⋙ F) (M ⋙ F) (F.mapCocone cA) (F.mapCocone cM)
    (isColimitOfPreserves F hA) (isColimitOfPreserves F hM) ?_ ?_ b ?_
  · intro i
    change (F.map (cA.ι.app i) ⊗ₘ F.map (cA.ι.app i)) ≫
        (Functor.LaxMonoidal.μ F cA.pt cA.pt ≫ F.map MonObj.mul) =
      (Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
        F.map MonObj.mul) ≫ F.map (cA.ι.app i)
    simp only [Category.assoc]
    have hn : (F.map (cA.ι.app i) ⊗ₘ F.map (cA.ι.app i)) ≫
        Functor.LaxMonoidal.μ F cA.pt cA.pt =
      Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫
        F.map (cA.ι.app i ⊗ₘ cA.ι.app i) :=
      Functor.LaxMonoidal.μ_natural F (cA.ι.app i) (cA.ι.app i)
    rw [reassoc_of% hn, ← F.map_comp, hcoeff, F.map_comp]
  · intro i
    change (F.map (cA.ι.app i) ⊗ₘ F.map (cM.ι.app i)) ≫
        (Functor.LaxMonoidal.μ F cA.pt cM.pt ≫ F.map (Mod.act cM.pt)) =
      (Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫
        F.map (Mod.act (M.obj i))) ≫ F.map (cM.ι.app i)
    simp only [Category.assoc]
    have hn : (F.map (cA.ι.app i) ⊗ₘ F.map (cM.ι.app i)) ≫
        Functor.LaxMonoidal.μ F cA.pt cM.pt =
      Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫
        F.map (cA.ι.app i ⊗ₘ cM.ι.app i) :=
      Functor.LaxMonoidal.μ_natural F (cA.ι.app i) (cM.ι.app i)
    rw [reassoc_of% hn, ← F.map_comp, hact, F.map_comp]
  · intro i
    change (Functor.LaxMonoidal.μ F (A.obj i) (A.obj i) ≫ F.map MonObj.mul) ≫
        b.hom.app i = F.obj (A.obj i) ◁ b.hom.app i ≫
          Functor.LaxMonoidal.μ F (A.obj i) (M.obj i) ≫ F.map (Mod.act (M.obj i))
    simpa only [Category.assoc] using hb i

/-- Any module morphism realizing the normalized finite-field colimit leg is an
isomorphism. On the compatible-root cover, take the colimit of the normalized
finite-field bases, retaining its equation on each leg. Tensor-colimit
extensionality proves that this basis is linear for the prescribed closure
action. Extend the finite-field basis with its unit normalization. Composing it
with the restriction of f gives the same map as the colimit basis: their leg
equations show equality after the coefficient inclusion, hence equality on one,
and regular-module hom extensionality finishes. Both bases are isomorphisms,
so f is an isomorphism on each slice. The cover detects isomorphisms of sheaves,
and the forgetful functor reflects isomorphisms of internal modules.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (2), normalized
colimit comparison.  This lemma supplies only the invertibility step; the
factorization itself is the preceding lemma.
(blueprint: lem-diagonal-closure-ordinary-line-factor-iso).
-/
theorem diagonalClosure_ordinaryLine_factor_isIso
    (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)
    (X : Scheme.{u}) (hX : IsUnit (l : Γ(X, ⊤)))
    (f : (Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)).obj
          (spRationalTwist X l E) ⟶ spQbarTwist X l)
    (hf : Mod.extendUnitHom (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X)
          (spRationalTwist X l E) ≫ f.hom = closureLineMap l E X) :
    IsIso f := by
  classical
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (show IsUnit (l : X.residueField x) from by
      let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
      simpa only [map_natCast] using hX.map φ).invertible
  obtain ⟨I, U, a, ζ, e, hc, hζ, he, _⟩ := Scheme.tateTwist_finite_locallyFree X l
  have hU : (Scheme.ProEt.topology X).CoversTop U := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
      MorphismProperty.Over.mkIdTerminal _ _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    rw [← Sieve.ofArrows_eq_ofObjects hT U a]
    exact Precoverage.generate_mem_toGrothendieck hc
  rw [← isIso_iff_of_reflects_iso f (Mod.forget _)]
  change IsIso f.hom
  apply Sheaf.isIso_of_coversTop hU
  intro t
  let R := condensedRingObj.{u} (Profinite.padicAlgClRingObj.{u} l) X
  let Q := spQbarTwist X l
  let A := Profinite.padicSubfieldRingObjFunctor.{u} l ⋙ upperStarFromPoint X
  let M := spRationalTwistDiagram X l
  let O := (Scheme.ProEt.topology X).overPullback AddCommGrpCat.{u + 1} (U t)
  let p := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl l E) X
  let : IsSifted (PadicAlgCl.FiniteIntermediateField l) := IsFiltered.isSifted
  let : ∀ E, MonObj (A.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField l,
      MonObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
    infer_instance
  let : ∀ E, ModObj (A.obj E) (M.obj E) := by
    change ∀ E : PadicAlgCl.FiniteIntermediateField l,
      ModObj (condensedRingObj.{u} (Profinite.continuousMapRingObj.{u} E.1) X)
        (spRationalTwist X l E).X
    exact fun E ↦ (spRationalTwist X l E).mod
  let cA := (upperStarFromPoint X).mapCocone (Profinite.padicAlgClRingObjCocone l)
  let cM := colimit.cocone M
  let : MonObj cA.pt := by change MonObj R; infer_instance
  let : ModObj cA.pt cM.pt := Q.mod
  let : (upperStarFromPoint X).IsLeftAdjoint :=
    (pointUpperStarLowerStarAdjunction.comp
      (ProEtale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).isLeftAdjoint
  let : O.IsLeftAdjoint :=
    ((Over.forgetAdjStar (U t)).sheafPushforwardContinuous
      ((Scheme.ProEt.topology X).over (U t)) (Scheme.ProEt.topology X)
      (E := AddCommGrpCat.{u + 1})).isLeftAdjoint
  have hA : IsColimit cA := isColimitOfPreserves (upperStarFromPoint X)
    (Profinite.isColimitPadicAlgClRingObjCocone l)
  have hcoeff (F : PadicAlgCl.FiniteIntermediateField l) :
      (cA.ι.app F ⊗ₘ cA.ι.app F) ≫ MonObj.mul (X := R) =
        MonObj.mul (X := A.obj F) ≫ cA.ι.app F := by
    exact (IsMonHom.mul_hom
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl l F) X)).symm
  have hact (F : PadicAlgCl.FiniteIntermediateField l) :
      (cA.ι.app F ⊗ₘ cM.ι.app F) ≫ Q.mod.smul =
        (spRationalTwist X l F).mod.smul ≫ cM.ι.app F := by
    change (coefficientMap.{u} (Profinite.padicSubfieldRingObjToPadicAlgCl l F) X ⊗ₘ
      colimit.ι (spRationalTwistDiagram X l) F) ≫
        (spQbarTwistAction_existsUnique X l).exists.choose.smul =
      Mod.act (spRationalTwist X l F).X ≫ colimit.ι (spRationalTwistDiagram X l) F
    simpa only [Profinite.padicSubfieldRingObjMap_id, coefficientMap_id,
      spRationalTwistMap_id, id_tensorHom_id, Category.id_comp] using
      (spQbarTwistAction_existsUnique X l).exists.choose_spec F F F (le_refl F) (le_refl F)
  obtain ⟨b, hb⟩ := spRationalRootDiagramBasis X l (U t)
    (fun n ↦ ζ n t) (fun n ↦ e n t) (fun n ↦ hζ n t) (fun n V r ↦ he n t V r)
  obtain ⟨q, hq⟩ := mappedColimitBasis O A M cA cM hA (colimit.isColimit M)
    hcoeff hact b hb
  let i : Mod.regular (O.obj (A.obj E)) ≅
      (O.mapMod (A.obj E)).obj (spRationalTwist X l E) :=
    Mod.isoMk (b.app E) (by
      change (Functor.LaxMonoidal.μ O (A.obj E) (A.obj E) ≫
          O.map (MonObj.mul (X := A.obj E))) ≫ b.hom.app E =
        O.obj (A.obj E) ◁ b.hom.app E ≫
          Functor.LaxMonoidal.μ O (A.obj E) (M.obj E) ≫
            O.map (Mod.act (spRationalTwist X l E).X)
      simpa only [Category.assoc, A, M, Functor.comp_obj,
        Profinite.padicSubfieldRingObjFunctor, spRationalTwistDiagram] using hb E)
  obtain ⟨d, hd⟩ := spSliceNormalizedScalarExtensionBasis X p (spRationalTwist X l E) (U t) i
  let g := d.hom ≫ (O.mapMod R).map f
  have hg : g = q.hom := by
    apply Mod.regular_hom_ext
    have hn : O.map p ≫ g.hom = O.map p ≫ q.hom.hom := by
      change O.map p ≫ d.hom.hom ≫ O.map f.hom = O.map p ≫ q.hom.hom
      rw [reassoc_of% hd, ← O.map_comp, hf]
      exact (hq E).symm
    have hp : MonObj.one (X := O.obj (A.obj E)) ≫ O.map p =
        MonObj.one (X := O.obj R) := IsMonHom.one_hom (O.map p)
    simpa only [← hp, Category.assoc] using
      congrArg (fun k ↦ MonObj.one (X := O.obj (A.obj E)) ≫ k) hn
  have : IsIso g := hg ▸ inferInstance
  have : IsIso ((O.mapMod R).map f) := IsIso.of_isIso_comp_left d.hom _
  exact (Mod.forget (O.obj R)).map_isIso ((O.mapMod R).map f)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
