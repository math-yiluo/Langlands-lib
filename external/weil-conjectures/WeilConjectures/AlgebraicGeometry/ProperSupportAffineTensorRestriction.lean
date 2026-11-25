/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
import WeilConjectures.AlgebraicGeometry.DerivedPullbackPerfect
import WeilConjectures.AlgebraicGeometry.CartesianTensorDataComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportTensorPullbackProperties
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Affine restriction of proper-support tensor data

Source: Stacks Project, Tag 0A1H, affine reduction; Tag 0A1D, tensor base change.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Restrict the input tensor data to an affine open, using its spectrum coordinates.
Source: Stacks Project, Tag 0A1H, the sentence reducing to an affine base, and Tag 0A1D.
Proof: set j = U.isoSpec.inv followed by U.ι, and form X' = X ×_S Spec Γ(U, O).
Let f' be its second projection, E' the derived pullback of E by its first projection,
and G' the termwise tensor pullback of G. Base change preserves finite presentation,
quasi-compactness and quasi-separatedness of f. Derived pullback preserves perfectness.
The tensor-pullback functor is additive, hence sends each zero term of G to a zero term;
local finite presentations pull back to local finite presentations. The stalk tensor
formula and base-change stability of flat modules give relative flatness of each term.
For a finitely presented module its pulled support is the inverse image of its support,
by Nakayama on the finite stalk module over the local ring map. The reduced structure
on that inverse image is a closed subscheme of the base change of the original reduced
support; properness survives base change and closed immersion, giving proper support.
Apply cartesian_tensor_data_comparison to f and j. Pull its isomorphism back along
U.isoSpec.hom, then use composition of derived pullbacks and the identity comparison
for U.isoSpec.hom followed by j = U.ι. This gives the displayed comparison.
The construction works on an empty affine open and for zero complexes; no Noetherian
approximation or direct-image perfectness is used.
(blueprint: lem-pc-proper-support-affine-tensor-restriction). -/
theorem properSupport_affine_tensor_restriction
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n))
    (U : S.Opens) [IsAffine U.toScheme] :
    ∃ (X' : Scheme.{u}) (f' : X' ⟶ Spec Γ(U.toScheme, ⊤)),
      LocallyOfFinitePresentation f' ∧ QuasiCompact f' ∧ QuasiSeparated f' ∧
      ∃ (hf' : LocallyOfFiniteType f') (E' : schemeDerivedCategory X'),
        Scheme.IsPerfect X' E' ∧
        ∃ G' : CochainComplex X'.Modules ℤ,
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G'.X n)) ∧
          (∀ n : ℤ, (G'.X n).IsFinitePresentation) ∧
          (∀ n : ℤ, (G'.X n).IsFlatOver f') ∧
          (∀ n : ℤ, @Scheme.Modules.HasSupportProperOver _ _ f' hf' (G'.X n)) ∧
          Nonempty ((derivedPullback U.ι).obj
              ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
            (derivedPullback U.toScheme.isoSpec.hom).obj
              ((schemeDerivedDirectImage f').obj (E' ⊗ DerivedCategory.Q.obj G'))) := by
  classical
  let j : Spec Γ(U.toScheme, ⊤) ⟶ S := U.toScheme.isoSpec.inv ≫ U.ι
  let q := pullback.fst f j
  let f' := pullback.snd f j
  let E' := (derivedPullback q).obj E
  let G' := ((Scheme.Modules.tensorPullback q).mapHomologicalComplex (.up ℤ)).obj G
  have hprops := fun n ↦ properSupport_tensorPullback_properties f j (G.X n)
    (hGflat n) (hGproper n)
  obtain ⟨a, b, hab⟩ := hGb
  refine ⟨pullback f j, f', inferInstance, inferInstance, inferInstance,
    inferInstance, E', derivedPullback_preserve_perfect q E hE, G',
    ⟨a, b, fun n hn ↦ (Scheme.Modules.tensorPullback q).map_isZero (hab n hn)⟩,
    (fun n ↦ (hprops n).1), (fun n ↦ (hprops n).2.1),
    (fun n ↦ (hprops n).2.2), ?_⟩
  obtain ⟨ebc⟩ := cartesian_tensor_data_comparison f j q f'
    (IsPullback.of_hasPullback f j) E
    (schemeDerivedQCohProperty_of_isPerfect X E hE) G
    ⟨b, fun n hn ↦ hab n (Or.inr hn)⟩ (fun n ↦ inferInstance) hGflat
    E' ⟨Iso.refl _⟩ G' (fun n ↦ Iso.refl _) (by
      intro n m
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl)
  obtain ⟨_, _, _, comp, _⟩ := exists_derivedPullbackComposition.{u, w}
  have hj : U.toScheme.isoSpec.hom ≫ j = U.ι := by
    dsimp [j]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let K := (schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)
  exact ⟨(eqToIso (congrArg (fun k ↦ (derivedPullback k).obj K) hj)).symm ≪≫
    ((comp U.toScheme.isoSpec.hom j).app K).symm ≪≫
    (derivedPullback U.toScheme.isoSpec.hom).mapIso ebc⟩

end AlgebraicGeometry
