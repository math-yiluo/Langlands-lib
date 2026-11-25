/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.Algebra.Homology.ScalarExtensionHom
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.SchemeIsoDerivedEquivalence
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.AffineBaseChangeSchemeComparisons
import WeilConjectures.AlgebraicGeometry.AffineBaseChangeModelIsosOfSchemeComparisons
public import WeilConjectures.AlgebraicGeometry.AffineBaseChangeRingDiagram
public import WeilConjectures.AlgebraicGeometry.AffineModelComparisonData

/-! # Coherent geometric isomorphisms of specified affine models
Source: Stacks Project, Tags 09RE, 08DW, 06Z0 and 0D5S.
(blueprint: lem-pc-affine-base-change-model-comparison-isos). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem exists_pair_of_nonempty {A : Sort u} {B : A → Sort w}
    (h : ∃ a, Nonempty (B a)) : ∃ a, ∃ _ : B a, True := by
  obtain ⟨a, ⟨b⟩⟩ := h
  exact ⟨a, b, trivial⟩

/-- The upper support bound of a projective complex gives native K-flatness.
Source: Stacks Project, Tag 064K; the proved upstream bounded-flat criterion. -/
private theorem boundedProjective_isKFlat
    {A : Type u} [CommRing A] (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (M.X n))
    (hproj : ∀ n : ℤ, Module.Projective A (M.X n)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M := by
  obtain ⟨a, b, hb⟩ := hbounded
  have : M.IsStrictlyLE b := (M.isStrictlyLE_iff b).2 (fun n hn ↦ hb n (Or.inr hn))
  have (X : ModuleCat.{u} A) : PreservesColimitsOfShape ℤ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} A)).flip.obj X) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (MonoidalCategory.tensorRight X))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  apply CochainComplex.kFlat_of_isStrictlyLE_of_flat M b
  intro n
  apply (ModuleCat.flat_iff_flat (M.X n)).2
  have : Module.Projective A (M.X n) := hproj n
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Coherent object isomorphisms between termwise affine models and geometric pullbacks.
This asserts no equivalence of derived module Hom sets and no preservation of bounds.
Source: Stacks Project, Tag 09RE, affine calculation; Tag 08DW(2), Tag 06Z0,
and Tag 0D5S (composition of derived pullbacks).
(blueprint: lem-pc-affine-base-change-model-comparison-isos).

Proof:
1. Write B = Gamma(Y). The pushouts defining F are tensor products over R(i).
   Spec sends these pushouts to pullbacks. Spec.preimage(t.hom followed by s)
   gives exactly the supplied structural morphism. Use t to identify Spec B with Y.
   The structural map r is invertible, since its other pushout leg is R(id).
2. The tail inclusion is final, so hc gives the colimit of its restricted R diagram.
   Under.pushout is left adjoint and preserves colimits. The forgetful functor from
   rings under B creates these nonempty connected colimits. Thus colimit F is the
   pushout of R(i) to B along c.ι(i). Spec identifies it with the limit pullback.
   The colimit injections correspond to the prescribed arrows of pullbacks.
3. Extend E₀ and K₀ along r and the subsequent structural maps. These remain
   bounded projective, hence termwise flat. The upper support bound and
   kFlat_of_isStrictlyLE_of_flat (Tag 064K) imply K-flatness.
   Termwise tilde/base-change, followed by
   the K-flat derived-pullback counit, supplies natural comparison isomorphisms.
   Compose with the pushout/pullback isomorphisms, with the localization comparison
   he for exact pushforward along t, and with the images of hPE and hQK and the
   counit of e. The scheme isomorphisms induce exact derived equivalences d, dlim;
   in their target categories this gives αE, αK at each stage and βE, βK at the colimit.
4. Apply naturality of termwise tilde/base-change and of the derived-pullback
   counit to f. Associativity of scalar extension identifies the resulting chain
   map with scalarExtensionHom. The composition comparisons are characterized by
   their counits; consequently their components agree with perfectHomComposition.
   Cancel each comparison with its inverse. The resulting conjugated equalities
   are exactly the two displayed equations. This uses no descent of morphisms.
   Pushout universal properties, finality of the nonempty tail, and the K-flat
   counit apply also to zero rings, zero complexes and empty spectra. -/
theorem exists_affineBaseChangeModelComparisonIsos
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Y : Scheme.{u}) [IsAffine Y] (s : Y ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (t : Spec (Scheme.Γ.obj (.op Y)) ≅ Y)
    (e : schemeDerivedCategory (Spec (Scheme.Γ.obj (.op Y))) ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q)
    (P Q : schemeDerivedCategory Y)
    (E₀ K₀ : CochainComplex (ModuleCat.{u} (Scheme.Γ.obj (.op Y))) ℤ)
    (hE : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (Scheme.Γ.obj (.op Y)) (E₀.X n) ∧
        Module.Projective (Scheme.Γ.obj (.op Y)) (E₀.X n))
    (hK : (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K₀.X n)) ∧
      ∀ n : ℤ, Module.Finite (Scheme.Γ.obj (.op Y)) (K₀.X n) ∧
        Module.Projective (Scheme.Γ.obj (.op Y)) (K₀.X n))
    (hPE : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj E₀))
    (hQK : e.inverse.obj Q ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} (Scheme.Γ.obj (.op Y)))
        (SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} (Scheme.Γ.obj (.op Y)) ⥤
                  SheafOfModules.{u} (moduleRings (Spec (Scheme.Γ.obj (.op Y))).toRingedSpace))
                  (tilde.functor (Scheme.Γ.obj (.op Y))))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj K₀)) :
    let F := affineBaseChangeRingDiagram R i Y s t
    let r := affineBaseChangeInitialMap R i Y s t
    let E := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀
    let K := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀
    affineModelComparisonData R c i Y s P Q F (colimit.cocone F) E K := by
  classical
  let F := affineBaseChangeRingDiagram R i Y s t
  let C := colimit.cocone F
  let r := affineBaseChangeInitialMap R i Y s t
  obtain ⟨σ, τ, hgeom⟩ := exists_affineBaseChangeSchemeComparisons R c hc i Y s t
  let E := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj E₀
  let K := ((ModuleCat.extendScalars r).mapHomologicalComplex (.up ℤ)).obj K₀
  have hstage (j : Set.Ici (⟨i, le_rfl⟩ : Set.Ici i)) :=
    exists_pair_of_nonempty (Scheme.exists_scheme_iso_derived_equivalence.{u, w, w} (σ j))
  choose d hd htrivial using hstage
  obtain ⟨dlim, ⟨hdlim⟩⟩ := Scheme.exists_scheme_iso_derived_equivalence.{u, w, w} τ
  have hEf := boundedProjective_isKFlat E₀ hE.1 (fun n ↦ (hE.2 n).2)
  have hKf := boundedProjective_isKFlat K₀ hK.1 (fun n ↦ (hK.2 n).2)
  change affineModelComparisonData R c i Y s P Q F C E K
  with_reducible exact (exists_affineBaseChangeModelIsosOfSchemeComparisons
    R c i Y s t e he P Q E₀ K₀ hEf hKf hPE hQK F C r E K rfl rfl σ τ hgeom d dlim hd hdlim)

end AlgebraicGeometry
