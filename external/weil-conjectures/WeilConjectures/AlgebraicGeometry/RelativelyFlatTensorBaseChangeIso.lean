/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.RelativelyFlatDerivedBaseChangeComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.KFlatPullback
/-! # Object comparison for relatively flat tensor base change

Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor
(blueprint: lem-pc-relatively-flat-tensor-base-change-iso).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

private noncomputable local instance tensorModelModules (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullback_kFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    [(Scheme.Modules.tensorPullback f).Additive]
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := Y.sheaf) P) :
    CochainComplex.IsKFlatTensor (R := X.sheaf)
      (((Scheme.Modules.tensorPullback f).mapHomologicalComplex (.up ℤ)).obj P) := by
  have h := CochainComplex.isKFlat_pullback f.base X.sheaf Y.sheaf ⟨f.c⟩ P hP
  convert h using 1
  rfl

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- Object-level form of the canonical relatively flat tensor base-change comparison.
The second tensor factor on the new scheme is ordinary termwise pullback.
Source: Stacks Project, Tag 0A1D, lemma-base-change-tensor.
Proof: choose a K-flat representative P of E. The derived monoidal construction
identifies E tensor Q(G) with Q(Tot(P tensor G)). Apply
relativelyFlat_derivedBaseChange_complex to this identification, E's quasi-coherent
cohomology, and the bounded-above, quasi-coherent, relatively flat terms of G.
Its invertible map gives an isomorphism to the direct image of ordinary pullback
of the total tensor complex. Termwise tensor-pullback compatibility identifies this
complex with Tot(g'*P tensor g'*G). Pullback of P is K-flat, so this total complex
represents Lg'*E tensor Q(g'*G). Compose the comparison with this identification
under the direct-image functor. This requires no properness or finite presentation.
Zero complexes and empty schemes are included; bounded-above G need not be K-flat
over O_X and is not replaced by its derived pullback.
(blueprint: lem-pc-relatively-flat-tensor-base-change-iso). -/
theorem relativelyFlat_tensor_baseChange_iso
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (g : T ⟶ S) (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ b : ℤ, ∀ n : ℤ, b < n → IsZero (G.X n))
    (hGqc : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f) :
    Nonempty ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj (E ⊗ DerivedCategory.Q.obj G)) ≅
      (schemeDerivedDirectImage (pullback.snd f g)).obj
        ((derivedPullback (pullback.fst f g)).obj E ⊗
          DerivedCategory.Q.obj
            (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
              (.up ℤ)).obj G))) := by
  classical
  let QX := DerivedCategory.Q
    (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  obtain ⟨P, s, hP, _, hs, _⟩ := CochainComplex.exists_isKFlatResolution
    (R := X.sheaf) (QX.objPreimage E)
  have : QuasiIso s := hs
  let eP : QX.obj P ≅ E := asIso (QX.map s) ≪≫ QX.objObjPreimageIso E
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj G) (fun _ ↦ hP)
  let a := (comparison.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  let α := (tensorIso eP (Iso.refl (QX.obj G))).symm ≪≫ a
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  have hbc := relativelyFlat_derivedBaseChange_complex f g E hE G hGb hGqc hGflat
    P hP eP α
  obtain ⟨F, hF, hmap, hadd, ε, hder, φ, _, _, _⟩ :=
    derivedPullback_tensorProduct (pullback.fst f g)
  have hEq : F = Scheme.Modules.tensorPullback (pullback.fst f g) :=
    CategoryTheory.Functor.ext hF (fun _ _ b ↦ hmap b)
  subst F
  let FC := (Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex (.up ℤ)
  obtain ⟨pulledComparison⟩ := kFlat_derivedTensor_comparison_natIso (pullback f g)
    ((Functor.const (Discrete PUnit.{1})).obj (FC.obj P))
    ((Functor.const (Discrete PUnit.{1})).obj (FC.obj G))
    (fun _ ↦ tensorPullback_kFlat (pullback.fst f g) P hP)
  let c := (pulledComparison.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  obtain ⟨_, _, _, _, _, _, _, F₀, hF₀, hmap₀, _, ε₀, _, _, hK₀⟩ :=
    (derivedPullback_spec (pullback.fst f g))
  have hEq₀ : F₀ = Scheme.Modules.tensorPullback (pullback.fst f g) :=
    CategoryTheory.Functor.ext hF₀ (fun _ _ b ↦ hmap₀ b)
  subst F₀
  have := hK₀ P hP
  let dP : (derivedPullback (pullback.fst f g)).obj (QX.obj P) ≅
      DerivedCategory.Q.obj (FC.obj P) :=
    asIso (ε₀.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))
  let targetIso := DerivedCategory.Q.mapIso (φ P G) ≪≫ c.symm ≪≫
    tensorIso (dP.symm ≪≫ (derivedPullback (pullback.fst f g)).mapIso eP)
      (Iso.refl _)
  exact ⟨@asIso _ _ _ _ _ hbc ≪≫ (schemeDerivedDirectImage (pullback.snd f g)).mapIso targetIso⟩

end AlgebraicGeometry
