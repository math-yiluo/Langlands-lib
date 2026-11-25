/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.Modules.Ext
import WeilConjectures.AlgebraicGeometry.BoundaryCechInjectiveMiddle
import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeRepresentative
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeGlobalLift
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.ConcreteCategory
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeBoundaryIdentification
import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import WeilConjectures.AlgebraicGeometry.CechHorseshoeLiftClass
import WeilConjectures.AlgebraicGeometry.CechHorseshoeCorrectionCochain
import WeilConjectures.Topology.Sheaves.CechComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# The Čech local-lift representative computes the connecting boundary

Source: Stacks Project, Cohomology of Sheaves, Lemma 0B8S, local-lift description of the
boundary, with Lemma 01EQ for the Čech-to-cohomology map
(blueprint: lem-sc-boundary-cech-compatibility).
-/

@[expose] public section

universe u wC wD

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem singleTrianglePlus_comm₃
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) :
    hS.singleTrianglePlus.mor₃ ≫
        ((DerivedCategory.Plus.singleFunctor C 0).map f.τ₁)⟦(1 : ℤ)⟧' =
      (DerivedCategory.Plus.singleFunctor C 0).map f.τ₃ ≫ hT.singleTrianglePlus.mor₃ := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  rw [← cancel_mono ((DerivedCategory.Plus.ι.commShiftIso (1 : ℤ)).hom.app
    ((DerivedCategory.Plus.singleFunctor C 0).obj T.X₁))]
  simp only [Functor.map_comp, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality]
  simp only [← Category.assoc]
  have h := (ShortComplex.ShortExact.singleTriangle.map hS hT f).comm₃
  dsimp only [ShortComplex.ShortExact.singleTrianglePlus,
    Pretriangulated.Triangle.mk]
  simp only [ObjectProperty.ι_map, ObjectProperty.homMk_hom]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.id_comp, Category.comp_id]
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem rightDerived_boundary_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) (n : ℕ) :
    (F.rightDerived n).map f.τ₃ ≫
        (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).inv.app T.X₃ ≫
        DerivedCategory.HomologySequence.δ
          ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
            hT.singleTrianglePlus) (n : ℤ) ((n + 1 : ℕ) : ℤ) (Nat.cast_add_one n).symm ≫
        (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
          (n + 1)).hom.app T.X₁ =
      ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).inv.app S.X₃ ≫
        DerivedCategory.HomologySequence.δ
          ((F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
            hS.singleTrianglePlus) (n : ℤ) ((n + 1 : ℕ) : ℤ) (Nat.cast_add_one n).symm ≫
        (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
          (n + 1)).hom.app S.X₁) ≫ (F.rightDerived (n + 1)).map f.τ₁ := by
  let τ : hS.singleTrianglePlus ⟶ hT.singleTrianglePlus :=
    { hom₁ := (DerivedCategory.Plus.singleFunctor _ 0).map f.τ₁
      hom₂ := (DerivedCategory.Plus.singleFunctor _ 0).map f.τ₂
      hom₃ := (DerivedCategory.Plus.singleFunctor _ 0).map f.τ₃
      comm₁ := by
        simpa [ShortComplex.ShortExact.singleTrianglePlus, ← Functor.map_comp] using
          congrArg ((DerivedCategory.Plus.singleFunctor _ 0).map) f.comm₁₂.symm
      comm₂ := by
        simpa [ShortComplex.ShortExact.singleTrianglePlus, ← Functor.map_comp] using
          congrArg ((DerivedCategory.Plus.singleFunctor _ 0).map) f.comm₂₃.symm
      comm₃ := singleTrianglePlus_comm₃ hS hT f }
  let G := F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι
  have h := (DerivedCategory.homologyFunctor _ 0).homologySequenceδ_naturality
    (G.mapTriangle.map τ) (n : ℤ) ((n + 1 : ℕ) : ℤ) (Nat.cast_add_one n).symm
  change (DerivedCategory.homologyFunctor _ (n : ℤ)).map (G.map τ.hom₃) ≫
      DerivedCategory.HomologySequence.δ (G.mapTriangle.obj hT.singleTrianglePlus)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (Nat.cast_add_one n).symm =
    DerivedCategory.HomologySequence.δ (G.mapTriangle.obj hS.singleTrianglePlus)
        (n : ℤ) ((n + 1 : ℕ) : ℤ) (Nat.cast_add_one n).symm ≫
      (DerivedCategory.homologyFunctor _ ((n + 1 : ℕ) : ℤ)).map (G.map τ.hom₁) at h
  rw [← Category.assoc,
    (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).inv.naturality]
  simp only [Category.assoc]
  dsimp only [Functor.comp_map, DerivedCategory.Plus.homologyFunctor]
  erw [← Category.assoc ((DerivedCategory.homologyFunctor _ (n : ℤ)).map _), h]
  simp only [Category.assoc]
  have he := (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
    (n + 1)).hom.naturality f.τ₁
  dsimp only [Functor.comp_map, DerivedCategory.Plus.homologyFunctor] at he
  erw [he]

set_option backward.isDefEq.respectTransparency false in
private theorem boundary_naturality (X : RingedSpace.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X).obj.obj (op ⊤)))]
    {S T : ShortComplex (SheafOfModules.{u} (moduleRings X))}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) :
    (RingedSpace.moduleCohomology X 0).map f.τ₃ ≫
        RingedSpace.moduleCohomologyBoundary X T hT 0 =
      RingedSpace.moduleCohomologyBoundary X S hS 0 ≫
        (RingedSpace.moduleCohomology X 1).map f.τ₁ := by
  let := (RingedSpace.moduleSheaves_abelian_enoughInjectives X).2
  unfold RingedSpace.moduleCohomologyBoundary RingedSpace.moduleCohomology
  exact rightDerived_boundary_naturality (RingedSpace.globalSectionsFunctor X) hS hT f 0

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: lem-sc-boundary-cech-compatibility) Let `0 → A → B → C → 0` be a short exact
sequence `S` of `O_X`-modules on a scheme `X`, `U` an open covering, `s` a global section of
`C` and `t i ∈ B(U i)` lifts of `s|_{U i}`. Then the differences
`t_{i₁}|_{U_{i₀} ∩ U_{i₁}} - t_{i₀}|_{U_{i₀} ∩ U_{i₁}}` are the images of the components of a
Čech `1`-cocycle `z` with values in `A` (unique, as `A → B` is injective on sections), and the
canonical comparison map `c_A : Ȟ¹(U, A) → H¹(X, A)` (any `c` with `IsModuleCechComparison`)
sends the class of `z` to the connecting class `∂(s)` of the long exact cohomology sequence
of `S`, where `∂` is `RingedSpace.moduleCohomologyBoundary` and `s` is read in `H⁰(X, C)`
through `toRightDerivedZero`. Source: Stacks, Cohomology, Lemma 0B8S, local-lift paragraph;
Lemma 01EQ.

Proof:
1. Choose a monomorphism `A → I` into an injective `O_X`-module
(lem-weil-pbc-scheme-modules-enough-injectives). Injectivity extends it across `A → B` to
`φ : B → I`. With `Q = coker(A → I)`, `φ` induces `ψ : C → Q`, and `(id_A, φ, ψ)` is a morphism
from `0 → A → B → C → 0` to `0 → A → I → Q → 0`. Naturality of the connecting maps of the
universal δ-functor (lem-weil-pbc-right-derived-universal-delta-functor) gives
`∂_B(s) = ∂_I(ψ(s))`.
2. The sections `φ(t_i)` are local lifts of `ψ(s)` in `I`. As `φ` restricts to the chosen
inclusion `A → I`, their pairwise differences are the image in `I` of `t_{i₁} - t_{i₀}`: the
`A`-valued Čech cocycle of the original sequence and that of the injective sequence coincide
(def-weil-pbc-site-cech-complex).
3. Apply lem-sc-boundary-cech-injective-middle to `0 → A → I → Q → 0`, `q = ψ(s)` and the lifts
`φ(t_i)`: `c_A([t_{i₁} - t_{i₀}]) = ∂_I(ψ(s))`, which is `∂_B(s)` by Step 1. -/
theorem boundary_cech_compatibility (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {ι : Type u} (U : ι → X.Opens) (hcover : iSup U = ⊤)
    (c : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homology 1 ⟶
      (RingedSpace.moduleCohomology X.toRingedSpace 1).obj S.X₁)
    (hc : IsModuleCechComparison U S.X₁ 1 c)
    (s : S.X₃.val.obj (op ⊤)) (t : ∀ i : ι, S.X₂.val.obj (op (U i)))
    (ht : ∀ i : ι, S.g.val.app (op (U i)) (t i) =
      S.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s) :
    ∃ z : ((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).cycles 1,
      (∀ y : Fin 2 → ι,
        S.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
          ((Pi.π (fun w : Fin 2 → ι ↦
            S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
            (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (t (y 1)) -
            S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (t (y 0))) ∧
      c (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).homologyπ 1 z) =
        RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s) := by
  let := enoughInjectives (X := X)
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let φ := Injective.ι S.X₂
  let a := S.f ≫ φ
  let T : ShortComplex X.Modules :=
    ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hT : T.ShortExact :=
    { exact := T.exact_of_g_is_cokernel (cokernelIsCokernel a)
      mono_f := by dsimp [T, a]; infer_instance
      epi_g := inferInstance }
  have ha : S.f ≫ φ = a := rfl
  have hz : S.f ≫ (φ ≫ T.g) = 0 := by
    rw [← Category.assoc, ha]
    exact cokernel.condition a
  let ψ := hS.exact.desc (φ ≫ T.g) hz
  have hψ : S.g ≫ ψ = φ ≫ T.g := hS.exact.g_desc _ _
  let f : S ⟶ T :=
    { τ₁ := 𝟙 S.X₁
      τ₂ := φ
      τ₃ := ψ
      comm₁₂ := by simpa [T] using ha.symm
      comm₂₃ := hψ.symm }
  let q := ψ.val.app (op ⊤) s
  let x := fun i : ι ↦ φ.val.app (op (U i)) (t i)
  have hx : ∀ i : ι, T.g.val.app (op (U i)) (x i) =
      T.X₃.val.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op q := by
    intro i
    have hi := ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app (op (U i))) hψ) (t i)
    change ψ.val.app (op (U i)) (S.g.val.app (op (U i)) (t i)) =
      T.g.val.app (op (U i)) (φ.val.app (op (U i)) (t i)) at hi
    rw [ht i] at hi
    exact hi.symm.trans (PresheafOfModules.naturality_apply ψ.val _ s)
  let : Injective T.X₂ := by
    dsimp [T, a, φ]
    infer_instance
  let : Mono φ := by dsimp [φ]; infer_instance
  obtain ⟨z, hz, hcq⟩ := boundary_cech_injective_middle X T hT U hcover c hc q x hx
  refine ⟨z, ?_, ?_⟩
  · intro y
    apply (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf
        (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))).map φ)).mp (by infer_instance)
    change T.f.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        ((Pi.π (fun w : Fin 2 → ι ↦
          S.X₁.presheafModuleCat.obj (op (∏ᶜ fun k : Fin 2 ↦ U (w k)))) y)
          (((CategoryTheory.cechComplexFunctor U).obj S.X₁.presheafModuleCat).iCycles 1 z)) =
      φ.val.app (op (∏ᶜ fun k : Fin 2 ↦ U (y k)))
        (S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (t (y 1)) -
          S.X₂.val.presheaf.map (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (t (y 0)))
    refine (hz y).trans ?_
    rw [map_sub]
    congr 1
    · exact (PresheafOfModules.naturality_apply φ.val
        (Pi.π (fun k : Fin 2 ↦ U (y k)) 1).op (t (y 1))).symm
    · exact (PresheafOfModules.naturality_apply φ.val
        (Pi.π (fun k : Fin 2 ↦ U (y k)) 0).op (t (y 0))).symm
  · have hn := boundary_naturality X.toRingedSpace hS hT f
    have hn' := ConcreteCategory.congr_hom hn
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s)
    have hzero := ConcreteCategory.congr_hom
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.naturality ψ).symm s
    change (RingedSpace.moduleCohomology X.toRingedSpace 0).map ψ
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s) =
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app T.X₃ q at hzero
    change RingedSpace.moduleCohomologyBoundary X.toRingedSpace T hT 0
        ((RingedSpace.moduleCohomology X.toRingedSpace 0).map ψ
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s)) =
      (RingedSpace.moduleCohomology X.toRingedSpace 1).map (𝟙 S.X₁)
        (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ s))
      at hn'
    rw [hzero, CategoryTheory.Functor.map_id, ModuleCat.id_apply] at hn'
    exact hcq.trans hn'

end AlgebraicGeometry.Scheme.Modules
