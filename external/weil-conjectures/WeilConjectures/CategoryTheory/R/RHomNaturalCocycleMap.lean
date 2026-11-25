/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
import WeilConjectures.CategoryTheory.R.RHomInjectiveCocycleFamilyExists
import WeilConjectures.CategoryTheory.R.RHomNaturalCocycleExtension

/-!
# The natural cocycle comparison for RHom

Source: Stacks Tags 06XR (1) and 070I
(blueprint: lem-sc-p1-rhom-natural-cocycle-map).
-/

@[expose] public section

universe w w₂ v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.Functor

/-- There is a natural additive comparison, normalized on injective complexes.
Source: Stacks Tags 06XR (1) and 070I
(blueprint: lem-sc-p1-rhom-natural-cocycle-map).

Proof: On a bounded below complex of injectives I, send a cocycle M → Iⁿ to its
localized map M[0] → I[n]. A boundary gives a null-homotopic map by
Cocycle.fromSingleMk_mem_coboundaries_iff, so this descends to cohomology and is additive.
The invertible total-derived unit identifies this cohomology with Hⁿ(RHom(M,QI)).
A map of injective complexes preserves the cocycle construction. A homotopy between
maps induces equal maps on cohomology and in the derived category. The equivalence
from the bounded below homotopy category of injective objects to D+ therefore extends
these homomorphisms to D+. Its counit and the naturality of the derived unit give
naturality for all derived morphisms. For an arbitrary injective complex, lift its
representing isomorphism through the fully faithful K-injective localization; the
same cocycle calculation gives the displayed normalization. Thus the normalization
determines the maps uniquely, and no arbitrary cohomology comparison is chosen. -/
theorem exists_rhom_natural_cocycle_map
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w₂} AddCommGrpCat.{v}] (M : C) :
    let V := preadditiveCoyoneda.obj (op M)
    let RV := V.rightDerivedFunctorPlus
    let H (n : ℤ) := DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{v} n
    let S := (DerivedCategory.singleFunctor C 0).obj M
    ∃ τ : ∀ (X : DerivedCategory.Plus C) (n : ℤ),
        (H n).obj (RV.obj X) →+ (S ⟶ X.obj⟦n⟧),
      (∀ (X Y : DerivedCategory.Plus C) (g : X ⟶ Y) (n : ℤ)
          (a : (H n).obj (RV.obj X)),
        τ Y n ((H n).map (RV.map g) a) =
          τ X n a ≫ ((DerivedCategory.Plus.ι (C := C)).map g)⟦n⟧') ∧
      (∀ (I : CochainComplex.Plus C) (_hi : ∀ k : ℤ, Injective (I.obj.X k))
          (n : ℤ) (f : M ⟶ I.obj.X n) (hf : f ≫ I.obj.d n (n + 1) = 0),
        let J := (V.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.obj
        let a := J.homologyπ n ((J.sc n).abCyclesIso.inv
          ⟨f, by
            change f ≫ I.obj.d n ((ComplexShape.up ℤ).next n) = 0
            rw [CochainComplex.next]
            exact hf⟩)
        let b := (DerivedCategory.Plus.homologyFunctorObjQIso
          (V.mapCochainComplexPlus.obj I) n).inv a
        let η := V.rightDerivedFunctorPlusUnit.app I
        τ ((DerivedCategory.Plus.Q (C := C)).obj I) n ((H n).map η b) =
          ShiftedHom.map (Cocycle.equivHomShift.symm
              (Cocycle.fromSingleMk f (zero_add n) (n + 1) rfl hf)) DerivedCategory.Q ≫
            ((DerivedCategory.Plus.QCompιIso C).inv.app I)⟦n⟧') := by
  dsimp only
  obtain ⟨F⟩ := exists_rhom_injective_cocycle_family M
  obtain ⟨τ, hnat, hrep⟩ := extend_rhom_injective_cocycle_family F
  refine ⟨τ, hnat, ?_⟩
  intro I hi n f hf
  simpa only [hrep I hi n] using F.normalize I hi n f hf

end CategoryTheory.Functor
