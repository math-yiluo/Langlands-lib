/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonShiftSquareData
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonShiftSquareTransport

/-! # Shift square for localized tensor comparison

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-shift-square).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

-- Preserve the existing derived-category hypothesis even though this reduction does not use it.
set_option linter.unusedSectionVars false in
set_option backward.defeqAttrib.useBackward true in
/-- The comparison arrows for U and its inverse shift are conjugate.
Source: Stacks Project, Tag 0DJA(1), via Tag 0BYJ and the tensor shift maps.

Proof: put V = U[-n]. Use the first-variable tensor shift isomorphism
V tensor Q = (U tensor Q)[-n] and the scalar-extension shift isomorphism.
Keep the derived functor and universal counit of mU. Its canonical shift
comparison is obtained by uniqueness of the left-derived functor of the
additive extension-of-scalars functor. Reindex cohomology by j -> j-n:
transport the A tensor_R B action using the cohomology shift isomorphism.
Naturality in multiplication by a in A proves cohomologyIso_smul. Transport
ordinaryIso and ordinaryToLocalized through the termwise scalar-extension
shift maps; on tensors their specified formulas are unchanged. Define the
comparison by the counit formula comparison_eq and define its localization
by the extension/restriction adjunction, proving localized_eq. This constructs
mV without any choice of a witness of model existence. At degree i+n the
cohomology shift map gives eS after scalar extension to C; the target shift
map for F(U) tensor N gives eT. Naturality of the first-variable tensor shift
map in Q -> N and monoidality of F identifies the ordinary comparison square.
The counit shift compatibility gives its derived source square; transposing
localized_eq through the scalar adjunction gives the displayed conjugacy.
The first-variable tensor shift involves no extra signs. For n=0
use identity reindexing; zero complexes and arbitrary t are included. Neither
flatness of C nor K-flatness of U or Q is used by this transport statement.
(blueprint: lem-pc-localized-tensor-comparison-shift-square). -/
theorem exists_localizedTensorComparison_shift_square
    (U : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    ∃ (mV : BaseDerivedTensorCohomologyModel R A B ((U⟦-n⟧) ⊗ Q) C)
      (eS : (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mV.cohomology (i + n)) ≅
        (extendScalars (algebraMap (A ⊗[R] B) C)).obj (mU.cohomology i))
      (eT : (F.obj (U⟦-n⟧) ⊗ N).homology (i + n) ≅ (F.obj U ⊗ N).homology i),
    mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i =
    eS.inv ≫ (mV.localizedComparison (i + n) ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F (U⟦-n⟧) Q).inv ≫ (F.obj (U⟦-n⟧) ◁ t)) (i + n)) ≫
        eT.hom := by
  intro F
  let e : ((U⟦-n⟧) ⊗ Q) ≅ (U ⊗ Q)⟦-n⟧ :=
    CochainComplex.mapBifunctorShift₁Iso U Q (curriedTensor (ModuleCat.{u} A)) (-n)
  let eK : F.obj ((U⟦-n⟧) ⊗ Q) ≅ (F.obj (U ⊗ Q))⟦-n⟧ :=
    F.mapIso e ≪≫ (F.commShiftIso (-n)).app (U ⊗ Q)
  let eT : F.obj (U⟦-n⟧) ⊗ N ≅ (F.obj U ⊗ N)⟦-n⟧ :=
    tensorIso ((F.commShiftIso (-n)).app U) (Iso.refl N) ≪≫
    CochainComplex.mapBifunctorShift₁Iso (F.obj U) N (curriedTensor (ModuleCat.{u} C)) (-n)
  let shK : ((F.obj (U ⊗ Q))⟦-n⟧).homology (i + n) ≅
      (F.obj (U ⊗ Q)).homology i :=
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
      (by omega)).app (F.obj (U ⊗ Q))
  let shT : ((F.obj U ⊗ N)⟦-n⟧).homology (i + n) ≅
      (F.obj U ⊗ N).homology i :=
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
      (by omega)).app (F.obj U ⊗ N)
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (.up ℤ) (i + n)
  obtain ⟨mV, eS, hmodel⟩ := exists_shift_square_data R A B C
    (U ⊗ Q) ((U⟦-n⟧) ⊗ Q) n e mU i
  refine ⟨mV, eS, H.mapIso eT ≪≫ shT, ?_⟩
  let f := (Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)
  let fV := (Functor.Monoidal.μIso F (U⟦-n⟧) Q).inv ≫ (F.obj (U⟦-n⟧) ◁ t)
  have hcomplex : fV ≫ eT.hom = eK.hom ≫ f⟦-n⟧' := by
    simpa only [F, fV, f, eT, eK, e, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc] using
      localizedTensorComparison_shift_transport R A B C U Q N n t
  have hshift : H.map (f⟦-n⟧') ≫ shT.hom =
      shK.hom ≫ HomologicalComplex.homologyMap f i :=
    (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} C) (-n) (i + n) i
      (by omega)).hom.naturality f
  have hsquare : HomologicalComplex.homologyMap fV (i + n) ≫
      (H.mapIso eT ≪≫ shT).hom =
      (H.mapIso eK ≪≫ shK).hom ≫ HomologicalComplex.homologyMap f i := by
    change H.map fV ≫ (H.map eT.hom ≫ shT.hom) =
      (H.map eK.hom ≫ shK.hom) ≫ HomologicalComplex.homologyMap f i
    rw [← Category.assoc, ← H.map_comp, hcomplex, H.map_comp, Category.assoc,
      hshift, Category.assoc]
  change mU.localizedComparison i ≫ HomologicalComplex.homologyMap f i = _
  change mU.localizedComparison i = eS.inv ≫ mV.localizedComparison (i + n) ≫
    (H.mapIso eK ≪≫ shK).hom at hmodel
  rw [hmodel]
  simp only [Category.assoc]
  rw [← hsquare]

end ModuleCat
