/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import Mathlib.Algebra.Ring.Shrink
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import WeilConjectures.SixFunctors.FiniteCtfInternalEtaleRealization
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.CategoryTheory.SixFunctors.LocalizingSubcategoryUniverse
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts

/-!
# Finite-coefficient proper direct image on the localizing categories

Source: blueprint main-20261015, chap-Construction-of-f,
sk-prop-ctf-finite-proper/sk-prop-ctf-finite-proper-localizing.md
(blueprint: corollary-proper-direct-image-finite-coefficients-localizing).

The finite ring is represented canonically by its finite discrete condensed ring.
All subcategories in the statements are the recorded constant-model constructible
finite-Tor predicate and `localizingClosureProEtale`; the functors are the published
module-object six functors, and the base-change map is the recorded ambient exchange
`CondensedRing.condensedAmbientExchange`. Thus the statements retain the specified
coefficient identification while using the recorded condensed objects.

## Main definitions

* `finiteDiscreteCondensedCoefficient`: the condensed ring of a finite discrete ring.
* `finiteCoefficientLocalizingProperties`: the Dctf, localizing-restriction, exactness
  and sum clauses for a module-object derived functor.

## Main statements

* `finiteProperLocalizing`: clause (1).
* `finiteProperLocalizing_baseChange`: clause (2).
* `finiteOpenLocalizing`: the extension-by-zero part of clause (3).
* `finiteCompactificationLocalizing`: the compactification part of clause (3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor CategoryTheory.Obj CategoryTheory.MonoidalClosed

namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

section PrivateComparisonProofs

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

section TensorInstanceCache

variable (T : AlgebraicGeometry.Scheme.{u})
  (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1})
  [MonObj R] [IsCommMonObj R]

private theorem cachedTensorLeft :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorRight :
    ∀ (X₁ X₂ X₃ : GradedObject ℤ (Mod
      (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R)),
      GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := by infer_instance

private theorem cachedTensorColimLeft :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).obj M) := by
  intro M
  infer_instance

private theorem cachedTensorColimRight :
    ∀ M : Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R,
      PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor _).flip.obj M) := by
  intro M
  infer_instance

omit [IsCommMonObj R] in
private theorem cachedExactIntegerColimits :
    HasExactColimitsOfShape ℤ
      (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) R) := by
  infer_instance

end TensorInstanceCache

attribute [local instance] cachedTensorLeft cachedTensorRight
  cachedTensorColimLeft cachedTensorColimRight cachedExactIntegerColimits

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem maps_localizingClosure
    {C D : Type u} [Category.{v} C] [Category.{v'} D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (S : ObjectProperty C) (T : ObjectProperty D) (F : C ⥤ D)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P)
    (hT : IsLocalizingSubcategory (localizingClosure T))
    (hgen : ∀ K, S K → P K)
    (hpres : ∀ K, S K → T (F.obj K))
    (hsums : ∀ (I : Type v) (J : Discrete I ⥤ C),
      (∀ i : I, P (J.obj ⟨i⟩)) → PreservesColimit J F) :
    ∀ K, localizingClosure S K → localizingClosure T (F.obj K) := by
  let Q := localizingClosure T
  letI : P.IsTriangulated := hP.1
  letI : P.IsClosedUnderIsomorphisms := hP.2.1
  letI : Q.IsTriangulated := hT.1
  letI : Q.IsClosedUnderIsomorphisms := hT.2.1
  let R := P ⊓ Q.inverseImage F
  have hR : IsLocalizingSubcategory R := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro I J hJ hJR
    letI := hJ
    letI := hsums I J (fun i ↦ (hJR i).1)
    exact ⟨hP.2.2 J hJ (fun i ↦ (hJR i).1),
      Q.prop_of_iso (preservesColimitIso F J).symm
        (hT.prop_colimit (J ⋙ F) inferInstance (fun i ↦ (hJR i).2))⟩
  intro K hK
  exact (hK R hR (fun L hL ↦ ⟨hgen L hL,
    fun V _ hV ↦ hV _ (hpres L hL)⟩)).2

/-- A functor preserves an existing direct sum of objects of a localizing subcategory as soon as
its restriction to the subcategory preserves direct sums of that shape: the subcategory is closed
under the direct sum (`IsLocalizingSubcategory.isClosedUnderColimitsOfShape_discrete`), so its
inclusion creates it. -/
private theorem preserves_of_localizing
    {C D : Type*} [Category* C] [Category* D]
    [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P) (F : C ⥤ D)
    {I : Type*} [PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F)]
    (K : Discrete I ⥤ C) (hK : ∀ i : I, P (K.obj ⟨i⟩)) : PreservesColimit K F := by
  apply PreservesColimit.mk'
  intro hcol
  let := hcol
  let := hP.2.1
  let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
    hP.isClosedUnderColimitsOfShape_discrete I
  let L := P.lift K (fun j ↦ hK j.as)
  letI : HasColimit (L ⋙ P.ι) := hcol
  letI : CreatesColimit L P.ι :=
    createsColimitFullSubcategoryInclusionOfClosed (Discrete I) P L
  letI : HasColimit L := hasColimit_of_created L P.ι
  have hh := isColimitOfPreserves (P.ι ⋙ F) (colimit.isColimit L)
  exact preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves P.ι (colimit.isColimit L)) hh

private theorem preserves_on_subcategory
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {I : Type*} (P : ObjectProperty C) [HasColimitsOfShape (Discrete I) C]
    [P.IsClosedUnderColimitsOfShape (Discrete I)]
    (e : C ≌ C') (t : D ≌ D') (F : C ⥤ D) (G : C' ⥤ D')
    (i : F ⋙ t.functor ≅ e.functor ⋙ G)
    (hs : ∀ (M : I → C), (∀ j, P (M j)) →
      PreservesColimit (Discrete.functor (fun j ↦ e.functor.obj (M j))) G) :
    PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) := by
  constructor
  intro J
  let M := fun j : I ↦ J.obj ⟨j⟩
  have hJ : Discrete.functor M ≅ J := Discrete.natIso (fun _ ↦ Iso.refl _)
  suffices h : PreservesColimit (Discrete.functor M) (P.ι ⋙ F) by
    letI := h
    exact preservesColimit_of_iso_diagram (P.ι ⋙ F) hJ
  letI := hs (fun j ↦ (M j).obj) (fun j ↦ (M j).property)
  letI : PreservesColimit (Discrete.functor M ⋙ P.ι ⋙ e.functor) G :=
    preservesColimit_of_iso_diagram
      (K₁ := Discrete.functor (fun j ↦ e.functor.obj (M j).obj))
      G (Discrete.natIso (fun _ ↦ Iso.refl _))
  letI : PreservesColimit (Discrete.functor M) (P.ι ⋙ e.functor) :=
    comp_preservesColimit P.ι e.functor
  letI : PreservesColimit (Discrete.functor M) ((P.ι ⋙ e.functor) ⋙ G) :=
    comp_preservesColimit _ _
  letI : PreservesColimit (Discrete.functor M) ((P.ι ⋙ F) ⋙ t.functor) :=
    preservesColimit_of_natIso _
      ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft P.ι i.symm ≪≫
        (Functor.associator _ _ _).symm)
  exact preservesColimit_of_reflects_of_preserves (P.ι ⋙ F) t.functor

private theorem transported_generator
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (S : ObjectProperty C) (T : ObjectProperty D) (Q : ObjectProperty E)
    [Q.IsClosedUnderIsomorphisms] (e : S.FullSubcategory ≌ T.FullSubcategory)
    (V : C ⥤ E) (F : D ≌ E)
    (i : e.functor ⋙ T.ι ≅ S.ι ⋙ V ⋙ F.inverse)
    (hV : ∀ L, S L → Q (V.obj L)) (K : T.FullSubcategory) :
    Q (F.functor.obj K.obj) := by
  let L := e.inverse.obj K
  let j : F.inverse.obj (V.obj L.obj) ≅ K.obj :=
    (i.app L).symm ≪≫ T.ι.mapIso (e.counitIso.app K)
  exact Q.prop_of_iso
    ((F.counitIso.app (V.obj L.obj)).symm ≪≫ F.functor.mapIso j)
    (hV L.obj L.property)

namespace AlgebraicGeometry.ProEtale

open CondensedRing

attribute [local instance] unboundedLocalizingPullbackCommShift

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  upperStarFromPoint DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] CondensedRing.condensedAmbientExchange
  CondensedRing.condensedAmbientPullbackComparison CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem ordinary_preserves_coproduct
    (B : Type (u + 1)) [CommRing B] [Finite B] {k : Type u} [Field k]
    {Z T : Scheme.{u}} (f : Z ⟶ T) [IsProper f]
    (aZ : Z ⟶ Spec (.of k)) (aT : T ⟶ Spec (.of k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    [LocallyOfFiniteType aT] [QuasiCompact aT] (hf : f ≫ aT = aZ)
    {I : Type (u + 1)}
    (M : I → _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} B)))
    (hM : ∀ i, DerivedCategory.etaleOriginHomology B Z (M i)) :
    PreservesColimit (Discrete.functor M)
      (lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor := by
  letI := isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology
    B f aZ aT hf M hM
  exact PreservesCoproduct.of_iso_comparison _ M

private theorem encoding_triangulated
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (T : Scheme.{u}) (e : FiniteDiscreteOrdinary.Encoding A T) :
    e.fixedDerived.functor.IsTriangulated := by
  change (e.ordinary.functor ⋙ e.fixed.functor).mapDerivedCategory.IsTriangulated
  infer_instance

-- Transport the specified fixed-interval equivalence.
private theorem encoding_generator_etaleOrigin
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p] (hp : 0 < p) (hne : p ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
    (E : ∀ T : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A T)
    (T : Over (Spec (.of k)))
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    (K : ConstantModelConstructibleFiniteTor (FiniteDiscreteOrdinary.coefficient A) T.left) :
    DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) T.left
      ((E T.left).fixedDerived.functor.obj K.obj) := by
  obtain ⟨a, b, htor⟩ := K.property.2
  obtain ⟨hreal, _⟩ := FiniteDiscreteOrdinary.finiteCtfInternalEtaleRealization
    ℓ p k hp hne A E
  obtain ⟨eT, ⟨heT⟩⟩ := hreal T (min a b) b (min_le_right _ _)
  exact transported_generator _ _
    (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) T.left) eT
    (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T.left).mapDerivedCategory
    (E T.left).fixedDerived heT
    (fun C _ ↦ DerivedCategory.etaleOriginHomology_mapDerivedCategory_obj C)
    ⟨K.obj, K.property.1, htor.mono (min_le_left _ _) le_rfl⟩

attribute [local irreducible] FiniteDiscreteOrdinary.Encoding.fixedDerived

end AlgebraicGeometry.ProEtale
end PrivateComparisonProofs

attribute [local instance] cachedTensorLeft cachedTensorRight
  cachedTensorColimLeft cachedTensorColimRight cachedExactIntegerColimits

namespace AlgebraicGeometry.ProEtale

open CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The condensed ring of a finite discrete commutative ring: the continuous-map
condensed ring `S ↦ C(S, A)` for the discrete topology on `A`.
Source: blueprint corollary-proper-direct-image-finite-coefficients-localizing, statement,
coefficient identification of lem-weil-pbc-finite-discrete-condensed-ring-constant
(blueprint: corollary-proper-direct-image-finite-coefficients-localizing). -/
noncomputable def finiteDiscreteCondensedCoefficient (A : Type u) [CommRing A] [Finite A] :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverse.{u, u} A

/-- The canonical monoid structure on the finite discrete condensed coefficient, the
published pointwise ring-object structure of the continuous-map condensed ring.
Source: blueprint corollary-proper-direct-image-finite-coefficients-localizing, statement,
coefficient identification (blueprint:
corollary-proper-direct-image-finite-coefficients-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_monObj
    (A : Type u) [CommRing A] [Finite A] :
    MonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  exact Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A

/-- Commutativity of the canonical finite discrete condensed coefficient.
Source: blueprint corollary-proper-direct-image-finite-coefficients-localizing, statement,
coefficient identification (blueprint:
corollary-proper-direct-image-finite-coefficients-localizing). -/
noncomputable instance finiteDiscreteCondensedCoefficient_isCommMonObj
    (A : Type u) [CommRing A] [Finite A] :
    IsCommMonObj (finiteDiscreteCondensedCoefficient A) := by
  unfold finiteDiscreteCondensedCoefficient
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) :=
    Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} A
  exact Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} A

/-- The Dctf and localizing-restriction clauses for a module-object derived functor `F`:
`F` maps `Dctf(X)` into `Dctf(Y)` (the recorded `constantModelBoundedConstructible` and
finite Tor amplitude), maps `Loc(Dctf(X))` into `Loc(Dctf(Y))` (the recorded
`localizingClosureProEtale`), sends distinguished triangles of the source closure to
distinguished triangles (exactness of the restriction), and preserves every small
coproduct of objects of the source closure (the empty one included).
Source: blueprint corollary-proper-direct-image-finite-coefficients-localizing, statement, clauses
(1) and (3) (blueprint: corollary-proper-direct-image-finite-coefficients-localizing). -/
def finiteCoefficientLocalizingProperties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}}
    (F : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) ⥤
      DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)))
    [F.CommShift ℤ] : Prop :=
  (∀ K, (constantModelBoundedConstructible Λ X K ∧
      DerivedCategory.finiteTorAmplitude _ K) →
    (constantModelBoundedConstructible Λ Y (F.obj K) ∧
      DerivedCategory.finiteTorAmplitude _ (F.obj K))) ∧
  (∀ K, localizingClosureProEtale Λ X K →
    localizingClosureProEtale Λ Y (F.obj K)) ∧
  (∀ T : Triangle
      (DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    T ∈ distTriang _ →
    localizingClosureProEtale Λ X T.obj₁ →
    localizingClosureProEtale Λ X T.obj₂ →
    localizingClosureProEtale Λ X T.obj₃ →
      F.mapTriangle.obj T ∈ distTriang _) ∧
  (∀ (I : Type (u + 2))
    (D : Discrete I ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
    (∀ i : I, localizingClosureProEtale Λ X (D.obj ⟨i⟩)) →
      PreservesColimit D F)

open scoped CategoryTheory.MonoidalClosed in
attribute [local instance] unboundedLocalizingPullbackCommShift

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11 finiteProperCache12
  cachedModuleMonoidal cachedModuleBraided cachedModuleSymmetric cachedDerivedMonoidal
  cachedModuleClosed cachedModuleFlatResolution cachedDerivedTensorStructure

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

attribute [local irreducible] CondensedRing.lowerStar CondensedRing.upperStar
  upperStarFromPoint DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.monoidalCategoryStruct
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local irreducible] CondensedRing.condensedAmbientExchange
  CondensedRing.condensedAmbientPullbackComparison CondensedRing.leftDerivedUpperStarComp
  CondensedRing.derivedUpperStarLowerStarAdjunction

attribute [local irreducible] FiniteDiscreteOrdinary.Encoding.fixedDerived

namespace CondensedRing

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] FiniteDiscreteOrdinary.coefficientEncoding
  ProEtale.derivedBaseChangeMap ProEtale.upperStar ProEtale.lowerStar
  ProEtale.derivedUpperStarLowerStarAdjunction ProEtale.leftDerivedUpperStarComp

end CondensedRing

section Setting

variable (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : 0 < p) (hpℓ : p ≠ ℓ)
  (k : Type u) [Field k] [CharP k p]
  (A : Type u) [CommRing A] [Finite A]
  (hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ ^ n : ℕ) • (1 : A) = 0)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]

include hℓ hp hpℓ hA k

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Keep the canonical derived functors abstract during elaboration.
/-- Clause (1): proper pushforward preserves the recorded finite-coefficient Dctf and
restricts to an exact sum-preserving functor of the localizing closures.
Source: blueprint sk-prop-ctf-finite-proper-localizing, clause (1)
(blueprint: corollary-proper-direct-image-finite-coefficients-localizing).

Proof:
1. Use the normalized section-action equivalence for the finite discrete ring. Its
   derived equivalence identifies each internal Dctf generator with an etale realization,
   by `finiteCtfInternalEtaleRealization` for a fixed ordered Tor interval.
2. Pull back the replete triangulated property of having etale-origin cohomology along
   that equivalence. Exact coproducts make it localizing at the Hom universe; an existing
   larger coproduct has small nonzero support, so it is localizing in the object universe.
3. The source theorem
   `isIso_sigmaComparison_rightDerivedLowerStar_of_etaleOriginHomology` gives coproduct
   preservation on that subcategory. Transport through `encodingDerivedPushforwardIso`,
   reflect the colimit through the target equivalence, and extend to larger index sets
   by the same small-support argument.
4. `continuous_finiteProper_preserves` supplies Dctf preservation. Intersect the classical
   subcategory with the inverse image of the target localizing closure. This intersection
   is replete, triangulated, and closed under all existing ambient coproducts by step 3.
   It contains the generators, hence contains their localizing closure. The ordinary
   right derived functor is triangulated, giving the asserted exactness. -/
theorem finiteProperLocalizing (f : X ⟶ Y) [f.IsOver (Spec (.of k))] [IsProper f] :
    finiteCoefficientLocalizingProperties (finiteDiscreteCondensedCoefficient A)
      (f)_*⟦finiteDiscreteCondensedCoefficient A⟧.rightDerivedFunctor := by
  classical
  letI : Fact ℓ.Prime := ⟨hℓ⟩
  letI : Fact (ringChar k).Prime :=
    ⟨by simpa only [ringChar.eq k p] using
      ((CharP.char_is_prime_or_zero k p).resolve_right (Nat.ne_of_gt hp))⟩
  letI : Fact (ringChar k ≠ ℓ) := ⟨by simpa only [ringChar.eq k p] using hpℓ⟩
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : IsTopologicalRing A := by infer_instance
  change finiteCoefficientLocalizingProperties (FiniteDiscreteOrdinary.coefficient A)
    (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
  let SX : Over (Spec (.of k)) := Over.mk (X ↘ Spec (.of k))
  let SY : Over (Spec (.of k)) := Over.mk (Y ↘ Spec (.of k))
  letI : LocallyOfFiniteType SX.hom := ‹LocallyOfFiniteType (X ↘ Spec (.of k))›
  letI : QuasiCompact SX.hom := ‹QuasiCompact (X ↘ Spec (.of k))›
  letI : IsSeparated SX.hom := ‹IsSeparated (X ↘ Spec (.of k))›
  letI : LocallyOfFiniteType SY.hom := ‹LocallyOfFiniteType (Y ↘ Spec (.of k))›
  letI : QuasiCompact SY.hom := ‹QuasiCompact (Y ↘ Spec (.of k))›
  letI : IsSeparated SY.hom := ‹IsSeparated (Y ↘ Spec (.of k))›
  let E (T : Scheme.{u}) := (FiniteDiscreteOrdinary.encoding_exists A T).some
  let P : ObjectProperty (DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :=
    (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) X).inverseImage
      (E X).fixedDerived.functor
  have hPsmall : P.IsTriangulated := by
    let : (E X).fixedDerived.functor.IsTriangulated := encoding_triangulated A X (E X)
    dsimp only [P]
    infer_instance
  have hPiso : P.IsClosedUnderIsomorphisms := by dsimp only [P]; infer_instance
  have hP : IsLocalizingSubcategory P := by
    let := hPsmall
    let := hPiso
    apply isLocalizingSubcategory_of_locallySmall.{u + 1}
    refine ⟨hPsmall, hPiso, ?_⟩
    intro I D hD hobj
    letI := hD
    exact (DerivedCategory.etaleOriginHomology (ULift.{u + 1} A) X).prop_of_isColimit
      (isColimitOfPreserves (E X).fixedDerived.functor (colimit.isColimit D))
      (fun i ↦ hobj i.as)
  have hgen : ∀ K, (constantModelBoundedConstructible
      (FiniteDiscreteOrdinary.coefficient A) X K ∧
      _root_.DerivedCategory.finiteTorAmplitude (FiniteDiscreteOrdinary.Internal A X) K) →
      P K := by
    intro K hK
    exact encoding_generator_etaleOrigin ℓ p k hp hpℓ A E SX ⟨K, hK⟩
  let F := (CondensedRing.lowerStar (FiniteDiscreteOrdinary.coefficient A) f).rightDerivedFunctor
  let G := (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor
  let i : F ⋙ (E Y).fixedDerived.functor ≅ (E X).fixedDerived.functor ⋙ G :=
    FiniteDiscreteOrdinary.encodingDerivedPushforwardIso A f (E Y) (E X)
  have hs : ∀ (I : Type (u + 1)), PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) := by
    intro I
    letI : HasColimitsOfShape (Discrete I)
        (DerivedCategory (FiniteDiscreteOrdinary.Internal A X)) :=
      Adjunction.hasColimitsOfShape_of_equivalence (E X).fixedDerived.functor
    let : P.IsClosedUnderColimitsOfShape (Discrete I) :=
      hP.isClosedUnderColimitsOfShape_discrete I
    apply preserves_on_subcategory P (E X).fixedDerived (E Y).fixedDerived F G i
    intro M hM
    exact ordinary_preserves_coproduct (ULift.{u + 1} A) f
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (by simp) _ hM
  have hslarge (I : Type (u + 2)) :
      PreservesColimitsOfShape (Discrete I) (P.ι ⋙ F) :=
    Functor.preservesColimitsOfShape_discrete_of_small (P.ι ⋙ F) hs I
  have hsums (I : Type (u + 2))
      (D : Discrete I ⥤ DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
      (hD : ∀ i : I, P (D.obj ⟨i⟩)) : PreservesColimit D F := by
    let := hslarge I
    exact preserves_of_localizing P hP F D hD
  have hsumsSmall (I : Type (u + 1))
      (D : Discrete I ⥤ DerivedCategory (FiniteDiscreteOrdinary.Internal A X))
      (hD : ∀ i : I, P (D.obj ⟨i⟩)) : PreservesColimit D F := by
    let := hs I
    exact preserves_of_localizing P hP F D hD
  let ff : SX ⟶ SY := Over.homMk f (by
    change f ≫ (Y ↘ Spec (.of k)) = X ↘ Spec (.of k)
    exact comp_over f _)
  letI : IsProper ff.left := ‹IsProper f›
  have hpres := CondensedRing.continuous_finiteProper_preserves A ℓ
    (by obtain ⟨n, _, hn⟩ := hA; exact ⟨n, hn⟩) k
    SX SY ff
  have hQ := (localizingClosure_exists (FiniteDiscreteOrdinary.coefficient A) Y
    (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
      fun K ↦ _root_.DerivedCategory.finiteTorAmplitude _ K)).2.2.2.1
  letI : F.IsTriangulated := inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K hK
    exact hpres ⟨K, hK⟩
  · exact maps_localizingClosure
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) X ⊓
        fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M)
      (constantModelBoundedConstructible (FiniteDiscreteOrdinary.coefficient A) Y ⊓
        fun M ↦ _root_.DerivedCategory.finiteTorAmplitude _ M) F P hP hQ hgen
      (fun K hK ↦ hpres ⟨K, hK⟩) hsumsSmall
  · intro T hT _ _ _
    exact Functor.map_distinguished _ T hT
  · intro I D hD
    exact hsums I D (fun i ↦ hD i P hP hgen)

-- Keep the canonical derived functors abstract during elaboration.
end Setting

end AlgebraicGeometry.ProEtale
