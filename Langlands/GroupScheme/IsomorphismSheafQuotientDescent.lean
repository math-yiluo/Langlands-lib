import Langlands.GroupScheme.IsomorphismSheafActionQuotient
import Langlands.AlgebraicGeometry.AlgebraicSpace.ExtensionProduct
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof

/-! # Scheme representations of the Isom action quotient from local models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.LocalGroupIso.ActionQuotient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {S : Scheme.{u}} {G H A : GroupScheme S}
    (a : AutomorphicAction A G)

/-- The quotient sheaf with an arbitrary represented relative parameter. -/
def withParameter (U : Over S) : FppfSheaf S :=
  ⟨extProd (sheaf (H := H) a).obj U, extProd.isSheaf (sheaf a).property⟩

/-- The original class map with the relative parameter retained. -/
def mapWithParameter (U : Over S) :
    extProd (presheaf G H) U ⟶ (withParameter (H := H) a U).obj :=
  extProd.mapLeft (classMap a).hom

theorem mapWithParameter_isLocallySurjective (U : Over S) :
    CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (mapWithParameter (H := H) a U) := by
  let := classMap_isLocallySurjective (H := H) a
  constructor
  intro T z
  apply (fppfTopology S).superset_covering ?_
    (CategoryTheory.Presheaf.imageSieve_mem (fppfTopology S) (classMap a).hom z.1)
  rintro V r ⟨e, he⟩
  exact ⟨(e, ⟨r ≫ z.2.down⟩), Prod.ext he rfl⟩

/-- Actual local schemes representing Isom families and their exact orbit quotient.
The quotient's structure map to the local base is separated and locally quasi-finite. -/
structure LocalPresentation (U : Over S) where
  isomParameter : Over S
  isomIso : (schemeYoneda S).obj isomParameter ≅ extProd (presheaf G H) U
  isomProjection : isomParameter ⟶ U
  isomIso_snd : isomIso.hom ≫ extProd.snd = (schemeYoneda S).map isomProjection
  parameter : Over S
  projection : parameter ⟶ U
  classMap : isomParameter ⟶ parameter
  comm : classMap ≫ projection = isomProjection
  flat : Flat classMap.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation classMap.left
  surjective : Surjective classMap.left
  separated : IsSeparated projection.left
  locallyQuasiFinite : LocallyQuasiFinite projection.left
  locallyOfFiniteType : LocallyOfFiniteType projection.left
  kernel : ∀ (T : Over S) (p p' : T ⟶ isomParameter),
    p ≫ classMap = p' ≫ classMap ↔ p ≫ isomProjection = p' ≫ isomProjection ∧
      ∃ d : T ⟶ A.X,
        act a d (isomIso.hom.app (op T) ⟨p⟩).1 = (isomIso.hom.app (op T) ⟨p'⟩).1

attribute [instance] LocalPresentation.flat LocalPresentation.locallyOfFinitePresentation
  LocalPresentation.surjective

namespace LocalPresentation

variable {a} {U : Over S} (P : LocalPresentation (H := H) a U)

theorem presentationMap_eq_iff (ha : a.IsFaithful) (T : Over S)
    (p p' : T ⟶ P.isomParameter) :
    (P.isomIso.hom ≫ mapWithParameter a U).app (op T) ⟨p⟩ =
        (P.isomIso.hom ≫ mapWithParameter a U).app (op T) ⟨p'⟩ ↔
      p ≫ P.classMap = p' ≫ P.classMap := by
  have hsnd (q : T ⟶ P.isomParameter) :
      (P.isomIso.hom.app (op T) ⟨q⟩).2 = ULift.up (q ≫ P.isomProjection) :=
    congrArg (fun k => k.app (op T) ⟨q⟩) P.isomIso_snd
  change ((ActionQuotient.classMap a).hom.app (op T) (P.isomIso.hom.app (op T) ⟨p⟩).1,
      (P.isomIso.hom.app (op T) ⟨p⟩).2) =
    ((ActionQuotient.classMap a).hom.app (op T) (P.isomIso.hom.app (op T) ⟨p'⟩).1,
      (P.isomIso.hom.app (op T) ⟨p'⟩).2) ↔ _
  rw [Prod.mk.injEq, classMap_eq_iff a ha, hsnd, hsnd, ULift.up.injEq]
  exact and_comm.trans (P.kernel T p p').symm

/-- The local quotient scheme represents the canonical quotient with its original parameter. -/
theorem exists_iso (ha : a.IsFaithful) :
    ∃ e : (schemeYoneda S).obj P.parameter ≅ (withParameter a U).obj,
      (schemeYoneda S).map P.classMap ≫ e.hom =
        P.isomIso.hom ≫ mapWithParameter a U := by
  let := mapWithParameter_isLocallySurjective (H := H) a U
  have hlocal : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (P.isomIso.hom ≫ mapWithParameter a U) := inferInstance
  exact exists_iso_of_locallySurjective_of_same_kernel
    (P.isomIso.hom ≫ mapWithParameter a U) P.classMap hlocal
      (isLocallySurjective_schemeYoneda_map P.classMap) (P.presentationMap_eq_iff ha)

theorem iso_snd
    (e : (schemeYoneda S).obj P.parameter ≅ (withParameter a U).obj)
    (he : (schemeYoneda S).map P.classMap ≫ e.hom =
      P.isomIso.hom ≫ mapWithParameter a U) :
    e.hom ≫ extProd.snd = (schemeYoneda S).map P.projection := by
  let q := (schemeSheaf S).map P.classMap
  have : Sheaf.IsLocallySurjective q := isLocallySurjective_schemeYoneda_map P.classMap
  have : Epi q := inferInstance
  let r : (schemeSheaf S).obj P.parameter ⟶ (schemeSheaf S).obj U :=
    ObjectProperty.homMk (e.hom ≫ extProd.snd)
  let s := (schemeSheaf S).map P.projection
  have h : q ≫ r = q ≫ s := by
    apply ObjectProperty.hom_ext
    change (schemeYoneda S).map P.classMap ≫ e.hom ≫ extProd.snd =
      (schemeYoneda S).map P.classMap ≫ (schemeYoneda S).map P.projection
    rw [← Category.assoc, he, Category.assoc,
      show mapWithParameter (H := H) a U ≫ extProd.snd = extProd.snd from rfl,
      P.isomIso_snd, ← Functor.map_comp, P.comm]
  exact congrArg (fun k => k.hom) ((cancel_epi q).mp h)

/-- The local representation is the actual base change of the quotient over the local base. -/
theorem isPullback
    (e : (schemeYoneda S).obj P.parameter ≅ (withParameter a U).obj)
    (he : (schemeYoneda S).map P.classMap ≫ e.hom =
      P.isomIso.hom ≫ mapWithParameter a U)
    (g : U ⟶ Over.mk (𝟙 S)) :
    IsPullback (e.hom ≫ extProd.fst) ((schemeYoneda S).map P.projection)
      ((Over.mkIdTerminal.isTerminalObj (schemeYoneda S)).from (sheaf a).obj)
      ((schemeYoneda S).map g) := by
  let t := Over.mkIdTerminal.isTerminalObj (schemeYoneda S)
  have hpb := IsPullback.of_is_product
    (FunctorToTypes.binaryProductLimit (sheaf (H := H) a).obj ((schemeYoneda S).obj U)) t
  change IsPullback (extProd.fst : extProd (sheaf a).obj U ⟶ _)
    extProd.snd (t.from (sheaf a).obj)
    (t.from ((schemeYoneda S).obj U)) at hpb
  have hg : t.from ((schemeYoneda S).obj U) = (schemeYoneda S).map g := t.hom_ext _ _
  rw [hg] at hpb
  exact hpb.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Category.comp_id _).symm
    ((P.iso_snd e he).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

end LocalPresentation

/-- A scheme representing the action quotient of all natural Isom families. -/
structure Representation where
  parameter : Over S
  iso : (schemeYoneda S).obj parameter ≅ (sheaf (H := H) a).obj

/-- The represented quotient class as a natural map on every Isom family. -/
def Representation.mapToParameter (R : Representation (H := H) a) :
    presheaf G H ⟶ (schemeYoneda S).obj R.parameter :=
  (classMap a).hom ≫ R.iso.inv

@[reassoc (attr := simp)] theorem Representation.mapToParameter_iso_hom
    (R : Representation (H := H) a) :
    R.mapToParameter a ≫ R.iso.hom = (classMap a).hom := by
  simp [Representation.mapToParameter]

/-- Separated locally quasi-finite quotient models on a covering sieve descend to a scheme. -/
def representationOfLocalPresentations (ha : a.IsFaithful)
    (J : Sieve (Over.mk (𝟙 S))) (hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)))
    (hlocal : ∀ ⦃U : Over S⦄ (g : U ⟶ Over.mk (𝟙 S)), J g →
      Nonempty (LocalPresentation (H := H) a U)) :
    Representation (H := H) a := by
  apply Classical.choice
  let t := Over.mkIdTerminal.isTerminalObj (schemeYoneda S)
  obtain ⟨Q, _, e, _⟩ :=
    Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent
      S (sheaf (H := H) a) (Over.mk (𝟙 S)) (t.from _) J hJ (by
        intro U g hg
        let P := Classical.choice (hlocal g hg)
        obtain ⟨e, he⟩ := P.exists_iso ha
        exact ⟨P.parameter, P.projection, e.hom ≫ extProd.fst, P.isPullback e he g,
          P.separated, P.locallyQuasiFinite, P.locallyOfFiniteType⟩)
  exact ⟨⟨Q, e⟩⟩

end Langlands.GroupScheme.LocalGroupIso.ActionQuotient
