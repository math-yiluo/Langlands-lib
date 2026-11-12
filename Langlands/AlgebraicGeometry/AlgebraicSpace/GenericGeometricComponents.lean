import Langlands.AlgebraicGeometry.AlgebraicSpace.SplitGenericAtlasCover
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricComponentTransport
import Langlands.AlgebraicGeometry.FiniteEtaleGenericComponentSplittingProof
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberGenericConstancy

/-! # Generic constancy of actual geometric fibre components -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open SchemeFiberGeometry GeometricComponentTransport

variable {S T : Scheme.{u}} {U : Over S}

/-- The chart obtained by restricting to an open and then pulling back is an
actual chart for base change along the composite. -/
def openBaseChangeAtlasIso (U : Over S) (V : S.Opens) (g : T ⟶ V.toScheme) :
    Over.mk (Limits.pullback.snd (U.hom ∣_ V) g) ≅
      (Over.pullback (g ≫ V.ι)).obj U := by
  let h := (IsPullback.of_hasPullback (U.hom ∣_ V) g).paste_horiz
    (isPullback_morphismRestrict U.hom V).flip
  exact Over.isoMk h.isoPullback h.isoPullback_hom_snd

/-- Pull an atlas back through an open restriction using its actual restricted scheme. -/
def openBaseChangeAtlasMap {F : Presheaf S}
    (a : (schemeYoneda S).obj U ⟶ F) (V : S.Opens) (g : T ⟶ V.toScheme) :
    (schemeYoneda T).obj (Over.mk (Limits.pullback.snd (U.hom ∣_ V) g)) ⟶
      (restrictPresheaf (g ≫ V.ι)).obj F :=
  (schemeYoneda T).map (openBaseChangeAtlasIso U V g).hom ≫ restrictAtlas (g ≫ V.ι) a

/-- The actual restricted chart is etale. -/
theorem isEtale_openBaseChangeAtlasMap {F : Presheaf S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a)
    (V : S.Opens) (g : T ⟶ V.toScheme) :
    IsEtale (openBaseChangeAtlasMap a V g) :=
  IsEtale.iso_comp ((schemeYoneda T).mapIso (openBaseChangeAtlasIso U V g))
    (relative_restrictAtlas _ ha)

/-- The actual restricted chart is geometrically surjective. -/
theorem isSurjective_openBaseChangeAtlasMap {F : Presheaf S}
    (a : (schemeYoneda S).obj U ⟶ F) (hs : IsSurjective a)
    (V : S.Opens) (g : T ⟶ V.toScheme) :
    IsSurjective (openBaseChangeAtlasMap a V g) := by
  have : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso
    ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget T)).relative
      (schemeYoneda T)) _ _).mpr (relative_restrictAtlas _ hs)

/-- Actual geometric fibre components are constant on a nonempty open of an
irreducible Noetherian base, without a generic splitting assumption. -/
theorem exists_open_geometricComponentsEquiv
    [IsNoetherian S] [IrreducibleSpace S]
    (X : AlgebraicSpace S) (hX : IsQuasiSeparated X)
    (a : (schemeYoneda S).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] :
    ∃ V : Set S, IsOpen V ∧ V.Nonempty ∧ ∀ p ∈ V, ∀ q ∈ V,
      Nonempty
        (@_root_.ConnectedComponents
            (Points (X.presheaf ⨯ (schemeYoneda S).obj
              (Over.mk (componentCountGeometricPoint p)))) (pointTopology _) ≃
          @_root_.ConnectedComponents
            (Points (X.presheaf ⨯ (schemeYoneda S).obj
              (Over.mk (componentCountGeometricPoint q)))) (pointTopology _)) := by
  obtain ⟨V, _, S', g, hAff, hIrr, hSur, hFin, hEt, _, _, _, η', hη', hgeom⟩ :=
    finiteTypeFiniteEtaleGenericComponentSplitting U.hom
  let := hAff
  let := hIrr
  let := hSur
  let := hFin
  let := hEt
  let : IsNoetherian S' :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian g
      toCompactSpace := inferInstance }
  let h := g ≫ V.ι
  let U' : Over S' := Over.mk (Limits.pullback.snd (U.hom ∣_ V) g)
  let : LocallyOfFiniteType U'.hom := by
    change LocallyOfFiniteType (Limits.pullback.snd (U.hom ∣_ V) g)
    infer_instance
  let : QuasiCompact U'.hom := by
    change QuasiCompact (Limits.pullback.snd (U.hom ∣_ V) g)
    infer_instance
  let a' : (schemeYoneda S').obj U' ⟶ (baseChange h X).presheaf :=
    openBaseChangeAtlasMap a V g
  obtain ⟨W, hW, hηW, hcomp⟩ :=
    exists_open_geometricComponentsEquiv_of_split_generic
      (baseChange h X) (IsQuasiSeparated.baseChange hX) a'
      (isEtale_openBaseChangeAtlasMap a ha V g)
      (isSurjective_openBaseChangeAtlasMap a hs V g) hη' hgeom
  refine ⟨h '' W, h.isOpenMap W hW, ⟨h η', η', hηW, rfl⟩, ?_⟩
  rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩
  exact ⟨(baseChangeGeometricFibreEquiv h X a ha hs p').symm.trans
    ((hcomp p' hp').some.trans
      ((hcomp q' hq').some.symm.trans
        (baseChangeGeometricFibreEquiv h X a ha hs q')))⟩

/-- The exact host count is constant on a nonempty open of an irreducible
Noetherian affine base. -/
theorem exists_open_geometricFibreComponentCount
    (B : Type u) [CommRing B] [IsNoetherianRing B]
    [IrreducibleSpace (Spec (CommRingCat.of B))]
    (X : AlgebraicSpace (Spec (CommRingCat.of B))) (hX : IsQuasiSeparated X)
    {U : Over (Spec (CommRingCat.of B))}
    (a : (schemeYoneda _).obj U ⟶ X.presheaf) (ha : IsEtale a) (hs : IsSurjective a)
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] :
    ∃ V : Set (Spec (CommRingCat.of B)), IsOpen V ∧ V.Nonempty ∧
      ∀ p ∈ V, ∀ q ∈ V,
        geometricFibreComponentCount B X p = geometricFibreComponentCount B X q := by
  obtain ⟨V, hV, hne, hcomp⟩ := exists_open_geometricComponentsEquiv X hX a ha hs
  exact ⟨V, hV, hne, fun p hp q hq => ENat.card_congr (hcomp p hp q hq).some⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
