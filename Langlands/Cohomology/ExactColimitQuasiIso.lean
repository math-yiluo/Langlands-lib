import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Limits.Connected

/-!
# Exact colimits of complexes preserve quasi-isomorphisms

Harris 1999, §2, p.306, obtains the quasi-isomorphism (2.6) by passing to the direct limit over
`H` of quasi-isomorphisms. This module proves the homological algebra behind that step, for an
abelian category `A` whose colimits of shape `J` exist and are exact
(`HasExactColimitsOfShape J A`; for filtered `J` this is AB5): a morphism of `J`-diagrams of
complexes in `A` that is a quasi-isomorphism at every object induces a quasi-isomorphism between
colimits (`quasiIso_isColimit_map`, `quasiIso_colimMap`), and for connected `J`, if every leg of
a cocone is a quasi-isomorphism, so is the morphism from a colimit to its vertex
(`quasiIso_isColimit_desc`).

The proof regards a diagram of complexes as a complex of diagrams (`functorComplex`), where
quasi-isomorphisms are detected objectwise (Mathlib's
`HomologicalComplex.quasiIso_iff_evaluation`), and applies the exact functor
`colim : (J ⥤ A) ⥤ A`, which preserves homology and hence quasi-isomorphisms. The result is the
degreewise colimit (`colimitCocone`, `isColimitColimitCocone`).
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

universe v u v' u' w

namespace ExactColimit

variable {J : Type u'} [Category.{v'} J] {A : Type u} [Category.{v} A] [Abelian A]
  {ι : Type w} {c : ComplexShape ι}

/-- A diagram of complexes as a complex of diagrams: in degree `n` the diagram
`j ↦ (F j).X n`. -/
@[simps]
def functorComplex (F : J ⥤ HomologicalComplex A c) : HomologicalComplex (J ⥤ A) c where
  X n := F ⋙ HomologicalComplex.eval A c n
  d n n' :=
    { app j := (F.obj j).d n n'
      naturality _ _ f := (F.map f).comm n n' }
  shape n n' h := by
    ext j
    exact (F.obj j).shape n n' h
  d_comp_d' n n' n'' _ _ := by
    ext j
    exact (F.obj j).d_comp_d n n' n''

/-- A morphism of diagrams of complexes as a morphism of complexes of diagrams. -/
@[simps]
def functorComplexMap {F G : J ⥤ HomologicalComplex A c} (f : F ⟶ G) :
    functorComplex F ⟶ functorComplex G where
  f n := Functor.whiskerRight f (HomologicalComplex.eval A c n)
  comm' n n' _ := by
    ext j
    exact (f.app j).comm n n'

/-- If a morphism of diagrams of complexes is a quasi-isomorphism at every object, then so is the
corresponding morphism of complexes of diagrams. -/
lemma quasiIso_functorComplexMap {F G : J ⥤ HomologicalComplex A c} (f : F ⟶ G)
    (hf : ∀ j, QuasiIso (f.app j)) : QuasiIso (functorComplexMap f) :=
  (HomologicalComplex.quasiIso_iff_evaluation _).2 fun j => hf j

variable [HasColimitsOfShape J A]

/-- The degreewise colimit cocone of a diagram of complexes, with vertex `colim` applied in each
degree to `functorComplex F`. -/
@[simps]
def colimitCocone (F : J ⥤ HomologicalComplex A c) : Cocone F where
  pt := (colim.mapHomologicalComplex c).obj (functorComplex F)
  ι :=
    { app j :=
        { f n := colimit.ι (F ⋙ HomologicalComplex.eval A c n) j
          comm' n n' _ := ι_colimMap ((functorComplex F).d n n') j }
      naturality _ _ f := by
        ext n
        exact (colimit.w (F ⋙ HomologicalComplex.eval A c n) f).trans (Category.comp_id _).symm }

/-- The degreewise colimit cocone is a colimit cocone. -/
def isColimitColimitCocone (F : J ⥤ HomologicalComplex A c) : IsColimit (colimitCocone F) :=
  HomologicalComplex.isColimitOfEval _ _ fun n =>
    colimit.isColimit (F ⋙ HomologicalComplex.eval A c n)

/-- `colim` applied degreewise to `functorComplexMap f` is compatible with the coprojections. -/
lemma colimitCocone_ι_app_comp_map {F G : J ⥤ HomologicalComplex A c} (f : F ⟶ G) (j : J) :
    (colimitCocone F).ι.app j ≫ (colim.mapHomologicalComplex c).map (functorComplexMap f) =
      f.app j ≫ (colimitCocone G).ι.app j := by
  ext n
  exact ι_colimMap _ j

variable [HasExactColimitsOfShape J A]

/-- For colimits of shape `J` that exist and are exact, a morphism of diagrams of complexes that
is a quasi-isomorphism at every object induces a quasi-isomorphism between any colimits. -/
theorem quasiIso_isColimit_map {F G : J ⥤ HomologicalComplex A c} (f : F ⟶ G)
    (hf : ∀ j, QuasiIso (f.app j)) {s : Cocone F} (hs : IsColimit s) {t : Cocone G}
    (ht : IsColimit t) : QuasiIso (hs.map t f) := by
  have : (colim : (J ⥤ A) ⥤ A).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have := quasiIso_functorComplexMap f hf
  have h : hs.map t f = (hs.coconePointUniqueUpToIso (isColimitColimitCocone F)).hom ≫
      (colim.mapHomologicalComplex c).map (functorComplexMap f) ≫
        ((isColimitColimitCocone G).coconePointUniqueUpToIso ht).hom := hs.hom_ext fun j => by
    rw [IsColimit.ι_map, IsColimit.comp_coconePointUniqueUpToIso_hom_assoc]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    refine Eq.trans ?_ (congrArg (· ≫ ((isColimitColimitCocone G).coconePointUniqueUpToIso ht).hom)
      (colimitCocone_ι_app_comp_map f j)).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (f.app j ≫ ·)
      ((isColimitColimitCocone G).comp_coconePointUniqueUpToIso_hom ht j).symm
  rw [h]
  have h₁ : QuasiIso ((colim.mapHomologicalComplex c).map (functorComplexMap f)) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology _ _
  have h₂ : QuasiIso ((isColimitColimitCocone G).coconePointUniqueUpToIso ht).hom := inferInstance
  exact quasiIso_comp _ _ (hφ := inferInstance) (hφ' := quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂))

/-- For colimits of shape `J` that exist and are exact, `colimMap` of a morphism of diagrams of
complexes that is a quasi-isomorphism at every object is a quasi-isomorphism. -/
theorem quasiIso_colimMap [HasColimitsOfShape J (HomologicalComplex A c)]
    {F G : J ⥤ HomologicalComplex A c} (f : F ⟶ G) (hf : ∀ j, QuasiIso (f.app j)) :
    QuasiIso (colimMap f) :=
  quasiIso_isColimit_map f hf (colimit.isColimit F) (colimit.isColimit G)

/-- For a connected `J` and colimits of shape `J` that exist and are exact: if every leg of a
cocone over a diagram of complexes is a quasi-isomorphism, so is the morphism from any colimit
to its vertex. -/
theorem quasiIso_isColimit_desc [IsConnected J] {F : J ⥤ HomologicalComplex A c} {s : Cocone F}
    (hs : IsColimit s) (t : Cocone F) (ht : ∀ j, QuasiIso (t.ι.app j)) : QuasiIso (hs.desc t) := by
  have h := quasiIso_isColimit_map t.ι ht hs (isColimitConstCocone J t.pt)
  have e : hs.desc t = hs.map (constCocone J t.pt) t.ι := hs.hom_ext fun j => by
    rw [IsColimit.fac]
    exact (Category.comp_id _).symm.trans (hs.ι_map (constCocone J t.pt) t.ι j).symm
  rw [e]
  exact h

end ExactColimit

end Langlands.Cohomology
