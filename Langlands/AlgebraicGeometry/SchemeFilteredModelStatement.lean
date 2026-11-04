import Langlands.AlgebraicGeometry.SchemeFilteredRingTail
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Model morphisms over the original filtered ring stages -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

/-- The actual Hom quotient over the original initial-stage tail has the
separate injectivity and surjectivity properties, and is the Hom colimit. -/
def InitialRingModelHomColimitComparison : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))),
    let G := initialRingAlgebraDiagram F j₀
    let d := initialRingAlgebraCocone F j₀ c
    (QuasiCompact X.hom → LocallyOfFiniteType Y.hom →
      Function.Injective (spectrumHomColimitMap (F.obj j₀) G d X Y)) ∧
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      Function.Surjective (spectrumHomColimitMap (F.obj j₀) G d X Y)) ∧
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      Function.Bijective (spectrumHomColimitMap (F.obj j₀) G d X Y) ∧
        Nonempty (IsColimit (spectrumHomCocone (F.obj j₀) G d X Y)))

/-- Factorization, eventual equality, and descent of a prescribed isomorphism
use the original spectrum maps and actual arrows from the chosen stage. -/
def InitialRingModelMorphismDescent : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))),
    let G := initialRingAlgebraDiagram F j₀
    let D := spectrumDiagram (F.obj j₀) G
    let t := spectrumStructure (F.obj j₀) G
    let C := spectrumCone (F.obj j₀) G (initialRingAlgebraCocone F j₀ c)
    let p := Spec.map (c.ι.app j₀)
    let hp : ∀ j, C.π.app j ≫ t.app j = p :=
      spectrumCone_compat (F.obj j₀) G (initialRingAlgebraCocone F j₀ c)
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation Y.hom →
      ∀ f : LimitHom X.hom Y.hom p,
        ∃ (j : Under j₀) (fj : SpectrumLevelHom (F.obj j₀) G X Y j),
          toLimit D t X.hom Y.hom C p hp (op j) fj = f) ∧
    (QuasiCompact X.hom → LocallyOfFiniteType Y.hom →
      ∀ (i j : Under j₀)
        (fi : SpectrumLevelHom (F.obj j₀) G X Y i)
        (fj : SpectrumLevelHom (F.obj j₀) G X Y j),
        toLimit D t X.hom Y.hom C p hp (op i) fi =
          toLimit D t X.hom Y.hom C p hp (op j) fj →
        ∃ (k : Under j₀) (r : i ⟶ k) (s : j ⟶ k),
          restrict D t X.hom Y.hom r.op fi = restrict D t X.hom Y.hom s.op fj) ∧
    (QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFinitePresentation X.hom →
      QuasiCompact Y.hom → QuasiSeparated Y.hom → LocallyOfFinitePresentation Y.hom →
      ∀ (e : pullback p X.hom ≅ pullback p Y.hom)
        (he : e.hom ≫ pullback.fst p Y.hom = pullback.fst p X.hom),
        ∃ (j : Under j₀)
          (ej : pullback (Spec.map (F.map j.hom)) X.hom ≅
            pullback (Spec.map (F.map j.hom)) Y.hom)
          (hej : ej.hom ≫ pullback.fst (Spec.map (F.map j.hom)) Y.hom =
            pullback.fst (Spec.map (F.map j.hom)) X.hom),
          toLimit D t X.hom Y.hom C p hp (op j) ⟨ej.hom, hej⟩ = ⟨e.hom, he⟩)

/-- The Hom-colimit comparison and prescribed model descent over the actual
initial ring and its original later stages. -/
def InitialRingModelDescent : Prop :=
  InitialRingModelHomColimitComparison.{u} ∧ InitialRingModelMorphismDescent.{u}

end Langlands.AlgebraicGeometry.SchemeLimitModel
