import Langlands.GroupScheme.SchemeActionQuotientSheaf
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof

/-! # Effective descent of local scheme models for an action quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

open Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {A : GroupScheme S} {X : Over S}
  (b : SchemeAction A X)

/-- An actual scheme representation of the canonical quotient sheaf, together
with its compatible class morphism. -/
structure QuotientRepresentation where
  parameter : Over S
  classMap : X ⟶ parameter
  iso : (schemeYoneda S).obj parameter ≅ b.quotientSheaf.obj
  comm : (schemeYoneda S).map classMap ≫ iso.hom = b.quotientMap.hom

/-- A local quotient comparison respects the represented parameter. -/
theorem quotientWithParameterIso_snd
    (U M : Over S) (q : X ⨯ U ⟶ M) (π : M ⟶ U)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left]
    (hcomm : q ≫ π = prod.snd)
    (e : (schemeYoneda S).obj M ≅ (b.quotientWithParameter U).obj)
    (he : (schemeYoneda S).map q ≫ e.hom = b.quotientMapWithParameter U) :
    e.hom ≫ extProd.snd = (schemeYoneda S).map π := by
  dsimp only [quotientWithParameter] at e he ⊢
  let q' := (schemeSheaf S).map q
  have : Sheaf.IsLocallySurjective q' := isLocallySurjective_schemeYoneda_map q
  have : Epi q' := inferInstance
  let r : (schemeSheaf S).obj M ⟶ (schemeSheaf S).obj U :=
    ObjectProperty.homMk (e.hom ≫ extProd.snd)
  let s := (schemeSheaf S).map π
  have h : q' ≫ r = q' ≫ s := by
    apply ObjectProperty.hom_ext
    change (schemeYoneda S).map q ≫ e.hom ≫ extProd.snd =
      (schemeYoneda S).map q ≫ (schemeYoneda S).map π
    rw [← Category.assoc, he, ← Functor.map_comp, hcomm]
    rfl
  exact congrArg (fun f => f.hom) ((cancel_epi q').mp h)

/-- A product representation compatible with its parameter is a pullback
over the relative base. -/
theorem isPullback_quotientWithParameterIso
    (U M : Over S) (π : M ⟶ U)
    (e : (schemeYoneda S).obj M ≅ (b.quotientWithParameter U).obj)
    (he : e.hom ≫ extProd.snd = (schemeYoneda S).map π)
    (g : U ⟶ Over.mk (𝟙 S)) :
    IsPullback (e.hom ≫ extProd.fst) ((schemeYoneda S).map π)
      ((Over.mkIdTerminal.isTerminalObj (schemeYoneda S)).from b.quotientSheaf.obj)
      ((schemeYoneda S).map g) := by
  dsimp only [quotientWithParameter] at e he ⊢
  let t := Over.mkIdTerminal.isTerminalObj (schemeYoneda S)
  have hpb := IsPullback.of_is_product
    (FunctorToTypes.binaryProductLimit b.quotientSheaf.obj ((schemeYoneda S).obj U)) t
  change IsPullback (extProd.fst : extProd b.quotientSheaf.obj U ⟶ _)
    extProd.snd (t.from b.quotientSheaf.obj)
    (t.from ((schemeYoneda S).obj U)) at hpb
  have hg : t.from ((schemeYoneda S).obj U) = (schemeYoneda S).map g :=
    t.hom_ext _ _
  rw [hg] at hpb
  exact hpb.of_iso' e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Category.comp_id _).symm (he.trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- Separated locally quasi-finite local presentations of a free-action quotient
descend to an actual representing scheme. -/
def quotientRepresentationOfLocalPresentations
    (hfree : ∀ (T : Over S) (p : T ⟶ X),
      Function.Injective (fun d : T ⟶ A.X => b.act d p))
    (J : Sieve (Over.mk (𝟙 S))) (hJ : J ∈ fppfTopology S (Over.mk (𝟙 S)))
    (hlocal : ∀ ⦃U : Over S⦄ (g : U ⟶ Over.mk (𝟙 S)), J g →
      ∃ (M : Over S) (π : M ⟶ U) (q : X ⨯ U ⟶ M),
        Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left ∧
        q ≫ π = prod.snd ∧ IsSeparated π.left ∧
        LocallyQuasiFinite π.left ∧ LocallyOfFiniteType π.left ∧
        ∀ (T : Over S) (p p' : T ⟶ X ⨯ U),
          p ≫ q = p' ≫ q ↔ p ≫ prod.snd = p' ≫ prod.snd ∧
            ∃ d : T ⟶ A.X, b.act d (p ≫ prod.fst) = p' ≫ prod.fst) :
    b.QuotientRepresentation := by
  apply Classical.choice
  let t := Over.mkIdTerminal.isTerminalObj (schemeYoneda S)
  obtain ⟨Q, _, e, _⟩ :=
    Langlands.AlgebraicGeometry.LocallyQuasiFiniteDescent.fppfSeparatedLocallyQuasiFiniteDescent
      S b.quotientSheaf (Over.mk (𝟙 S)) (t.from _) J hJ (by
        intro U g hg
        obtain ⟨M, π, q, hflat, hlfp, hsurj, hcomm, hsep, hlqf, hlft, hker⟩ :=
          hlocal g hg
        let := hflat
        let := hlfp
        let := hsurj
        obtain ⟨e, he⟩ := b.exists_iso_quotientWithParameter hfree U M q hker
        exact ⟨M, π, e.hom ≫ extProd.fst,
          b.isPullback_quotientWithParameterIso U M π e
            (b.quotientWithParameterIso_snd U M q π hcomm e he) g,
          hsep, hlqf, hlft⟩)
  refine ⟨⟨Q, (schemeYoneda S).preimage (b.quotientMap.hom ≫ e.inv), e, ?_⟩⟩
  simp only [Functor.map_preimage]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => b.quotientMap.hom ≫ k) e.inv_hom_id).trans
      (Category.comp_id _))

end Langlands.GroupScheme.SchemeAction
