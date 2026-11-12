import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCoverStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperCoverFPComposite
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperCoverFPApprox
import Langlands.AlgebraicGeometry.AlgebraicSpace.BaseCompositionDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasIsoTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentableTransport
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.ChowCoverStatement

/-! # Proper finitely presented scheme covers from weak Chow covers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A space is separated when its structural morphism is separated. -/
theorem isSeparated_of_isSeparatedMorphism_structural {X : AlgebraicSpace S}
    (h : IsSeparatedMorphism (structuralMorphism X)) : IsSeparated X := by
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S)
  change P (diag X.presheaf)
  rw [BaseComposition.diag_iff_diagonal_terminal P]
  exact (MorphismProperty.arrow_mk_iso_iff P.diagonal
    (Arrow.isoMk' (hom (structuralMorphism X)) (terminal.from X.presheaf) (Iso.refl _)
      ((basePresheafIsTerminal S).uniqueUpToIso terminalIsTerminal)
      (terminalIsTerminal.hom_ext _ _))).mp h

/-- A scheme mapping to a separated space by a morphism represented by separated morphisms
is separated over the base. -/
theorem isSeparated_hom_of_relative {X : AlgebraicSpace S} (hX : IsSeparated X) {U : Over S}
    {a : (schemeYoneda S).obj U ⟶ X.presheaf}
    (ha : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsSeparated.{u})
      (Over.forget S)).relative (schemeYoneda S) a) :
    _root_.AlgebraicGeometry.IsSeparated U.hom := by
  let W : MorphismProperty (Presheaf S) :=
    (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).relative (schemeYoneda S)
  have : W.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  have : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})).toIsStableUnderComposition
  have h₁ : W.diagonal a := by
    let hr := ha.rep
    let δ : U ⟶ hr.pullback a := hr.lift' (𝟙 U) (𝟙 U) rfl
    have hδf : δ ≫ hr.fst' a = 𝟙 U := hr.lift'_fst _ _ _
    have hδs : δ ≫ hr.snd a = 𝟙 U := hr.lift'_snd _ _ _
    have : _root_.AlgebraicGeometry.IsSeparated (hr.snd a).left := ha.property_snd a
    have : _root_.AlgebraicGeometry.IsClosedImmersion (δ.left ≫ (hr.snd a).left) := by
      rw [← Over.comp_left, hδs]
      exact inferInstanceAs (_root_.AlgebraicGeometry.IsClosedImmersion (𝟙 U.left))
    have : _root_.AlgebraicGeometry.IsClosedImmersion δ.left :=
      IsClosedImmersion.of_comp δ.left (hr.snd a).left
    have hW : W ((schemeYoneda S).map δ) :=
      MorphismProperty.relative_map
        (P := MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
          (Over.forget S)) this
    have hsq := hr.isPullback' a
    have heq : (schemeYoneda S).map δ ≫ hsq.isoPullback.hom = pullback.diagonal a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hsq.isoPullback_hom_fst, ← Functor.map_comp, hδf,
          CategoryTheory.Functor.map_id, pullback.diagonal_fst]
      · rw [Category.assoc, hsq.isoPullback_hom_snd, ← Functor.map_comp, hδs,
          CategoryTheory.Functor.map_id, pullback.diagonal_snd]
    change W (pullback.diagonal a)
    rw [← heq]
    exact (MorphismProperty.cancel_right_of_respectsIso W _ _).mpr hW
  have h₂ : W.diagonal (terminal.from X.presheaf) :=
    (BaseComposition.diag_iff_diagonal_terminal W _).mp hX
  have h₃ := W.diagonal.comp_mem _ _ h₁ h₂
  rw [terminalIsTerminal.hom_ext (a ≫ terminal.from X.presheaf) (terminal.from _)] at h₃
  exact isSeparated_of_representableBy
    ((Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ U).symm (Iso.refl _))
    ((BaseComposition.diag_iff_diagonal_terminal W _).mpr h₃)

/-- A relative property is kept by composition with a presheaf isomorphism. -/
theorem relative_comp_iso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {F G H : Presheaf S} {f : F ⟶ G}
    (hf : (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) f)
    (e : G ≅ H) :
    (MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S) (f ≫ e.hom) := by
  let := MorphismProperty.RespectsIso.inverseImage P (Over.forget S)
  exact (MorphismProperty.cancel_right_of_respectsIso
    ((MorphismProperty.inverseImage P (Over.forget S)).relative (schemeYoneda S)) _ _).mpr hf

/-- Weak Chow covers give the proper finitely presented scheme covers of proper algebraic
spaces over affine bases. -/
theorem properSchemeCover_of_chowCover (h : ProperSchemeCover.ChowCoverStatement.{u}) :
    ProperSchemeCoverStatement.{u} := by
  intro S _ X _ hXa hXp
  obtain ⟨R, _, g, X₀, hsep₀, hat₀, ⟨e⟩⟩ :=
    exists_noetherian_model S X (isSeparated_of_isSeparatedMorphism_structural hXp.1) hXa
  obtain ⟨U₀, a₀, hsurj, hprop, hlft, -⟩ := h (Spec R) X₀ hsep₀ hat₀
  have huc := MorphismProperty.relative_monotone (F := schemeYoneda (Spec R))
    (P := MorphismProperty.inverseImage @_root_.AlgebraicGeometry.IsProper (Over.forget _))
    (P' := MorphismProperty.inverseImage (@UniversallyClosed.{u}) (Over.forget _))
    (fun _ _ _ hf => (show _root_.AlgebraicGeometry.IsProper _ from hf).toUniversallyClosed)
    _ hprop
  have hsepU : _root_.AlgebraicGeometry.IsSeparated U₀.hom :=
    isSeparated_hom_of_relative hsep₀ (MorphismProperty.relative_monotone
      (fun _ _ _ hf => (show _root_.AlgebraicGeometry.IsProper _ from hf).toIsSeparated) _ hprop)
  have : MorphismProperty.RespectsIso (@Surjective.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.RespectsIso (@UniversallyClosed.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let eX := (forgetToPresheaf S).mapIso e
  let a : (schemeYoneda S).obj ((Over.pullback g).obj U₀) ⟶ X.presheaf :=
    restrictAtlas g a₀ ≫ eX.hom
  have ha : (MorphismProperty.inverseImage (@UniversallyClosed.{u}) (Over.forget S)).relative
      (schemeYoneda S) a :=
    relative_comp_iso _ (relative_restrictAtlas _ huc) eX
  have : UniversallyClosed ((Over.pullback g).obj U₀).hom :=
    universallyClosed_of_relative_of_structural X _ a ha hXp.2.2.2
  have : _root_.AlgebraicGeometry.IsSeparated ((Over.pullback g).obj U₀).hom :=
    MorphismProperty.pullback_snd (P := @_root_.AlgebraicGeometry.IsSeparated) _ _ hsepU
  have : LocallyOfFiniteType U₀.hom := hlft
  have : LocallyOfFinitePresentation ((Over.pullback g).obj U₀).hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFinitePresentation) _ _
      (inferInstance : LocallyOfFinitePresentation U₀.hom)
  have : LocallyOfFiniteType ((Over.pullback g).obj U₀).hom :=
    MorphismProperty.pullback_snd (P := @LocallyOfFiniteType) _ _ hlft
  exact ⟨(Over.pullback g).obj U₀, a,
    relative_comp_iso _ (relative_restrictAtlas _ hsurj) eX, ⟨⟩, inferInstance⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
