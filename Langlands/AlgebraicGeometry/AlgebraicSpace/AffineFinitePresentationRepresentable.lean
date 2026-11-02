import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-!
# Presheaves represented by affine finitely presented schemes

A presheaf on the full slice of schemes over `B` is affine finitely presented
representable when it is naturally isomorphic to the lifted functor of points of
a scheme over `B` whose structure morphism is affine and locally of finite
presentation. Such presheaves are closed under binary products and under
equalizers.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {B : Scheme.{u}}

/-- A presheaf on schemes over `B` is naturally isomorphic to the lifted functor of
points of a scheme over `B` that is affine and locally of finite presentation. -/
def IsAffineFinitePresentationRepresentable (F : Presheaf B) : Prop :=
  ∃ I : Over B, Nonempty ((schemeYoneda B).obj I ≅ F) ∧
    IsAffineHom I.hom ∧ LocallyOfFinitePresentation I.hom

namespace IsAffineFinitePresentationRepresentable

/-- The property is invariant under natural isomorphisms of presheaves. -/
lemma of_iso {F G : Presheaf B} (hF : IsAffineFinitePresentationRepresentable F)
    (e : F ≅ G) : IsAffineFinitePresentationRepresentable G := by
  obtain ⟨I, ⟨eI⟩, h₁, h₂⟩ := hF
  exact ⟨I, ⟨eI ≪≫ e⟩, h₁, h₂⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The binary product in `Over B` of two schemes affine and locally of finite
presentation over `B` is again affine and locally of finite presentation. -/
lemma prod_hom (I J : Over B) [IsAffineHom I.hom] [LocallyOfFinitePresentation I.hom]
    [IsAffineHom J.hom] [LocallyOfFinitePresentation J.hom] :
    IsAffineHom (I ⨯ J).hom ∧ LocallyOfFinitePresentation (I ⨯ J).hom := by
  have e : (I ⨯ J).hom =
      (Over.prodLeftIsoPullback I J).hom ≫ pullback.fst I.hom J.hom ≫ I.hom := by
    rw [Over.prodLeftIsoPullback_hom_fst_assoc, Over.w]
  have : IsAffineHom (pullback.fst I.hom J.hom) :=
    MorphismProperty.pullback_fst _ _ ‹IsAffineHom J.hom›
  rw [e]
  exact ⟨inferInstance, inferInstance⟩

/-- The point of any limit binary fan of two affine finitely presented
representable presheaves is affine finitely presented representable. -/
lemma of_isLimit_binaryFan {F G : Presheaf B}
    (hF : IsAffineFinitePresentationRepresentable F)
    (hG : IsAffineFinitePresentationRepresentable G)
    {c : BinaryFan F G} (hc : IsLimit c) :
    IsAffineFinitePresentationRepresentable c.pt := by
  obtain ⟨I, ⟨eI⟩, hI₁, hI₂⟩ := hF
  obtain ⟨J, ⟨eJ⟩, hJ₁, hJ₂⟩ := hG
  obtain ⟨h₁, h₂⟩ := prod_hom I J
  refine ⟨I ⨯ J, ⟨?_⟩, h₁, h₂⟩
  exact PreservesLimitPair.iso (schemeYoneda B) I J ≪≫ prod.mapIso eI eJ ≪≫
    (hc.conePointUniqueUpToIso (prodIsProd F G)).symm

/-- In the slice over `B`, two morphisms from a scheme `I` to a scheme `E` that is
affine and locally of finite presentation have an equalizer whose structure
morphism is affine and locally of finite presentation whenever that of `I` is. -/
lemma exists_isLimit_fork (I E : Over B) [IsAffineHom E.hom]
    [LocallyOfFinitePresentation E.hom] (a b : I ⟶ E) :
    ∃ (Z : Over B) (j : Z ⟶ I) (w : j ≫ a = j ≫ b),
      Nonempty (IsLimit (Fork.ofι j w)) ∧
      (IsAffineHom I.hom → IsAffineHom Z.hom) ∧
      (LocallyOfFinitePresentation I.hom → LocallyOfFinitePresentation Z.hom) := by
  have : IsSeparated E.hom := IsSeparated.of_isAffineHom E.hom
  obtain ⟨Z, j, hj, hjlfp, hfac⟩ :=
    exists_isClosedImmersion_locallyOfFinitePresentation_iff_comp_eq_of_isSeparated
      E.hom I.hom a.left b.left (Over.w a) (Over.w b)
  have hjlfp' : LocallyOfFinitePresentation j := hjlfp inferInstance
  have hab : j ≫ a.left = j ≫ b.left := ((hfac j).mpr ⟨𝟙 Z, Category.id_comp j⟩)
  let Z' : Over B := Over.mk (j ≫ I.hom)
  let j' : Z' ⟶ I := Over.homMk j
  have w : j' ≫ a = j' ≫ b := by
    ext
    exact hab
  refine ⟨Z', j', w, ⟨?_⟩, fun _ ↦ ?_, fun _ ↦ ?_⟩
  · refine Fork.IsLimit.mk' _ fun s ↦ ?_
    have hs : s.ι.left ≫ a.left = s.ι.left ≫ b.left := by
      simpa using congrArg CommaMorphism.left s.condition
    let ψ := ((hfac s.ι.left).mp hs).choose
    have hψ : ψ ≫ j = s.ι.left := ((hfac s.ι.left).mp hs).choose_spec
    refine ⟨Over.homMk ψ (by simp [Z', reassoc_of% hψ]), ?_, ?_⟩
    · ext
      exact hψ
    · intro m hm
      ext
      rw [← cancel_mono j]
      simpa [j', hψ] using congrArg CommaMorphism.left hm
  · dsimp [Z']
    infer_instance
  · dsimp [Z']
    infer_instance

/-- The point of any limit fork of two maps between affine finitely presented
representable presheaves is affine finitely presented representable. -/
lemma of_isLimit_fork {F G : Presheaf B}
    (hF : IsAffineFinitePresentationRepresentable F)
    (hG : IsAffineFinitePresentationRepresentable G)
    {a b : F ⟶ G} {c : Fork a b} (hc : IsLimit c) :
    IsAffineFinitePresentationRepresentable c.pt := by
  obtain ⟨I, ⟨eI⟩, hI₁, hI₂⟩ := hF
  obtain ⟨E, ⟨eE⟩, hE₁, hE₂⟩ := hG
  let a' : I ⟶ E := (schemeYoneda B).preimage (eI.hom ≫ a ≫ eE.inv)
  let b' : I ⟶ E := (schemeYoneda B).preimage (eI.hom ≫ b ≫ eE.inv)
  obtain ⟨Z, j, w, ⟨hZ⟩, hZ₁, hZ₂⟩ := exists_isLimit_fork I E a' b'
  refine ⟨Z, ⟨?_⟩, hZ₁ hI₁, hZ₂ hI₂⟩
  have hY : IsLimit ((schemeYoneda B).mapCone (Fork.ofι j w)) :=
    isLimitOfPreserves (schemeYoneda B) hZ
  have hY' : IsLimit (Fork.ofι ((schemeYoneda B).map j)
      (by rw [← Functor.map_comp, ← Functor.map_comp, w]) :
        Fork ((schemeYoneda B).map a') ((schemeYoneda B).map b')) :=
    (isLimitMapConeForkEquiv (schemeYoneda B) w) hY
  let d : Fork a b := Fork.ofι ((schemeYoneda B).map j ≫ eI.hom) (by
    have ha : (schemeYoneda B).map a' = eI.hom ≫ a ≫ eE.inv := by simp [a']
    have hb : (schemeYoneda B).map b' = eI.hom ≫ b ≫ eE.inv := by simp [b']
    have := congrArg (fun k ↦ (schemeYoneda B).map k) w
    simp only [Functor.map_comp, ha, hb] at this
    simpa [Category.assoc] using this =≫ eE.hom)
  have hd : IsLimit d :=
    Fork.isLimitOfIsos _ hY' d eI eE (Iso.refl _)
      (by simp [a']) (by simp [b']) (by simp [d])
  exact hd.conePointUniqueUpToIso hc

end IsAffineFinitePresentationRepresentable

end Langlands.AlgebraicGeometry.AlgebraicSpace
