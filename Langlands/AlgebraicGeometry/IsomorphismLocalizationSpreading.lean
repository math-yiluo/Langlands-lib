import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedSurjectivityLimitDescent
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingGerm
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Spreading isomorphisms from a prime localization -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.AlgebraicGeometry.IsomorphismLocalization

open AlgebraicSpace AffineLimit SchemeLimitModel.Geometry
open UnramifiedFunctor.ChartGluing

/-- Isomorphisms between finitely presented relative schemes are detected at
one incoming stage of an affine cofiltered limit. -/
theorem isomorphisms_structural_descent :
    SchemeStructuralPropertyDescent.{u} (MorphismProperty.isomorphisms Scheme) := by
  intro I _ _ D S X Y _ _ t a b f w _ _ _ _ _ _ c hc p hp
  change IsIso (baseChangeMap a b f w p) ↔
    ∃ i, IsIso (baseChangeMap a b f w (t.app i))
  constructor
  · intro h
    obtain ⟨hO, hS⟩ := (isIso_iff_isOpenImmersion_and_surjective _).mp h
    obtain ⟨i, hi⟩ := (openImmersion_schemeStructuralPropertyDescent
      D t a b f w c hc p hp).mp hO
    obtain ⟨j, hj⟩ := (surjective_schemeStructuralPropertyDescent
      D t a b f w c hc p hp).mp hS
    obtain ⟨k, r, s, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    have hOk : IsOpenImmersion (baseChangeMap a b f w (t.app k)) :=
      MorphismProperty.of_isPullback (morphismDiagram_cartesian a b f w D t r).flip hi
    have hSk : Surjective (baseChangeMap a b f w (t.app k)) :=
      MorphismProperty.of_isPullback (morphismDiagram_cartesian a b f w D t s).flip hj
    exact ⟨k, (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨hOk, hSk⟩⟩
  · rintro ⟨i, hi⟩
    exact MorphismProperty.of_isPullback
      (P := MorphismProperty.isomorphisms Scheme)
      (coneMorphism_cartesian a b f w D t c p hp i).flip hi

/-- An isomorphism after prime localization is already an isomorphism after
inverting one element outside that prime. Neither scheme need be affine. -/
theorem exists_away_isIso_of_atPrime
    {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime]
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization.AtPrime L P]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y)
    (hf : IsIso (((Over.pullback (Spec.algebraMap R L)).map f).left)) :
    ∃ g ∉ P, IsIso (((Over.pullback
      (Spec.algebraMap R (Localization.Away g))).map f).left) := by
  let F := locDiagram P ⋙ Under.forget (CommRingCat.of R)
  let rc := (Under.forget (CommRingCat.of R)).mapCocone (locCocone P L)
  have hrc : IsColimit rc :=
    isColimitOfPreserves (Under.forget (CommRingCat.of R)) (isColimitLocCocone P L)
  let D := F.op ⋙ Scheme.Spec
  let (i : (DivIdx P)ᵒᵖ) : IsAffine (D.obj i) := by
    change IsAffine (Spec (CommRingCat.of (Localization.Away i.unop.elt)))
    infer_instance
  let c : Cone D := Scheme.Spec.mapCone rc.op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec hrc.op
  let t : D ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) :=
    { app i := Spec.map ((locDiagram P).obj i.unop).hom
      naturality := by
        intro i j r
        change Spec.map (((locDiagram P).map r.unop).right) ≫
          Spec.map ((locDiagram P).obj j.unop).hom =
          Spec.map ((locDiagram P).obj i.unop).hom ≫ 𝟙 _
        rw [Category.comp_id, ← Spec.map_comp, Under.w] }
  have hp (i : (DivIdx P)ᵒᵖ) :
      c.π.app i ≫ t.app i = Spec.algebraMap R L := by
    change Spec.map (((locCocone P L).ι.app i.unop).right) ≫
      Spec.map ((locDiagram P).obj i.unop).hom = _
    rw [← Spec.map_comp, Under.w]
    rfl
  let Q : MorphismProperty Scheme.{u} := MorphismProperty.isomorphisms Scheme
  have htop : Q (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.algebraMap R L)) :=
    (Q.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f (Spec.algebraMap R L))).mp hf
  obtain ⟨i, hi⟩ := (isomorphisms_structural_descent
    D t X.hom Y.hom f.left (Over.w f) c hc (Spec.algebraMap R L) hp).mp htop
  exact ⟨i.unop.elt, i.unop.mem,
    (Q.arrow_mk_iso_iff
      (overPullbackSchemeArrowIso f
        (Spec.algebraMap R (Localization.Away i.unop.elt)))).mpr hi⟩

/-- The prime-localization spreading assertion for finitely presented schemes. -/
def Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P : Ideal R) [P.IsPrime]
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization.AtPrime L P]
    (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFinitePresentation X.hom] [QuasiCompact X.hom] [QuasiSeparated X.hom]
    [LocallyOfFinitePresentation Y.hom] [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y),
    IsIso (((Over.pullback (Spec.algebraMap R L)).map f).left) →
    ∃ g ∉ P, IsIso (((Over.pullback
      (Spec.algebraMap R (Localization.Away g))).map f).left)

/-- Prime-localized isomorphisms spread over a principal base neighborhood. -/
theorem spreading : Statement.{u} := @exists_away_isIso_of_atPrime.{u}

end Langlands.AlgebraicGeometry.IsomorphismLocalization
