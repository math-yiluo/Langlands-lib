import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeCentralizerModel
import Langlands.GroupScheme.Torus.RelativeCentralizerDescent
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical

/-! # Geometry of centralizers of groups of multiplicative type -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

/-- Finite presentation of the actual affine coordinate algebra. -/
theorem finitePresentation_algebra (hG : LocallyOfFinitePresentation G.X.hom) :
    Algebra.FinitePresentation R (algebra G) := by
  have : IsIso (groupSchemeIso G).hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso
      (groupSchemeIso G))).hom)
  have h : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R (algebra G)))) := by
    change LocallyOfFinitePresentation
      (Corepresented.groupScheme (functor G) (corepresentation G)).X.hom
    have := hG
    rw [← Over.w (groupSchemeIso G).hom.hom.hom]
    infer_instance
  exact RingHom.finitePresentation_algebraMap.1
    ((HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1 h)

end AffineCoordinates

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)

/-- Finite presentation of the actual fixed subgroup requires no smoothness. -/
theorem locallyOfFinitePresentation_schemeFixedGroupScheme
    (hG : LocallyOfFinitePresentation G.X.hom) :
    LocallyOfFinitePresentation (schemeFixedGroupScheme a).X.hom := by
  let := AffineCoordinates.finitePresentation_algebra G hG
  let := finitePresentation_schemeFixedQuotient a
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom
      (algebraMap R (AffineCoordinates.algebra G ⧸ schemeFixedIdeal a))))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2
    (RingHom.finitePresentation_algebraMap.2 inferInstance)

end CharacterAction

variable {S : Scheme.{u}} {G : GroupScheme S} {H : CommGroupScheme S}

/-- A target-local geometric property of centralizer models can be checked
on an fppf cover, using uniqueness of their all-test representations. -/
theorem torusCentralizer_property_of_fppfCover
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    (𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S) (i : H.toGrp ⟶ G)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (h : ∀ k, ∃ (L : GroupScheme (𝒰.X k))
      (l : L ⟶ (GroupScheme.baseChange (𝒰.f k)).obj G),
      ((torusCentralizer i).baseChange (𝒰.f k)).IsRepresentedBy l ∧ P L.X.hom) :
    P Z.X.hom := by
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒰
  intro k
  obtain ⟨L, l, hl, hL⟩ := h k
  let e := (Grp.forget _).mapIso ((hz.baseChange (𝒰.f k)).isoOfIsRepresentedBy hl)
  have he : IsIso e.hom.left := (inferInstance : IsIso ((Over.forget _).mapIso e).hom)
  have hw : e.hom.left ≫ L.X.hom =
      ((GroupScheme.baseChange (𝒰.f k)).obj Z).X.hom := Over.w e.hom
  change P ((GroupScheme.baseChange (𝒰.f k)).obj Z).X.hom
  exact hw ▸ (P.cancel_left_of_respectsIso e.hom.left L.X.hom).2 hL

open RelativeMultiplicativeType

/-- An affine-base diagonalizable model gives a closed centralizer with
every property verified on its actual fixed-ideal model. -/
theorem diagonalizableCentralizer_model_overSpec
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
    {H : CommGroupScheme (Spec R)} [IsAffine G.X.left]
    (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) :
    ∃ (Z : GroupScheme (Spec R)) (z : Z ⟶ G),
      IsClosedSubgroup z ∧ (torusCentralizer i).IsRepresentedBy z ∧
      (LocallyOfFinitePresentation G.X.hom → LocallyOfFinitePresentation Z.X.hom) ∧
      (Smooth G.X.hom → Smooth Z.X.hom) := by
  obtain ⟨M, _, _, ⟨e⟩⟩ := hH
  let e' : H.toGrp ≅ (Diagonalizable.groupScheme R M).toGrp :=
    e ≪≫ Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) M
  let j := e'.inv ≫ i
  have hrep := Diagonalizable.isRepresentedBy_relativeCentralizerHom j
  change (torusCentralizer (e'.symm.hom ≫ i)).IsRepresentedBy
    (Diagonalizable.relativeCentralizerHom j) at hrep
  rw [torusCentralizer_eq_centralizer_range,
    SubgroupFunctor.range_precomp_iso, ← torusCentralizer_eq_centralizer_range] at hrep
  exact ⟨Diagonalizable.relativeCentralizerGroupScheme j,
    Diagonalizable.relativeCentralizerHom j,
    Diagonalizable.isClosedSubgroup_relativeCentralizerHom j, hrep,
    CharacterAction.locallyOfFinitePresentation_schemeFixedGroupScheme
      (AutomorphicAction.conjugation j),
    Diagonalizable.smooth_relativeCentralizerGroupScheme j⟩

/-- A diagonalizable source has a closed centralizer over any base scheme. -/
theorem diagonalizableCentralizer_isClosedRepresentable_of_affine
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp) :
    (torusCentralizer i).IsClosedRepresentable := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply torusCentralizer_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  change ((torusCentralizer i).baseChange b).IsClosedRepresentable
  rw [← torusCentralizer_baseChange b i]
  obtain ⟨Z, z, hz, hrep, _, _⟩ :=
    diagonalizableCentralizer_model_overSpec (R := S.affineOpenCover.X k)
      (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b)
  exact ⟨Z, z, hrep, hz⟩

/-- The full centralizer of a relative multiplicative-type group has a
closed representative, without finite-presentation or smoothness assumptions. -/
theorem relativeMultiplicativeTypeCentralizer_isClosedRepresentable_of_affine
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) :
    (torusCentralizer i).IsClosedRepresentable := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply torusCentralizer_isClosedRepresentable_of_fppfCover 𝒰 i
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  rw [← torusCentralizer_baseChange b i]
  exact diagonalizableCentralizer_isClosedRepresentable_of_affine
    (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (h𝒰 k)

local instance : MorphismProperty.IsLocalAtTarget
    (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _

local instance : MorphismProperty.IsLocalAtTarget
    (@Smooth : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _

/-- Every representative of a diagonalizable centralizer is locally of finite
presentation if the affine ambient group is. -/
theorem diagonalizableCentralizer_locallyOfFinitePresentation
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hG : LocallyOfFinitePresentation G.X.hom) :
    LocallyOfFinitePresentation Z.X.hom := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply torusCentralizer_property_of_fppfCover (@LocallyOfFinitePresentation) 𝒰 i hz
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  obtain ⟨L, l, _, hl, hlfp, _⟩ :=
    diagonalizableCentralizer_model_overSpec (R := S.affineOpenCover.X k)
      (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b)
  refine ⟨L, l, ?_, hlfp (MorphismProperty.pullback_snd G.X.hom b hG)⟩
  change ((torusCentralizer i).baseChange b).IsRepresentedBy l
  rwa [← torusCentralizer_baseChange b i]

/-- Every representative of a diagonalizable centralizer in a smooth affine
group is smooth. -/
theorem diagonalizableCentralizer_smooth_of_smooth
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsDiagonalizable H.toGrp)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hG : Smooth G.X.hom) : Smooth Z.X.hom := by
  let 𝒰 : Scheme.Cover.{u} Scheme.fppfPrecoverage S :=
    S.affineOpenCover.openCover.changeProp (Q := @Flat ⊓ @LocallyOfFinitePresentation)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  apply torusCentralizer_property_of_fppfCover (@Smooth) 𝒰 i hz
  intro k
  let b := S.affineOpenCover.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  let : IsAffine (B.obj G).X.left := isAffine_of_isAffineHom (B.obj G).X.hom
  obtain ⟨L, l, _, hl, _, hsmooth⟩ :=
    diagonalizableCentralizer_model_overSpec (R := S.affineOpenCover.X k)
      (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (hH.baseChange b)
  refine ⟨L, l, ?_, hsmooth (MorphismProperty.pullback_snd G.X.hom b hG)⟩
  change ((torusCentralizer i).baseChange b).IsRepresentedBy l
  rwa [← torusCentralizer_baseChange b i]

/-- Finite presentation of the actual centralizer descends from its
diagonalizable models on a splitting fppf cover. -/
theorem relativeMultiplicativeTypeCentralizer_locallyOfFinitePresentation
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hG : LocallyOfFinitePresentation G.X.hom) :
    LocallyOfFinitePresentation Z.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply torusCentralizer_property_of_fppfCover (@LocallyOfFinitePresentation) 𝒰 i hz
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hrep := hz.baseChange b
  rw [← torusCentralizer_baseChange b i] at hrep
  exact ⟨B.obj Z, B.map z, hz.baseChange b,
    diagonalizableCentralizer_locallyOfFinitePresentation
      (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (h𝒰 k) hrep
      (MorphismProperty.pullback_snd G.X.hom b hG)⟩

/-- Every representative of the centralizer of a relative multiplicative-type
group in a smooth affine group is smooth. -/
theorem relativeMultiplicativeTypeCentralizer_smooth_of_smooth
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp)
    {Z : GroupScheme S} {z : Z ⟶ G} (hz : (torusCentralizer i).IsRepresentedBy z)
    (hG : Smooth G.X.hom) : Smooth Z.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  apply torusCentralizer_property_of_fppfCover (@Smooth) 𝒰 i hz
  intro k
  let b := 𝒰.f k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj G).X.hom :=
    MorphismProperty.pullback_snd G.X.hom b inferInstance
  have hrep := hz.baseChange b
  rw [← torusCentralizer_baseChange b i] at hrep
  exact ⟨B.obj Z, B.map z, hz.baseChange b,
    diagonalizableCentralizer_smooth_of_smooth
      (H := (CommGroupScheme.baseChange b).obj H) (B.map i) (h𝒰 k) hrep
      (MorphismProperty.pullback_snd G.X.hom b hG)⟩

/-- Choose an actual closed group scheme, its inclusion into the ambient
group, and its all-test centralizer representation. -/
def relativeMultiplicativeTypeCentralizerClosedModel
    [IsAffineHom G.X.hom] (i : H.toGrp ⟶ G) (hH : IsMultiplicativeType H.toGrp) :
    SubgroupFunctor.ClosedRepresentative (torusCentralizer i) :=
  SubgroupFunctor.ClosedRepresentative.ofIsClosedRepresentable
    (relativeMultiplicativeTypeCentralizer_isClosedRepresentable_of_affine i hH)

end Langlands.GroupScheme
