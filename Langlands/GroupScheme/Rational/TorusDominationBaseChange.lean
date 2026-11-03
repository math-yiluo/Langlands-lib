import Langlands.GroupScheme.Rational.TorusGeneratedEnvelopeDomination
import Langlands.GroupScheme.Torus.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Field extension of pointed torus domination -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PointedTorusDomination

/-- A quasi-compact schematically dominant morphism remains dominant after flat
base change, using the actual pullback functor on over schemes. -/
theorem isDominant_pullback_map {S S' : Scheme.{u}} (b : S' ⟶ S)
    [Flat b] {X Y : Over S} (p : X ⟶ Y)
    [IsSchemeTheoreticallyDominant p.left] [QuasiCompact p.left] :
    IsDominant ((Over.pullback b).map p).left := by
  have hp : IsPullback ((Over.pullback b).map p).left
      (pullback.fst X.hom b) (pullback.fst Y.hom b) p.left := by
    refine .of_right (t := .flip <| .of_hasPullback Y.hom b)
      (by simpa using (.flip <| .of_hasPullback X.hom b)) (by simp)
  have : IsSchemeTheoreticallyDominant ((Over.pullback b).map p).left :=
    IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact ((Over.pullback b).map p).left :=
    MorphismProperty.of_isPullback hp.flip inferInstance
  infer_instance

/-- Pullback of a pointed scheme morphism remains pointed, with no
multiplicativity assumption on that morphism. -/
theorem pullback_map_one {S S' : Scheme.{u}} (b : S' ⟶ S)
    {P H : GroupScheme S} (p : P.X ⟶ H.X)
    (hp : (1 : Over.mk (𝟙 S) ⟶ P.X) ≫ p = 1) :
    (1 : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj P).X) ≫
      (Over.pullback b).map p =
        (1 : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj H).X) := by
  have hp' : η[P.X] ≫ p = η[H.X] := by
    change (1 : 𝟙_ (Over S) ⟶ P.X) ≫ p = (1 : 𝟙_ (Over S) ⟶ H.X) at hp
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using hp
  change (toUnit _ ≫ (Functor.LaxMonoidal.ε (Over.pullback b) ≫
      (Over.pullback b).map η[P.X])) ≫ (Over.pullback b).map p =
    toUnit _ ≫ (Functor.LaxMonoidal.ε (Over.pullback b) ≫
      (Over.pullback b).map η[H.X])
  simp only [Category.assoc, ← Functor.map_comp, hp']

end PointedTorusDomination

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : GroupScheme (Spec (CommRingCat.of k))}

/-- Dominance from a torus forces the target to be connected. -/
theorem HasPointedTorusDomination.connectedSpace (h : HasPointedTorusDomination H) :
    ConnectedSpace H.X.left := by
  obtain ⟨P, p, hP, hd, -⟩ := h
  have : ConnectedSpace P.X.left := hP.connectedSpace
  have : PreconnectedSpace H.X.left := hd.denseRange.preconnectedSpace p.left.continuous
  have : Nonempty H.X.left := ⟨p.left (Classical.choice inferInstance)⟩
  exact ⟨inferInstance⟩

/-- Over an arbitrary field extension, the actual pullback of a dominant
torus parametrization of a reduced affine group is dominant. -/
theorem PointedTorusDomination.isDominant_baseChange
    [IsReduced H.X.left] [IsAffineHom H.X.hom]
    {P : GroupScheme (Spec (CommRingCat.of k))}
    (hP : IsTorus P) (p : P.X ⟶ H.X) (hd : IsDominant p.left) :
    IsDominant ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map p).left := by
  have : IsDominant p.left := hd
  have : IsSchemeTheoreticallyDominant p.left :=
    IsSchemeTheoreticallyDominant.of_isDominant p.left
  have : IsAffine P.X.left := SplittingAssembly.isAffine_of_isTorus P hP
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : QuasiCompact p.left := inferInstance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (fieldExtension_fpqc k K).2.1
  exact PointedTorusDomination.isDominant_pullback_map _ p

/-- Pointed torus domination is preserved by arbitrary extension of the
ground field for reduced affine targets. -/
theorem HasPointedTorusDomination.baseChange_of_isReduced
    [IsReduced H.X.left] [IsAffineHom H.X.hom]
    (h : HasPointedTorusDomination H) :
    HasPointedTorusDomination ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  exact ⟨_, (Over.pullback _).map p, hP.baseChange,
    PointedTorusDomination.isDominant_baseChange hP p hd,
    PointedTorusDomination.pullback_map_one _ p hp⟩

/-- Pointed torus domination of a smooth affine group survives every field
extension, including inseparable and transcendental extensions. -/
theorem HasPointedTorusDomination.baseChange
    [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (h : HasPointedTorusDomination H) :
    HasPointedTorusDomination ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj H) := by
  have : ConnectedSpace H.X.left := h.connectedSpace
  have : GeometricallyIntegral H.X.hom :=
    smoothConnectedAffineGeometry.1 k H inferInstance inferInstance inferInstance
  have : IsReduced H.X.left :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian H.X.hom
  exact h.baseChange_of_isReduced

/-- An actual pointed dominant parametrization by a split ground-field torus. -/
def HasPointedSplitTorusDomination (H : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (P : GroupScheme (Spec (CommRingCat.of k))) (p : P.X ⟶ H.X),
    IsSplitTorus P ∧ IsDominant p.left ∧
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) ≫ p = 1

/-- Split torus domination is in particular torus domination. -/
theorem HasPointedSplitTorusDomination.hasPointedTorusDomination
    (h : HasPointedSplitTorusDomination H) : HasPointedTorusDomination H := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  exact ⟨P, p, hP.isTorus, hd, hp⟩

/-- A pointed torus parametrization of a reduced affine group becomes a
pointed split-torus parametrization over some field extension. -/
theorem HasPointedTorusDomination.exists_extension_hasPointedSplitTorusDomination
    [IsReduced H.X.left] [IsAffineHom H.X.hom]
    (h : HasPointedTorusDomination H) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      HasPointedSplitTorusDomination ((GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj H) := by
  obtain ⟨P, p, hP, hd, hp⟩ := h
  let E := hP.splittingExtension
  exact ⟨E.carrier, inferInstance, inferInstance, _, (Over.pullback _).map p,
    E.isSplitTorus, PointedTorusDomination.isDominant_baseChange hP p hd,
    PointedTorusDomination.pullback_map_one _ p hp⟩

end Langlands.GroupScheme
