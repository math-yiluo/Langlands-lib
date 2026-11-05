import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionTensorBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionLocalTopology

/-! # Coefficient isomorphisms for actual affine-chart Weil restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable (A B D : Type u) [CommRing A] [CommRing B] [CommRing D]
  [Algebra A B] [Algebra A D] (e : B ≃ₐ[A] D)

/-- The actual coefficient-spectrum isomorphism, with its contravariant
orientation. -/
def weilCoefficientSpecIso :
    Spec (CommRingCat.of D) ≅ Spec (CommRingCat.of B) :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op

/-- The coefficient-spectrum isomorphism respects the given base algebra
structures. -/
@[reassoc (attr := simp)]
theorem weilCoefficientSpecIso_hom_base :
    (weilCoefficientSpecIso A B D e).hom ≫ Spec.algebraMap A B =
      Spec.algebraMap A D := by
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap A B)) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun a => e.commutes a)

/-- The actual pullback of the target along the coefficient isomorphism. -/
abbrev weilCoefficientTarget (Y : Over (Spec (CommRingCat.of B))) :
    Over (Spec (CommRingCat.of D)) :=
  (Over.pullback (weilCoefficientSpecIso A B D e).hom).obj Y

/-- Changing coefficients on an actual test scheme and then forgetting
through the spectrum isomorphism agrees with the original test pullback. -/
def weilCoefficientTestIso (T : Over (Spec (CommRingCat.of A))) :
    (Over.map (weilCoefficientSpecIso A B D e).hom).obj (ringBaseChange A D T) ≅
      ringBaseChange A B T :=
  Over.isoMk
    (asIso (pullback.map T.hom (Spec.algebraMap A D)
      T.hom (Spec.algebraMap A B)
      (𝟙 _) (weilCoefficientSpecIso A B D e).hom (𝟙 _)
      (by simp) (by simp)))
    (by simp [ringBaseChange])

/-- The actual test identification is natural on all schemes. -/
theorem weilCoefficientTestIso_natural
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S) :
    (Over.map (weilCoefficientSpecIso A B D e).hom).map
        ((Over.pullback (Spec.algebraMap A D)).map f) ≫
        (weilCoefficientTestIso A B D e S).hom =
      (weilCoefficientTestIso A B D e T).hom ≫
        (Over.pullback (Spec.algebraMap A B)).map f := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp [weilCoefficientTestIso, Over.pullback_map_left, Category.assoc]
  · simp [weilCoefficientTestIso, Over.pullback_map_left, Category.assoc]

variable [Module.Finite A B] [Module.Projective A B]

omit [Module.Projective A B] in
include e in
/-- Finite generation is transported through the actual algebra isomorphism. -/
theorem weilCoefficientFinite : Module.Finite A D :=
  Module.Finite.equiv e.toLinearEquiv

omit [Module.Finite A B] in
include e in
/-- Projectivity is transported through the actual algebra isomorphism. -/
theorem weilCoefficientProjective : Module.Projective A D :=
  Module.Projective.of_equiv' e.toLinearEquiv

variable (Y : Over (Spec (CommRingCat.of B))) [LocallyOfFiniteType Y.hom]

local instance coefficientTargetLocallyOfFiniteType :
    LocallyOfFiniteType (weilCoefficientTarget A B D e Y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd Y.hom (weilCoefficientSpecIso A B D e).hom))

/-- The independently glued Weil scheme after coefficient transport.
Its finite projectivity is derived from the original extension. -/
abbrev affineChartWeilRestrictionCoefficient :
    Over (Spec (CommRingCat.of A)) := by
  letI := weilCoefficientFinite A B D e
  letI := weilCoefficientProjective A B D e
  exact affineChartWeilRestriction A D (weilCoefficientTarget A B D e Y)

omit [Module.Finite A B] [Module.Projective A B] [LocallyOfFiniteType Y.hom] in
/-- Coefficient transport preserves finite affine neighborhoods because its
actual projection to the target is affine. -/
theorem hasFiniteAffineNeighborhoods_weilCoefficientTarget
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    HasFiniteAffineNeighborhoods (weilCoefficientTarget A B D e Y).left := by
  let : IsAffineHom (pullback.fst Y.hom (weilCoefficientSpecIso A B D e).hom) :=
    MorphismProperty.pullback_fst Y.hom (weilCoefficientSpecIso A B D e).hom
      inferInstance
  exact hasFiniteAffineNeighborhoods_of_affine
    (pullback.fst Y.hom (weilCoefficientSpecIso A B D e).hom) hY

/-- Transport the original actual counit comparison through the test
isomorphism and lift it to the actual coefficient-pulled-back target. -/
def affineChartWeilRestrictionCoefficientComparison
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    ringBaseChange A D T ⟶ weilCoefficientTarget A B D e Y :=
  (Over.mapPullbackAdj (weilCoefficientSpecIso A B D e).hom).homEquiv _ Y
    ((weilCoefficientTestIso A B D e T).hom ≫
      affineChartWeilRestrictionComparison A B Y T p)

/-- The projection to the original target recovers its original counit
comparison after the actual test identification. -/
@[simp]
theorem affineChartWeilRestrictionCoefficientComparison_fst
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    (affineChartWeilRestrictionCoefficientComparison A B D e Y T p).left ≫
        pullback.fst Y.hom (weilCoefficientSpecIso A B D e).hom =
      (weilCoefficientTestIso A B D e T).hom.left ≫
        (affineChartWeilRestrictionComparison A B Y T p).left := by
  simp [affineChartWeilRestrictionCoefficientComparison, Over.mapPullbackAdj]

/-- Coefficient transport is natural on all actual test schemes. -/
theorem affineChartWeilRestrictionCoefficientComparison_natural
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionCoefficientComparison A B D e Y T (f ≫ p) =
      (Over.pullback (Spec.algebraMap A D)).map f ≫
        affineChartWeilRestrictionCoefficientComparison A B D e Y S p := by
  unfold affineChartWeilRestrictionCoefficientComparison
  rw [affineChartWeilRestrictionComparison_natural, ← Category.assoc,
    ← weilCoefficientTestIso_natural A B D e f, Category.assoc]
  exact (Over.mapPullbackAdj
    (weilCoefficientSpecIso A B D e).hom).homEquiv_naturality_left _ _

variable [IsSeparated Y.hom]

local instance coefficientTargetIsSeparated :
    IsSeparated (weilCoefficientTarget A B D e Y).hom :=
  inferInstanceAs (IsSeparated
    (pullback.snd Y.hom (weilCoefficientSpecIso A B D e).hom))

/-- The original Weil scheme represents the actual transported functor on
every test scheme, using the canonical transported counit. -/
def affineChartWeilRestrictionCoefficientTestEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A B Y) ≃
      (ringBaseChange A D T ⟶ weilCoefficientTarget A B D e Y) :=
  (affineChartWeilRestrictionTestEquiv A B Y hY T).trans
    ((Iso.homCongr (weilCoefficientTestIso A B D e T).symm (Iso.refl Y)).trans
      ((Over.mapPullbackAdj (weilCoefficientSpecIso A B D e).hom).homEquiv _ Y))

/-- The equivalence has exactly the previously defined counit map. -/
@[simp]
theorem affineChartWeilRestrictionCoefficientTestEquiv_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionCoefficientTestEquiv A B D e Y hY T p =
      affineChartWeilRestrictionCoefficientComparison A B D e Y T p := by
  change (Over.mapPullbackAdj _).homEquiv _ Y (_ ≫ _ ≫ 𝟙 Y) = _
  rw [Category.comp_id]
  rfl

/-- The natural equivalence into the two independently glued Weil schemes.
Finite projectivity and target geometry for the second scheme are derived. -/
def affineChartWeilRestrictionCoefficientRepresentingEquiv
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A))) :
    (T ⟶ affineChartWeilRestriction A B Y) ≃
      (T ⟶ affineChartWeilRestrictionCoefficient A B D e Y) := by
  letI := weilCoefficientFinite A B D e
  letI := weilCoefficientProjective A B D e
  exact (affineChartWeilRestrictionCoefficientTestEquiv A B D e Y hY T).trans
    (affineChartWeilRestrictionTestEquiv A D (weilCoefficientTarget A B D e Y)
      (hasFiniteAffineNeighborhoods_weilCoefficientTarget A B D e Y hY) T).symm

/-- Naturality of the comparison between the separately constructed
representing schemes. -/
theorem affineChartWeilRestrictionCoefficientRepresentingEquiv_natural
    (hY : HasFiniteAffineNeighborhoods Y.left)
    {T S : Over (Spec (CommRingCat.of A))} (f : T ⟶ S)
    (p : S ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionCoefficientRepresentingEquiv A B D e Y hY T (f ≫ p) =
      f ≫ affineChartWeilRestrictionCoefficientRepresentingEquiv A B D e Y hY S p := by
  let := weilCoefficientFinite A B D e
  let := weilCoefficientProjective A B D e
  unfold affineChartWeilRestrictionCoefficientRepresentingEquiv
  simp only [Equiv.trans_apply, affineChartWeilRestrictionCoefficientTestEquiv_apply,
    affineChartWeilRestrictionCoefficientComparison_natural]
  exact affineChartWeilRestrictionInverse_natural A D
    (weilCoefficientTarget A B D e Y) _ f _

/-- The canonical morphism between the actual Weil schemes. -/
def affineChartWeilRestrictionCoefficientHom
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    affineChartWeilRestriction A B Y ⟶
      affineChartWeilRestrictionCoefficient A B D e Y :=
  affineChartWeilRestrictionCoefficientRepresentingEquiv A B D e Y hY _ (𝟙 _)

/-- The representing equivalence is composition with the fixed canonical
morphism on every test scheme. -/
theorem affineChartWeilRestrictionCoefficientRepresentingEquiv_eq_comp
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    affineChartWeilRestrictionCoefficientRepresentingEquiv A B D e Y hY T p =
      p ≫ affineChartWeilRestrictionCoefficientHom A B D e Y hY := by
  simpa only [Category.comp_id, affineChartWeilRestrictionCoefficientHom] using
    affineChartWeilRestrictionCoefficientRepresentingEquiv_natural
      A B D e Y hY p (𝟙 _)

/-- The comparison is invertible by its bijections on all actual tests. -/
instance affineChartWeilRestrictionCoefficientHom_isIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    IsIso (affineChartWeilRestrictionCoefficientHom A B D e Y hY) := by
  apply isIso_of_yoneda_map_bijective
  intro T
  simp_rw [← affineChartWeilRestrictionCoefficientRepresentingEquiv_eq_comp]
  exact (affineChartWeilRestrictionCoefficientRepresentingEquiv
    A B D e Y hY T).bijective

/-- An actual coefficient algebra isomorphism induces the canonical
isomorphism between the independently glued Weil schemes. -/
def affineChartWeilRestrictionCoefficientIso
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    affineChartWeilRestriction A B Y ≅
      affineChartWeilRestrictionCoefficient A B D e Y :=
  asIso (affineChartWeilRestrictionCoefficientHom A B D e Y hY)

/-- The canonical scheme isomorphism preserves the second scheme's original
counit comparison, with the explicitly transported original comparison. -/
@[simp]
theorem affineChartWeilRestrictionCoefficientIso_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (T : Over (Spec (CommRingCat.of A)))
    (p : T ⟶ affineChartWeilRestriction A B Y) :
    letI := weilCoefficientFinite A B D e
    letI := weilCoefficientProjective A B D e
    affineChartWeilRestrictionComparison A D (weilCoefficientTarget A B D e Y) T
        (p ≫ (affineChartWeilRestrictionCoefficientIso A B D e Y hY).hom) =
      affineChartWeilRestrictionCoefficientComparison A B D e Y T p := by
  let := weilCoefficientFinite A B D e
  let := weilCoefficientProjective A B D e
  change affineChartWeilRestrictionTestEquiv A D (weilCoefficientTarget A B D e Y)
    (hasFiniteAffineNeighborhoods_weilCoefficientTarget A B D e Y hY) T
      (p ≫ affineChartWeilRestrictionCoefficientHom A B D e Y hY) = _
  rw [← affineChartWeilRestrictionCoefficientRepresentingEquiv_eq_comp]
  exact (affineChartWeilRestrictionTestEquiv A D (weilCoefficientTarget A B D e Y)
    (hasFiniteAffineNeighborhoods_weilCoefficientTarget A B D e Y hY) T).apply_symm_apply
      (affineChartWeilRestrictionCoefficientTestEquiv A B D e Y hY T p)

variable (S : Type u) [CommRing S] [Algebra A S]
  [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S] [IsOpenUnits S]

/-- Coefficient transport preserves the independently defined local-ring
point topologies. Neither coefficient algebra requires a topology. -/
def affineChartWeilRestrictionCoefficientPointHomeomorph
    (hY : HasFiniteAffineNeighborhoods Y.left) :
    letI : TopologicalSpace (RingPoint A (affineChartWeilRestriction A B Y) S) :=
      schemePointTopology A (affineChartWeilRestriction A B Y) S
    letI : TopologicalSpace
        (RingPoint A (affineChartWeilRestrictionCoefficient A B D e Y) S) :=
      schemePointTopology A (affineChartWeilRestrictionCoefficient A B D e Y) S
    RingPoint A (affineChartWeilRestriction A B Y) S ≃ₜ
      RingPoint A (affineChartWeilRestrictionCoefficient A B D e Y) S :=
  schemePointIsoHomeomorph A S (affineChartWeilRestrictionCoefficientIso A B D e Y hY)

/-- The point homeomorphism is postcomposition with the same canonical
scheme isomorphism. -/
@[simp]
theorem affineChartWeilRestrictionCoefficientPointHomeomorph_apply
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) S) :
    affineChartWeilRestrictionCoefficientPointHomeomorph A B D e Y S hY p =
      p ≫ (affineChartWeilRestrictionCoefficientIso A B D e Y hY).hom := rfl

/-- The point homeomorphism has the same exact original-counit law. -/
@[simp]
theorem affineChartWeilRestrictionCoefficientPointHomeomorph_comparison
    (hY : HasFiniteAffineNeighborhoods Y.left)
    (p : RingPoint A (affineChartWeilRestriction A B Y) S) :
    letI := weilCoefficientFinite A B D e
    letI := weilCoefficientProjective A B D e
    affineChartWeilRestrictionComparison A D (weilCoefficientTarget A B D e Y)
        (ringTest A S)
        (affineChartWeilRestrictionCoefficientPointHomeomorph A B D e Y S hY p) =
      affineChartWeilRestrictionCoefficientComparison A B D e Y (ringTest A S) p := by
  rw [affineChartWeilRestrictionCoefficientPointHomeomorph_apply]
  exact affineChartWeilRestrictionCoefficientIso_comparison A B D e Y hY _ p

end Langlands.AlgebraicGeometry.PointTopology
