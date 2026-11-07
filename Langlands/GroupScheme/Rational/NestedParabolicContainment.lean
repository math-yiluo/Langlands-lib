import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.BorelPromotion
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.ClosedSubgroupMonomorphism
import Langlands.GroupScheme.BaseChangeReflection

/-! # Containment of the outer radical in a nested parabolic -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A group with a rational Levi factor is connected. -/
theorem IsRationalLeviSubgroup.connectedSpace
    {L P : GroupScheme (Spec (CommRingCat.of k))} {l : L ⟶ P}
    (hl : IsRationalLeviSubgroup l) : ConnectedSpace P.X.left := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  have : Smooth L.X.hom := hl.isConnectedReductive.smooth
  have : IsAffineHom L.X.hom := hl.isConnectedReductive.isAffineHom
  have : ConnectedSpace L.X.left := hl.isConnectedReductive.connectedSpace
  have : Smooth U.X.hom := hr.1.smooth
  have : IsAffineHom P.X.hom := hl.isAffineHom
  have : IsAffineHom U.X.hom := hr.1.isClosedSubgroup.isAffineHom
  have : ConnectedSpace U.X.left := hr.1.connectedSpace
  have : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  have : ConnectedSpace (L.X ⊗ U.X).left := by
    change ConnectedSpace ↥(pullback L.X.hom U.X.hom)
    infer_instance
  have : IsIso (subgroupMultiplication l r) := hmul
  have : IsIso (subgroupMultiplication l r).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (subgroupMultiplication l r)))
  exact (subgroupMultiplication l r).left.surjective.connectedSpace
    (subgroupMultiplication l r).left.continuous

/-- A smooth connected normal unipotent subgroup of an overgroup lies in each
ambient parabolic contained in that overgroup. -/
theorem range_normalUnipotent_le_nestedParabolic
    {G P Q U : GroupScheme (Spec (CommRingCat.of k))}
    (p : P ⟶ G) (q : Q ⟶ G) (a : P ⟶ Q) (r : U ⟶ Q)
    (hp : IsParabolicSubgroup p) (hq : IsClosedSubgroup q)
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (ha : a ≫ q = p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    SubgroupFunctor.range r ≤ SubgroupFunctor.range a := by
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Mono a.hom.hom :=
    (IsClosedSubgroup.of_comp hq (ha ▸ hp.isClosedSubgroup)).mono_overHom
  obtain ⟨hsurj, hflat, hqc⟩ := fieldExtension_fpqc k (AlgebraicClosure k)
  have : Surjective b := hsurj
  have : Flat b := hflat
  have : QuasiCompact b := hqc
  apply SubgroupFunctor.le_range_of_baseChange_le b a
  rw [← SubgroupFunctor.range_baseChangeHom,
    ← SubgroupFunctor.range_baseChangeHom]
  have : ConnectedSpace (F.obj Q).X.left :=
    Q.connectedSpace_baseChange_of_smooth_affine b
  have : Smooth (F.obj Q).X.hom := by
    change Smooth (pullback.snd Q.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  obtain ⟨B, j, f, hj, hf⟩ := hp.exists_isBorelSubgroup
  have hf' : (f ≫ F.map a) ≫ F.map q = j := by
    rw [Category.assoc, ← F.map_comp, ha]
    exact hf
  have hc : IsBorelSubgroup (f ≫ F.map a) :=
    IsBorelSubgroup.of_comp (hq.baseChange b) (hf' ▸ hj)
  exact (normalUnipotentBorelContainment (AlgebraicClosure k) (F.obj Q)
    (F.obj U) (F.map r) hr.2.isClosedSubgroup hr.2.smooth
    hr.2.connectedSpace hr.2.isUnipotent hr.2.isNormal B (f ≫ F.map a) hc).trans
      (SubgroupFunctor.range_le_of_factor f rfl)

end Langlands.GroupScheme
