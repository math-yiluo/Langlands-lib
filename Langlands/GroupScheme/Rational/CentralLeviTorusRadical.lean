import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientReduction
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Absolute.UnipotentPointsSolvable
import Langlands.GroupScheme.Absolute.RegularCocharacterSolvable
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.Torus.Geometry

/-! # Central tori of a Levi factor lie in the ambient solvable radical -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {L U P : GroupScheme S}
    (l : L ⟶ P) (r : U ⟶ P) [IsIso (subgroupMultiplication l r)]
    (hn : (SubgroupFunctor.range r).IsNormal)

/-- The Levi projection is smooth when the radical is smooth. -/
theorem smooth_leviRetraction [Smooth U.X.hom] :
    Smooth (leviRetraction l r hn).hom.hom.left := by
  rw [leviRetraction_hom_hom]
  let : IsIso (inv (subgroupMultiplication l r)).left :=
    (Over.forget S).map_isIso _
  change Smooth ((inv (subgroupMultiplication l r)).left ≫
    (pullback.fst L.X.hom U.X.hom))
  infer_instance

/-- Geometric connectedness of the radical gives geometric connectedness of
the Levi projection. -/
theorem geometricallyConnected_leviRetraction [GeometricallyConnected U.X.hom] :
    GeometricallyConnected (leviRetraction l r hn).hom.hom.left := by
  rw [leviRetraction_hom_hom]
  let : IsIso (inv (subgroupMultiplication l r)).left :=
    (Over.forget S).map_isIso _
  change GeometricallyConnected ((inv (subgroupMultiplication l r)).left ≫
    (pullback.fst L.X.hom U.X.hom))
  have : MorphismProperty.RespectsIso @GeometricallyConnected.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr
    inferInstance

/-- The radical maps to the identity under the actual Levi retraction. -/
theorem radical_comp_leviRetraction : r ≫ leviRetraction l r hn = 0 := by
  apply hom_ext_points
  intro T x
  simp only [Grp.comp_hom_hom, Grp.zero_hom, Mon.zero_hom,
    ← Hom.one_def, MonObj.comp_one, ← Category.assoc]
  exact (comp_leviRetraction_eq_one_iff l r hn _).mpr ⟨x, rfl⟩

variable {A : GroupScheme S} (a : A ⟶ L)

/-- The actual radical homomorphism into the inverse image of any Levi subgroup. -/
def leviPreimageRadicalLift :
    U ⟶ SubgroupPreimage.groupScheme (leviRetraction l r hn) a :=
  pullback.lift r 0 (by
    rw [radical_comp_leviRetraction]
    simp)

@[simp] theorem leviPreimageRadicalLift_comp_inclusion :
    leviPreimageRadicalLift l r hn a ≫
      SubgroupPreimage.inclusion (leviRetraction l r hn) a = r :=
  pullback.lift_fst _ _ _

@[simp] theorem leviPreimageRadicalLift_comp_projection :
    leviPreimageRadicalLift l r hn a ≫
      SubgroupPreimage.projection (leviRetraction l r hn) a = 0 :=
  pullback.lift_snd _ _ _

/-- On each test scheme, the inverse image of a subgroup with solvable points
has solvable points if the radical does. -/
theorem isSolvable_points_leviPreimage (T : Over S)
    [Group.IsSolvable (T ⟶ U.X)] [Group.IsSolvable (T ⟶ A.X)] :
    Group.IsSolvable
      (T ⟶ (SubgroupPreimage.groupScheme (leviRetraction l r hn) a).X) := by
  let q := leviRetraction l r hn
  let i := SubgroupPreimage.inclusion q a
  let p := SubgroupPreimage.projection q a
  let f : (T ⟶ U.X) →*
      (T ⟶ (SubgroupPreimage.groupScheme q a).X) :=
    { toFun := fun n => n ≫ (leviPreimageRadicalLift l r hn a).hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  let g : (T ⟶ (SubgroupPreimage.groupScheme q a).X) →* (T ⟶ A.X) :=
    { toFun := fun x => x ≫ p.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun _ _ => MonObj.mul_comp _ _ _ }
  apply Group.isSolvable_of_ker_le_range f g
  intro x hx
  have hxp : x ≫ p.hom.hom = 1 := hx
  have hxq : (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
    rw [Category.assoc, (SubgroupPreimage.isPullback q a).w,
      ← Category.assoc, hxp, MonObj.one_comp]
  have hxrange := (comp_leviRetraction_eq_one_iff l r hn _).mp hxq
  change ∃ n : T ⟶ U.X, n ≫ r.hom.hom = x ≫ i.hom.hom at hxrange
  obtain ⟨n, hnr⟩ := hxrange
  refine ⟨n, ?_⟩
  change n ≫ (leviPreimageRadicalLift l r _ a).hom.hom = x
  apply (SubgroupPreimage.isPullback q a).hom_ext
  · change (n ≫ (leviPreimageRadicalLift l r _ a).hom.hom) ≫ i.hom.hom =
      x ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, leviPreimageRadicalLift_comp_inclusion]
    exact hnr
  · change (n ≫ (leviPreimageRadicalLift l r _ a).hom.hom) ≫ p.hom.hom =
      x ≫ p.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, leviPreimageRadicalLift_comp_projection]
    simpa only [Grp.zero_hom, Mon.zero_hom, ← Hom.one_def, MonObj.comp_one]
      using hxp.symm

end Base

section Field

variable {k : Type u} [Field k]
    {L P R : GroupScheme (Spec (CommRingCat.of k))} {l : L ⟶ P} {rR : R ⟶ P}
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ L)

/-- A closed central torus of an actual rational Levi lies in every represented
ground-field solvable radical of the ambient group. -/
theorem IsRationalLeviSubgroup.range_centralTorus_le_solvableRadical
    (hl : IsRationalLeviSubgroup l) (hR : IsSolvableRadical rR)
    (hA : IsTorus A.toGrp) (ha : IsClosedSubgroup a) (hca : IsCentral a) :
    SubgroupFunctor.range (a ≫ l) ≤ SubgroupFunctor.range rR := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  let : IsAffineHom P.X.hom := hl.isAffineHom
  let : IsClosedImmersion r.hom.hom.left := hr.1.isClosedSubgroup
  let : IsAffineHom U.X.hom := by
    rw [← Over.w r.hom.hom]
    infer_instance
  let : Smooth U.X.hom := hr.1.smooth
  let : ConnectedSpace U.X.left := hr.1.connectedSpace
  let : GeometricallyConnected U.X.hom := U.geometricallyConnected_of_connected
  let q := leviRetraction l r hr.1.isNormal
  let : Smooth q.hom.hom.left := smooth_leviRetraction l r hr.1.isNormal
  let : GeometricallyConnected q.hom.hom.left :=
    geometricallyConnected_leviRetraction l r hr.1.isNormal
  let : Smooth A.X.hom := hA.smooth
  let : ConnectedSpace A.X.left := hA.connectedSpace
  let H := SubgroupPreimage.groupScheme q a
  let i := SubgroupPreimage.inclusion q a
  let p := SubgroupPreimage.projection q a
  have hi : IsClosedSubgroup i := SubgroupPreimage.isClosedSubgroup q a ha
  have hs : Smooth H.X.hom := SubgroupPreimage.smooth q a
  let : Smooth p.hom.hom.left := SubgroupPreimage.smooth_projection q a
  let : GeometricallyConnected p.hom.hom.left :=
    MorphismProperty.of_isPullback (SubgroupPreimage.isPullback_scheme q a) inferInstance
  have hc : ConnectedSpace H.X.left :=
    GeometricallyConnected.connectedSpace p.hom.hom.left p.hom.hom.left.isOpenMap
  have hsol : IsSolvableGroupScheme H := by
    apply isSolvableGroupScheme_of_isSolvable_points
    let : Group.IsSolvable (algebraicClosurePoint k ⟶ U.X) :=
      isSolvable_points_of_isUnipotent hr.1.isUnipotent _
    exact isSolvable_points_leviPreimage l r hr.1.isNormal a _
  have hnormal : (SubgroupFunctor.range i).IsNormal :=
    SubgroupPreimage.isNormal q a hca.range_isNormal
  have hle := hR.greatest H i hi hs hc hsol hnormal
  intro T x hx
  apply hle T
  rw [SubgroupPreimage.range_inclusion, SubgroupFunctor.mem_comap]
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  refine SubgroupFunctor.mem_range.mpr ⟨y, ?_⟩
  change y ≫ a.hom.hom = (y ≫ (a ≫ l).hom.hom) ≫ q.hom.hom
  rw [Grp.comp_hom_hom, Category.assoc, Category.assoc,
    ← Grp.comp_hom_hom, levi_comp_leviRetraction, Grp.id_hom_hom, Category.comp_id]

/-- The actual factor of a closed central Levi torus through the specified
represented solvable radical. -/
def IsRationalLeviSubgroup.centralTorusRadicalFactor
    (hl : IsRationalLeviSubgroup l) (hR : IsSolvableRadical rR)
    (hA : IsTorus A.toGrp) (ha : IsClosedSubgroup a) (hca : IsCentral a) :
    A.toGrp ⟶ R := by
  let : IsClosedImmersion rR.hom.hom.left := hR.isClosedSubgroup
  let hrep : (SubgroupFunctor.range rR).IsRepresentedBy rR :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  exact hrep.factorHom (a ≫ l)
    (hl.range_centralTorus_le_solvableRadical a hR hA ha hca)

/-- The factor is compatible with the original inclusion in the ambient group. -/
theorem IsRationalLeviSubgroup.centralTorusRadicalFactor_comp
    (hl : IsRationalLeviSubgroup l) (hR : IsSolvableRadical rR)
    (hA : IsTorus A.toGrp) (ha : IsClosedSubgroup a) (hca : IsCentral a) :
    hl.centralTorusRadicalFactor a hR hA ha hca ≫ rR = a ≫ l := by
  unfold IsRationalLeviSubgroup.centralTorusRadicalFactor
  exact SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- The factor embeds the same torus as a closed subgroup of the radical. -/
theorem IsRationalLeviSubgroup.isClosedSubgroup_centralTorusRadicalFactor
    (hl : IsRationalLeviSubgroup l) (hR : IsSolvableRadical rR)
    (hA : IsTorus A.toGrp) (ha : IsClosedSubgroup a) (hca : IsCentral a) :
    IsClosedSubgroup (hl.centralTorusRadicalFactor a hR hA ha hca) := by
  apply IsClosedSubgroup.of_comp hR.isClosedSubgroup
  rw [IsRationalLeviSubgroup.centralTorusRadicalFactor_comp]
  let : IsClosedImmersion a.hom.hom.left := ha
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  change IsClosedImmersion (a.hom.hom.left ≫ l.hom.hom.left)
  infer_instance

end Field

end Langlands.GroupScheme
