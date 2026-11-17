import Langlands.GroupScheme.Reductive.RelativeIsogenyRootPower
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.FiniteHomDimension

/-! # Unit coefficients of finite actual root restrictions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Multiplicative
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]

/-- The standard additive-line endomorphism obtained by coefficient base change. -/
def baseChangeEndomorphism (A : Type u) [CommRing A] [Algebra R A]
    (f : Ga R ⟶ Ga R) : Ga A ⟶ Ga A :=
  baseChangeRoot A f ≫ (gaIso (R := R) A).hom

/-- The coordinate of coefficient base change is the original coordinate on the
same scheme, regarded over the original base. -/
theorem gaCoord_baseChangeEndomorphism (A : Type u) [CommRing A] [Algebra R A]
    (f : Ga R ⟶ Ga R) (Z : Over (Spec (CommRingCat.of A))) (a : Γ(Z.left, ⊤)) :
    gaCoord (rootPoint (baseChangeEndomorphism A f) Z a) =
      gaCoord (rootPoint f ((Over.map (algebraBaseMap R A)).obj Z) a) := by
  change (VectorGroup.coordinates (CommRingCat.of A) 1 Z
    (rootPoint (baseChangeRoot A f) Z a ≫ (gaIso (R := R) A).hom.hom.hom)).toAdd 0 = _
  rw [coordinates_comp_gaIso_hom]
  change (VectorGroup.coordinates (CommRingCat.of R) 1
    ((Over.map (algebraBaseMap R A)).obj Z)
    (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (Ga R) Z
      (rootPoint (baseChangeRoot A f) Z a))).toAdd 0 = _
  rw [baseChangePointsEquiv_rootPoint]

/-- Coefficient base change preserves finiteness. -/
theorem isFinite_baseChangeEndomorphism (A : Type u) [CommRing A] [Algebra R A]
    (f : Ga R ⟶ Ga R) [IsFinite f.hom.hom.left] :
    IsFinite (baseChangeEndomorphism A f).hom.hom.left := by
  have : IsFinite ((GroupScheme.baseChange (algebraBaseMap R A)).map f).hom.hom.left :=
    MorphismProperty.of_isPullback
      (baseChange_map_isPullback (algebraBaseMap R A) f).flip inferInstance
  have : IsIso (gaIso (R := R) A).inv.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) A).inv))
  have : IsIso (gaIso (R := R) A).hom.hom.hom.left :=
    (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) A).hom))
  change IsFinite (((gaIso (R := R) A).inv.hom.hom.left ≫
    ((GroupScheme.baseChange (algebraBaseMap R A)).map f).hom.hom.left) ≫
      (gaIso (R := R) A).hom.hom.hom.left)
  infer_instance

/-- A finite endomorphism of the additive group over a field is epimorphic. -/
theorem epi_of_isFinite {K : Type u} [Field K] (f : Ga K ⟶ Ga K)
    [IsFinite f.hom.hom.left] : Epi f.hom.hom := by
  let hV : RelativeRoot.IsVectorGroupOfDimension (Ga K) 1 :=
    ⟨VectorGroup.coordinates (CommRingCat.of K) 1, VectorGroup.isNaturalVectorCoordinates⟩
  let : IsAffineHom (Ga K).X.hom := hV.isAffineHom
  let : Smooth (Ga K).X.hom := hV.smooth
  let : ConnectedSpace (Ga K).X.left := hV.connectedSpace
  have h := isIsogeny_of_isFinite_of_finrank_eq f rfl
  let : Flat f.hom.hom.left := h.2.1
  let : Surjective f.hom.hom.left := h.2.2
  let : Epi f.hom.hom.left := Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

/-- A power formula for an epimorphic additive-line map has nonzero coefficient. -/
theorem coefficient_ne_zero_of_epi {K : Type u} [Field K] (f : Ga K ⟶ Ga K)
    [Epi f.hom.hom] (c : K) (q : ℕ)
    (hf : ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Γ(Z.left, ⊤)),
      rootPoint f Z a = VectorGroup.scalarPoint _ Z (baseScalar Z c * a ^ q)) : c ≠ 0 := by
  intro hc
  have hzero : f.hom.hom = 1 := by
    have h := hf (Ga K).X (gaCoord (𝟙 (Ga K).X))
    rw [rootPoint, VectorGroup.scalarPoint_coordinate, Category.id_comp] at h
    rw [h]
    apply VectorGroup.points_ext
    intro j
    simp only [VectorGroup.coordinates_scalarPoint, baseScalar, hc, map_zero, zero_mul,
      map_one, toAdd_one, Pi.zero_apply]
  have hid : 𝟙 (Ga K).X = (1 : (Ga K).X ⟶ (Ga K).X) := by
    apply (cancel_epi f.hom.hom).mp
    simp only [Category.comp_id, MonObj.comp_one, hzero]
  let Z := Corepresented.RingCoordinates.specOver (CommRingCat.of K) (CommAlgCat.of K K)
  let x : Z ⟶ (Ga K).X := VectorGroup.scalarPoint _ Z 1
  have hx : x = 1 := by
    calc
      x = x ≫ 𝟙 (Ga K).X := (Category.comp_id _).symm
      _ = x ≫ 1 := congrArg (x ≫ ·) hid
      _ = 1 := MonObj.comp_one _
  have h := congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of K)).hom (gaCoord z)) hx
  exact one_ne_zero (by
    simpa only [x, gaCoord, VectorGroup.coordinates_scalarPoint, map_one,
      toAdd_one, Pi.zero_apply, map_zero] using h)

/-- A finite additive-line power map over any commutative ring has unit
coefficient. Field fibres detect this unit property. -/
theorem isUnit_coefficient_of_power_of_isFinite (f : Ga R ⟶ Ga R)
    [IsFinite f.hom.hom.left] (c : R) (q : ℕ)
    (hf : ∀ (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A),
      (scalarOperation f).app A a = algebraMap R A c * a ^ q) : IsUnit c := by
  have hc := (scalarOperation f).isUnit_value_one_of_fields (by
    intro K _ _
    let fK := baseChangeEndomorphism K f
    let : IsFinite fK.hom.hom.left := isFinite_baseChangeEndomorphism K f
    let : Epi fK.hom.hom := epi_of_isFinite fK
    have hbc (Z : Over (Spec (CommRingCat.of K))) (a : Γ(Z.left, ⊤)) :
        rootPoint fK Z a =
          VectorGroup.scalarPoint _ Z (baseScalar Z (algebraMap R K c) * a ^ q) := by
      apply VectorGroup.points_ext
      intro j
      rw [Subsingleton.elim j 0]
      change gaCoord (rootPoint (baseChangeEndomorphism K f) Z a) = _
      rw [gaCoord_baseChangeEndomorphism, rootPoint_eq_of_scalarOperation hf,
        gaCoord, VectorGroup.coordinates_scalarPoint, baseScalar_map,
        VectorGroup.coordinates_scalarPoint]
    have hn := coefficient_ne_zero_of_epi fK (algebraMap R K c) q hbc
    simpa only [hf, one_pow, mul_one] using hn)
  simpa only [hf, Algebra.algebraMap_self, RingHom.id_apply, one_pow, mul_one] using hc

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.RelativeIsogeny

open LocalRootGroup LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
  {J J' : Type u} [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced]
  (hP : IsFibrewiseRootDatumOf I G i P) (hQ : IsFibrewiseRootDatumOf I' H j Q)
  {p : ℕ} (r : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (tau : splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I ⟶
    splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I')
  (hweight : ∀ m : I' → ℤ, tau ≫ splitTorus.exponentCharacter _ I' m =
    splitTorus.exponentCharacter _ I (r.weightMap m))
  (phi : G ⟶ H) (hphi : i ≫ phi = CommGroupScheme.groupHom tau ≫ j)
  (hH : IsReductive H)
  (hmaxH : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j)
  (b : J')
  {u : Ga R ⟶ G} {v : Ga R ⟶ H}
  (hu : IsRootParametrization i (P.root (r.indexEquiv b)) u)
  (hv : IsRootParametrization j (Q.root b) v)
  [IsFinite phi.hom.hom.left]

/-- An actual root restriction of a finite ambient map is finite. -/
theorem rootRestriction_isFinite :
    IsFinite (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv).hom.hom.left := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  have : IsClosedImmersion u.hom.hom.left := hu.isClosedSubgroup
  have : IsClosedImmersion v.hom.hom.left := hv.isClosedSubgroup
  have hcomp : f.hom.hom.left ≫ v.hom.hom.left =
      u.hom.hom.left ≫ phi.hom.hom.left := by
    exact congrArg (fun h : Ga R ⟶ H => h.hom.hom.left)
      (rootRestriction_comp i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)
  have : IsFinite (f.hom.hom.left ≫ v.hom.hom.left) := hcomp.symm ▸ inferInstance
  exact IsFinite.of_comp f.hom.hom.left v.hom.hom.left

/-- Finiteness forces the prescribed-power coefficient to be a unit over the
entire local base ring. -/
theorem isUnit_rootRestrictionCoefficient :
    IsUnit (rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv) := by
  let f := rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  let : IsFinite f.hom.hom.left :=
    rootRestriction_isFinite i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv
  exact isUnit_coefficient_of_power_of_isFinite f _ (r.rootFactor b)
    (rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)

/-- The unit coefficient of the actual supplied-root restriction. -/
def rootRestrictionUnit : Rˣ :=
  (isUnit_rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv).unit

@[simp] theorem coe_rootRestrictionUnit :
    (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) =
      rootRestrictionCoefficient i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv :=
  IsUnit.unit_spec _

/-- The actual root restriction has a unit-coefficient power formula on every
coefficient algebra. -/
theorem rootRestriction_unit_power (A : CommAlgCat.{u} (CommRingCat.of R)) (a : A) :
    (scalarOperation (rootRestriction i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv)).app A a =
      algebraMap R A (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) *
        a ^ r.rootFactor b := by
  rw [coe_rootRestrictionUnit]
  exact rootRestriction_power i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv A a

/-- The unit-coefficient formula holds in the ambient group on every scheme
test, including nonreduced tests. -/
theorem rootRestriction_unit_power_rootPoint (Z : Over (Spec (CommRingCat.of R)))
    (a : Γ(Z.left, ⊤)) :
    rootPoint u Z a ≫ phi.hom.hom =
      rootPoint v Z (baseScalar Z
        (rootRestrictionUnit i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv : R) *
          a ^ r.rootFactor b) := by
  rw [coe_rootRestrictionUnit]
  exact rootRestriction_power_rootPoint i j hP hQ r tau hweight phi hphi hH hmaxH b hu hv Z a

end Langlands.GroupScheme.RelativeIsogeny
