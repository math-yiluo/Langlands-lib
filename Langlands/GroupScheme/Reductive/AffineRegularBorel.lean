import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.SplitExistence.IntegralBase
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SmoothOverRing
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Descent.RelativeSolvedData

/-! # Actual relative Borels through a coordinate split maximal torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

variable {I J : Type u} [Fintype I] [Finite J]
  (P : RootDatum J (I → ℤ) (I → ℤ))

/-- Finitely many roots in the coordinate lattice admit a simultaneously
regular integer exponent vector. -/
theorem exists_regularExponent :
    ∃ n : I → ℤ, ∀ a : J, ∑ j, P.root a j * n j ≠ 0 := by
  classical
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨f, hf⟩ := SplitExistence.exists_dual_coroot_ne_zero P.flip
  have hsum (x : I → ℤ) : f x = ∑ j, x j * f (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show (Pi.single j (x j) : I → ℤ) = x j • (Pi.single j (1 : ℤ) : I → ℤ) by
      ext l
      by_cases h : l = j <;> simp [h]]
    simp only [map_smul, smul_eq_mul]
  exact ⟨fun j => f (Pi.single j 1), fun a => by
    rw [← hsum]
    exact hf a⟩

/-- A chosen regular integer exponent depending only on the common root datum. -/
def regularExponent : I → ℤ := (exists_regularExponent P).choose

theorem regularExponent_spec (a : J) :
    ∑ j, P.root a j * regularExponent P j ≠ 0 :=
  (exists_regularExponent P).choose_spec a

end CoordinateRootDatum

namespace AffineRegularBorel

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (n : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual cocharacter with the supplied coordinate exponents in the ambient group. -/
def cocharacter : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G :=
  CommGroupScheme.groupHom
    (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I n) ≫ i

/-- Its actual dynamic parabolic source over the original affine base. -/
abbrev borel : GroupScheme (Spec (CommRingCat.of R)) :=
  Dynamic.Affine.parabolicScheme (cocharacter i n)

/-- The actual dynamic parabolic inclusion. -/
abbrev inclusion : borel i n ⟶ G :=
  Dynamic.Affine.parabolicHom (cocharacter i n)

/-- The coordinate torus lies in the constructed dynamic parabolic on every test scheme. -/
theorem torus_range_le :
    SubgroupFunctor.range i ≤ SubgroupFunctor.range (inclusion i n) := by
  calc
    SubgroupFunctor.range i ≤ Dynamic.centralizer (cocharacter i n) :=
      range_le_centralizer_groupHom_comp
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I n)
    _ ≤ Dynamic.parabolic (cocharacter i n) :=
      Dynamic.centralizer_le_parabolic (cocharacter i n)
    _ = SubgroupFunctor.range (inclusion i n) :=
      (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i n)).2.symm

omit [IsAffineHom G.X.hom] in
/-- The actual cocharacter has the same fixed exponents on every field-valued fibre. -/
theorem cocharacter_baseChange (k : Type u) [Field k] [Algebra R k] :
    Dynamic.baseChangeCocharacter (algebraBaseMap R k) (cocharacter i n) =
      CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) ≫
          splitTorus.baseChangeHom (K := k) G I i := by
  rw [cocharacter, Dynamic.baseChangeCocharacter_comp,
    ← splitTorus.groupHom_exponentCocharacter_baseChange
      (Spec (CommRingCat.of R)) I (algebraBaseMap R k) n]
  simp only [splitTorus.baseChangeHom, Category.assoc, Iso.hom_inv_id_assoc]

variable {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : IsFibrewiseRootDatumOf I G i P)
  (hn : ∀ a : J, ∑ j, P.root a j * n j ≠ 0)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP hn in
/-- The chosen exponent cocharacter is regular on each prescribed field-valued fibre. -/
theorem isRegular_field (k : Type u) [Field k] [Algebra R k] :
    IsRegularCocharacter (splitTorus.baseChangeHom (K := k) G I i)
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I n) := by
  intro α hα
  rw [← (hP.field k).2.1] at hα
  obtain ⟨a, rfl⟩ := hα
  rw [CoordinateRootDatum.fieldRealization_root,
    splitTorus.latticePairing_exponentCharacter_exponentCocharacter]
  exact hn a

include hP hn hG hmax in
/-- The actual dynamic inclusion becomes a Borel on every field-valued fibre. -/
theorem isBorel_field (k : Type u) [Field k] [Algebra R k] :
    IsBorelSubgroup ((GroupScheme.baseChange (algebraBaseMap R k)).map (inclusion i n)) := by
  let : Smooth G.X.hom := hG.smooth
  let b := algebraBaseMap R k
  let F := GroupScheme.baseChange b
  have hred := hG.isConnectedReductive_algebraMap k
  let : IsAffineHom (F.obj G).X.hom := hred.isAffineHom
  have hrep := (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i n)).baseChange b
  rw [← Dynamic.parabolic_baseChange, cocharacter_baseChange] at hrep
  exact (regularCocharacterBorel k (F.obj G) hred
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (splitTorus.baseChangeHom (K := k) G I i)
    (isSplitTorus_splitTorus I)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k)).1
      _ (isRegular_field i n P hP hn k) _ _
      ((Dynamic.Affine.isClosedSubgroup_parabolicHom _).baseChange b) hrep

include hP hn hG hmax in
/-- The actual dynamic inclusion is geometric Borel on every field-valued fibre. -/
theorem isGeometricBorel_field (k : Type u) [Field k] [Algebra R k] :
    IsGeometricBorelSubgroup
      ((GroupScheme.baseChange (algebraBaseMap R k)).map (inclusion i n)) := by
  let b := algebraBaseMap R k
  let a := toAlgebraicClosure k
  let c := algebraBaseMap R (AlgebraicClosure k)
  have hcomp : a ≫ b = c := by
    dsimp [a, b, c, algebraBaseMap, toAlgebraicClosure]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq R k (AlgebraicClosure k)]
  let eB := Descent.pullbackComparison b a c hcomp (borel i n)
  let eG := Descent.pullbackComparison b a c hcomp G
  have h := ((isBorel_field i n P hP hn hG hmax (AlgebraicClosure k)).iso_comp eB).comp_iso
    eG.symm
  change IsBorelSubgroup
    ((eB.hom ≫ (GroupScheme.baseChange c).map (inclusion i n)) ≫ eG.inv) at h
  rw [← Descent.pullbackComparison_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] at h
  exact ⟨isBorel_field i n P hP hn hG hmax k, h⟩

include hP hn hG hmax in
/-- Fibrewise regularity produces an actual relative Borel through the torus. -/
theorem isRelativeBorel :
    IsRelativeBorelSubgroup (inclusion i n) := by
  let : Smooth G.X.hom := hG.smooth
  have hgeo : ∀ s : Spec (CommRingCat.of R),
      IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom (inclusion i n) s) := by
    intro s
    let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
    let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
    have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
        (Spec (CommRingCat.of R)).fromSpecResidueField s := Spec.map_preimage _
    have h := isGeometricBorel_field i n P hP hn hG hmax
      ((Spec (CommRingCat.of R)).residueField s)
    rwa [hb] at h
  exact ⟨⟨(dynamicSmooth_ring R G (cocharacter i n) (borel i n) (inclusion i n)).1
      (Dynamic.Affine.isRepresentedBy_parabolicHom _),
    (Dynamic.Affine.isClosedSubgroup_parabolicHom _).isAffineHom,
    (Dynamic.Affine.isRepresentedBy_parabolicHom _).1,
    fun s => (hgeo s).isParabolicSubgroup⟩, hgeo⟩

end AffineRegularBorel

section Construction

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- A common full fibrewise root datum supplies an actual relative Borel through
the given closed coordinate split maximal torus over the original affine base. -/
def IsFibrewiseRootDatumOf.relativeQuasiSplitTorusData
    (hP : IsFibrewiseRootDatumOf I G i P) (hG : IsReductive G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i) :
    RelativeQuasiSplitTorusData G := by
  let : Finite J := hP.finite
  let n := CoordinateRootDatum.regularExponent P
  have hn := CoordinateRootDatum.regularExponent_spec P
  exact
    { reductive := hG
      borel := ⟨AffineRegularBorel.borel i n, AffineRegularBorel.inclusion i n,
        AffineRegularBorel.isRelativeBorel i n P hP hn hG hmax⟩
      torus := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I
      torusInclusion := i
      torusIsTorus := RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)
      torusClosed := hi
      torusMaximal := hmax
      torus_le_borel := AffineRegularBorel.torus_range_le i n }

end Construction

end Langlands.GroupScheme
