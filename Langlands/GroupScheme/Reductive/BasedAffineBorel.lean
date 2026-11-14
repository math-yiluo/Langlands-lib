import Langlands.GroupScheme.Reductive.AffineRegularBorel
import Langlands.GroupScheme.Reductive.IntegralWeylVectorProperties

/-! # Relative Borels from the canonical sum of positive coroots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace BasedBorelExponent

section Sum

variable {J X Y : Type*} [Fintype J] [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (b : P.Base)

/-- The canonical integral cocharacter-lattice element determined by a base. -/
def positiveCorootSum : Y :=
  Langlands.IntegralWeylVector.positiveRootSum P.flip b.flip

variable [P.IsReduced]

/-- Every root pairs with the positive-coroot sum as twice its height. -/
theorem pairing_root_positiveCorootSum (a : J) :
    P.toLinearMap (P.root a) (positiveCorootSum P b) = 2 * b.height a := by
  let : Module.IsTorsionFree ℤ X :=
    (LinearMap.IsPerfPair.bijective_left P.toLinearMap).injective.moduleIsTorsionFree
      _ (fun r x => map_smul P.toLinearMap r x)
  let : Module.IsTorsionFree ℤ Y :=
    (LinearMap.IsPerfPair.bijective_left P.flip.toLinearMap).injective.moduleIsTorsionFree
      _ (fun r y => map_smul P.flip.toLinearMap r y)
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int a
  rw [RootPairing.Base.height_eq_sum hf, hf, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h2 : P.toLinearMap (P.root j) (positiveCorootSum P b) = 2 :=
    Langlands.IntegralWeylVector.pairing_positiveRootSum_simple P.flip b.flip ⟨j, hj⟩
  rw [map_zsmul, LinearMap.smul_apply, h2, smul_eq_mul, mul_comm]

/-- The positive-coroot sum is regular on every root without any spanning hypothesis. -/
theorem pairing_root_positiveCorootSum_ne_zero (a : J) :
    P.toLinearMap (P.root a) (positiveCorootSum P b) ≠ 0 := by
  rw [pairing_root_positiveCorootSum]
  exact mul_ne_zero (by decide) (b.height_ne_zero a)

end Sum

section Transport

variable {J X Y J' X' Y' : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
  {P : RootDatum J X Y} {Q : RootDatum J' X' Y'}
  (b : P.Base) (c : Q.Base) (e : RootPairing.Equiv P Q)
  (he : ∀ j : J, j ∈ b.support ↔ e.indexEquiv j ∈ c.support)

include he in
/-- Based equivalences preserve heights in the dual bases, with the
contravariant coweight convention explicit. -/
theorem coroot_height_eq (a : J') :
    b.flip.height (e.indexEquiv.symm a) = c.flip.height a := by
  classical
  have hs (j : J') : j ∈ c.support ↔ e.indexEquiv.symm j ∈ b.support := by
    simpa only [Equiv.apply_symm_apply] using (he (e.indexEquiv.symm j)).symm
  have hcor (j : J') :
      e.coweightMap (Q.coroot j) = P.coroot (e.indexEquiv.symm j) :=
    RootPairing.Hom.coroot_coweightMap_apply P Q j e.toHom
  obtain ⟨f, -, -, hf⟩ := c.flip.exists_root_eq_sum_int a
  change Q.coroot a = ∑ j ∈ c.support, f j • Q.coroot j at hf
  have hroot : P.coroot (e.indexEquiv.symm a) =
      ∑ j ∈ b.support, f (e.indexEquiv j) • P.coroot j := by
    calc
      _ = e.coweightMap (Q.coroot a) := (hcor a).symm
      _ = ∑ j ∈ c.support, f j • P.coroot (e.indexEquiv.symm j) := by
        rw [hf, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_zsmul, hcor]
      _ = _ := Finset.sum_equiv e.indexEquiv.symm hs
        (fun j _ => by rw [Equiv.apply_symm_apply])
  rw [RootPairing.Base.height_eq_sum hroot, RootPairing.Base.height_eq_sum hf]
  exact (Finset.sum_equiv e.indexEquiv.symm hs
    (fun j _ => by rw [Equiv.apply_symm_apply])).symm

variable [Fintype J] [Fintype J']

include he in
/-- Based root-datum equivalences preserve the actual positive-coroot sum. -/
theorem positiveCorootSum_coweightMap :
    e.coweightMap (positiveCorootSum Q c) = positiveCorootSum P b := by
  classical
  unfold positiveCorootSum Langlands.IntegralWeylVector.positiveRootSum
  rw [map_sum]
  apply Finset.sum_equiv e.indexEquiv.symm
  · intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, RootPairing.Base.isPos_iff]
    rw [coroot_height_eq b c e he]
  · intro j _
    exact RootPairing.Hom.coroot_coweightMap_apply P Q j e.toHom

end Transport

end BasedBorelExponent

namespace AffineRegularBorel

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I] [Fintype J]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base)
  (hP : IsFibrewiseRootDatumOf I G i P) (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)

include hP in
/-- A supplied field-valued fibre identifies the canonical exponent with
the regular positive-coroot sum for the actual lattice pairing. -/
theorem positiveCorootExponent_regular (k : Type u) [Field k] [Algebra R k] (a : J) :
    ∑ j, P.root a j * BasedBorelExponent.positiveCorootSum P b j ≠ 0 := by
  let : P.IsReduced := hP.isReduced
  rw [← hP.pairing k]
  exact BasedBorelExponent.pairing_root_positiveCorootSum_ne_zero P b a

include hP hG hmax in
/-- The dynamic parabolic of the canonical based exponent is relative Borel
over the original ring, including the zero ring. -/
theorem isRelativeBorel_positiveCorootSum :
    IsRelativeBorelSubgroup (inclusion i (BasedBorelExponent.positiveCorootSum P b)) := by
  let n := BasedBorelExponent.positiveCorootSum P b
  let : Smooth G.X.hom := hG.smooth
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hgeo : ∀ s : Spec (CommRingCat.of R),
      IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom (inclusion i n) s) := by
    intro s
    let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
    let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
    have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
        (Spec (CommRingCat.of R)).fromSpecResidueField s := Spec.map_preimage _
    have hn := positiveCorootExponent_regular i P b hP
      ((Spec (CommRingCat.of R)).residueField s)
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

/-- A supplied based full fibrewise root datum constructs the actual relative
Borel from its canonical positive-coroot exponent, through the original torus. -/
def IsFibrewiseRootDatumOf.relativeQuasiSplitTorusDataOfBase
    (hP : IsFibrewiseRootDatumOf I G i P) (b : P.Base) (hG : IsReductive G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i) :
    RelativeQuasiSplitTorusData G := by
  let : Fintype J := @Fintype.ofFinite J hP.finite
  let n := BasedBorelExponent.positiveCorootSum P b
  exact
    { reductive := hG
      borel := ⟨AffineRegularBorel.borel i n, AffineRegularBorel.inclusion i n,
        AffineRegularBorel.isRelativeBorel_positiveCorootSum i P b hP hG hmax⟩
      torus := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I
      torusInclusion := i
      torusIsTorus := RelativeTorus.IsTorus.of_isSplitTorus (isSplitTorus_splitTorus I)
      torusClosed := hi
      torusMaximal := hmax
      torus_le_borel := AffineRegularBorel.torus_range_le i n }

end Construction

end Langlands.GroupScheme
