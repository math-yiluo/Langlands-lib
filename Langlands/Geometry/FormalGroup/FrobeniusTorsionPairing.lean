import Langlands.Geometry.FormalGroup.RelativeFrobenius
import Langlands.Geometry.FormalGroup.TorsionPolarizationSimilitude

/-! # Relative Frobenius on the represented torsion pairings -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme Hom.FiniteKernelModel
open scoped CategoryTheory.MonObj CategoryTheory.Obj

attribute [local instance] coefficientAlgebra coefficientScalarTower
set_option backward.isDefEq.respectTransparency false

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ : Type} [Finite σ] {M : ModuleLaw O R σ}
variable {π : O} (hM : M.IsPiDivisible π)
variable {p : ℕ} [ExpChar R p] (m : ℕ) (θ : R →ₐ[O] R)
variable (hθ : θ.toRingHom = iterateFrobenius R p m)

local notation "Base" => Spec (CommRingCat.of R)
local notation "aff" => algSpec (CommRingCat.of R)
local notation "res" => Over.map (coefficientSpecMap θ)
local notation "kernel" n => (hM.torsionKernelModel n)

/-- Absolute Frobenius of an affine test is a morphism over the original base
when its source is viewed over the base through coefficient Frobenius. -/
def affineFrobeniusTestMap (A : CommAlgCat.{v} R) [ExpChar A p] :
    (res).obj ((aff).obj (op A)) ⟶ (aff).obj (op A) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (iterateFrobenius A p m))) (by
    change Spec.map (CommRingCat.ofHom (iterateFrobenius A p m)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ coefficientSpecMap θ
    rw [← Spec.map_comp, coefficientSpecMap, ← Spec.map_comp]
    exact congrArg (fun f : R →+* A => Spec.map (CommRingCat.ofHom f))
      (show (iterateFrobenius A p m).comp (algebraMap R A) =
          (algebraMap R A).comp θ.toRingHom from
        hθ.symm ▸ ((algebraMap R A).iterateFrobenius_comm p m).symm))

private theorem affineFrobeniusTestMap_appTop (A : CommAlgCat.{v} R) [ExpChar A p]
    (z : Γ(((aff).obj (op A)).left, ⊤)) :
    (affineFrobeniusTestMap m θ hθ A).left.appTop z = z ^ (p ^ m) := by
  let e := Scheme.ΓSpecIso (CommRingCat.of A)
  apply (ConcreteCategory.bijective_of_isIso e.hom).1
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (iterateFrobenius A p m))) z
  change e.hom ((affineFrobeniusTestMap m θ hθ A).left.appTop z) =
    (e.hom z) ^ (p ^ m) at h
  exact h.trans (map_pow e.hom.hom z (p ^ m)).symm

private theorem modelPullback_coordinates {f : Hom M M}
    (K : Hom.FiniteKernelModel f) {g : Hom (M.map θ) (M.map θ)} (e : f.map θ = g)
    (L : Hom.FiniteKernelModel g) (T : Over Base) (x : T ⟶ L.commGroupScheme.X) :
    (K.globalPointsEquiv ((res).obj T) (GroupScheme.baseChangePointsEquiv
      (coefficientSpecMap θ) K.commGroupScheme.toGrp T
      (x ≫ ((e ▸ K.pullbackIso θ) L).hom.toMul.hom.hom))).toAdd.val =
      (L.globalPointsEquiv T x).toAdd.val := by
  subst g
  rw [K.pullbackIso_hom_points]
  let points := (GroupScheme.baseChangePointsEquiv (coefficientSpecMap θ)
    K.commGroupScheme.toGrp T).trans (K.globalPointsEquiv ((res).obj T))
  unfold pullbackPointsEquiv
  change (points (points.symm _)).toAdd.val = _
  rw [points.apply_symm_apply]
  rfl

private theorem torsionPointBaseChange_coordinates (n : ℕ) (T : Over Base)
    (x : T ⟶ ((hM.map θ).torsionSchemeInclusions.obj n).X) :
    ((kernel n).globalPointsEquiv ((res).obj T)
      (hM.torsionPointBaseChangeEquiv θ n T x)).toAdd.val =
      (((hM.map θ).torsionKernelModel n).globalPointsEquiv T x).toAdd.val :=
  modelPullback_coordinates θ (kernel n) (scalarHom_map M (π ^ n) θ)
    ((hM.map θ).torsionKernelModel n) T x

private theorem frobenius_torsionPoint_restrict (n : ℕ) (A : CommAlgCat.{v} R) [ExpChar A p]
    (x : (aff).obj (op A) ⟶ (hM.torsionSchemeInclusions.obj n).X) :
    hM.torsionPointBaseChangeEquiv θ n ((aff).obj (op A))
        (x ≫ ((M.frobeniusHom p m θ hθ).scalarTorsionSchemeMap hM (hM.map θ) n).toMul.hom.hom) =
      affineFrobeniusTestMap m θ hθ A ≫ x := by
  let T := (aff).obj (op A)
  let K := kernel n
  let L := (hM.map θ).torsionKernelModel n
  let f := M.frobeniusHom p m θ hθ
  let a := affineFrobeniusTestMap m θ hθ A
  refine (K.globalPointsEquiv ((res).obj T)).injective
    (congrArg Multiplicative.ofAdd (Subtype.ext ?_))
  change (K.globalPointsEquiv ((res).obj T)
      (hM.torsionPointBaseChangeEquiv θ n T
        (x ≫ (f.scalarTorsionSchemeMap hM (hM.map θ) n).toMul.hom.hom))).toAdd.val =
    (K.globalPointsEquiv ((res).obj T) (a ≫ x)).toAdd.val
  rw [torsionPointBaseChange_coordinates, K.globalPointsEquiv_naturality]
  have h := K.commGroupSchemeMap_globalPoints L (f.scalarTorsionPointNatTrans π n) x
  change L.globalPointsEquiv T (x ≫ (f.scalarTorsionSchemeMap hM (hM.map θ) n).toMul.hom.hom) = _ at h
  rw [h]
  apply SeriesPoint.ext
  intro i
  let z : SeriesPoint (globalAlgebra T) σ Empty := (K.globalPointsEquiv T x).toAdd.val
  change (SeriesPoint.eval ((CoordinateMap.frobeniusPow p m).map
      (algebraMap R (globalAlgebra T))) z).val i =
    MvPowerSeries.map a.left.appTop.hom (z.val i)
  let _ : ExpChar (globalAlgebra T) p :=
    expChar_of_injective_ringHom (f := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1 p
  rw [CoordinateMap.map_frobeniusPow, CoordinateMap.eval_frobeniusPow]
  apply MvPowerSeries.ext
  intro d
  obtain rfl : d = 0 := Subsingleton.elim _ _
  change MvPowerSeries.constantCoeff (z.val i ^ (p ^ m)) =
    a.left.appTop (MvPowerSeries.constantCoeff (z.val i))
  exact (map_pow MvPowerSeries.constantCoeff (z.val i) (p ^ m)).trans
    (affineFrobeniusTestMap_appTop m θ hθ A (MvPowerSeries.constantCoeff (z.val i))).symm

private theorem frobenius_pairing_affine [Fact p.Prime] {τ : Type} [Finite τ]
    {N : ModuleLaw O R τ} (hN : N.IsPiDivisible π) (e : TorsionCartierDuality hM hN)
    (n : ℕ) (A : CommAlgCat.{v} R)
    (x : (aff).obj (op A) ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : (aff).obj (op A) ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    (e.baseChange θ).pairing n
        (x ≫ ((M.frobeniusHom p m θ hθ).scalarTorsionSchemeMap hM (hM.map θ) n).toMul.hom.hom)
        (y ≫ ((N.frobeniusHom p m θ hθ).scalarTorsionSchemeMap hN (hN.map θ) n).toMul.hom.hom) =
      (e.pairing n x y) ^ (p ^ m) := by
  let T := (aff).obj (op A)
  rcases subsingleton_or_nontrivial A with hA | hA
  · apply (Gm.affinePointsEquiv T.hom).injective
    apply Units.ext
    exact (Subsingleton.elim : ∀ a b : A, a = b) _ _
  let _ : CharP R p := (expChar_prime_iff R (Fact.out : p.Prime)).1 inferInstance
  let _ : CharP A p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2
    (by simpa only [map_natCast, map_zero] using
      congrArg (algebraMap R A) (CharP.cast_eq_zero R p))
  let eT := Gm.pointsEquiv Base T
  apply eT.injective
  change eT ((e.baseChange θ).pairing n _ _) = eT (e.pairing n x y ^ (p ^ m))
  rw [e.baseChange_pairing, frobenius_torsionPoint_restrict, frobenius_torsionPoint_restrict,
    e.pairing_restrict, Gm.pointsEquiv_naturality, map_pow]
  apply Units.ext
  exact affineFrobeniusTestMap_appTop m θ hθ A (eT (e.pairing n x y)).val

/-- Under coefficient Frobenius, the actual pairing of two relative Frobenius
images is the `p ^ m`-th power of the original pairing on every scheme test. -/
theorem TorsionCartierDuality.frobenius_pairing [Fact p.Prime] {τ : Type} [Finite τ]
    {N : ModuleLaw O R τ} {hN : N.IsPiDivisible π} (e : TorsionCartierDuality hM hN)
    (n : ℕ) (T : Over Base)
    (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    (e.baseChange θ).pairing n
        (x ≫ ((M.frobeniusHom p m θ hθ).scalarTorsionSchemeMap hM (hM.map θ) n).toMul.hom.hom)
        (y ≫ ((N.frobeniusHom p m θ hθ).scalarTorsionSchemeMap hN (hN.map θ) n).toMul.hom.hom) =
      (e.pairing n x y) ^ (p ^ m) := by
  let adj := algΓAlgSpecAdjunction (CommRingCat.of R)
  let A := globalAlgebra T
  let j : T ⟶ (aff).obj (op A) := adj.unit.app T
  have factor (C : CommAlgCat.{v} R) (z : T ⟶ (aff).obj (op C)) :
      ∃ z' : (aff).obj (op A) ⟶ (aff).obj (op C), z = j ≫ z' := by
    let f := (adj.homEquiv T (op C)).symm z
    exact ⟨(aff).map f, ((adj.homEquiv T (op C)).apply_symm_apply z).symm.trans
      (adj.homEquiv_unit T (op C) f)⟩
  obtain ⟨x', hx⟩ := factor (kernel n).coordinateAlgebra x
  obtain ⟨y', hy⟩ := factor (hN.torsionKernelModel n).coordinateAlgebra y
  have hp := frobenius_pairing_affine hM m θ hθ hN e n A x' y'
  simp only [hx, hy, Category.assoc, TorsionCartierDuality.pairing_restrict, hp]
  apply (Gm.pointsEquiv Base T).injective
  rw [map_pow, Gm.pointsEquiv_naturality, Gm.pointsEquiv_naturality, map_pow, map_pow]

/-- The natural-number scalar acts on a represented torsion point by the
corresponding power in its multiplicatively written point group. -/
theorem scalarTorsionSchemeMap_natCast_points (n k : ℕ) (T : Over Base)
    (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X) :
    x ≫ ((M.scalarHom (k : O)).scalarTorsionSchemeMap hM hM n).toMul.hom.hom = x ^ k := by
  let K := kernel n
  let E := K.globalPointsEquiv T
  let f := M.scalarHom (k : O)
  let z := (E x).toAdd
  apply E.injective
  calc
    E (x ≫ (f.scalarTorsionSchemeMap hM hM n).toMul.hom.hom) =
        Multiplicative.ofAdd ((f.scalarTorsionPointNatTrans π n).app (globalAlgebra T) z) :=
      K.commGroupSchemeMap_globalPoints K (f.scalarTorsionPointNatTrans π n) x
    _ = Multiplicative.ofAdd (k • z) := by
      refine congrArg Multiplicative.ofAdd (Subtype.ext ?_)
      change f.onAlgebraPoints z.val = k • z.val
      exact (scalarHom_onAlgebraPoints M (k : O) (globalAlgebra T) z.val).trans
        (Nat.cast_smul_eq_nsmul (R := O) k z.val)
    _ = E (x ^ k) := (show Multiplicative.ofAdd (k • z) = (E x) ^ k from rfl).trans (map_pow E x k).symm

/-- The integral relative Frobenius of a polarized formal module has multiplier
`p ^ m` for the scalar-power torsion polarization. -/
theorem frobeniusHom_isTorsionSimilitude [Fact p.Prime] (P : TorsionPrincipalPolarization hM) :
    (M.frobeniusHom p m θ hθ).IsTorsionSimilitude P (P.baseChange θ) ((p : O) ^ m) := by
  intro n T x y
  let e := P.toTorsionCartierDuality
  let pair : (T ⟶ (hM.torsionSchemeInclusions.obj n).X) →* (T ⟶ (Gm Base).X) :=
    MonoidHom.mk' (fun z => e.pairing n z y) (fun z w => e.pairing_mul_left n z w y)
  have h := e.frobenius_pairing hM m θ hθ n T x y
  change (e.baseChange θ).pairing n _ _ = e.pairing n _ y
  rw [h, ← Nat.cast_pow, scalarTorsionSchemeMap_natCast_points]
  exact (map_pow pair x (p ^ m)).symm

end Langlands.FormalGroup.ModuleLaw
