import Langlands.AlgebraicGeometry.PointTopology.AffineLineOrigin
import Langlands.AlgebraicGeometry.PointTopology.SchemePoints
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Artinian.Module

/-!
# The punctured affine line and the dual-number point
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped DualNumber

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- The basic open D(t) of the actual affine line. -/
def affineLinePuncturedOpen :
    (ringTest R (MvPolynomial Unit R)).left.Opens :=
  PrimeSpectrum.basicOpen (MvPolynomial.X ())

/-- The actual punctured affine line over the base. -/
def affineLinePuncture : Over (Spec (CommRingCat.of R)) :=
  openOver R (ringTest R (MvPolynomial Unit R)) (affineLinePuncturedOpen R)

/-- The actual open inclusion of the punctured affine line. -/
def affineLinePunctureι :
    affineLinePuncture R ⟶ ringTest R (MvPolynomial Unit R) :=
  openOverι R (ringTest R (MvPolynomial Unit R)) (affineLinePuncturedOpen R)

instance affineLinePunctureι_isOpenImmersion :
    IsOpenImmersion (affineLinePunctureι R).left := by
  change IsOpenImmersion (affineLinePuncturedOpen R).ι
  infer_instance

variable (S : Type u) [CommRing S] [Algebra R S]

/-- Containment in D(t) is a unit condition on the actual point coordinate. -/
theorem range_subset_affineLinePuncturedOpen_iff
    (p : RingPoint R (ringTest R (MvPolynomial Unit R)) S) :
    Set.range p.left ⊆ affineLinePuncturedOpen R ↔
      IsUnit (affineLinePointEquiv R S p) := by
  obtain ⟨s, rfl⟩ := (affineLinePointEquiv R S).symm.surjective p
  rw [Equiv.apply_symm_apply]
  change (Set.range (PrimeSpectrum.comap
    (MvPolynomial.aeval (R := R) (fun _ : Unit => s)).toRingHom) ⊆
      ((PrimeSpectrum.basicOpen (MvPolynomial.X () : MvPolynomial Unit R)) :
        Set (PrimeSpectrum (MvPolynomial Unit R)))) ↔ IsUnit s
  rw [Set.range_subset_iff]
  change (∀ x : PrimeSpectrum S,
    (MvPolynomial.aeval (R := R) (fun _ : Unit => s)) (MvPolynomial.X ()) ∉
      x.asIdeal) ↔ IsUnit s
  simp only [MvPolynomial.aeval_X]
  constructor
  · intro h
    by_contra hs
    obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits hs
    exact h ⟨I, hI.isPrime⟩ hsI
  · intro hs x hx
    exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hx hs)

/-- The point range of the actual puncture is exactly the unit-coordinate locus. -/
theorem range_affineLinePuncture_points :
    Set.range (fun p : RingPoint R (affineLinePuncture R) S =>
      p ≫ affineLinePunctureι R) =
        {p | IsUnit (affineLinePointEquiv R S p)} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply (range_subset_affineLinePuncturedOpen_iff R S _).mp
    exact (openPointEquiv R (ringTest R (MvPolynomial Unit R)) S
      (affineLinePuncturedOpen R) q).property
  · intro hp
    have h := (range_subset_affineLinePuncturedOpen_iff R S p).mpr hp
    exact ⟨openPointLift R (ringTest R (MvPolynomial Unit R)) S
      (affineLinePuncturedOpen R) p h,
        openPointMap_lift R (ringTest R (MvPolynomial Unit R)) S
          (affineLinePuncturedOpen R) p h⟩

variable (K : Type u) [Field K]

/-- Dual numbers over a field are Artinian: their underlying module embeds in K × K. -/
theorem dualNumber_isArtinianRing : IsArtinianRing K[ε] := by
  let : IsScalarTower K K[ε] K[ε] :=
    ⟨fun a b c => by
      change (a • b) * c = a • (b * c)
      apply TrivSqZeroExt.ext <;>
        simp [smul_eq_mul, mul_add, mul_assoc]⟩
  have h : IsArtinian K K[ε] :=
    isArtinian_of_injective
      ((TrivSqZeroExt.fstHom K K K).toLinearMap.prod (TrivSqZeroExt.sndHom K K))
      (by
        intro x y hxy
        exact TrivSqZeroExt.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  exact isArtinian_of_tower K h

/-- The actual point of the affine line with coordinate epsilon. -/
def dualNumberAffineLinePoint :
    RingPoint K (ringTest K (MvPolynomial Unit K)) K[ε] :=
  (affineLinePointEquiv K K[ε]).symm ε

@[simp] theorem dualNumberAffineLinePoint_coordinate :
    affineLinePointEquiv K K[ε] (dualNumberAffineLinePoint K) = ε :=
  (affineLinePointEquiv K K[ε]).apply_symm_apply ε

/-- The dual-number coordinate is nonzero. -/
theorem dualNumber_eps_ne_zero : (ε : K[ε]) ≠ 0 := by
  intro h
  have h' : (1 : K) = 0 := congrArg TrivSqZeroExt.snd h
  exact one_ne_zero h'

/-- The dual-number coordinate is not a unit. -/
theorem dualNumber_eps_not_isUnit : ¬ IsUnit (ε : K[ε]) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, DualNumber.fst_eps]
  exact not_isUnit_zero

end Langlands.AlgebraicGeometry.PointTopology
