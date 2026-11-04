import Langlands.GroupScheme.Nilpotent.Basic
import Langlands.GroupScheme.Nilpotent.TorusDescent
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Rational.UnipotentPointsNilpotent
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Nilpotence of central extensions on all test schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {G H : GroupScheme S} {p : G ⟶ H}

/-- The kernel of the point homomorphism of a central-kernel map is central
over every relative scheme test. -/
theorem IsCentral.pointKernel_le_center (hp : IsCentral (kernelι p))
    (T : Over S) :
    (((yonedaGrp.map p).app (op T)).hom).ker ≤ Subgroup.center (T ⟶ G.X) := by
  intro x hx
  have hc := (isCentral_kernelι_iff p).1 hp T x hx
  exact Subgroup.mem_center_iff.2 fun y => (commute_of_mem_center hc y).eq.symm

/-- Nilpotence reflects along any homomorphism with central scheme kernel.
Surjectivity on the point groups is unnecessary. -/
theorem isNilpotent_points_of_isCentral_kernelι (hp : IsCentral (kernelι p))
    (T : Over S) [Group.IsNilpotent (T ⟶ H.X)] :
    Group.IsNilpotent (T ⟶ G.X) := by
  let f : (T ⟶ G.X) →* (T ⟶ H.X) :=
    { toFun := fun x => x ≫ p.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun x y => MonObj.mul_comp x y _ }
  exact Subgroup.isNilpotent_of_ker_le_center f (hp.pointKernel_le_center T)

end Base

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A central kernel increases an all-test lower-central-series bound by at
most one, including for nonreduced tests. -/
theorem HasUniformNilpotentPoints.of_isCentral_kernelι
    {d : ℕ} (hH : HasUniformNilpotentPoints H d) (p : G ⟶ H)
    (hp : IsCentral (kernelι p)) : HasUniformNilpotentPoints G (d + 1) := by
  intro T
  let f : (T ⟶ G.X) →* (T ⟶ H.X) :=
    { toFun := fun x => x ≫ p.hom.hom
      map_one' := MonObj.one_comp _
      map_mul' := fun x y => MonObj.mul_comp x y _ }
  apply Subgroup.lowerCentralSeries_succ_eq_bot
  apply le_trans _ (show f.ker ≤ Subgroup.center (T ⟶ G.X) from
    hp.pointKernel_le_center T)
  apply (Subgroup.map_eq_bot_iff (f := f) _).1
  rw [Subgroup.map_lowerCentralSeries, ← le_bot_iff]
  exact (hH T) ▸ Subgroup.lowerCentralSeries_mono d le_top

/-- Geometric nilpotence reflects along a map with central scheme kernel.
Neither group needs to be smooth or connected. -/
theorem IsNilpotentGroupScheme.of_isCentral_kernelι
    (hH : IsNilpotentGroupScheme H) (p : G ⟶ H)
    (hp : IsCentral (kernelι p)) : IsNilpotentGroupScheme G := by
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  have hc : IsCentral (kernelι (B.map p)) := by
    have hc := (hp.baseChange b).comp (kernelBaseChangeIso b p).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc
  let : Group.IsNilpotent
      (Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶ (B.obj H).X) := hH
  exact isNilpotent_points_of_isCentral_kernelι hc _

/-- A map with central scheme kernel and an affine finite-type unipotent
target gives uniform nilpotence on every test of its source. -/
theorem exists_hasUniformNilpotentPoints_of_isCentral_kernelι_of_isUnipotent
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (p : G ⟶ H) (hp : IsCentral (kernelι p)) (hH : IsUnipotent H) :
    ∃ d, HasUniformNilpotentPoints G d := by
  obtain ⟨d, hd⟩ := exists_hasUniformNilpotentPoints_of_isUnipotent hH
  exact ⟨d + 1, hd.of_isCentral_kernelι p hp⟩

/-- In particular, the source of such a map is geometrically nilpotent. -/
theorem isNilpotentGroupScheme_of_isCentral_kernelι_of_isUnipotent
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (p : G ⟶ H) (hp : IsCentral (kernelι p)) (hH : IsUnipotent H) :
    IsNilpotentGroupScheme G := by
  obtain ⟨d, hd⟩ :=
    exists_hasUniformNilpotentPoints_of_isCentral_kernelι_of_isUnipotent p hp hH
  exact hd.isNilpotentGroupScheme

end Langlands.GroupScheme
