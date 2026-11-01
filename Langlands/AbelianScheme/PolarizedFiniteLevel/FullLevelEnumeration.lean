import Langlands.AbelianScheme.PolarizedFiniteLevel.FibreDetection

/-! # Enumeration of actual torsion by a supplied ordered full level -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S S' : Scheme.{u}} {A B : AbelianScheme S} {g n : ℕ}

/-- All linear combinations of an ordered tuple, as actual global torsion sections. -/
def enumerateTuple (v : SectionTuple A g n) :
    (Fin (2 * g) → ZMod n) →ₗ[ZMod n] Level A.toGrp (Over.mk (𝟙 S)) n :=
  Fintype.linearCombination (ZMod n) v

@[simp] theorem enumerateTuple_single (v : SectionTuple A g n) (i : Fin (2 * g)) :
    enumerateTuple v (Pi.single i 1) = v i := by
  simp [enumerateTuple]

/-- Restriction of the global enumeration is the prescribed fibre coordinate map. -/
theorem FullLevel.enumerateTuple_fibre (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Fin (2 * g) → ZMod n) :
    levelRestrict A.toGrp (Over.homMk s (by simp)) n (enumerateTuple v.sections a) =
      v.fibreCoordinates K s a := by
  rw [FullLevel.fibreCoordinates_apply]
  simp only [enumerateTuple, Fintype.linearCombination_apply, map_sum, ZMod.map_smul,
    fibreTuple]

/-- The restricted enumeration is bijective on every geometric fibre. -/
theorem FullLevel.enumerateTuple_fibre_bijective (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    Function.Bijective (fun a : Fin (2 * g) → ZMod n =>
      levelRestrict A.toGrp
        (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) n
        (enumerateTuple v.sections a)) := by
  simpa only [v.enumerateTuple_fibre] using (v.fibreCoordinates K s).bijective

/-- Enumeration commutes with every actual abelian-scheme homomorphism. -/
theorem enumerateTuple_map (v : SectionTuple A g n) (f : A ⟶ B)
    (a : Fin (2 * g) → ZMod n) :
    enumerateTuple (mapTuple f v) a =
      levelHomLinear f (Over.mk (𝟙 S)) n (enumerateTuple v a) := by
  simp [enumerateTuple, Fintype.linearCombination_apply, mapTuple]

/-- Enumeration commutes with arbitrary actual base change. -/
theorem enumerateTuple_pullback (v : SectionTuple A g n) (b : S' ⟶ S)
    (a : Fin (2 * g) → ZMod n) :
    levelBaseChangeLinear A.toGrp b (Over.mk (𝟙 S')) n
        (enumerateTuple (pullbackTuple b v) a) =
      levelRestrict A.toGrp (Over.homMk b (by simp)) n (enumerateTuple v a) := by
  simp only [enumerateTuple, Fintype.linearCombination_apply, map_sum, map_smul,
    ZMod.map_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (levelBaseChange b A.toGrp (Over.mk (𝟙 S')) n).apply_symm_apply _

/-- The enumerated point as an actual global section of the torsion scheme. -/
def torsionSection (v : SectionTuple A g n) (a : Fin (2 * g) → ZMod n) :
    Over.mk (𝟙 S) ⟶ (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X :=
  Additive.toMul ((kernelLevelEquiv A.toGrp (Over.mk (𝟙 S)) n).symm
    (enumerateTuple v a))

/-- The actual enumerated section has exactly the asserted geometric coordinates. -/
theorem FullLevel.torsionSection_fibre (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (a : Fin (2 * g) → ZMod n) :
    kernelLevelEquiv A.toGrp (Over.mk s) n
        (Additive.ofMul ((Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) ≫
          torsionSection v.sections a)) =
      v.fibreCoordinates K s a := by
  rw [← v.enumerateTuple_fibre K s]
  simpa only [torsionSection, AddEquiv.apply_symm_apply] using
      (levelRestrict_kernelLevelEquiv A.toGrp
        (Over.homMk s (by simp) : Over.mk s ⟶ Over.mk (𝟙 S)) n
        ((kernelLevelEquiv A.toGrp (Over.mk (𝟙 S)) n).symm
          (enumerateTuple v.sections a))).symm

/-- Every geometric point of the actual torsion scheme has a unique coefficient tuple. -/
theorem FullLevel.existsUnique_torsionSection (v : FullLevel A g n)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (x : Over.mk s ⟶ (GroupScheme.kernel (GroupScheme.multiplication A.toGrp (n : ℤ))).X) :
    ∃! a : Fin (2 * g) → ZMod n,
      (Over.homMk s (by simp)) ≫ torsionSection v.sections a = x := by
  let y := kernelLevelEquiv A.toGrp (Over.mk s) n (Additive.ofMul x)
  refine ⟨(v.fibreCoordinates K s).symm y, ?_, ?_⟩
  · apply Additive.ofMul.injective
    apply (kernelLevelEquiv A.toGrp (Over.mk s) n).injective
    rw [v.torsionSection_fibre, LinearEquiv.apply_symm_apply]
  · intro a ha
    apply (v.fibreCoordinates K s).injective
    rw [LinearEquiv.apply_symm_apply, ← v.torsionSection_fibre, ha]

end Langlands.AbelianScheme.PolarizedFiniteLevel
