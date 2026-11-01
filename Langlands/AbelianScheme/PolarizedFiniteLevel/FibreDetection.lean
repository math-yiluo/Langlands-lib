import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Detection of finite-level maps by the ordered sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open GroupScheme.Tate

variable {S : Scheme.{u}} {A B : AbelianScheme S} {g n : ℕ}

/-- Postcomposition by an actual abelian-scheme homomorphism on finite torsion,
with its canonical residue-linear structure. -/
def levelHomLinear (f : A ⟶ B) (T : Over S) (n : ℕ) :
    Level A.toGrp T n →ₗ[ZMod n] Level B.toGrp T n :=
  (levelMap T (groupHom f) n).toZModLinearMap n

@[simp] theorem levelHomLinear_apply (f : A ⟶ B) (T : Over S) (n : ℕ)
    (x : Level A.toGrp T n) :
    levelHomLinear f T n x = levelMap T (groupHom f) n x := rfl

/-- Agreement on the global ordered sections determines the induced linear map
on every geometric torsion fibre. -/
theorem FullLevel.fibreLevelMap_ext (v : FullLevel A g n) {f k : A ⟶ B}
    (h : ∀ i, levelMap (Over.mk (𝟙 S)) (groupHom f) n (v.sections i) =
      levelMap (Over.mk (𝟙 S)) (groupHom k) n (v.sections i))
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    levelHomLinear f (Over.mk s) n = levelHomLinear k (Over.mk s) n := by
  apply (v.fibreBasis K s).ext
  intro i
  simp only [FullLevel.fibreBasis_apply, levelHomLinear_apply, ← fibreTuple_map]
  exact congrArg (fun w : SectionTuple B g n => fibreTuple w s i) (funext h)

variable {P : Prerequisites.{u}} {d : ℕ} {a b : Datum P S g d n}

/-- The section equation of a polarized isomorphism is the actual tuple equation. -/
theorem PolarizedIso.mapTuple_eq (e : PolarizedIso a b) :
    mapTuple e.abelianIso.hom a.level.sections = b.level.sections := by
  funext i
  exact e.level_eq i

/-- A polarized isomorphism carries the restricted ordered tuple on each fibre. -/
theorem PolarizedIso.fibreTuple_eq (e : PolarizedIso a b)
    {K : Type u} [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (i : Fin (2 * g)) :
    levelIsoLinear e.abelianIso (Over.mk s) n (fibreTuple a.level.sections s i) =
      fibreTuple b.level.sections s i := by
  change levelMap (Over.mk s) (groupHom e.abelianIso.hom) n _ = _
  rw [← fibreTuple_map, e.mapTuple_eq]

/-- Two polarized isomorphisms have the same action on each geometric torsion fibre. -/
theorem PolarizedIso.fibreLevelIso_eq (e f : PolarizedIso a b)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    levelIsoLinear e.abelianIso (Over.mk s) n =
      levelIsoLinear f.abelianIso (Over.mk s) n := by
  apply (a.level.fibreBasis K s).ext'
  intro i
  simp only [FullLevel.fibreBasis_apply, e.fibreTuple_eq, f.fibreTuple_eq]

/-- A polarized automorphism preserving the ordered level acts as the identity
on every geometric torsion fibre. -/
theorem PolarizedIso.fibreLevelIso_eq_refl (e : PolarizedIso a a)
    (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S) :
    levelIsoLinear e.abelianIso (Over.mk s) n =
      LinearEquiv.refl (ZMod n) (Level a.abelian.toGrp (Over.mk s) n) := by
  apply (a.level.fibreBasis K s).ext'
  intro i
  simpa only [FullLevel.fibreBasis_apply, LinearEquiv.refl_apply] using
    e.fibreTuple_eq s i

end Langlands.AbelianScheme.PolarizedFiniteLevel
