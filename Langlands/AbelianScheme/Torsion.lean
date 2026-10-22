import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.Multiplication

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme
universe u
variable {S : Scheme.{u}}

/-- Integer torsion is the group-scheme kernel of integer multiplication. -/
def torsion (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) : Grp (Over S) :=
  kernel (multiplication G n)

/-- The canonical inclusion of the torsion subgroup scheme. -/
def torsionι (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) : torsion G n ⟶ G :=
  kernelι (multiplication G n)

instance torsion_isCommMonObj (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    IsCommMonObj (torsion G n).X :=
  kernel_isCommMonObj (multiplication G n)

instance torsionι_mono (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    Mono (torsionι G n).hom.hom := kernelι_mono (multiplication G n)

/-- The torsion scheme is the scheme fibre product with the unit section. -/
lemma torsion_isPullback_scheme (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) :
    IsPullback (torsionι G n).hom.hom.left (torsion G n).X.hom
      (multiplication G n).hom.hom.left η[G.X].left :=
  kernel_isPullback_scheme (multiplication G n)

instance torsionι_isClosedImmersion (G : Grp (Over S)) [IsCommMonObj G.X]
    [IsSeparated G.X.hom] (n : ℤ) : IsClosedImmersion (torsionι G n).hom.hom.left :=
  kernelι_isClosedImmersion (multiplication G n)

/-- The actual kernel subgroup of multiplication on all points of a test scheme. -/
def torsionPoints (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) (T : Over S) :
    Subgroup (T ⟶ G.X) :=
  (((yonedaGrp.map (multiplication G n)).app (.op T)).hom.ker)

@[simp]
lemma mem_torsionPoints (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ)
    (T : Over S) (x : T ⟶ G.X) : x ∈ torsionPoints G n T ↔ x ^ n = 1 := by
  change x ≫ (multiplication G n).hom.hom = 1 ↔ x ^ n = 1
  rw [points_multiplication]

/-- The canonical group equivalence between scheme points and integer torsion. -/
def torsionPointsEquiv (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ) (T : Over S) :
    (T ⟶ (torsion G n).X) ≃* torsionPoints G n T :=
  kernelPointsEquiv (multiplication G n) T

@[simp]
lemma torsionPointsEquiv_val (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ)
    (T : Over S) (x : T ⟶ (torsion G n).X) :
    (torsionPointsEquiv G n T x).val = x ≫ (torsionι G n).hom.hom := rfl

/-- Restriction of torsion points by precomposition of test-scheme maps. -/
def torsionPointsRestrict (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ)
    {T T' : Over S} (a : T' ⟶ T) : torsionPoints G n T →* torsionPoints G n T' :=
  kernelPointsRestrict (multiplication G n) a

lemma torsionPointsEquiv_naturality (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ)
    {T T' : Over S} (a : T' ⟶ T) (x : T ⟶ (torsion G n).X) :
    torsionPointsEquiv G n T' (a ≫ x) =
      torsionPointsRestrict G n a (torsionPointsEquiv G n T x) :=
  kernelPointsEquiv_naturality (multiplication G n) a x

/-- A section factors uniquely through the torsion inclusion exactly when killed by `n`. -/
lemma existsUnique_torsion_lift_iff (G : Grp (Over S)) [IsCommMonObj G.X] (n : ℤ)
    (T : Over S) (x : T ⟶ G.X) :
    (∃! y : T ⟶ (torsion G n).X, y ≫ (torsionι G n).hom.hom = x) ↔ x ^ n = 1 := by
  constructor
  · rintro ⟨y, rfl, _⟩
    exact (mem_torsionPoints G n T _).mp (torsionPointsEquiv G n T y).property
  · intro hx
    let z : torsionPoints G n T := ⟨x, (mem_torsionPoints G n T x).mpr hx⟩
    refine ⟨(torsionPointsEquiv G n T).symm z, ?_, ?_⟩
    · exact congrArg Subtype.val ((torsionPointsEquiv G n T).apply_symm_apply z)
    · intro y hy
      apply (torsionPointsEquiv G n T).injective
      apply Subtype.ext
      simpa only [torsionPointsEquiv_val, MulEquiv.apply_symm_apply] using hy

end Langlands.GroupScheme
