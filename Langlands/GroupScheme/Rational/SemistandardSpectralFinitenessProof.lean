import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Finiteness of the intrinsic semistandard index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Relative-root signs of fixed-torus cocharacters distinguish the actual
semistandard triples and embed them in a finite type. -/
theorem semistandardSpectralFiniteness : SemistandardSpectralFinitenessStatement.{u} := by
  classical
  intro k _ G hG T i hi
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Finite (relativeRoots i) := (hi.isSplitSubtorus.1.finite_relativeRoots i).to_subtype
  choose ζ hζ using semistandardSpectralDynamicCoverage k G hG T i hi
  let rootSigns (p : SemistandardSpectralIndex i) (α : relativeRoots i) : Ordering :=
    compare (latticePairing T α.val (ζ p)) 0
  refine Finite.of_injective rootSigns ?_
  intro p q hpq
  obtain ⟨hP, hM, hU⟩ := relativeRootSignsDetermineDynamic k G hG T i hi (ζ p) (ζ q) (by
    intro α hα
    have hcompare : compare (latticePairing T α (ζ p)) 0 =
        compare (latticePairing T α (ζ q)) 0 :=
      congrFun hpq ⟨α, hα⟩
    simp only [← compare_ge_iff_ge (α := ℤ), ← compare_eq_iff_eq (α := ℤ),
      ← compare_gt_iff_gt (α := ℤ), hcompare, iff_self, and_self])
  calc
    p = SemistandardSpectralIndex.ofCocharacter hG (ζ p) := (hζ p).symm
    _ = SemistandardSpectralIndex.ofCocharacter hG (ζ q) :=
      SemistandardSpectralIndex.ofCocharacter_eq hG _ _ hP hM hU
    _ = q := hζ q

end Langlands.GroupScheme
