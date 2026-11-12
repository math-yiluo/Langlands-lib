import Langlands.GroupScheme.GaloisPointRational

/-! # Naturality of rational scalar extension -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- Extension of scalars on rational points commutes with homomorphisms of group schemes. -/
theorem rationalExtend_map {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    (x : rationalPoints G) :
    rationalExtend k L H (rationalPoints.map f x) =
      rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map f)
        (rationalExtend k L G x) := by
  apply (baseChangeCoeffEquiv k L H).injective
  rw [baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_rationalExtend,
    baseChangeCoeffEquiv_rationalExtend, rationalCoeffEquiv_map]
  exact DFunLike.congr_fun (G.affinePointsTarget_naturality f _) _

end Langlands.GroupScheme.GaloisPointComparison
