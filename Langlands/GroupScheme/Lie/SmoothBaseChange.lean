import Langlands.GroupScheme.Lie.FiniteLocalFrames
import Langlands.AbelianScheme.CotangentBaseChangeProof
import Langlands.AbelianScheme.CotangentBaseChangeNaturalityProof
import Langlands.AlgebraicGeometry.ModuleDualPullbackLocalFree

/-! # Canonical Lie-sheaf base change for smooth group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
open Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    (hG : Smooth G.X.hom)

/-- The actual Lie sheaf of any smooth group scheme commutes with arbitrary
base change. -/
def smoothLieBaseChangeIso :
    (pullback b).obj G.Lie ≅ ((baseChange b).obj G).Lie := by
  letI : IsIso (cotangentBaseChangeMap b G) := cotangentBaseChangeIsIso S T b G
  letI : IsIso (dualPullbackComparison b G.cotangentAtIdentity) :=
    isIso_dualPullbackComparison_of_localGeneratorsData b
      (G.cotangentFiniteLocalBasisData hG)
  exact asIso (dualPullbackComparison b G.cotangentAtIdentity) ≪≫
    (asIso (dualMap (cotangentBaseChangeMap b G))).symm

/-- The comparison is characterized by the actual cotangent comparison and the
canonical dual-pullback map. -/
@[reassoc]
theorem smoothLieBaseChangeIso_characterization :
    (smoothLieBaseChangeIso b G hG).hom ≫ dualMap (cotangentBaseChangeMap b G) =
      dualPullbackComparison b G.cotangentAtIdentity := by
  let : IsIso (cotangentBaseChangeMap b G) := cotangentBaseChangeIsIso S T b G
  simp [smoothLieBaseChangeIso]

/-- The cotangent/dual characterization determines the actual Lie comparison. -/
theorem smoothLieBaseChangeIso_unique
    (ell : (pullback b).obj G.Lie ≅ ((baseChange b).obj G).Lie)
    (hell : ell.hom ≫ dualMap (cotangentBaseChangeMap b G) =
      dualPullbackComparison b G.cotangentAtIdentity) :
    ell = smoothLieBaseChangeIso b G hG := by
  let : IsIso (cotangentBaseChangeMap b G) := cotangentBaseChangeIsIso S T b G
  apply Iso.ext
  apply (cancel_mono (dualMap (cotangentBaseChangeMap b G))).mp
  rw [hell, smoothLieBaseChangeIso_characterization]

/-- The canonical Lie comparison is natural in every homomorphism between
smooth group schemes. -/
@[reassoc]
theorem smoothLieBaseChangeIso_naturality {H : GroupScheme S}
    (hH : Smooth H.X.hom) (f : G ⟶ H) :
    (pullback b).map (lieMap f) ≫ (smoothLieBaseChangeIso b H hH).hom =
      (smoothLieBaseChangeIso b G hG).hom ≫ lieMap ((baseChange b).map f) := by
  let : IsIso (cotangentBaseChangeMap b H) := cotangentBaseChangeIsIso S T b H
  have hd := congrArg (fun k => dualMap k) (cotangentBaseChangeMap_naturality b f)
  simp only [dualMap_comp] at hd
  change dualMap (cotangentBaseChangeMap b G) ≫
      dualMap ((pullback b).map (cotangentMap f)) =
    lieMap ((baseChange b).map f) ≫ dualMap (cotangentBaseChangeMap b H) at hd
  apply (cancel_mono (dualMap (cotangentBaseChangeMap b H))).mp
  simp only [Category.assoc]
  rw [smoothLieBaseChangeIso_characterization, ← hd, ← Category.assoc,
    smoothLieBaseChangeIso_characterization]
  exact dualPullbackComparison_naturality b (cotangentMap f)

end Langlands.GroupScheme
