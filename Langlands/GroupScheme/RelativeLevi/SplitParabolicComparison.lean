import Langlands.GroupScheme.RelativeLevi.SplitCentralizerComparison
import Langlands.GroupScheme.RelativeLevi.SplitFaceCocharacterComparison
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # Actual parabolic comparison from contracting subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]
  (χ χ' : (Gm S).toGrp ⟶ G)

/-- The limit decomposition shows that inclusions of the actual contracting and
centralizer functors force the corresponding inclusion of parabolics. -/
theorem parabolic_le_of_unipotent_centralizer_le
    (hU : unipotent χ ≤ unipotent χ') (hZ : centralizer χ ≤ centralizer χ') :
    parabolic χ ≤ parabolic χ' := by
  intro T p hp
  let g : (parabolic χ).carrier T := ⟨p, hp⟩
  have hu := unipotent_le_parabolic χ' T (hU T (mul_inv_limit_mem_unipotent χ g))
  have hz := centralizer_le_parabolic χ' T (hZ T (limit_mem_centralizer χ g))
  have hm := mul_mem hu hz
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

/-- Equal actual contracting and centralizer functors determine the parabolic
on every scheme test of a separated group scheme. -/
theorem parabolic_eq_of_unipotent_centralizer_eq
    (hU : unipotent χ = unipotent χ') (hZ : centralizer χ = centralizer χ') :
    parabolic χ = parabolic χ' :=
  le_antisymm
    (parabolic_le_of_unipotent_centralizer_le χ χ' (le_of_eq hU) (le_of_eq hZ))
    (parabolic_le_of_unipotent_centralizer_le χ' χ (le_of_eq hU.symm) (le_of_eq hZ.symm))

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.AffineRegularBorel

open LocalSplitCell

variable {R : Type u} [CommRing R] [Nontrivial R]
  {I J : Type u} [Fintype I] [Fintype J] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ))
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  (hP : IsFibrewiseRootDatumOf I G i P)
  (fam : J → (Ga R ⟶ G))
  (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a))
  (v v' : I → ℤ)
  (hU : Dynamic.unipotent (cocharacter i v) = Dynamic.unipotent (cocharacter i v'))

local instance affine_ambient : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

include hG hmax hP hfam hU in
/-- For one actual split maximal torus, equality of contracting functors forces
equality of parabolics. Root-sign detection first fixes the zero-root face. -/
theorem parabolic_eq_of_unipotent_eq :
    Dynamic.parabolic (cocharacter i v) = Dynamic.parabolic (cocharacter i v') := by
  let : P.IsReduced := hP.isReduced
  have hz (a : J) : coPairing (P.root a) v = 0 ↔ coPairing (P.root a) v' = 0 :=
    SplitParabolicFaceChart.coPairing_zero_iff_of_sameContracting hU hfam a
  have hZ := splitTorus.RelativeCocharacterCentralizer.centralizer_eq_of_zero_iff
    i P hG hmax hP v v' hz
  exact Dynamic.parabolic_eq_of_unipotent_centralizer_eq _ _ hU hZ

/-- The actual ambient-compatible isomorphism between the two affine dynamic
parabolic representatives, obtained from proved equality of subgroup functors. -/
def parabolicIsoOfUnipotentEq : borel i v ≅ borel i v' :=
  (Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i v)).isoOfIsRepresentedBy
    (show (Dynamic.parabolic (cocharacter i v)).IsRepresentedBy (inclusion i v') from by
      rw [parabolic_eq_of_unipotent_eq i P hG hmax hP fam hfam v v' hU]
      exact Dynamic.Affine.isRepresentedBy_parabolicHom (cocharacter i v'))

/-- The comparison preserves the exact specified ambient inclusion. -/
theorem parabolicIsoOfUnipotentEq_hom_comp :
    (parabolicIsoOfUnipotentEq i P hG hmax hP fam hfam v v' hU).hom ≫ inclusion i v' =
      inclusion i v :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.AffineRegularBorel
