import Langlands.Global.AdelicNormOneSectionCompactCover
import Langlands.GroupScheme.Rational.StandardMinimalLeviStructure
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Compact norm-one representatives for split minimal parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Standard

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hmax : IsMaximalTorus i)

/-- When the maximal split torus is a maximal torus, it is isomorphic to the
actual canonical minimal standard Levi, compatibly with their original inclusions. -/
def splitMinimalLeviIso : T.toGrp ≅ leviScheme i ν ∅ := by
  have hT : (standardLevi i ν ∅).IsRepresentedBy i := by
    have : IsClosedImmersion i.hom.hom.left := hmax.2.1
    refine ⟨Over.mono_of_mono_left _, ?_⟩
    rw [standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν,
      maximalTorusCentralizer F G hG T i hmax]
  exact hT.isoOfIsRepresentedBy (isRepresentedBy_leviHom i ν ∅)

@[simp] theorem splitMinimalLeviIso_hom_comp :
    (splitMinimalLeviIso i ν hG hi hν hmax).hom ≫ leviHom i ν ∅ = i := by
  exact SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

/-- The existing standard-Levi torus factor is exactly the canonical isomorphism. -/
theorem splitMinimalLeviIso_hom :
    (splitMinimalLeviIso i ν hG hi hν hmax).hom =
      standardLeviTorusFactor i ν ∅ (isRepresentedBy_leviHom i ν ∅) := by
  apply (isRepresentedBy_leviHom i ν ∅).hom_ext
  rw [splitMinimalLeviIso_hom_comp, standardLeviTorusFactor_comp]

include hG hi hν hmax

/-- The actual canonical minimal standard Levi of a split group is a split torus. -/
theorem isSplitTorus_emptyLevi_of_maximalTorus :
    IsSplitTorus (leviScheme i ν ∅) :=
  IsSplitTorus.of_iso (splitMinimalLeviIso i ν hG hi hν hmax).symm hi.1.1

end Langlands.GroupScheme.Standard

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hmax : IsMaximalTorus i)

include hG hi hν hmax

/-- Compact norm-one representatives for the actual minimal standard Levi of a split group. -/
theorem hasCompactNormOneRationalCover_emptyLevi_of_maximalTorus :
    HasCompactNormOneRationalCover (Standard.leviScheme i ν ∅) :=
  hasCompactNormOneRationalCover_of_isSplitTorus F _
    (Standard.isSplitTorus_emptyLevi_of_maximalTorus i ν hG hi hν hmax)

/-- The actual canonical minimal standard parabolic of a split connected reductive group
has compact rational representatives in its full character-norm-one subgroup. This uses
no compactness or fundamental-set theorem for the ambient reductive group. -/
theorem hasCompactNormOneRationalCover_emptyParabolic_of_maximalTorus :
    HasCompactNormOneRationalCover (Standard.parabolicScheme i ν ∅) :=
  hasCompactNormOneRationalCover_of_splitTorusLevi
    (Standard.isRationalLeviSubgroup_empty i ν hG hi hν)
    (Standard.isSplitTorus_emptyLevi_of_maximalTorus i ν hG hi hν hmax)

end Langlands.Global.AdelicGroupPoints
