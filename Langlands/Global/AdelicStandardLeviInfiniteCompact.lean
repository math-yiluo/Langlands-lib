import Langlands.Global.AdelicLeadingCuspidalComponents
import Langlands.Global.AdelicMaximalCompactFactors

/-! # The maximal infinite compact on a standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  (K : Subgroup (AdelicGroupPoints F G))

/-- A maximal adelic compact intersection on the Levi induces a maximal
intersection of the infinite compact on that Levi. -/
def StandardLeviInfiniteCompactMaximalityStatement : Prop :=
  IsMaximalCompactSubgroup F (fam.M J) (K.comap (map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom) →
    CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact (K.comap (ofInfinite F G).toMonoidHom) J)

theorem leviInfiniteCompact_isMaximal : StandardLeviInfiniteCompactMaximalityStatement fam J K := by
  intro h
  let j := fam.l J ≫ fam.p J
  have heq : fam.leviInfiniteCompact (K.comap (ofInfinite F G).toMonoidHom) J =
      (K.comap (map F (fam.M J) G j).toMonoidHom).comap (ofInfinite F (fam.M J)).toMonoidHom := by
    ext x
    change ofInfinite F G ((fam.M J).affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)) x) ∈ K ↔
      map F (fam.M J) G j (ofInfinite F (fam.M J) x) ∈ K
    rw [map_ofInfinite]
  rw [heq]
  exact h.isMaximalCompact_comap_ofInfinite

end Langlands.Global.StandardParabolicFamily
