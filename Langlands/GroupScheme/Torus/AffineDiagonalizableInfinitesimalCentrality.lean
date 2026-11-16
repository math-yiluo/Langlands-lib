import Langlands.GroupScheme.Torus.DiagonalizableInfinitesimalCentrality
import Langlands.GroupScheme.AffineHopfCoordinates
import Langlands.GroupScheme.CorepresentedComultiplication
import Langlands.GroupScheme.CentralIsogeny.BaseChange
import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange

/-! # Nilpotent centrality for diagonalizable sources and affine targets -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AffineDiagonalizableInfinitesimalCentrality

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
  [IsAffine G.X.left]

set_option backward.isDefEq.respectTransparency false in
/-- An arbitrary affine target can be replaced by its coordinate Hopf spectrum. -/
theorem isCentral_of_hopfSpec_source
    {N : Type u} [AddCommGroup N]
    (i : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R N)) ⟶ G)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  let e := AffineCoordinates.hopfSpecIso G
  let π : AffineCoordinates.hopfAlgebra G ⟶ Diagonalizable.hopfAlgebra R N :=
    (hopfSpec.fullyFaithful.preimage (i ≫ e.inv)).unop
  have hπ : (hopfSpec R).map π.op = i ≫ e.inv :=
    hopfSpec.fullyFaithful.map_preimage _
  have hcπ : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map
      ((hopfSpec R).map π.op)) := by
    rw [hπ, Functor.map_comp]
    exact hc.comp_iso
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).mapIso e.symm)
  have h := (DiagonalizableInfinitesimalCentrality.isCentral_of_nilpotent_quotient
    π I hI hcπ).comp_iso e
  simpa only [hπ, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- A supplied standard diagonalizable presentation suffices; the source itself
need not be given as a Hopf spectrum. -/
theorem isCentral_of_diagonalizable_presentation
    {N : Type u} [AddCommGroup N]
    (e : (Diagonalizable.groupScheme R N).toGrp ≅ H) (i : H ⟶ G)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  let d := Diagonalizable.hopfSpecIso R N ≪≫ e
  have hd : IsCentral
      ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map (d.hom ≫ i)) := by
    rw [Functor.map_comp]
    exact hc.comp _
  have h := (isCentral_of_hopfSpec_source (d.hom ≫ i) I hI hd).comp d.inv
  simpa only [Iso.inv_hom_id_assoc] using h

/-- A relatively diagonalizable source over an affine base has centrality lifted
from any nilpotent quotient of the base ring. -/
theorem isCentral_of_isDiagonalizable
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) (i : H ⟶ G)
    (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    IsCentral i := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := hH
  let d : (Diagonalizable.groupScheme R N).toGrp ≅ H :=
    (Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec R)) N).symm ≪≫ e.symm
  exact isCentral_of_diagonalizable_presentation d i I hI hc

/-- The unchanged monomorphic source, equipped with commutativity obtained from
the lifted centrality. -/
def commGroupSchemeOfNilpotentQuotient
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) (i : H ⟶ G)
    [Mono i.hom.hom] (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    CommGroupScheme (Spec R) :=
  (isCentral_of_isDiagonalizable hH i I hI hc).commGroupScheme

@[simp]
theorem commGroupSchemeOfNilpotentQuotient_toGrp
    (hH : RelativeMultiplicativeType.IsDiagonalizable H) (i : H ⟶ G)
    [Mono i.hom.hom] (I : Ideal R) (hI : IsNilpotent I)
    (hc : IsCentral ((GroupScheme.baseChange (Spec.algebraMap R (R ⧸ I))).map i)) :
    (commGroupSchemeOfNilpotentQuotient hH i I hI hc).toGrp = H := rfl

end Langlands.GroupScheme.AffineDiagonalizableInfinitesimalCentrality
