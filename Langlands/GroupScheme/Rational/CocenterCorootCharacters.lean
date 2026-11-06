import Langlands.GroupScheme.Torus.CorootCharacterComparison
import Langlands.GroupScheme.Torus.MaximalSubgroupKernelComparison
import Langlands.GroupScheme.Derived.CocenterQuotientStructuralReduction
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanNecessity
import Langlands.GroupScheme.FieldSeparatedProof

/-! # Actual cocenter characters from compatible derived tori -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {M D : GroupScheme (Spec (CommRingCat.of k))}
    {S T Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A supplied fppf cocenter quotient is surjective on integral cocharacters
of a split torus when the derived product is surjective and its full
intersection with that torus is a torus. -/
theorem cocenter_cocharacter_surjective_of_product_of_intersection
    (d : D ⟶ M) (hd : IsDerivedSubgroup d) (t : T.toGrp ⟶ M)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hT : IsSplitTorus T.toGrp) (hQ : IsSplitTorus Q.toGrp)
    (hprod : Surjective (subgroupProductMap d t).left)
    (hI : IsTorus (subgroupIntersection t d)) :
    Function.Surjective (fun ν : cocharacterLattice T =>
      ν ≫ (Additive.ofMul (t ≫ q) : T ⟶ Q)) := by
  let f : T ⟶ Q := Additive.ofMul (t ≫ q)
  let : IsSeparated Q.toGrp.X.hom := fieldSeparated k Q.toGrp
  have hsurj : Surjective (t ≫ q).hom.hom.left :=
    hd.surjective_comp_of_surjective_product t q hprod hq.2.1
  let : Epi (CommGroupScheme.groupHom f) :=
    hT.isTorus.epi_of_surjective_hom hQ.isTorus (t ≫ q) hsurj
  have hK : IsTorus (kernel (t ≫ q)) :=
    isTorus_kernel_comp_of_isTorus_intersection t d q hd.1 hq.2.2.2 hI
  let : Smooth (kernel (CommGroupScheme.groupHom f)).X.hom := hK.smooth
  let : ConnectedSpace (kernel (CommGroupScheme.groupHom f)).X.left := hK.connectedSpace
  exact hT.cocharacter_surjective_of_smooth_connected_kernel hQ f

namespace characterLattice

/-- Actual cocenter pullback identifies the quotient character lattice with
a selected coroot annihilator. Full-intersection geometry and an actual
semisimple subgroup datum discharge the lattice exactness and finite-index
premises; product surjectivity and the coroot-span comparison remain explicit. -/
def cocenterCorootAnnihilatorEquiv
    (d : D ⟶ M) (hd : IsDerivedSubgroup d) (hD : IsSemisimple D)
    (t : T.toGrp ⟶ M) (ht : IsClosedSubgroup t)
    (a : S.toGrp ⟶ D) (ha : IsMaximalTorus a) (φ : S ⟶ T)
    (hcomp : CommGroupScheme.groupHom φ ≫ t = a ≫ d)
    (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q)
    (hT : IsSplitTorus T.toGrp) (hS : IsSplitTorus S.toGrp)
    (hQ : IsSplitTorus Q.toGrp)
    (hprod : Surjective (subgroupProductMap d t).left)
    (hI : IsTorus (subgroupIntersection t d))
    {J : Type v} {K : Type w}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (R : RootDatum K (characterLattice S) (cocharacterLattice S))
    (s : Set J) (hP : P.toLinearMap = latticePairing T)
    (hR : haveI := hD.isConnectedReductive.isAffineHom
      IsRootDatumOf a R)
    (hmap : (R.corootSpan ℤ).map (RealTorusSpace.cocharacterMapInt φ) =
      Submodule.span ℤ (P.coroot '' s)) :
    characterLattice Q ≃ₗ[ℤ] Langlands.RootDatum.corootAnnihilator P s := by
  let : IsAffineHom D.X.hom := hD.isConnectedReductive.isAffineHom
  let : Smooth D.X.hom := hD.isConnectedReductive.smooth
  let : Finite K := hR.finite_index hS
  let : Module.Finite ℤ (characterLattice S) := hS.finite_characterLattice
  let : Finite (cocharacterLattice S ⧸ R.corootSpan ℤ) :=
    R.finite_quotient_rootSpan_iff_corootSpan.mp
      (hD.finite_quotient_rootSpan hS ha.2.1 hR)
  let : (latticePairing Q).IsPerfPair :=
    CocharacterUniformizer.latticePairing_isPerfPair k Q hQ
  exact corootAnnihilatorEquivOfComparison P R s
    (Additive.ofMul (t ≫ q) : T ⟶ Q) φ hP
    (cocenter_cocharacter_surjective_of_product_of_intersection
      d hd t q hq hT hQ hprod hI)
    (cocharacter_comp_eq_zero_iff_of_maximalSubgroupTorus
      t d a φ q ht hd.1 ha hcomp hI hq.2.2.2) hmap

end characterLattice

end Langlands.GroupScheme
