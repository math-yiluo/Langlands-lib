import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionHelpers
import Langlands.GroupScheme.Torus.ConnectedQuotientCommutative
import Langlands.Algebra.CocommutativeGradedGroupLike
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof
import Langlands.GroupScheme.Rational.PTorsionHopfCoordinates
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Mathlib.RingTheory.FiniteType

/-! # Extensions of groups of multiplicative type over a field -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

namespace CentralExtensionHopfSpec

/-- Over an algebraically closed field, a commutative affine finite-type extension of
    diagonalizable groups is diagonalizable with finitely generated characters. -/
theorem exists_iso_diagonalizable_of_commutative_extension
    {k : Type u} [Field k] [IsAlgClosed k]
    {H G K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsCommMonObj G.X]
    {N M : Type u} [AddCommGroup N] [AddCommGroup M]
    (eH0 : H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) N).toGrp)
    (eK0 : K ≅ (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp)
    (i : H ⟶ G) (hi : IsClosedSubgroup i) (p : G ⟶ K)
    (hq : IsFppfQuotient (SubgroupFunctor.range i) p) :
    ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
      Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) := by
  classical
  let R := CommRingCat.of k
  let A := AffineCoordinates.hopfAlgebra G
  let eG := AffineCoordinates.hopfSpecIso G
  let eH : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R N)) ≅ H :=
    Diagonalizable.hopfSpecIso R N ≪≫ eH0.symm
  let eK : (hopfSpec R).obj (op (Diagonalizable.hopfAlgebra R M)) ≅ K :=
    Diagonalizable.hopfSpecIso R M ≪≫ eK0.symm
  let π : A ⟶ Diagonalizable.hopfAlgebra R N :=
    (hopfSpec.fullyFaithful.preimage (eH.hom ≫ i ≫ eG.symm.hom)).unop
  let φ : Diagonalizable.hopfAlgebra R M ⟶ A :=
    (hopfSpec.fullyFaithful.preimage (eG.symm.inv ≫ p ≫ eK.symm.hom)).unop
  have hπ : (hopfSpec R).map π.op = eH.hom ≫ i ≫ eG.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hφ : (hopfSpec R).map φ.op = eG.symm.inv ≫ p ≫ eK.symm.hom :=
    hopfSpec.fullyFaithful.map_preimage _
  have hi' : IsClosedSubgroup ((hopfSpec R).map π.op) := by
    rw [hπ]
    exact IsClosedSubgroup.iso_comp eH (hi.comp_iso eG.symm)
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((hopfSpec R).map π.op))
      ((hopfSpec R).map φ.op) := by
    rw [hπ, hφ, SubgroupFunctor.range_iso_comp, SubgroupFunctor.range_comp_iso,
      ← Category.assoc]
    exact (hq.comapIso eG.symm).comp_iso eK.symm
  have hext := isExtension_diagonalizable φ π hi' hq'
  have h0 : GroupAlgebraCoaction.grade π.hom 0 ≤
      Submodule.span k {x : A | IsGroupLikeElem k x} := by
    intro a ha
    obtain ⟨b, rfl⟩ := hext.invariants a ha
    have hle : (Submodule.span k {x : AddMonoidAlgebra k M | IsGroupLikeElem k x}).map
        (φ.hom : AddMonoidAlgebra k M →ₗ[k] A) ≤
        Submodule.span k {x : A | IsGroupLikeElem k x} := by
      rw [Submodule.map_span_le]
      intro x hx
      exact Submodule.subset_span (hx.map φ.hom)
    apply hle
    refine Submodule.mem_map_of_mem ?_
    rw [AddMonoidAlgebra.span_isGroupLikeElem]
    exact Submodule.mem_top
  have : Coalgebra.IsCocomm k A := AffineCoordinates.hopfAlgebra_isCocomm G
  have hspan := GroupAlgebraCoaction.span_isGroupLikeElem_eq_top π.hom hext.surjective h0
  let eRec : A ≃ₐc[k] AddMonoidAlgebra k (Additive (GroupLike k A)) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike hspan).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv k k (GroupLike k A))
  have hft : Algebra.FiniteType k A := AffineCoordinates.algebraFiniteType G
  have hfg : AddGroup.FG (Additive (GroupLike k A)) :=
    AddMonoidAlgebra.finiteType_iff_group_fg.mp (hft.equiv eRec.toAlgEquiv)
  let e := AffineCoordinates.isoOfBialgEquiv G
    (Diagonalizable.hopfAlgebra R (Additive (GroupLike k A))) eRec
  exact ⟨Additive (GroupLike k A), inferInstance, hfg,
    ⟨e.symm ≪≫ Diagonalizable.hopfSpecIso R (Additive (GroupLike k A))⟩⟩

end CentralExtensionHopfSpec

/-- A commutative fppf extension of two multiplicative-type groups over a field
    is of multiplicative type. -/
theorem isMultiplicativeType_of_commutative_extension
    {k : Type u} [Field k] {H G K : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ G) (p : G ⟶ K) [Mono i.hom.hom]
    (hq : IsFppfQuotient (SubgroupFunctor.range i) p)
    (hH : IsMultiplicativeType H) (hK : IsMultiplicativeType K) [IsCommMonObj G.X] :
    IsMultiplicativeType G := by
  let L := AlgebraicClosure k
  let b := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let H' := (GroupScheme.baseChange b).obj H
  let G' := (GroupScheme.baseChange b).obj G
  let K' := (GroupScheme.baseChange b).obj K
  have hHL : IsMultiplicativeType H' :=
    MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k L H hH
  have hKL : IsMultiplicativeType K' :=
    MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic k L K hK
  obtain ⟨N, hN, hNfg, ⟨eH⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed H' hHL
  obtain ⟨M, hM, hMfg, ⟨eK⟩⟩ :=
    MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed K' hKL
  have hi' : IsClosedSubgroup ((GroupScheme.baseChange b).map i) :=
    (hq.isClosedSubgroup_of_field i).baseChange b
  have hq' : IsFppfQuotient (SubgroupFunctor.range ((GroupScheme.baseChange b).map i))
      ((GroupScheme.baseChange b).map p) := by
    rw [SubgroupFunctor.range_baseChangeHom]
    exact hq.baseChange b
  have : IsClosedImmersion ((GroupScheme.baseChange b).map i).hom.hom.left := hi'
  have : Mono ((GroupScheme.baseChange b).map i).hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom H'.X.hom := hHL.isAffineHom
  have : IsAffineHom K'.X.hom := hKL.isAffineHom
  have : LocallyOfFiniteType K'.X.hom := hKL.locallyOfFiniteType
  obtain ⟨hga, hgft⟩ := hq'.affine_finiteType_source ((GroupScheme.baseChange b).map i)
  let := hga
  let := hgft
  have : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have : IsCommMonObj G'.X :=
    Functor.isCommMonObj_obj (F := Over.pullback b) (M := G.X)
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ :=
    CentralExtensionHopfSpec.exists_iso_diagonalizable_of_commutative_extension eH eK
      ((GroupScheme.baseChange b).map i) hi' ((GroupScheme.baseChange b).map p) hq'
  exact ⟨L, inferInstance, inferInstance, Λ, hΛ, hfg, ⟨e⟩⟩

/-- SGA 3 IX 8.2 over every field, with arbitrary finitely generated torsion characters. -/
theorem multiplicativeTypeFieldExtension : MultiplicativeTypeFieldExtensionStatement.{u} := by
  intro k _ H G K i p hm hq
  let := hm
  have h1 : IsMultiplicativeType H → IsMultiplicativeType K →
      (IsCommMonObj G.X ∨ ConnectedSpace K.X.left) → IsMultiplicativeType G := by
    intro hH hK hc
    rcases hc with hc | hc
    · let := hc
      exact isMultiplicativeType_of_commutative_extension i p hq hH hK
    · let := hc
      let := isCommMonObj_of_connectedSpace i p hq hH hK
      exact isMultiplicativeType_of_commutative_extension i p hq hH hK
  exact ⟨h1, fun hH hK => exists_iso_diagonalizable_of_part_one i p hq h1 hH hK⟩

end Langlands.GroupScheme
