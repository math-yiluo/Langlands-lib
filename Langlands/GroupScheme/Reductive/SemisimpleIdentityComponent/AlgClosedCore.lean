import Langlands.Representation.Category.SubrepresentationRange
import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.RationalBridge
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationCharZeroStatement
import Langlands.GroupScheme.IdentityComponentRationalQuotient
import Langlands.Representation.Category.NormalRestrictionSemisimplicity
import Langlands.Representation.Category.FiniteIndexSemisimplicity

/-! # Identity components and semisimple representations over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleIdentityComponent

open MatrixRepresentation IdentityComponent

variable {k : Type u} [Field k]
  {J : GroupScheme (Spec (CommRingCat.of k))} [Smooth J.X.hom] [IsAffineHom J.X.hom]
  {n : Type} [Fintype n] [DecidableEq n]

/-- Two representations of possibly different monoids with the same image have the same
semisimplicity. -/
theorem isSemisimpleRepresentation_iff_of_range_eq {M M' V : Type*} [Monoid M] [Monoid M']
    [AddCommGroup V] [Module k V] (ρ : Representation k M V) (ρ' : Representation k M' V)
    (h : Set.range ρ = Set.range ρ') :
    ρ.IsSemisimpleRepresentation ↔ ρ'.IsSemisimpleRepresentation :=
  Langlands.Weil.FiniteIndexRestrictionSemisimplicity.isSemisimpleRepresentation_iff_of_range_eq ρ ρ' h

/-- The restriction of the rational-point representation to the rational points of the
identity component has the same image as the rational-point representation of the restriction
to the identity component. -/
theorem range_rationalRepresentation_comp_rationalIdentitySubgroup
    (ρ : MatrixRepresentation J n) :
    Set.range (ρ.rationalRepresentation.comp (rationalIdentitySubgroup J).subtype) =
      Set.range (ρ.restrict (identityComponentι J)).rationalRepresentation := by
  ext T
  constructor
  · rintro ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨y, hy⟩ := (mem_rationalIdentitySubgroup J x).1 hx
    refine ⟨y, LinearMap.ext fun v => ?_⟩
    change (ρ.restrict (identityComponentι J)).rationalRepresentation y v =
      ρ.rationalRepresentation x v
    rw [rationalRepresentation_apply, rationalRepresentation_apply, rationalMatrix_restrict]
    change _ = ((ρ.rationalMatrix x : Matrix n n k)) *ᵥ v
    rw [← hy]
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y ≫ (identityComponentι J).hom.hom, y, rfl⟩, LinearMap.ext fun v => ?_⟩
    change ρ.rationalRepresentation _ v = _
    rw [rationalRepresentation_apply, rationalRepresentation_apply, rationalMatrix_restrict]
    rfl

instance finiteIndex_rationalIdentitySubgroup :
    (rationalIdentitySubgroup J).FiniteIndex :=
  @Subgroup.finiteIndex_of_finite_quotient _ _ _ (finite_rationalComponentQuotient J)

variable [IsAlgClosed k] [CharZero k]

/-- If the identity component of a smooth affine group over an algebraically closed field of
characteristic zero is pseudo-reductive, every matrix representation has semisimple
rational-point representation. -/
theorem rationalRepresentation_isSemisimple_of_identityComponent
    (hJ : IsPseudoReductive (identityComponent J)) (ρ : MatrixRepresentation J n) :
    ρ.rationalRepresentation.IsSemisimpleRepresentation := by
  have hN : Representation.IsSemisimpleRepresentation (ρ.rationalRepresentation.comp
      (rationalIdentitySubgroup J).subtype) := by
    rw [isSemisimpleRepresentation_iff_of_range_eq _ _
      (range_rationalRepresentation_comp_rationalIdentitySubgroup ρ)]
    exact reductiveCharZeroSemisimplicityStatement k (identityComponent J) hJ n
      (ρ.restrict (identityComponentι J))
  exact finiteIndexSemisimplicityAscent k _ (n → k) (rationalIdentitySubgroup J)
    ρ.rationalRepresentation hN

omit [IsAlgClosed k] [CharZero k] in
/-- A closed-subgroup matrix representation restricts to a closed-subgroup matrix
representation of the identity component. -/
theorem isClosedSubgroup_restrict_identityComponentι {N : ℕ}
    {ψ : MatrixRepresentation J (Fin N)} (hψ : IsClosedSubgroup ψ) :
    IsClosedSubgroup (ψ.restrict (identityComponentι J)) := by
  let : IsClosedImmersion ψ.hom.hom.left := hψ
  unfold IsClosedSubgroup
  change IsClosedImmersion ((identityComponentι J) ≫ ψ).hom.hom.left
  rw [Grp.comp_hom_hom, Over.comp_left]
  infer_instance

/-- Given Milne's Theorem 22.42, a smooth affine group over an algebraically closed field of
characteristic zero with a faithful matrix representation whose rational-point representation is
semisimple has connected reductive identity component. -/
theorem identityComponent_isConnectedReductive_of_faithful
    (h22 : CharZeroReductiveSemisimpleRepresentationStatement.{u}) {N : ℕ}
    (ψ : MatrixRepresentation J (Fin N)) (hψ : IsClosedSubgroup ψ)
    (hss : ψ.rationalRepresentation.IsSemisimpleRepresentation) :
    IsConnectedReductive (identityComponent J) := by
  have hN : Representation.IsSemisimpleRepresentation (ψ.rationalRepresentation.comp
      (rationalIdentitySubgroup J).subtype) :=
    finiteDimensionalNormalRestrictionSemisimplicity k _ (Fin N → k)
      (rationalIdentitySubgroup J) ψ.rationalRepresentation hss
  rw [isSemisimpleRepresentation_iff_of_range_eq _ _
    (range_rationalRepresentation_comp_rationalIdentitySubgroup ψ)] at hN
  have : IsReduced (identityComponent J).X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      (identityComponent J).X.left (identityComponent J).X.hom
  have hss' : (ψ.restrict (identityComponentι J)).IsSemisimpleStable :=
    ((ψ.restrict (identityComponentι J)).isSemisimpleStable_iff_rationalRepresentation).2 hN
  exact ((h22 k (identityComponent J) inferInstance).2).2
    ⟨N, ψ.restrict (identityComponentι J), isClosedSubgroup_restrict_identityComponentι hψ,
      hss'⟩

end Langlands.GroupScheme.SemisimpleIdentityComponent
