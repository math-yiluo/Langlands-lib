import Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.AlgClosedCore
import Langlands.GroupScheme.Reductive.SemisimpleRepresentationFieldExtensionStatement
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.AffineLinearEmbeddingProof

/-! # Semisimple representations and the identity component over a field of characteristic zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SemisimpleIdentityComponent

open MatrixRepresentation IdentityComponent

variable {k : Type u} [Field k]

/-- Base change of a closed-subgroup matrix representation is a closed-subgroup matrix
representation. -/
theorem isClosedSubgroup_baseChange {R' : CommRingCat.{u}}
    {G : GroupScheme (Spec (CommRingCat.of k))} {n : Type} [Fintype n] [DecidableEq n]
    {ψ : MatrixRepresentation G n} (hψ : IsClosedSubgroup ψ)
    (b : Spec R' ⟶ Spec (CommRingCat.of k)) :
    IsClosedSubgroup (ψ.baseChange b) := by
  have h := hψ.baseChange b
  let : IsClosedImmersion ((GroupScheme.baseChange b).map ψ).hom.hom.left := h
  unfold IsClosedSubgroup
  rw [MatrixRepresentation.baseChange, Grp.comp_hom_hom, Over.comp_left]
  have : IsIso (GeneralLinear.baseChangeIso n b).hom.hom.hom.left := by
    have : IsIso (GeneralLinear.baseChangeIso n b).hom.hom.hom :=
      ⟨⟨(GeneralLinear.baseChangeIso n b).inv.hom.hom,
        by rw [← Grp.comp_hom_hom, Iso.hom_inv_id]; rfl,
        by rw [← Grp.comp_hom_hom, Iso.inv_hom_id]; rfl⟩⟩
    exact (inferInstance : IsIso ((Over.forget _).map (GeneralLinear.baseChangeIso n b).hom.hom.hom))
  infer_instance

variable [CharZero k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- The base change of `G` to an algebraic closure of `k`. -/
abbrev geometricGroup (G : GroupScheme (Spec (CommRingCat.of k))) :
    GroupScheme (Spec (CommRingCat.of (AlgebraicClosure k))) :=
  (GroupScheme.baseChange (toAlgebraicClosure k)).obj G

instance isReduced_geometricGroup : IsReduced (geometricGroup G).X.left :=
  Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
    (AlgebraicClosure k) (geometricGroup G).X.left (geometricGroup G).X.hom

omit [CharZero k] in
/-- Given Milne's Proposition 4.19, a matrix representation is semisimple when its base change
to an algebraic closure has semisimple rational-point representation. -/
theorem isSemisimpleStable_of_geometric_rational
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u})
    {m : Type} [Fintype m] [DecidableEq m] (ρ : MatrixRepresentation G m)
    (hρ : (ρ.baseChange (toAlgebraicClosure k)).rationalRepresentation.IsSemisimpleRepresentation) :
    ρ.IsSemisimpleStable := by
  have hK : (ρ.baseChange (toAlgebraicClosure k)).IsSemisimpleStable :=
    ((ρ.baseChange (toAlgebraicClosure k)).isSemisimpleStable_iff_rationalRepresentation).2 hρ
  exact (h419 k (AlgebraicClosure k) G m ρ).1.2 hK

/-- Given Milne's Proposition 4.19, the base change to an algebraic closure of a semisimple
matrix representation has semisimple rational-point representation (characteristic zero). -/
theorem geometric_rational_of_isSemisimpleStable
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u})
    {m : Type} [Fintype m] [DecidableEq m] (ρ : MatrixRepresentation G m)
    (hρ : ρ.IsSemisimpleStable) :
    (ρ.baseChange (toAlgebraicClosure k)).rationalRepresentation.IsSemisimpleRepresentation := by
  have hK : (ρ.baseChange (toAlgebraicClosure k)).IsSemisimpleStable :=
    (h419 k (AlgebraicClosure k) G m ρ).2.2 hρ (Or.inl inferInstance)
  exact ((ρ.baseChange (toAlgebraicClosure k)).isSemisimpleStable_iff_rationalRepresentation).1 hK

/-- **Milne 22.43, "if"**, given Proposition 4.19: if the identity component of a smooth affine
group of finite type over a field of characteristic zero is connected reductive, every matrix
representation is semisimple. -/
theorem isSemisimpleStable_of_identityComponent
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u})
    (hG : IsConnectedReductive (identityComponent G))
    {m : Type} [Fintype m] [DecidableEq m] (ρ : MatrixRepresentation G m) :
    ρ.IsSemisimpleStable := by
  have hK : IsConnectedReductive (identityComponent (geometricGroup G)) :=
    IsConnectedReductive.of_iso (baseChangeIso G (algebraMap k (AlgebraicClosure k))).symm
      (connectedReductiveFieldExtensionStatement k (AlgebraicClosure k) (identityComponent G) hG)
  apply isSemisimpleStable_of_geometric_rational h419
  exact rationalRepresentation_isSemisimple_of_identityComponent hK.isPseudoReductive _

/-- **Milne 22.43, "only if"**, given Theorem 22.42 and Proposition 4.19: if every matrix
representation of a smooth affine group of finite type over a field of characteristic zero is
semisimple, its identity component is connected reductive. -/
theorem identityComponent_isConnectedReductive
    (h22 : CharZeroReductiveSemisimpleRepresentationStatement.{u})
    (h419 : SemisimpleRepresentationFieldExtensionStatement.{u})
    (h : ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), ρ.IsSemisimpleStable) :
    IsConnectedReductive (identityComponent G) := by
  obtain ⟨N, ψ, hψ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have hK : IsConnectedReductive (identityComponent (geometricGroup G)) :=
    identityComponent_isConnectedReductive_of_faithful h22 (ψ.baseChange (toAlgebraicClosure k))
      (isClosedSubgroup_baseChange hψ _) (geometric_rational_of_isSemisimpleStable h419 ψ (h N ψ))
  apply IsConnectedReductive.of_fieldExtension (K := AlgebraicClosure k)
  exact IsConnectedReductive.of_iso (baseChangeIso G (algebraMap k (AlgebraicClosure k))) hK

end Langlands.GroupScheme.SemisimpleIdentityComponent
