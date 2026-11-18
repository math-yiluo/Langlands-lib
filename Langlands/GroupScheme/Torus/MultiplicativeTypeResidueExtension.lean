import Langlands.GroupScheme.Torus.MultiplicativeTypeFieldExtensionStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeFpqcTransfer
import Langlands.GroupScheme.Torus.MultiplicativeTypeExtensionBaseChange
import Langlands.GroupScheme.Torus.AffineRelativeDiagonalizable
import Langlands.GroupScheme.FppfQuotientComparison

/-! # residue-field step for multiplicative-type extensions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ExtensionReduction

/-- A relative diagonalizable presentation over a field supplies the
field-level multiplicative-type predicate. -/
theorem fieldMultiplicativeType_of_relativeDiagonalizable
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : RelativeMultiplicativeType.IsDiagonalizable G) : IsMultiplicativeType G := by
  obtain ⟨M, hM, hfg, ⟨e⟩⟩ := hG
  let := hM
  let := hfg
  let D := (Diagonalizable.groupScheme (CommRingCat.of k) M).toGrp
  have hD : IsMultiplicativeType D :=
    ⟨k, inferInstance, inferInstance, M, inferInstance, inferInstance,
      ⟨Diagonalizable.baseChangeIso (algebraBaseMap k k) M⟩⟩
  exact IsMultiplicativeType.of_iso
    (e ≪≫ (Diagonalizable.relativeModelIso (CommRingCat.of k) M).symm) hD

/-- The field theorem applies to the target alternative on the middle group:
connectedness of the middle group implies connectedness of its surjective quotient. -/
theorem fieldMultiplicativeType_of_extension
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u})
    {k : Type u} [Field k] (N G Q : GroupScheme (Spec (CommRingCat.of k)))
    (i : N ⟶ G) (q : G ⟶ Q) (hi : Mono i.hom.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (hfib : ConnectedSpace G.X.left ∨ IsCommMonObj G.X) : IsMultiplicativeType G := by
  apply (hfield k N G Q i q hi hq).1
    (fieldMultiplicativeType_of_relativeDiagonalizable hN)
    (fieldMultiplicativeType_of_relativeDiagonalizable hQ)
  rcases hfib with hconn | hcomm
  · have := hconn
    have : Surjective q.hom.hom.left := hq.2.1
    exact Or.inr (q.hom.hom.left.surjective.connectedSpace q.hom.hom.left.continuous)
  · exact Or.inl hcomm

/-- Every middle residue fibre in a split-endpoint extension is of field-level
multiplicative type, conditional on the exact field extension theorem. -/
theorem residueFiber_fieldMultiplicativeType_of_extension
    (hfield : MultiplicativeTypeFieldExtensionStatement.{u})
    {S : Scheme.{u}} (N G Q : GroupScheme S)
    (i : N ⟶ G) (q : G ⟶ Q) (hi : Mono i.hom.hom)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q)
    (hN : RelativeMultiplicativeType.IsDiagonalizable N)
    (hQ : RelativeMultiplicativeType.IsDiagonalizable Q)
    (hfib : ConnectedOrCommutativeFibers G) (s : S) :
    IsMultiplicativeType (RelativeIdentityComponent.residueFiber G s) := by
  let b := S.fromSpecResidueField s
  let F := baseChange b
  let := hi
  have hi' : Mono (F.map i).hom.hom := by
    change Mono ((Over.pullback b).map i.hom.hom)
    infer_instance
  have hq' : RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (F.map i)) (F.map q) := by
    change RelativeRoot.IsFppfQuotient (SubgroupFunctor.range ((baseChange b).map i))
      ((baseChange b).map q)
    simpa only [SubgroupFunctor.range_baseChangeHom] using hq.baseChange b
  exact fieldMultiplicativeType_of_extension hfield (F.obj N) (F.obj G) (F.obj Q)
    (F.map i) (F.map q) hi' hq' (hN.baseChange b) (hQ.baseChange b) (hfib s)

end Langlands.GroupScheme.ExtensionReduction
