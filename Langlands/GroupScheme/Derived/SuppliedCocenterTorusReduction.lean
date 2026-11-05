import Langlands.GroupScheme.Derived.CocenterQuotientStatement
import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof

/-! # Every supplied cocenter quotient is a torus, conditionally on existence -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every supplied commutative fppf quotient by an actual derived subgroup
of a connected reductive group is a torus. -/
def SuppliedCocenterTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (M D : GroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ M), IsConnectedReductive M → IsDerivedSubgroup d →
    ∀ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ Q.toGrp),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q → IsTorus Q.toGrp

/-- Quotient uniqueness transports the torus property from the cocenter
provided by the existence statement to every supplied quotient. -/
theorem suppliedCocenterTorus_of_existence
    (hexists : CocenterQuotientExistenceStatement.{u}) :
    SuppliedCocenterTorusStatement.{u} := by
  intro k _ M D d hM hd Q q hq
  obtain ⟨Q₀, q₀, _, hq₀, hQ₀, _⟩ := hexists k M D d hM hd
  let : IsAffineHom M.X.hom := hM.isAffineHom
  let : IsSeparated Q.toGrp.X.hom := fieldSeparated k Q.toGrp
  let : IsSeparated Q₀.toGrp.X.hom := fieldSeparated k Q₀.toGrp
  let : QuasiCompact q.hom.hom.left := by
    have : QuasiCompact (q.hom.hom.left ≫ Q.toGrp.X.hom) := by
      rw [Over.w q.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ Q.toGrp.X.hom
  let : QuasiCompact q₀.hom.hom.left := by
    have : QuasiCompact (q₀.hom.hom.left ≫ Q₀.toGrp.X.hom) := by
      rw [Over.w q₀.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ Q₀.toGrp.X.hom
  exact IsTorus.of_iso (FppfQuotientComparison.iso hq hq₀) hQ₀

/-- Every supplied cocenter has a finite Galois splitting extension in the
universe of its ground field, under the same existence input. -/
theorem suppliedCocenter_finiteGaloisSplitting_of_existence
    (hexists : CocenterQuotientExistenceStatement.{u})
    (k : Type u) [Field k] (M D : GroupScheme (Spec (CommRingCat.of k)))
    (d : D ⟶ M) (hM : IsConnectedReductive M) (hd : IsDerivedSubgroup d)
    (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : M ⟶ Q.toGrp)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E),
      FiniteDimensional k E ∧ IsGalois k E ∧
      IsSplitTorus (GaloisPointComparison.baseChanged k E Q.toGrp) :=
  torusFiniteGaloisSplitting k Q.toGrp
    (suppliedCocenterTorus_of_existence hexists k M D d hM hd Q q hq)

end Langlands.GroupScheme
