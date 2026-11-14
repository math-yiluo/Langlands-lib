import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # Statement: central isogenies detected on geometric fibres -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A surjective homomorphism of reductive groups over an arbitrary scheme is a
central isogeny precisely when its geometric fibre kernels are finite and
central (Conrad, Proposition 3.3.10). -/
def ReductiveCentralIsogenyFiberCriterionStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : GroupScheme S),
    IsReductive G → IsReductive H →
      ∀ (f : G ⟶ H), Surjective f.hom.hom.left →
        (IsCentralIsogeny f ↔
          ∀ s : S,
            IsFinite (kernel ((GroupScheme.baseChange (geometricPoint S s)).map f)).X.hom ∧
            IsCentral (kernelι ((GroupScheme.baseChange (geometricPoint S s)).map f)))

end Langlands.GroupScheme
