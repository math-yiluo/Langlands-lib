import Langlands.Representation.Induction.Definitions
import Langlands.Representation.Jacquet.Coinvariants
import Mathlib.Basic.Complex.Basic

open CategoryTheory

namespace Langlands.Induction

universe uG uV uW

section Map

variable {G : Type uG} [Group G]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The actual coinvariant map, bundled with its descended ambient equivariance. -/
noncomputable def normalCoinvariantsMap (N : Subgroup G) [N.Normal]
    {rho : Representation ℂ G V} {tau : Representation ℂ G W}
    (T : rho.IntertwiningMap tau) :
    (rho.toCoinvariants N).IntertwiningMap (tau.toCoinvariants N) where
  toLinearMap := Representation.Coinvariants.map _ _ (Jacquet.restrictMap T N)
  isIntertwining' g := by
    apply Representation.Coinvariants.hom_ext
    ext v
    change Representation.Coinvariants.mk _ (T (rho g v)) =
      Representation.Coinvariants.mk _ (tau g (T v))
    exact congrArg (Representation.Coinvariants.mk _)
      (Representation.IntertwiningMap.isIntertwining rho tau T g v)

end Map

/-- Canonical, natural interchange of compact induction and normal-subgroup
coinvariants when the normal subgroup lies in the inducing subgroup. -/
def CompactInductionNormalCoinvariants : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G],
    (∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ (H N : Subgroup G) [N.Normal],
      IsClosed (H : Set G) → IsClosed (N : Set G) → N ≤ H →
      ∃ e : ∀ A : Langlands.SmoothRep.{0, uG, uV} ℂ H,
        ((compactInduced H A.representation).toCoinvariants N).Equiv
          (compactInduced H (A.representation.toCoinvariants (N.subgroupOf H))),
        (∀ (A : Langlands.SmoothRep.{0, uG, uV} ℂ H)
            (f : CompactFunctions H A.representation) (g : G),
          eval H (A.representation.toCoinvariants (N.subgroupOf H))
              (e A (Representation.Coinvariants.mk
                ((compactInduced H A.representation).comp N.subtype) f)).val g =
            Representation.Coinvariants.mk
              (A.representation.comp (N.subgroupOf H).subtype)
              (eval H A.representation f.val g)) ∧
        (∀ (A B : Langlands.SmoothRep.{0, uG, uV} ℂ H) (T : A ⟶ B)
            (q : Representation.Coinvariants
              ((compactInduced H A.representation).comp N.subtype)),
          e B (Representation.Coinvariants.map _ _
              (Jacquet.restrictMap
                (compactInducedMap H (Langlands.SmoothRep.hom T)) N) q) =
            compactInducedMap H
              (normalCoinvariantsMap (N.subgroupOf H)
                (Langlands.SmoothRep.hom T)) (e A q))

end Langlands.Induction
