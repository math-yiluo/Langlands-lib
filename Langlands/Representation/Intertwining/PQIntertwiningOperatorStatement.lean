import Langlands.Representation.Intertwining.PQRegularity
import Langlands.Representation.Category.Basic

/-! # The intertwining operator `J_{Q|P}(σ)` of a `PQ`-regular representation (Renard VII.3.4)

For represented parabolics `P = MN` and `Q = MU` of a connected reductive group with the same
Levi subgroup `M`, a split component `A_M` of `M` and a `PQ`-regular smooth representation
`σ` of `M(F)`: for every equivariant identification `e` of the subquotient
`F^{<1̄}/F^{≤1̄}(σ)` of `r_Q^G ∘ i_P^G(σ)` with `σ`, there is exactly one intertwining operator
`J : i_P^G(σ) → i_Q^G(σ)` whose value at the identity on every `f ∈ F̃^{<1̄}(σ)` is the image
of `f` under `e`. Renard's `J_{Q|P}(σ)` is the case where `e` is induced by
`f ↦ ∫_{N̄∩U} f(u) du`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.3.4, Proposition, in derived form, for represented parabolics `P = MN` and
`Q = MU` with the same Levi subgroup `M` of `G` (`l ≫ p = lQ ≫ q`) and a split component
`a : A ⟶ M`. Let `σ` be a smooth representation of `M(F)` that is `PQ`-regular, and let `e`
be an `M(F)`-equivariant linear equivalence `F^{<1̄}/F^{≤1̄}(σ) ≃ σ`. Then there is exactly one
intertwining operator `J : i_P^G(σ) → i_Q^G(σ)` such that, for every `f ∈ F̃^{<1̄}(σ)`, the
value `J(f)(1)` is `e` applied to the class of the image `f̄` of `f` in `r_Q^G ∘ i_P^G(σ)`. -/
def PQIntertwiningOperatorStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
          IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
          ∀ e : ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)).quotientObj
              (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)) σ).ρ.Equiv σ.representation,
            ∃! J : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
                ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation,
              ∀ (f : (leviInductionFunctor p l r hp hr hl hmul).obj σ),
                f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
                  (identityParabolicDoubleCoset p q)).obj σ →
                ∀ (y : (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
                    q lQ rQ hq hrQ hlQ hmulQ).obj σ)
                  (hy : y ∈ (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ
                    hmulQ (identityParabolicDoubleCoset p q)).obj σ),
                  y = Jacquet.Localization.mk
                      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
                      (pointImage (rQ ≫ q)) 1 f →
                  Induction.eval (pointImage q)
                      (inducingRepresentation
                        (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
                        (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
                        (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ))
                      (J f) 1 =
                    e (((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                        (identityParabolicDoubleCoset p q)).quotientProjection
                      (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                        (identityParabolicDoubleCoset p q)) σ).hom ⟨y, hy⟩)

end Langlands.Aubert.General.RepresentedParabolic
