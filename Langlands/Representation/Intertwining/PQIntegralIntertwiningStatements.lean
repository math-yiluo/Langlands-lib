import Langlands.Representation.Intertwining.PQIntertwiningOperatorStatement
import Langlands.GroupScheme.Rational.SubgroupRelativeRoots
import Langlands.GroupScheme.Rational.RootProductStatement
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Integral normalization and composition of the operators `J_{Q|P}(σ)` (Renard VII.3.4–VII.3.5)

For represented parabolics `P = MN` and `Q = MU` with the same Levi subgroup `M`, an opposite
parabolic `P̄ = MN̄` of `P` and a Haar measure `haar` on `N̄(F) ∩ U(F)`, the predicate
`IsIntegralIntertwiner` says that an intertwining operator `J : i_P^G(σ) → i_Q^G(σ)` satisfies
Renard's formula `J(f)(1) = ∫_{N̄∩U} f(u) du` on `F̃^{<1̄}_{PQ}(σ)`, read against every linear
form on the space of `σ`.

`PQIntegralIntertwiningOperatorStatement` is the explicit form of VII.3.4: the identification
`F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` is induced by this integral, and for `PQ`-regular `σ` there is
exactly one `J` satisfying the formula. `PQIntertwiningCompositionStatement` is part (i) of the
Proposition of VII.3.5: `J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ) = J_{P₃|P₁}(σ)` for compatible measures
when `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Predicate

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance integralAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}

/-- Renard's integral formula for an intertwining operator `J : i_P^G(σ) → i_Q^G(σ)`, with
respect to a measure `haar` on a subgroup `V` of `G(F)` (Renard: a Haar measure on `N̄ ∩ U`):
for every `f ∈ F̃^{<1̄}_{PQ}(σ)` and every linear form `ℓ` on the space of `σ`, the function
`v ↦ ℓ(f(v))` on `V` is `haar`-integrable and `ℓ(J(f)(1)) = ∫_V ℓ(f(v)) dhaar(v)`. -/
def IsIntegralIntertwiner
    (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (V : Subgroup (rationalPoints G)) [MeasurableSpace V] (haar : Measure V)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (J : letI := leviPointTopology l hl
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
        ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation) : Prop :=
  letI := leviPointTopology l hl
  ∀ f : (leviInductionFunctor p l r hp hr hl hmul).obj σ,
    f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
      (identityParabolicDoubleCoset p q)).obj σ →
    ∀ ℓ : Module.Dual ℂ σ,
      Integrable (fun x : V => ℓ (Induction.eval (pointImage p)
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x)) haar ∧
      ℓ (Induction.eval (pointImage q)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
            (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)) (J f) 1) =
        ∫ x : V, ℓ (Induction.eval (pointImage p)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
            (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x) ∂haar

end Predicate

/-- Renard VII.3.4, explicit form. Let `P = MN` and `Q = MU` be represented parabolics with
the same Levi subgroup `M` of `G` (`l ≫ p = lQ ≫ q`), let `P̄ = MN̄` be a represented parabolic
opposite to `P` (same embedded Levi, `P(F) ∩ P̄(F) = M(F)`), and let `haar` be a Haar measure on
`V = N̄(F) ∩ U(F)`.
1. For every smooth representation `σ` of `M(F)` there is an `M(F)`-equivariant linear
   equivalence `e : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` such that, for every `f ∈ F̃^{<1̄}_{PQ}(σ)`
   and every linear form `ℓ`, `v ↦ ℓ(f(v))` is `haar`-integrable on `V` and
   `ℓ(e(f̄)) = ∫_V ℓ(f(v)) dhaar(v)`.
2. For every split component `a : A → M` and every `PQ`-regular `σ`, there is exactly one
   intertwining operator `J : i_P^G(σ) → i_Q^G(σ)` with `J(f)(1) = ∫_V f(v) dhaar(v)` for all
   `f ∈ F̃^{<1̄}_{PQ}(σ)` (in the sense of `IsIntegralIntertwiner`). -/
def PQIntegralIntertwiningOperatorStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U Pb Nb : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ))
      (pb : Pb ⟶ G) (lb : M ⟶ Pb) (rb : Nb ⟶ Pb)
      (_hpb : IsParabolicSubgroup pb) (_hlb : IsRationalLeviSubgroup lb)
      (_hrb : LeviSubgroup.IsGeometricUnipotentRadical rb)
      (_hmulb : IsIso (subgroupMultiplication lb rb)),
      l ≫ p = lQ ≫ q →
      lb ≫ pb = l ≫ p →
      pointImage p ⊓ pointImage pb = pointImage (l ≫ p) →
      let V : Subgroup (rationalPoints G) := pointImage (rb ≫ pb) ⊓ pointImage (rQ ≫ q)
      ∀ [MeasurableSpace V] [BorelSpace V] (haar : Measure V) [haar.IsHaarMeasure],
        haveI := hl.isConnectedReductive.isAffineHom
        letI := leviPointTopology l hl
        (∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
          ∃ e : ((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)).quotientObj
              (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                (identityParabolicDoubleCoset p q)) σ).ρ.Equiv σ.representation,
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
                ∀ ℓ : Module.Dual ℂ σ,
                  Integrable (fun x : V => ℓ (Induction.eval (pointImage p)
                    (inducingRepresentation
                      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x)) haar ∧
                  ℓ (e (((closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                        (identityParabolicDoubleCoset p q)).quotientProjection
                      (boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
                        (identityParabolicDoubleCoset p q)) σ).hom ⟨y, hy⟩)) =
                    ∫ x : V, ℓ (Induction.eval (pointImage p)
                      (inducingRepresentation
                        (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
                        (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
                        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x) ∂haar) ∧
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
          IsSplitComponent a →
          ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
            IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
            ∃! J : ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
                ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation,
              IsIntegralIntertwiner p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ V haar σ J

/-- Renard VII.3.5, Proposition, part (i). Let `P₁ = MN₁`, `P₂ = MN₂`, `P₃ = MN₃` be
represented parabolics of `G` with the same embedded Levi subgroup `M`, let `P̄ᵢ = MN̄ᵢ` be a
represented parabolic opposite to `Pᵢ` (same embedded Levi, `Pᵢ(F) ∩ P̄ᵢ(F) = M(F)`), and let
`a : A → M` be the split component. Write `Σ(X)` for the reduced roots of `A` in the
unipotent radical of `X` (nonzero weights of `A` on its tangent space that are indivisible
roots of `A` in `G`) and `d(Pᵢ, Pⱼ) = |Σ(Pᵢ) ∩ Σ(P̄ⱼ)|`. Assume
`d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`. Write `V₁₂ = N̄₁(F) ∩ N₂(F)`,
`V₂₃ = N̄₂(F) ∩ N₃(F)` and `V₁₃ = N̄₁(F) ∩ N₃(F)`. Then:
1. for all Haar measures `haar₁₂` on `V₁₂` and `haar₂₃` on `V₂₃` there is a Haar measure
   `haar₁₃` on `V₁₃` with `∫_{V₁₃} φ = ∫_{V₂₃} ∫_{V₁₂} φ(vu) dhaar₁₂(v) dhaar₂₃(u)` for every
   continuous compactly supported `φ : G(F) → ℂ`;
2. every `P₁P₃`-regular smooth representation `σ` of `M(F)` is `P₂P₃`-regular and
   `P₁P₂`-regular, and for Haar measures `haar₁₂`, `haar₂₃`, `haar₁₃` related as in 1, the
   operators `J_{P₂|P₁}(σ)`, `J_{P₃|P₂}(σ)`, `J_{P₃|P₁}(σ)` normalized by them
   (`IsIntegralIntertwiner`) satisfy `J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ) = J_{P₃|P₁}(σ)`. -/
def PQIntertwiningCompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ P₃ N₃ Pb₁ Nb₁ Pb₂ Nb₂ Pb₃ Nb₃ : GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (p₃ : P₃ ⟶ G) (l₃ : M ⟶ P₃) (r₃ : N₃ ⟶ P₃)
      (hp₃ : IsParabolicSubgroup p₃) (hl₃ : IsRationalLeviSubgroup l₃)
      (hr₃ : LeviSubgroup.IsGeometricUnipotentRadical r₃)
      (hmul₃ : IsIso (subgroupMultiplication l₃ r₃))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (pb₂ : Pb₂ ⟶ G) (lb₂ : M ⟶ Pb₂) (rb₂ : Nb₂ ⟶ Pb₂)
      (_hpb₂ : IsParabolicSubgroup pb₂) (_hlb₂ : IsRationalLeviSubgroup lb₂)
      (_hrb₂ : LeviSubgroup.IsGeometricUnipotentRadical rb₂)
      (_hmulb₂ : IsIso (subgroupMultiplication lb₂ rb₂))
      (pb₃ : Pb₃ ⟶ G) (lb₃ : M ⟶ Pb₃) (rb₃ : Nb₃ ⟶ Pb₃)
      (_hpb₃ : IsParabolicSubgroup pb₃) (_hlb₃ : IsRationalLeviSubgroup lb₃)
      (_hrb₃ : LeviSubgroup.IsGeometricUnipotentRadical rb₃)
      (_hmulb₃ : IsIso (subgroupMultiplication lb₃ rb₃)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → l₃ ≫ p₃ = l₁ ≫ p₁ →
      lb₁ ≫ pb₁ = l₁ ≫ p₁ → lb₂ ≫ pb₂ = l₁ ≫ p₁ → lb₃ ≫ pb₃ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₂ ⊓ pointImage pb₂ = pointImage (l₁ ≫ p₁) →
      pointImage p₃ ⊓ pointImage pb₃ = pointImage (l₁ ≫ p₁) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        let rootsIn : SubgroupFunctor G → Set (characterLattice A) := fun F =>
          RelativeRoot.subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩
            RelativeRoot.indivisibleRoots (a ≫ l₁ ≫ p₁)
        let d : SubgroupFunctor G → SubgroupFunctor G → ℕ := fun F F' =>
          (rootsIn F ∩ rootsIn F').ncard
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) +
            d (SubgroupFunctor.range (r₂ ≫ p₂)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) =
          d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₃ ≫ pb₃)) →
        d (SubgroupFunctor.range (r₁ ≫ p₁)) (SubgroupFunctor.range (rb₂ ≫ pb₂)) = 1 →
        let V₁₂ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂)
        let V₂₃ : Subgroup (rationalPoints G) := pointImage (rb₂ ≫ pb₂) ⊓ pointImage (r₃ ≫ p₃)
        let V₁₃ : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₃ ≫ p₃)
        ∀ [MeasurableSpace V₁₂] [BorelSpace V₁₂] [MeasurableSpace V₂₃] [BorelSpace V₂₃]
          [MeasurableSpace V₁₃] [BorelSpace V₁₃],
          let Compatible : Measure V₁₂ → Measure V₂₃ → Measure V₁₃ → Prop :=
            fun haar₁₂ haar₂₃ haar₁₃ =>
              ∀ φ : rationalPoints G → ℂ, Continuous φ → HasCompactSupport φ →
                ∫ x : V₁₃, φ x ∂haar₁₃ =
                  ∫ u : V₂₃, ∫ w : V₁₂, φ ((w : rationalPoints G) * u) ∂haar₁₂ ∂haar₂₃
          (∀ (haar₁₂ : Measure V₁₂) (haar₂₃ : Measure V₂₃),
            haar₁₂.IsHaarMeasure → haar₂₃.IsHaarMeasure →
            ∃ haar₁₃ : Measure V₁₃, haar₁₃.IsHaarMeasure ∧ Compatible haar₁₂ haar₂₃ haar₁₃) ∧
          haveI := hl₁.isConnectedReductive.isAffineHom
          letI := leviPointTopology l₁ hl₁
          ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
            IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃ a σ →
            IsPQRegular p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃ a σ ∧
            IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ ∧
            ∀ (haar₁₂ : Measure V₁₂) (haar₂₃ : Measure V₂₃) (haar₁₃ : Measure V₁₃),
              haar₁₂.IsHaarMeasure → haar₂₃.IsHaarMeasure → haar₁₃.IsHaarMeasure →
              Compatible haar₁₂ haar₂₃ haar₁₃ →
              ∀ (J₁₂ : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
                    σ).representation.IntertwiningMap
                  ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation)
                (J₂₃ : ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj
                    σ).representation.IntertwiningMap
                  ((leviInductionFunctor p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃).obj σ).representation)
                (J₁₃ : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
                    σ).representation.IntertwiningMap
                  ((leviInductionFunctor p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃).obj σ).representation),
                IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
                    V₁₂ haar₁₂ σ J₁₂ →
                IsIntegralIntertwiner p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃
                    V₂₃ haar₂₃ σ J₂₃ →
                IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₃ l₃ r₃ hp₃ hr₃ hl₃ hmul₃
                    V₁₃ haar₁₃ σ J₁₃ →
                J₂₃.comp J₁₂ = J₁₃

end Langlands.Aubert.General.RepresentedParabolic
