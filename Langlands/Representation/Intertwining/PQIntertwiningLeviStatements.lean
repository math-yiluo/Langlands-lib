import Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements

/-! # Intertwining operators and induction in stages (Renard VII.3.5 (ii)–(iii))

Parts (ii) and (iii) of the Proposition of VII.3.5 compare the integral-normalized
intertwining operators `J_{Q|P}(σ)` of `IsIntegralIntertwiner` with induction in stages
through a Levi subgroup `L ⊃ M`. Renard's "natural identification"
`i_P^G(σ) ≃ i_Q^G(i_{P∩L}^L(σ))` for a parabolic `Q = LU ⊃ P` sends `f` to `f̃` with
`f̃(g)(l) = δ_U(l)^{-1/2} f(lg)`; both statements read it through this formula.

`PQIntertwiningInnerLeviStatement` is part (ii): for `Q = LU` containing `P₁` and `P₂`,
`J^G_{P₂|P₁}(σ) = i_Q^G(J^L_{(P₂∩L)|(P₁∩L)}(σ))`. `PQIntertwiningOuterLeviStatement` is
part (iii): for a Levi `L ⊃ M` with `P₁ ∩ L = P₂ ∩ L` and `Qᵢ = PᵢL = LUᵢ`,
`J_{P₂|P₁}(σ) = J_{Q₂|Q₁}(i^L_{P₁∩L}(σ))`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VII.3.5, Proposition, part (ii). Let `P₁ = MN₁`, `P₂ = MN₂` be represented
parabolics of `G` with the same embedded Levi subgroup `M`, `P̄₁ = MN̄₁` a represented
parabolic opposite to `P₁`, and `Q = LU` a represented parabolic of `G` with
`P₁(F), P₂(F) ⊂ Q(F)`. Inside `L`, let `P₁' = MN₁'`, `P₂' = MN₂'` be represented parabolics
of `L` with the same embedded `M` (`l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁`) and
`Pᵢ'(F) = Pᵢ(F) ∩ L(F)` in `G(F)`, and `P̄₁' = MN̄₁'` a represented parabolic of `L` opposite
to `P₁'`. Let `a : A → M` be the split component, `emb : L(F) → G(F)` the embedding,
`V = N̄₁(F) ∩ N₂(F)`, `V' = N̄₁'(F) ∩ N₂'(F) ⊂ L(F)` and `c(x) = δ_U(x)^{1/2}` for
`x ∈ L(F)`. Then:
1. for every Haar measure `haar'` on `V'` there is a Haar measure `haar` on `V` with
   `∫_{V'} φ(emb x) dhaar'(x) = ∫_V φ(x) dhaar(x)` for continuous compactly supported `φ`;
2. for every smooth representation `σ` of `M(F)`:
   - every `f ∈ i_{P₁}^G(σ)` has an `f̃ ∈ i_Q^G(i_{P₁'}^L(σ))` with
     `f̃(g)(x) = c(x)⁻¹ f(emb(x) g)`;
   - if `σ` is `P₁P₂`-regular, then it is `P₁'P₂'`-regular, and for Haar measures related
     as in 1, the integral-normalized `J = J^G_{P₂|P₁}(σ)` (on `V`) and
     `J' = J^L_{P₂'|P₁'}(σ)` (on `V'`) satisfy `J'(f̃(g))(x) = c(x)⁻¹ J(f)(emb(x) g)`
     whenever `f̃(g)(x) = c(x)⁻¹ f(emb(x) g)` for all `g`, `x`: that is,
     `i_Q^G(J')(f̃) = (J f)~`. -/
def PQIntertwiningInnerLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ Pb₁ Nb₁ Q L U P₁' N₁' P₂' N₂' Pb₁' Nb₁' :
        GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → lb₁ ≫ pb₁ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      pointImage p₁ ≤ pointImage q → pointImage p₂ ≤ pointImage q →
      haveI := hlQ.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints L) := RationalPointFamily.pointTopology
      haveI := leviPoints_locallyCompactSpace q lQ hq hlQ
      haveI := leviPoints_nonarchimedeanGroup q lQ hq hlQ
      ∀ (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
        (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
        (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
        (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
        (p₂' : P₂' ⟶ L) (l₂' : M ⟶ P₂') (r₂' : N₂' ⟶ P₂')
        (hp₂' : IsParabolicSubgroup p₂') (hl₂' : IsRationalLeviSubgroup l₂')
        (hr₂' : LeviSubgroup.IsGeometricUnipotentRadical r₂')
        (hmul₂' : IsIso (subgroupMultiplication l₂' r₂'))
        (pb₁' : Pb₁' ⟶ L) (lb₁' : M ⟶ Pb₁') (rb₁' : Nb₁' ⟶ Pb₁')
        (_hpb₁' : IsParabolicSubgroup pb₁') (_hlb₁' : IsRationalLeviSubgroup lb₁')
        (_hrb₁' : LeviSubgroup.IsGeometricUnipotentRadical rb₁')
        (_hmulb₁' : IsIso (subgroupMultiplication lb₁' rb₁')),
        l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁ → l₂' ≫ p₂' = l₁' ≫ p₁' → lb₁' ≫ pb₁' = l₁' ≫ p₁' →
        pointImage p₁' ⊓ pointImage pb₁' = pointImage (l₁' ≫ p₁') →
        pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q) →
        pointImage (p₂' ≫ lQ ≫ q) = pointImage p₂ ⊓ pointImage (lQ ≫ q) →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
          IsSplitComponent a →
          let emb : rationalPoints L → rationalPoints G := rationalPoints.map (lQ ≫ q)
          let c : rationalPoints L → ℂ := fun x =>
            ((HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
                (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
                (pointImage q)
                (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ
                  hmulQ).le_normalizer
                (Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)) :
              ℂˣ) : ℂ)
          let V : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂)
          let V' : Subgroup (rationalPoints L) :=
            pointImage (rb₁' ≫ pb₁') ⊓ pointImage (r₂' ≫ p₂')
          ∀ [MeasurableSpace V] [BorelSpace V] [MeasurableSpace V'] [BorelSpace V'],
            let Compatible : Measure V' → Measure V → Prop := fun haar' haar =>
              ∀ φ : rationalPoints G → ℂ, Continuous φ → HasCompactSupport φ →
                ∫ x : V', φ (emb x) ∂haar' = ∫ x : V, φ x ∂haar
            (∀ haar' : Measure V', haar'.IsHaarMeasure →
              ∃ haar : Measure V, haar.IsHaarMeasure ∧ Compatible haar' haar) ∧
            haveI := hl₁.isConnectedReductive.isAffineHom
            letI := leviPointTopology l₁ hl₁
            ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
              let X₁ := (leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ
              let X₂ := (leviInductionFunctor p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂').obj σ
              let evalG₁ := fun (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
                  (g : rationalPoints G) =>
                Induction.eval (pointImage p₁)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
                    (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f g
              let evalG₂ := fun (f : (leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ)
                  (g : rationalPoints G) =>
                Induction.eval (pointImage p₂)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
                    (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ)) f g
              let evalL₁ := fun (φ : X₁) (x : rationalPoints L) =>
                Induction.eval (pointImage p₁')
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₁' l₁' r₁' hp₁'.isClosedSubgroup hr₁'
                      hmul₁')
                    (isClosed_pointImage_comp p₁' r₁' hp₁'.isClosedSubgroup
                      hr₁'.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₁' l₁' hp₁' hl₁').symm σ)) φ x
              let evalL₂ := fun (φ : X₂) (x : rationalPoints L) =>
                Induction.eval (pointImage p₂')
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₂' l₂' r₂' hp₂'.isClosedSubgroup hr₂'
                      hmul₂')
                    (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup
                      hr₂'.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₂' l₂' hp₂' hl₂').symm σ)) φ x
              let evalQ₁ := fun (F : (leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ
                    hmulQ).obj X₁) (g : rationalPoints G) =>
                Induction.eval (pointImage q)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
                    (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm X₁)) F g
              (∀ f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ,
                ∃ F : (leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj X₁,
                  ∀ (g : rationalPoints G) (x : rationalPoints L),
                    evalL₁ (evalQ₁ F g) x = (c x)⁻¹ • evalG₁ f (emb x * g)) ∧
              (IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ →
                IsPQRegular p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂'
                  a σ ∧
                ∀ (haar' : Measure V') (haar : Measure V),
                  haar'.IsHaarMeasure → haar.IsHaarMeasure → Compatible haar' haar →
                  ∀ (J : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
                        σ).representation.IntertwiningMap
                      ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation)
                    (J' : X₁.representation.IntertwiningMap X₂.representation),
                    IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
                      V haar σ J →
                    IsIntegralIntertwiner p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁'
                      p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂' V' haar' σ J' →
                    ∀ (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
                      (F : (leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj X₁),
                      (∀ (g : rationalPoints G) (x : rationalPoints L),
                        evalL₁ (evalQ₁ F g) x = (c x)⁻¹ • evalG₁ f (emb x * g)) →
                      ∀ (g : rationalPoints G) (x : rationalPoints L),
                        evalL₂ (J' (evalQ₁ F g)) x = (c x)⁻¹ • evalG₂ (J f) (emb x * g))

/-- Renard VII.3.5, Proposition, part (iii). Let `P₁ = MN₁`, `P₂ = MN₂` be represented
parabolics of `G` with the same embedded Levi subgroup `M` and `P̄₁ = MN̄₁` opposite to `P₁`.
Let `Q₁ = LU₁`, `Q₂ = LU₂` be represented parabolics of `G` with the same embedded Levi
subgroup `L`, `Q̄₁ = LŪ₁` opposite to `Q₁`, and `P₁(F) ⊂ Q₁(F)`, `P₂(F) ⊂ Q₂(F)`. Let
`P' = MN'` be a represented parabolic of `L` with the same embedded `M` and
`P'(F) = P₁(F) ∩ L(F) = P₂(F) ∩ L(F)` in `G(F)` (so `Qᵢ = PᵢL`). Let `a : A → M` and
`aL : A_L → L` be the split components, `emb : L(F) → G(F)` the embedding,
`V = N̄₁(F) ∩ N₂(F)`, `W = Ū₁(F) ∩ U₂(F)`, `cᵢ(x) = δ_{Uᵢ}(x)^{1/2}` for `x ∈ L(F)`, and
`X = i_{P'}^L(σ)`. Then:
1. for every Haar measure `haarW` on `W` there is a Haar measure `haarV` on `V` with
   `∫_W φ dhaarW = ∫_V φ dhaarV` for continuous compactly supported `φ : G(F) → ℂ`;
2. for every smooth representation `σ` of `M(F)`:
   - every `f ∈ i_{P₁}^G(σ)` has an `f̃ ∈ i_{Q₁}^G(X)` with `f̃(g)(x) = c₁(x)⁻¹ f(emb(x) g)`;
   - if `X` is `Q₁Q₂`-regular (for `aL`), then `σ` is `P₁P₂`-regular (for `a`), and for Haar
     measures related as in 1, the integral-normalized `J = J_{P₂|P₁}(σ)` (on `V`) and
     `J_Q = J_{Q₂|Q₁}(X)` (on `W`) satisfy `J_Q(f̃)(g)(x) = c₂(x)⁻¹ J(f)(emb(x) g)` whenever
     `f̃(g)(x) = c₁(x)⁻¹ f(emb(x) g)` for all `g`, `x`: that is, `J_Q(f̃) = (J f)~`. -/
def PQIntertwiningOuterLeviStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P₁ N₁ P₂ N₂ Pb₁ Nb₁ L Q₁ U₁ Q₂ U₂ Qb₁ Ub₁ P' N' :
        GroupScheme (Spec (CommRingCat.of k)))
      (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
      (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
      (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
      (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
      (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
      (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
      (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
      (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
      (pb₁ : Pb₁ ⟶ G) (lb₁ : M ⟶ Pb₁) (rb₁ : Nb₁ ⟶ Pb₁)
      (_hpb₁ : IsParabolicSubgroup pb₁) (_hlb₁ : IsRationalLeviSubgroup lb₁)
      (_hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
      (_hmulb₁ : IsIso (subgroupMultiplication lb₁ rb₁))
      (q₁ : Q₁ ⟶ G) (lQ₁ : L ⟶ Q₁) (rQ₁ : U₁ ⟶ Q₁)
      (hq₁ : IsParabolicSubgroup q₁) (hlQ₁ : IsRationalLeviSubgroup lQ₁)
      (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
      (hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁))
      (q₂ : Q₂ ⟶ G) (lQ₂ : L ⟶ Q₂) (rQ₂ : U₂ ⟶ Q₂)
      (hq₂ : IsParabolicSubgroup q₂) (hlQ₂ : IsRationalLeviSubgroup lQ₂)
      (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
      (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
      (qb₁ : Qb₁ ⟶ G) (lqb₁ : L ⟶ Qb₁) (rqb₁ : Ub₁ ⟶ Qb₁)
      (_hqb₁ : IsParabolicSubgroup qb₁) (_hlqb₁ : IsRationalLeviSubgroup lqb₁)
      (_hrqb₁ : LeviSubgroup.IsGeometricUnipotentRadical rqb₁)
      (_hmulqb₁ : IsIso (subgroupMultiplication lqb₁ rqb₁)),
      l₂ ≫ p₂ = l₁ ≫ p₁ → lb₁ ≫ pb₁ = l₁ ≫ p₁ →
      pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁) →
      lQ₂ ≫ q₂ = lQ₁ ≫ q₁ → lqb₁ ≫ qb₁ = lQ₁ ≫ q₁ →
      pointImage q₁ ⊓ pointImage qb₁ = pointImage (lQ₁ ≫ q₁) →
      pointImage p₁ ≤ pointImage q₁ → pointImage p₂ ≤ pointImage q₂ →
      haveI := hlQ₁.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints L) := RationalPointFamily.pointTopology
      haveI := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
      haveI := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
      ∀ (p' : P' ⟶ L) (l' : M ⟶ P') (r' : N' ⟶ P')
        (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
        (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
        (hmul' : IsIso (subgroupMultiplication l' r')),
        l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁ →
        pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₁ ⊓ pointImage (lQ₁ ≫ q₁) →
        pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₂ ⊓ pointImage (lQ₁ ≫ q₁) →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
          IsSplitComponent a →
        ∀ (AL : CommGroupScheme (Spec (CommRingCat.of k))) (aL : AL.toGrp ⟶ L),
          IsSplitComponent aL →
          let emb : rationalPoints L → rationalPoints G := rationalPoints.map (lQ₁ ≫ q₁)
          let c₁ : rationalPoints L → ℂ := fun x =>
            ((HaarModulus.closedHalfCharacter (pointImage (rQ₁ ≫ q₁))
                (isClosed_pointImage_comp q₁ rQ₁ hq₁.isClosedSubgroup hrQ₁.1.isClosedSubgroup)
                (pointImage q₁)
                (isSemidirectDecomposition_pointImage q₁ lQ₁ rQ₁ hq₁.isClosedSubgroup hrQ₁
                  hmulQ₁).le_normalizer
                (Subgroup.inclusion (pointImage_comp_le q₁ lQ₁)
                  (leviPointsEquiv q₁ lQ₁ hq₁ hlQ₁ x)) : ℂˣ) : ℂ)
          let c₂ : rationalPoints L → ℂ := fun x =>
            ((HaarModulus.closedHalfCharacter (pointImage (rQ₂ ≫ q₂))
                (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
                (pointImage q₂)
                (isSemidirectDecomposition_pointImage q₂ lQ₂ rQ₂ hq₂.isClosedSubgroup hrQ₂
                  hmulQ₂).le_normalizer
                (Subgroup.inclusion (pointImage_comp_le q₂ lQ₂)
                  (leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂ x)) : ℂˣ) : ℂ)
          let V : Subgroup (rationalPoints G) := pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂)
          let W : Subgroup (rationalPoints G) :=
            pointImage (rqb₁ ≫ qb₁) ⊓ pointImage (rQ₂ ≫ q₂)
          ∀ [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W],
            let Compatible : Measure W → Measure V → Prop := fun haarW haarV =>
              ∀ φ : rationalPoints G → ℂ, Continuous φ → HasCompactSupport φ →
                ∫ x : W, φ x ∂haarW = ∫ x : V, φ x ∂haarV
            (∀ haarW : Measure W, haarW.IsHaarMeasure →
              ∃ haarV : Measure V, haarV.IsHaarMeasure ∧ Compatible haarW haarV) ∧
            haveI := hl₁.isConnectedReductive.isAffineHom
            letI := leviPointTopology l₁ hl₁
            ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
              let X := (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ
              let evalG₁ := fun (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
                  (g : rationalPoints G) =>
                Induction.eval (pointImage p₁)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
                    (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f g
              let evalG₂ := fun (f : (leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ)
                  (g : rationalPoints G) =>
                Induction.eval (pointImage p₂)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
                    (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ)) f g
              let evalL := fun (φ : X) (x : rationalPoints L) =>
                Induction.eval (pointImage p')
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage p' l' r' hp'.isClosedSubgroup hr' hmul')
                    (isClosed_pointImage_comp p' r' hp'.isClosedSubgroup hr'.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv p' l' hp' hl').symm σ)) φ x
              let evalQ₁ := fun (F : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁
                    hmulQ₁).obj X) (g : rationalPoints G) =>
                Induction.eval (pointImage q₁)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage q₁ lQ₁ rQ₁ hq₁.isClosedSubgroup hrQ₁
                      hmulQ₁)
                    (isClosed_pointImage_comp q₁ rQ₁ hq₁.isClosedSubgroup hrQ₁.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv q₁ lQ₁ hq₁ hlQ₁).symm X)) F g
              let evalQ₂ := fun (F : (leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂
                    hmulQ₂).obj X) (g : rationalPoints G) =>
                Induction.eval (pointImage q₂)
                  (inducingRepresentation
                    (isSemidirectDecomposition_pointImage q₂ lQ₂ rQ₂ hq₂.isClosedSubgroup hrQ₂
                      hmulQ₂)
                    (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
                    (SmoothRep.pullback (leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂).symm X)) F g
              (∀ f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ,
                ∃ F : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X,
                  ∀ (g : rationalPoints G) (x : rationalPoints L),
                    evalL (evalQ₁ F g) x = (c₁ x)⁻¹ • evalG₁ f (emb x * g)) ∧
              (IsPQRegular q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂ aL X →
                IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ ∧
                ∀ (haarW : Measure W) (haarV : Measure V),
                  haarW.IsHaarMeasure → haarV.IsHaarMeasure → Compatible haarW haarV →
                  ∀ (J : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
                        σ).representation.IntertwiningMap
                      ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation)
                    (JQ : ((leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁
                        hmulQ₁).obj X).representation.IntertwiningMap
                      ((leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂
                        hmulQ₂).obj X).representation),
                    IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
                      V haarV σ J →
                    IsIntegralIntertwiner q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁
                      q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂ W haarW X JQ →
                    ∀ (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
                      (F : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁
                        hmulQ₁).obj X),
                      (∀ (g : rationalPoints G) (x : rationalPoints L),
                        evalL (evalQ₁ F g) x = (c₁ x)⁻¹ • evalG₁ f (emb x * g)) →
                      ∀ (g : rationalPoints G) (x : rationalPoints L),
                        evalL (evalQ₂ (JQ F) g) x = (c₂ x)⁻¹ • evalG₂ (J f) (emb x * g))

end Langlands.Aubert.General.RepresentedParabolic
