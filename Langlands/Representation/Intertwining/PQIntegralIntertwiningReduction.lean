import Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements
import Langlands.Representation.Intertwining.PQIntertwiningOperatorProof

/-! # Reduction of Renard VII.3.4 (integral form) to the integral identification

`PQIntegralIdentificationStatement` is the first clause of
`PQIntegralIntertwiningOperatorStatement`: the identification
`F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` can be chosen induced by `f ↦ ∫_{N̄∩U} f(v) dv`.
The theorem `pqIntegralIntertwiningOperator_of_identification` derives the whole
statement from it, using the proved `pqIntertwiningOperator` for the second clause.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The first clause of `PQIntegralIntertwiningOperatorStatement` (Renard VII.3.4, first
paragraph of the proof). Let `P = MN` and `Q = MU` be represented parabolics with the same
Levi subgroup `M` of `G`, let `P̄ = MN̄` be a represented parabolic opposite to `P` (same
embedded Levi, `P(F) ∩ P̄(F) = M(F)`), and let `haar` be a Haar measure on
`V = N̄(F) ∩ U(F)`. For every smooth representation `σ` of `M(F)` there is an
`M(F)`-equivariant linear equivalence `e : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` such that, for
every `f ∈ F̃^{<1̄}_{PQ}(σ)` and every linear form `ℓ`, `v ↦ ℓ(f(v))` is `haar`-integrable on
`V` and `ℓ(e(f̄)) = ∫_V ℓ(f(v)) dhaar(v)`. -/
def PQIntegralIdentificationStatement : Prop :=
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
        ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
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
                        (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f x) ∂haar

/-- Renard VII.3.4, explicit form, conditional on its first clause: the integral
identification of `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ)` with `σ` gives the unique integral-normalized
intertwining operator `J_{Q|P}(σ)` for every `PQ`-regular `σ`. -/
theorem pqIntegralIntertwiningOperator_of_identification
    (h : PQIntegralIdentificationStatement.{u, v}) :
    PQIntegralIntertwiningOperatorStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U Pb Nb p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    pb lb rb hpb hlb hrb hmulb hsame hbar hopp V _ _ haar _
  have hid := h k G hG P M N Q U Pb Nb p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ
    pb lb rb hpb hlb hrb hmulb hsame hbar hopp haar
  refine ⟨hid, ?_⟩
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  intro A a ha σ hregular
  obtain ⟨e, he⟩ := hid σ
  obtain ⟨J, hJ, hunique⟩ := pqIntertwiningOperator k G hG P M N Q U p l r hp hl hr hmul
    q lQ rQ hq hlQ hrQ hmulQ hsame A a ha σ hregular e
  refine ⟨J, ?_, ?_⟩
  · intro f hf ℓ
    have hy : Jacquet.Localization.mk
        ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
        (pointImage (rQ ≫ q)) 1 f ∈ (boundarySupportImage.{u, v} p l r hp hr hl hmul
          q lQ rQ hq hrQ hlQ hmulQ (identityParabolicDoubleCoset p q)).obj σ :=
      ⟨f, hf, rfl⟩
    obtain ⟨hint, heq⟩ := he f hf _ hy rfl ℓ
    exact ⟨hint, (congrArg ℓ (hJ f hf _ hy rfl)).trans heq⟩
  · have sep : ∀ x y : σ, (∀ ℓ : Module.Dual ℂ σ, ℓ x = ℓ y) → x = y := fun x y hxy =>
      sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff ℂ (x - y)).mp fun ℓ => by
        rw [map_sub, hxy ℓ, sub_self])
    intro J' hJ'
    apply hunique
    intro f hf y hy hyf
    subst hyf
    exact sep _ _ fun ℓ => (hJ' f hf ℓ).2.trans (he f hf _ hy rfl ℓ).2.symm

set_option linter.defProp false in
/-- The reduction of Renard VII.3.4 (explicit form) to its first clause, as a declaration
whose type is the implication. -/
def pqIntegralIntertwiningOperatorOfIdentification :
    PQIntegralIdentificationStatement.{u, v} →
      PQIntegralIntertwiningOperatorStatement.{u, v} :=
  pqIntegralIntertwiningOperator_of_identification.{u, v}

end Langlands.Aubert.General.RepresentedParabolic
