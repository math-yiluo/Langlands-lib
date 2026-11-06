import Mathlib.GroupTheory.DoubleCoset
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Filtration.ObjectDefinitions
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # Jacquet modules of supercuspidal inductions along conjugate Levis

Renard 2026, VI.5.3, Proposition (iii) (printed p.173/PDF p.179): let `P = MN` and
`Q = LU` be parabolic subgroups of `G` with `M` and `L` conjugate, and `ρ` a supercuspidal
representation of `M`. Then `r_Q^G i_P^G ρ` has a filtration by subrepresentations whose
successive quotients are the conjugates `w·ρ`, `w ∈ W(L, M)/W_L`. In particular
`r_Q^G i_P^G ρ` is supercuspidal.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.5.3, Proposition (iii): for actual rational parabolics `P = MN` and `Q = LU`
of `G` with `M` conjugate to `L` under `G(F)`, and a supercuspidal smooth representation `ρ`
of `M(F)` (every normalized Jacquet module of `ρ` for a proper actual parabolic of `M`
vanishes), the normalized Jacquet module `τ = r_Q^G i_P^G ρ` has the following properties.

* There are an enumeration `c` of the double cosets `P(F) w Q(F)` that contain an element
  `w` with `w L w⁻¹ = M`, a representative `z i` of each with `z i · L · (z i)⁻¹ = M`,
  witnessed by an isomorphism `φ i : L ≅ M` given by conjugation by `z i`, the map `e i`
  of `φ i` on rational points, and a filtration of `τ` by subrepresentations with one step
  for each such double coset, whose `i`th successive quotient is the conjugate
  `x ↦ ρ (z i x (z i)⁻¹)` of `ρ`.
* `τ` is supercuspidal: its normalized Jacquet module for every proper actual rational
  parabolic of `L` vanishes. -/
def LeviJacquetInductionSupercuspidalFiltrationStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q L U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      (∃ (g : rationalPoints G) (φ : M ≅ L),
          φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom) →
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      haveI := hlQ.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ hlQ
      haveI : LocallyCompactSpace (rationalPoints L) :=
        leviPoints_locallyCompactSpace q lQ hq hlQ
      haveI : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q lQ hq hlQ
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
        (∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj ρ)) →
        (∃ (m : ℕ)
          (c : Fin m ≃
            {x : DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
                (pointImage q : Set (rationalPoints G)) //
              ∃ (w : rationalPoints G) (ψ : L ≅ M),
                DoubleCoset.mk (pointImage p) (pointImage q) w = x ∧
                  ψ.hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso w).hom})
          (z : Fin m → rationalPoints G) (φ : Fin m → (L ≅ M))
          (e : Fin m → (rationalPoints L ≃ₜ* rationalPoints M)),
          (∀ i, DoubleCoset.mk (pointImage p) (pointImage q) (z i) = (c i).1) ∧
          (∀ i, (φ i).hom ≫ l ≫ p = lQ ≫ q ≫ (G.innerIso (z i)).hom) ∧
          (∀ i x, e i x = rationalPoints.map (φ i).hom x) ∧
          ∃ s : ObjectRepFiltration
              (SmoothRep.toRep.obj
                ((leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj
                  ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))) m,
            ∀ i, Nonempty ((s.gradedRepresentation i).ρ.Equiv
              (SmoothRep.pullback (e i) ρ).representation)) ∧
        ∀ (P' L' U' : GroupScheme (Spec (CommRingCat.of k)))
          (p' : P' ⟶ L) (l' : L' ⟶ P') (r' : U' ⟶ P')
          (hp' : IsParabolicSubgroup p') (hl' : IsRationalLeviSubgroup l')
          (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
          (hmul' : IsIso (subgroupMultiplication l' r')),
          ¬ IsIso p' → Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj
            ((leviJacquetFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj
              ((leviInductionFunctor p l r hp hr hl hmul).obj ρ)))

end Langlands.Aubert.General.RepresentedParabolic
