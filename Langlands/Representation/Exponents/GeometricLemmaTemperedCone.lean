import Langlands.Representation.Exponents.GeometricLemmaExponentTransfer
import Langlands.Representation.Exponents.RadicalWeightTransfer
import Langlands.Representation.Exponents.ArbitraryParabolicTempered
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # The exponent cone condition for parabolic induction from a glued geometric lemma

If `r_Q ∘ i_P` is glued from the pieces of intersection data, then every normalized
Jacquet exponent along `Q` of `i_P σ`, for a tempered `σ`, has normalized real part in
the nonnegative cone of every presentation of `Q` whose relative roots are closed under
negation.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [Smooth G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance temperedConeAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P) (hp : IsParabolicSubgroup p)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r) (hl : IsRationalLeviSubgroup l)
  (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (hq : IsParabolicSubgroup q)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ) (hlQ : IsRationalLeviSubgroup lQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- Renard VII.2.2, the cone half for one parabolic `Q = L U` of `G`. Suppose that
`r_Q ∘ i_P` is glued from the pieces of intersection data `D i`. Let `σ` be a tempered
representation of `M(F)` whose Jacquet modules along the parabolics `P'` of the data are
admissible. Then every normalized Jacquet exponent along `Q` of `i_P σ`, for a split
component `a` of `L`, has normalized real part in the nonnegative cone of every
presentation of `(q, lQ, a)` whose relative roots are closed under negation. -/
theorem normalizedRealPart_mem_nonnegCone_of_isGluedFrom {m : ℕ}
    {z : Fin m → rationalPoints G}
    (D : ∀ i, GeometricLemmaIntersectionDatum p l r hp hr hl hmul
      q lQ rQ hq hrQ hlQ hmulQ (z i))
    (hD : IsGluedFrom
      (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ)
      (fun i => (D i).pieceFunctor))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ L}
    (ha : IsSplitComponent a) (pres : ParabolicRootPresentation q lQ a)
    (hneg : ∀ α ∈ relativeRoots pres.data.i, -α ∈ relativeRoots pres.data.i) :
    haveI := hl.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
    haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
    haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
    ∀ σ : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      IsNormalizedExponentTempered hl.isConnectedReductive σ →
      (∀ i, letI := leviPointTopology (D i).l' (D i).hl'
        ((leviJacquetFunctor (D i).p' (D i).l' (D i).r' (D i).hp' (D i).hr' (D i).hl'
          (D i).hmul').obj σ).IsAdmissible) →
      ∀ χ : rationalPoints A.toGrp →* ℂˣ,
        IsNormalizedJacquetExponent q lQ rQ hq hlQ hrQ hmulQ ha
          ((leviInductionFunctor p l r hp hr hl hmul).obj σ) χ →
        Plancherel.SplitTorus.normalizedRealPart ha.isCentralSplitTorus.1.1 χ ∈
          pres.nonnegCone := by
  have := hl.isConnectedReductive.isAffineHom
  have := hl.isConnectedReductive.smooth
  let := leviPointTopology l hl
  have := leviPoints_locallyCompactSpace p l hp hl
  have := leviPoints_nonarchimedeanGroup p l hp hl
  intro σ hσ hJ χ hχ
  rw [isNormalizedJacquetExponent_iff_leviJacquet] at hχ
  obtain ⟨i, hi⟩ := hD.exists_isGeneralizedEigencharacter σ (rationalPoints.map a) χ hχ
  obtain ⟨A', a', f, ha', hf⟩ := (D i).exists_isSplitComponent_factor ha
  obtain ⟨ψ, hψ, hψχ⟩ := (D i).exists_isNormalizedJacquetExponent_of_piece ha ha'
    (Additive.ofMul f) hf σ (hJ i) χ hi
  have hcone := hσ.parabolic (D i).p' (D i).l' (a' ≫ (D i).φ.hom) (D i).hp' (D i).hl'
    (ha'.comp_iso (D i).φ)
  obtain ⟨presM⟩ := hcone.1
  have hmem := hcone.2 presM _ (D i).r' (D i).hr' (D i).hmul' ψ hψ
  have hopen := ((isNormalizedJacquetExponent_iff_isOpen_ker_and _ _ _ _ _ _ _ _ σ ψ).mp hψ).1
  have := (ha'.comp_iso (D i).φ).isAffine
  rw [← hψχ, Plancherel.SplitTorus.normalizedRealPart_comp_points
    ha.isCentralSplitTorus.1.1 (ha'.comp_iso (D i).φ).isCentralSplitTorus.1.1
    (Additive.ofMul f) ψ hopen]
  exact (D i).restrictReal_mem_nonnegCone (Additive.ofMul f) hf pres presM hneg hmem

end Langlands.Aubert.General.RepresentedParabolic
