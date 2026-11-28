import Langlands.TraceFormula.DivisionAlgebraSimpleTraceComparisonStatement
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicIwasawaAssembly
import Langlands.Global.AdelicLocalCharacterNorm
import Langlands.Global.AdelicLocalInclusion
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.Representation.Archimedean.SmoothVectors
import Langlands.Representation.Character.Basic
import Langlands.Representation.Hecke.CornerAction
import Langlands.Representation.Hecke.UnimodularStar
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Unitary.DiscretePart
import Langlands.Representation.Unitary.IntegratedOperator

/-!
# Restricted tensor product trace factorization on an irreducible summand of `L²([G])`

Let `F` be a number field and `G` a connected reductive group over `F`, with the canonical
`L²([G])`, `[G] = A_G G(F) \ G(𝔸_F)` (`RestrictionSplitCentre.canonicalMeasure`), its right
regular representation `R = RestrictionSplitCentre.canonicalL2RightAction` and the integrated
operators `R(f) = canonicalIntegratedAction F G hG f hf` for `Measure.haar` on `G(𝔸_F)`. Fix
compact open subgroups `U v ≤ G(F_v)` at the finite places that form an integral family (the
values of every regular function on `U v` are integral for almost all `v`, and every point of
`G(𝔸_F)` has its components in `U v` for almost all `v`), Haar measures `μp v` on `G(F_v)` with
`μp v (U v) = 1` for almost all `v`, and a Haar measure `μinf` on `G(F_∞)`.

For an irreducible closed invariant subspace `P` of `L²([G])`, the statement
`GroupSchemeL2RestrictedTraceFactorizationStatement` gives

* at every finite place `p`, an irreducible admissible representation `ρ p` of `G(F_p)` that
  occurs in `P` and such that `P` is `ρ p`-isotypic;
* an irreducible unitary representation `σ` of `G(F_∞)` that occurs isometrically in `P` and
  such that `P` is `σ`-isotypic;
* a finite set `Ebad` of finite places outside which `P` has a nonzero `U p`-fixed vector and
  `ρ p` has a one-dimensional space of `U p`-fixed vectors;
* at every finite place `p` where `ρ p` has a one-dimensional space of `U p`-fixed vectors, a
  character `χ` of the Hecke algebra of `(G(F_p), U p)`, bounded by the `L¹` norm and compatible
  with `h ↦ h⋆`, by which the Hecke algebra acts on the `U p`-fixed vectors of `P` and of `ρ p`;
* a constant `c > 0` such that, for every finite set `S ⊇ Ebad` of finite places, the trace on
  `P` of `R(f)` for the restricted tensor product
  `f(g) = f_∞(g_∞) ∏_{p ∈ S} f_p(g_p) ∏_{p ∉ S} 1_{U p}(g_p)` is
  `c · tr σ(f_∞) · ∏_{p ∈ S} Θ_{ρ p}(f_p)`, whenever `f` is integrable and the compression of
  `R(f)` to `P` and `σ(f_∞)` are trace class.

The statement is derived from Flath's factorization of irreducible unitary representations of
`G(𝔸_F)` (Flath 1979, Theorem 4; Getz–Hahn, Theorems 5.7.1 and 6.6.1), the unramified Hecke
algebra (Getz–Hahn, Theorem 5.5.2 and Corollary 5.5.6), the type I property of the local groups
(Getz–Hahn, Theorem 3.10.2) and Folland's tensor product theorem (Folland, Theorem 7.17). The
module contains no proof; the paired Markdown gives the sources and the argument.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.Analysis.OperatorIdeals Langlands.HarmonicAnalysis

namespace Langlands.TraceFormula

/-- **Restricted tensor product trace factorization on an irreducible summand of `L²([G])`.**

Data: a number field `F : Type`; an affine group scheme `G` over `F`, locally of finite type,
with `hG : IsConnectedReductive G`; the total disconnectedness of `G(F_v)` at every finite place
`v` (instance binder); compact open subgroups `U v` of `G(F_v)` for the finite places, such that
(i) `IsUniformlyIntegral F G (extendFinite F G (U ·))`: every regular function on `G` takes
integral values on `U v` for almost all `v`, and (ii) for every `g ∈ G(𝔸_F)`, `g_v ∈ U v` for
almost all `v`; Haar measures `μp v` on `G(F_v)` with `μp v (U v) = 1` for almost all `v`; a Haar
measure `μinf` on `G(F_∞) = InfiniteAdelicGroupPoints F G`. Write `L²` for
`Lp ℂ 2 (canonicalMeasure F G)`, `R` for `canonicalL2RightAction F G centralSplitTorusCharacter hG`
and `R_v y = R (ofPlace F G (.inr v) y)` for the action of `G(F_v)`. Let `P` be an irreducible
subrepresentation of `R` (`Langlands.Analysis.IsIrreducibleSubrepresentation`: closed, nonzero,
invariant, with no closed invariant subspaces other than `⊥` and `P`).

Then there are representations `ρ p` of `G(F_p)` on complex vector spaces `V p : Type` with
`hρ p : IsAdmissible (ρ p)` for every finite place `p`, a representation `σ` of `G(F_∞)` by
bounded operators on a complex Hilbert space `H : Type` preserving the norm (`hσnorm`) with
`μinf`-measurable orbit maps (`hσmeas`), and a finite set `Ebad` of finite places, such that:

1. every `ρ p` is irreducible;
2. (realization at `p`) there is a nonzero linear `j₀ : V p → L²` with range in `P` and
   `j₀ (ρ p y x) = R_p y (j₀ x)`;
3. (isotypy at `p`) every smooth irreducible representation `ρ'` of `G(F_p)` on `V' : Type` with
   a nonzero linear `j : V' → L²` with range in `P` and `j (ρ' y x) = R_p y (j x)` is isomorphic
   to `ρ p`;
4. `σ` is jointly continuous and 5. topologically irreducible;
6. (realization at `∞`) there is a linear isometry `jinf : H → L²` with values in `P` and
   `jinf (σ g x) = R (ofInfinite F G g) (jinf x)`;
7. (isotypy at `∞`) every jointly continuous, norm-preserving, topologically irreducible
   representation `σ'` of `G(F_∞)` on a complex Hilbert space `H' : Type` with a nonzero bounded
   linear `j : H' → L²` with values in `P` and `j (σ' g x) = R (ofInfinite F G g) (j x)` is
   unitarily equivalent to `σ`;
8. (unramified places) for every finite place `p ∉ Ebad`, some nonzero vector of `P` is a
   `U p`-fixed smooth vector of `R_p`, and the `U p`-fixed vectors of `ρ p` form a line;
9. (Hecke characters) for every finite place `p` at which the `U p`-fixed vectors of `ρ p` form a
   line, there is a `ℂ`-algebra homomorphism `χ : Corner (μp p) (U p) → ℂ` such that every `h`
   acts on every `U p`-fixed smooth vector of `R_p` lying in `P` (by `Hecke.cornerAction`) as
   multiplication by `χ h`, `‖χ h‖ ≤ ∫ ‖h‖ dμp p`, `χ (star h) = conj (χ h)` for
   `(star h)(g) = conj (h g⁻¹)`, and every `h` acts on the `U p`-fixed vectors of `ρ p` by `χ h`;
10. (trace factorization) there is `c > 0` such that for every finite set `S ⊇ Ebad` of finite
   places, every `μinf`-integrable `finf` with `σf = ∫ finf(g) σ(g) dμinf(g)` trace class, and
   every family `fs p` of Schwartz–Bruhat functions on `G(F_p)`, if `f` is the indicator function
   of `{y | ∀ p ∉ S, y_p ∈ U p}` times `y ↦ finf (y_∞) * ∏_{p ∈ S} fs p (y_p)`, `f` is integrable
   for `Measure.haar` (`hf`) and the compression of `canonicalIntegratedAction F G hG f hf` to `P`
   is trace class, then its trace is
   `c * operatorTrace σf * ∏_{p ∈ S} Character.distribution (μp p) (ρ p) (hρ p) (fs p)`. -/
def GroupSchemeL2RestrictedTraceFactorizationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    [∀ v : Langlands.Global.FinitePlace F,
      TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]
    (U : ∀ v : Langlands.Global.FinitePlace F, OpenSubgroup (PlaceGroupPoints F G (.inr v)))
    (hU : ∀ v, IsCompact (U v : Set (PlaceGroupPoints F G (.inr v)))),
    IsUniformlyIntegral F G (extendFinite F G fun v => (U v).toSubgroup) →
    (∀ g : AdelicGroupPoints F G,
      ∀ᶠ v : Langlands.Global.FinitePlace F in Filter.cofinite, atPlace F G (.inr v) g ∈ U v) →
    ∀ (μp : ∀ v : Langlands.Global.FinitePlace F, Measure (PlaceGroupPoints F G (.inr v)))
      [∀ v, (μp v).IsHaarMeasure],
    (∀ᶠ v : Langlands.Global.FinitePlace F in Filter.cofinite, μp v (U v) = 1) →
    ∀ (μinf : Measure (InfiniteAdelicGroupPoints F G)) [μinf.IsHaarMeasure],
    let R := RestrictionSplitCentre.canonicalL2RightAction F G centralSplitTorusCharacter hG
    let Rloc : ∀ v : Langlands.Global.FinitePlace F,
        Representation ℂ (PlaceGroupPoints F G (.inr v))
          (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) :=
      fun v => R.comp (ofPlace F G (.inr v))
    ∀ (P : Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)))
      [CompleteSpace P], Langlands.Analysis.IsIrreducibleSubrepresentation R P →
      ∃ (V : Langlands.Global.FinitePlace F → Type) (_ : ∀ p, AddCommGroup (V p))
        (_ : ∀ p, Module ℂ (V p))
        (ρ : ∀ p, Representation ℂ (PlaceGroupPoints F G (.inr p)) (V p))
        (hρ : ∀ p, IsAdmissible (ρ p))
        (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H)
        (σ : InfiniteAdelicGroupPoints F G →* (H →L[ℂ] H))
        (hσnorm : ∀ g x, ‖σ g x‖ = ‖x‖)
        (hσmeas : ∀ x : H, AEStronglyMeasurable (fun g => σ g x) μinf)
        (Ebad : Finset (Langlands.Global.FinitePlace F)),
        (∀ p, (ρ p).IsIrreducible) ∧
        (∀ p, ∃ j₀ : V p →ₗ[ℂ] Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G),
          j₀ ≠ 0 ∧ LinearMap.range j₀ ≤ P ∧ ∀ y x, j₀ (ρ p y x) = Rloc p y (j₀ x)) ∧
        (∀ (p : Langlands.Global.FinitePlace F) (V' : Type) [AddCommGroup V'] [Module ℂ V']
            (ρ' : Representation ℂ (PlaceGroupPoints F G (.inr p)) V'),
          IsSmooth ρ' → ρ'.IsIrreducible →
          ∀ j : V' →ₗ[ℂ] Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G), j ≠ 0 →
            LinearMap.range j ≤ P → (∀ y x, j (ρ' y x) = Rloc p y (j x)) →
            ∃ E : V' ≃ₗ[ℂ] V p, ∀ y x, E (ρ' y x) = ρ p y (E x)) ∧
        Langlands.Archimedean.IsContinuousRepresentation σ ∧
        Langlands.Archimedean.IsTopologicallyIrreducible σ ∧
        (∃ jinf : H →ₗᵢ[ℂ] Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G),
          (∀ x, jinf x ∈ P) ∧ ∀ g x, jinf (σ g x) = R (ofInfinite F G g) (jinf x)) ∧
        (∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
            (σ' : InfiniteAdelicGroupPoints F G →* (H' →L[ℂ] H')),
          Langlands.Archimedean.IsContinuousRepresentation σ' →
          (∀ g x, ‖σ' g x‖ = ‖x‖) →
          Langlands.Archimedean.IsTopologicallyIrreducible σ' →
          ∀ j : H' →L[ℂ] Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G), j ≠ 0 →
            (∀ x, j x ∈ P) → (∀ g x, j (σ' g x) = R (ofInfinite F G g) (j x)) →
            ∃ E : H' ≃ₗᵢ[ℂ] H, ∀ g x, E (σ' g x) = σ g (E x)) ∧
        (∀ p ∉ Ebad,
          (∃ x : fixedVectors (smoothPart (Rloc p)) (U p).toSubgroup,
            ((x : smoothVectors (Rloc p)) :
              Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) ∈ P ∧ x ≠ 0) ∧
          Module.finrank ℂ (fixedVectors (ρ p) (U p).toSubgroup) = 1) ∧
        (∀ p, Module.finrank ℂ (fixedVectors (ρ p) (U p).toSubgroup) = 1 →
          ∃ χ : Hecke.HeckeAlgebra.Corner (μp p) (U p) (hU p) →ₐ[ℂ] ℂ,
            (∀ (h : Hecke.HeckeAlgebra.Corner (μp p) (U p) (hU p))
                (x : fixedVectors (smoothPart (Rloc p)) (U p).toSubgroup),
              ((x : smoothVectors (Rloc p)) :
                Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G)) ∈ P →
              Hecke.cornerAction (μp p) (smoothPart (Rloc p)) (isSmooth_smoothPart (Rloc p))
                (U p) (hU p) h x = χ h • x) ∧
            (∀ h, ‖χ h‖ ≤ ∫ g, ‖h g‖ ∂(μp p)) ∧
            (∀ h, χ (star h) = starRingEnd ℂ (χ h)) ∧
            ∀ (h : Hecke.HeckeAlgebra.Corner (μp p) (U p) (hU p))
              (x : fixedVectors (ρ p) (U p).toSubgroup),
              Hecke.cornerAction (μp p) (ρ p) (hρ p).1 (U p) (hU p) h x = χ h • x) ∧
        ∃ c : ℝ, 0 < c ∧
          ∀ S : Finset (Langlands.Global.FinitePlace F), Ebad ⊆ S →
          ∀ (finf : InfiniteAdelicGroupPoints F G → ℂ) (hfinf : Integrable finf μinf),
            let σf : H →L[ℂ] H :=
              Langlands.Analysis.integratedIsometricAction μinf σ hσnorm hσmeas finf hfinf
            IsTraceClass σf →
            ∀ fs : ∀ p : Langlands.Global.FinitePlace F,
                SchwartzBruhat (PlaceGroupPoints F G (.inr p)),
              let f : AdelicGroupPoints F G → ℂ := fun x =>
                {y : AdelicGroupPoints F G | ∀ p ∉ S, atPlace F G (.inr p) y ∈ U p}.indicator
                  (fun y => finf (infinite F G y) * ∏ p ∈ S, fs p (atPlace F G (.inr p) y)) x
              ∀ hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)),
                let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
                  canonicalIntegratedAction F G hG f hf ∘L P.subtypeL
                IsTraceClass (E := (P : Submodule ℂ _)) RPf →
                  operatorTrace (E := (P : Submodule ℂ _)) RPf =
                    (c : ℂ) * operatorTrace σf *
                      ∏ p ∈ S, Character.distribution (μp p) (ρ p) (hρ p) (fs p)

end Langlands.TraceFormula
