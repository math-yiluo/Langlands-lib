import Langlands.Representation.Aubert.General.CorrectedFiltrationStatements
import Langlands.Representation.Aubert.SubgroupTransition
import Langlands.Representation.Geometric.ClosedSubgroupDefinitions

/-!
# Interface data for the surviving graded transitions

Explicit inputs for a conditional proof of
`CorrectedFiltration.CorrectedGradedTransitionTarget`:

* `inducingObject`: the unnormalized quotient action of `P_J` on the actual
  coinvariants `E_{U_J}`, as a smooth `P_J`-representation;
* `SurvivingSupportHypotheses`: openness, left `P_J`-invariance and the
  single-cell difference of the two support sets at a surviving grade;
* `OrbitJacquetData`: a map from the actual orbit piece to
  `Ad(m)(r_K E)` that descends to an isomorphism on the `U_I`-coinvariants and
  turns the pointwise coinvariant transitions into equalities.

Nothing is asserted here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G)) (hU : Antitone U)

/-- The unnormalized quotient action `p · [v] = [p v]` of `P_J` on the actual
coinvariants `E_{U_J}`, as a smooth representation of `P_J`. Under
unimodularity of `U_J` this is the inducing representation of `E_J = i_J r_J E`
(`inducingRepresentation_jacquet_eq`). -/
abbrev inducingObject (E : SmoothRep.{0, uG, max uG uV} ℂ G) (J : Finset ι) :
    Induction.SmoothRep.{0, uG, max uG uV} ℂ (P J) :=
  Jacquet.Localization.smoothObject (U J) 1 (P J) (h J).le_normalizer
    (Jacquet.Localization.isInvariant_one (U J) (P J) (h J).le_normalizer) E

variable (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))

/-- The support inputs at the grade `i` of `r_I(E_J)`, `J = S \ s`, for a lift
`m` of `w⁻¹`: both support sets `G_{θ_i'}` and `G_{θ_{i+1}'}` are open, the
larger one is left `P_J`-invariant, and their difference is the single double
coset `P_J m⁻¹ P_I`. -/
structure SurvivingSupportHypotheses (I s : Finset ι) (i : ℕ) (m : G) : Prop where
  isOpen_lower : IsOpen (groupSupport P T cs I s i)
  isOpen_upper : IsOpen (groupSupport P T cs I s (i + 1))
  left_upper : ∀ p ∈ P (Finset.univ \ s), ∀ g ∈ groupSupport P T cs I s (i + 1),
    p * g ∈ groupSupport P T cs I s (i + 1)
  sdiff_eq : groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i =
    {g | ∃ p ∈ P (Finset.univ \ s), ∃ q ∈ P I, g = p * m⁻¹ * q}

/-- Orbit Jacquet data at a grade with Weyl element `w`, lift `m` of `w⁻¹` and
`M K = m⁻¹ (M I) m`. For every surviving `J = S \ s` (`K ⊆ J`, `w` minimal in
`W_J w W_I`), `Θ s` is a linear map from the actual orbit piece
`c-Ind_{P_I ∩ m P_J m⁻¹}^{P_I}(E_{U_J} ∘ Ad(m⁻¹))` to `Ad(m)(r_K E)` which is
`U_I`-invariant, `M_I`-equivariant for the normalized Jacquet action, surjective,
and has kernel inside the actual `U_I`-relations. Functions related by the
pointwise transition `E_{U_J} → E_{U_J'}` have the same image. -/
structure OrbitJacquetData (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (w : Group.RelativeWeyl.Weyl T) (m : G) (K : Finset ι)
    (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K) where
  /-- The orbit maps. -/
  Θ : ∀ s : Finset ι, K ⊆ Finset.univ \ s →
    Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w →
    ((Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
        (inducingObject P M U h E (Finset.univ \ s))) →ₗ[ℂ]
      ((conjugationFunctor (m : G) hK).obj
        ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).obj E))
  unipotent_invariant : ∀ s hKs hs (u : U I) φ,
    Θ s hKs hs (((Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
        (inducingObject P M U h E (Finset.univ \ s))).ρ ⟨u, (h I).unipotent_le u.2⟩ φ) =
      Θ s hKs hs φ
  levi_equivariant : ∀ s hKs hs (l : M I) φ,
    ((HaarModulus.closedInverseHalfCharacter (U I) (hclosed I) (M I)
        (h I).levi_le_normalizer l : ℂˣ) : ℂ) •
      Θ s hKs hs (((Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
        (inducingObject P M U h E (Finset.univ \ s))).ρ ⟨l, (h I).levi_le l.2⟩ φ) =
      ((conjugationFunctor (m : G) hK).obj
        ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).obj E)).representation l
        (Θ s hKs hs φ)
  surjective : ∀ s hKs hs, Function.Surjective (Θ s hKs hs)
  ker_le : ∀ s hKs hs φ, Θ s hKs hs φ = 0 →
    φ ∈ Jacquet.Localization.relations
      ((Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
        (inducingObject P M U h E (Finset.univ \ s))).ρ
      ((U I).subgroupOf (P I)) 1
  transition : ∀ (s t : Finset ι) (hst : s ⊆ t) hKs hs hKt ht
    (φ : (Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
      (inducingObject P M U h E (Finset.univ \ s)))
    (ψ : (Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ t)) (P I) m).obj
      (inducingObject P M U h E (Finset.univ \ t))),
    (∀ q : P I,
      Induction.eval _ _ ψ.val q =
        Jacquet.Localization.transitionLinear (U (Finset.univ \ s)) (U (Finset.univ \ t))
          (hU (Finset.sdiff_subset_sdiff_right Finset.univ hst)) 1 1 (fun _ => rfl)
          E.representation (Induction.eval _ _ φ.val q)) →
    Θ t hKt ht ψ = Θ s hKs hs φ

end Langlands.Aubert.General.CorrectedFiltration
