import Langlands.Representation.Aubert.General.CorrectedGradedReduction
import Langlands.Representation.Aubert.General.CorrectedFiltrationNatural

/-!
# Naturality of the conditional surviving graded transitions

Naturality in the ambient representation of the restriction `R_s` and of the
graded map `β_s = Θ_s ∘ R_s` of `CorrectedGradedReduction`, along the term and
step maps of `CorrectedFiltrationNatural`:

* `stepRestriction_natural`: `R_s` commutes with `i_J r_J φ` on values,
  unconditionally;
* `OrbitJacquetData.IsNatural`: the corresponding naturality of the orbit maps
  `Θ`, a hypothesis;
* `stepGradedMap_natural`: under it, the naturality square of `β_s` with the
  step map `r_I(i_J r_J φ)` and `Ad(m)(r_K φ)`.
-/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

section Natural

variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
  {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B)

/-- The actual Jacquet map `r_U φ` is `[v] ↦ [φ v]` on the coinvariants. -/
theorem jacquetFunctor_map_hom {Q L N : Subgroup G} (hQ : IsSemidirectDecomposition Q L N)
    (hN : IsClosed (N : Set G)) (x : (jacquetFunctor.{uG, max uG uV} hQ hN).obj A) :
    SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} hQ hN).map φ) x =
      Jacquet.Localization.mapLinear N 1 (SmoothRep.hom φ) x :=
  rfl

/-- The term map `i_J r_J φ` acts on values by `[v] ↦ [φ v]`. -/
theorem termMap_eval (s : Finset ι) (f : term P M U h hclosed A s) (x : G) :
    Induction.eval _ _ (SmoothRep.hom (termMap P M U h hclosed φ s) f) x =
      Jacquet.Localization.mapLinear (U (Finset.univ \ s)) 1 (SmoothRep.hom φ)
        (Induction.eval _ _ f x) :=
  rfl

variable [SigmaCompactSpace G] [T2Space G]
  [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))
  {I s : Finset ι} {i : ℕ} {m : G}
  (H : SurvivingSupportHypotheses P T cs I s i m)

/-- The term map as a map of the steps `inductionStep`, viewed as
subrepresentations of the restriction to `P_I`. -/
def stepSubrepresentationMap (I s : Finset ι) (i : ℕ)
    (f : stepSubrepresentation P M U h hclosed T cs A I s i) :
    stepSubrepresentation P M U h hclosed T cs B I s i :=
  ⟨SmoothRep.hom (termMap P M U h hclosed φ s) f.1, termMap_mem_inductionStep φ I s i f.2⟩

/-- Naturality of `R_s`: `R_s (i_J r_J φ f) (q) = [φ] (R_s f (q))` for every
`q ∈ P_I`. -/
theorem stepRestriction_natural
    (f : stepSubrepresentation P M U h hclosed T cs A I s (i + 1)) (q : P I) :
    Induction.eval _ _ (stepRestriction P M U h hclosed hδ T cs hPc H B
        (stepSubrepresentationMap P M U h hclosed T cs φ I s (i + 1) f)).val q =
      Jacquet.Localization.mapLinear (U (Finset.univ \ s)) 1 (SmoothRep.hom φ)
        (Induction.eval _ _ (stepRestriction P M U h hclosed hδ T cs hPc H A f).val q) := by
  have a := stepRestriction_eval P M U h hclosed hδ T cs hPc H B
    (stepSubrepresentationMap P M U h hclosed T cs φ I s (i + 1) f) q
  have b := stepRestriction_eval P M U h hclosed hδ T cs hPc H A f q
  refine a.trans ?_
  rw [b]
  rfl

end Natural

section OrbitNatural

variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)} {hU : Antitone U}
  {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}
  {I : Finset ι} {A B : SmoothRep.{0, uG, max uG uV} ℂ G}
  {w : Group.RelativeWeyl.Weyl T} {m : G} {K : Finset ι}
  {hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K}

/-- Naturality of orbit Jacquet data along `φ : A ⟶ B`: for every surviving
`s`, orbit functions `ψ` for `A` and `ψ'` for `B` with
`ψ'(q) = [φ](ψ(q))` for all `q ∈ P_I` satisfy `Θ'_s ψ' = [φ](Θ_s ψ)`, where
`[φ]` is the induced map of `U_J`-coinvariants, respectively of
`U_K`-coinvariants. -/
def OrbitJacquetData.IsNatural (DA : OrbitJacquetData P M U h hclosed hU T cs I A w m K hK)
    (DB : OrbitJacquetData P M U h hclosed hU T cs I B w m K hK) (φ : A ⟶ B) : Prop :=
  ∀ (s : Finset ι) (hKs : K ⊆ Finset.univ \ s)
    (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w)
    (ψ : (Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
      (inducingObject P M U h A (Finset.univ \ s)))
    (ψ' : (Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
      (inducingObject P M U h B (Finset.univ \ s))),
    (∀ q : P I, Induction.eval _ _ ψ'.val q =
      Jacquet.Localization.mapLinear (U (Finset.univ \ s)) 1 (SmoothRep.hom φ)
        (Induction.eval _ _ ψ.val q)) →
    DB.Θ s hKs hs ψ' = Jacquet.Localization.mapLinear (U K) 1 (SmoothRep.hom φ) (DA.Θ s hKs hs ψ)

end OrbitNatural

section StepNatural

variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
  [SigmaCompactSpace G] [T2Space G]
  [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))
  {I s : Finset ι} {i : ℕ} {m : G}
  (H : SurvivingSupportHypotheses P T cs I s i m)
  {A B : SmoothRep.{0, uG, max uG uV} ℂ G} (φ : A ⟶ B)
  (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
  (hU : Antitone U) {w : Group.RelativeWeyl.Weyl T} {K : Finset ι}
  (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)
  (DA : OrbitJacquetData P M U h hclosed hU T cs I A w m K hK)
  (DB : OrbitJacquetData P M U h hclosed hU T cs I B w m K hK)
  (hKs : K ⊆ Finset.univ \ s)
  (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w)

/-- Naturality of `β_s` on elements: if the orbit maps are natural along `φ`,
then `β_s^B (r_I(i_J r_J φ) x) = Ad(m)(r_K φ) (β_s^A x)` on the step `i + 1`. -/
theorem stepGradedMap_natural_apply (hnat : DA.IsNatural DB φ)
    (x : SmoothRep.subrepresentation
      ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed A s))
      (step P M U h hclosed T cs A I s (i + 1))) :
    SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H B hNc hU hK DB hKs hs)
        (SmoothRep.hom (stepMap T cs φ I s (i + 1)) x) =
      SmoothRep.hom ((conjugationFunctor m hK).map
          ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).map φ))
        (SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H A hNc hU hK DA hKs hs) x) := by
  obtain ⟨x, f, hf, rfl⟩ := x
  have hφf := termMap_mem_inductionStep φ I s (i + 1) hf
  have ex : SmoothRep.hom (stepMap T cs φ I s (i + 1))
      ⟨Jacquet.Localization.mk (term P M U h hclosed A s).representation (U I) 1 f,
        ⟨f, hf, rfl⟩⟩ =
      ⟨Jacquet.Localization.mk (term P M U h hclosed B s).representation (U I) 1
        (SmoothRep.hom (termMap P M U h hclosed φ s) f), ⟨_, hφf, rfl⟩⟩ :=
    Subtype.ext rfl
  refine (congrArg (SmoothRep.hom
    (stepGradedMap P M U h hclosed hδ T cs hPc H B hNc hU hK DB hKs hs)) ex).trans ?_
  have eB := stepGradedMap_mk P M U h hclosed hδ T cs hPc H B hNc hU hK DB hKs hs _ hφf
  have eA := stepGradedMap_mk P M U h hclosed hδ T cs hPc H A hNc hU hK DA hKs hs f hf
  refine eB.trans (Eq.trans ?_ (congrArg (SmoothRep.hom ((conjugationFunctor m hK).map
    ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).map φ))) eA).symm)
  exact hnat s hKs hs _ _
    (stepRestriction_natural P M U h hclosed hδ T cs φ hPc H ⟨f, hf⟩)

/-- Naturality square of `β_s`: if the orbit maps are natural along `φ`, then
`r_I(i_J r_J φ)|_{step (i+1)} ≫ β_s^B = β_s^A ≫ Ad(m)(r_K φ)`. -/
theorem stepGradedMap_natural (hnat : DA.IsNatural DB φ) :
    stepMap T cs φ I s (i + 1) ≫
        stepGradedMap P M U h hclosed hδ T cs hPc H B hNc hU hK DB hKs hs =
      stepGradedMap P M U h hclosed hδ T cs hPc H A hNc hU hK DA hKs hs ≫
        (conjugationFunctor m hK).map
          ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).map φ) := by
  have hh : SmoothRep.hom (stepMap T cs φ I s (i + 1) ≫
        stepGradedMap P M U h hclosed hδ T cs hPc H B hNc hU hK DB hKs hs) =
      SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H A hNc hU hK DA hKs hs ≫
        (conjugationFunctor m hK).map
          ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).map φ)) := by
    ext x
    exact stepGradedMap_natural_apply P M U h hclosed hδ T cs hPc H φ hNc hU hK DA DB hKs hs
      hnat x
  simpa only [SmoothRep.ofHom_hom] using congrArg SmoothRep.ofHom hh

end StepNatural

end Langlands.Aubert.General.CorrectedFiltration
