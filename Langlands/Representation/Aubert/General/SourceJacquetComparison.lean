import Langlands.Representation.Aubert.General.GeometricK0Target
import Langlands.Representation.Aubert.General.SupportCategory

/-! # Comparing an actual source Jacquet functor with a standard restriction -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

open SmoothRep

universe uI uG uV

section Identity

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The existing identity-conjugation object isomorphisms are natural. -/
def conjugationFunctorOneNatIso {L : Subgroup G}
    (hn : ∀ x : G, x ∈ L ↔ (1 : G)⁻¹ * x * 1 ∈ L) :
    conjugationFunctor.{uG, uV} 1 hn ≅ 𝟭 (SmoothRep.{0, uG, uV} ℂ L) :=
  NatIso.ofComponents (conjugationFunctorOneIso hn) (fun {A B} f => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A subgroup equality supplies the membership witness for identity transport. -/
theorem identityConjugationMembership {L L' : Subgroup G} (h : L = L') :
    ∀ x : G, x ∈ L' ↔ (1 : G)⁻¹ * x * 1 ∈ L := by
  intro x
  simp [h]

end Identity

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {M Q L N Q' L' N' : Subgroup G}

private theorem normalizedJacquetFunctor_eq_of_radical_eq
    {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
    [NonarchimedeanGroup H] {V V' A : Subgroup H} (hVV' : V = V')
    (hV : IsClosed (V : Set H)) (hV' : IsClosed (V' : Set H))
    (hAV : A ≤ Subgroup.normalizer (V : Set H))
    (hAV' : A ≤ Subgroup.normalizer (V' : Set H)) :
    normalizedJacquetFunctor.{uG, uV} V A hV hAV =
      normalizedJacquetFunctor V' A hV' hAV' := by
  subst V'
  rfl

/-- Equal ambient Levis and equal restricted radicals identify the actual
normalized Jacquet functors. The parabolic enters only through its supplied
semidirect decomposition; its equality is not needed for this comparison. -/
def leviNormalizedJacquetIsoOfEq
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M) (hL'M : L' ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (h' : IsSemidirectDecomposition
      (Q'.subgroupOf M) (L'.subgroupOf M) (N'.subgroupOf M))
    (hN : IsClosed (N : Set G)) (hN' : IsClosed (N' : Set G))
    (hLL' : L = L') (hNN' : N.subgroupOf M = N'.subgroupOf M) :
    leviNormalizedJacquetFunctor.{uG, uV} hM hLM h hN ⋙
        conjugationFunctor 1 (identityConjugationMembership hLL') ≅
      leviNormalizedJacquetFunctor hM hL'M h' hN' := by
  subst L'
  letI := hM.locallyCompactSpace
  have hJac := normalizedJacquetFunctor_eq_of_radical_eq hNN'
    (hN.preimage continuous_subtype_val) (hN'.preimage continuous_subtype_val)
    h.levi_le_normalizer h'.levi_le_normalizer
  change (normalizedJacquetFunctor _ _ _ _ ⋙
      SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM).symm) ⋙
        conjugationFunctor 1 (identityConjugationMembership rfl) ≅
    normalizedJacquetFunctor _ _ _ _ ⋙
      SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hLM).symm
  rw [hJac]
  exact Functor.isoWhiskerLeft _ (conjugationFunctorOneNatIso _) ≪≫
    Functor.rightUnitor _

end Levi

section GeometricSource

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)
  (hM : ∀ I, IsClosed (M I : Set G)) (hU : ∀ I, IsClosed (U I : Set G))

/-- The actual source Jacquet functor, after the identity identification of
its Levi, is the literal standard restriction once the displayed structural
identities have been supplied. No structural identity is proved here. -/
def geometricSourceJacquetComparisonIso
    (I J K : Finset ι) (n : G)
    (hs : GeometricSourceDecomposition P M U I J n)
    (hKJ : M K ≤ M J)
    (hK : IsSemidirectDecomposition
      ((P K).subgroupOf (M J)) ((M K).subgroupOf (M J)) ((U K).subgroupOf (M J)))
    (hLevi : geometricSourceIntersection (M I) (M J) n = M K)
    (hRadical : (geometricSourceIntersection (U I) (M J) n).subgroupOf (M J) =
      (U K).subgroupOf (M J)) :
    geometricSourceJacquetFunctor.{uI, uG, uV} P M U hM hU I J n hs ⋙
        conjugationFunctor 1 (identityConjugationMembership hLevi) ≅
      leviNormalizedJacquetFunctor (hM J) hKJ hK (hU K) :=
  leviNormalizedJacquetIsoOfEq (hM J) inf_le_left hKJ hs hK
    (isClosed_geometricSourceIntersection (U I) (M J) (hU I) (hM J) n)
    (hU K) hLevi hRadical

end GeometricSource

end Langlands.Aubert.General
