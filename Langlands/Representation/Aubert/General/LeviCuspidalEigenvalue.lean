import Langlands.Representation.Aubert.General.CorollaryExchangeAssembly
import Langlands.Representation.Aubert.General.RationalCuspidalEigenvalueProof
import Langlands.Representation.Aubert.General.RationalLeviCuspidalJacquet

/-!
# The cuspidal eigenvalue of the unadjusted operator inside a standard Levi

For an actual family of semidirect decompositions whose full-subset term has
`P univ = ⊤` and `U univ = ⊥`, the full term `i_univ ∘ r_univ` returns the
class of the input, and every proper term vanishes on a representation whose
proper Jacquet modules are zero objects. Hence the unadjusted operator has
eigenvalue `(-1)^|ι|` on such a class. Inside the closed Levi `M J`, the
restricted families at `leviIndex J univ = J` have exactly these endpoints, so
`D_{M_J} [σ] = (-1)^|J| [σ]` for every `σ` with `IsCorollaryLeviCuspidal`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

section Top

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G}

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The Levi and unipotent parts of a semidirect decomposition meet trivially. -/
theorem IsSemidirectDecomposition.disjoint_levi_unipotent
    (h : IsSemidirectDecomposition P M U) : Disjoint M U := by
  rw [Subgroup.disjoint_def]
  intro x hxM hxU
  have hx := Subgroup.disjoint_def.mp h.isComplement'.disjoint
    (x := (⟨x, h.levi_le hxM⟩ : P)) hxM hxU
  exact congrArg Subtype.val hx

/-- The trivial subgroup is unimodular. -/
theorem isUnimodularModulus_of_eq_bot (hU : IsClosed (U : Set G)) (hbot : U = ⊥) :
    IsUnimodularModulus U hU := by
  intro u
  have hu : (⟨u, Subgroup.le_normalizer u.2⟩ : Subgroup.normalizer (U : Set G)) = 1 := by
    apply Subtype.ext
    have hmem : (u : G) ∈ (⊥ : Subgroup G) := hbot ▸ u.2
    exact Subgroup.mem_bot.mp hmem
  rw [hu, map_one]

end Top

section Operator

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))

/-- The eigenvalue `(-1)^|ι|` of the unadjusted operator on the class of a
finite-length representation all of whose proper Jacquet modules are zero
objects, for a family with `P univ = ⊤` and `U univ = ⊥`. -/
theorem alternatingOperator_ofRepresentation_of_isZero_jacquet
    (hPtop : P Finset.univ = ⊤) (hUbot : U Finset.univ = ⊥)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.HasFiniteLength)
    (hcusp : ∀ I : Finset ι, I ≠ Finset.univ →
      IsZero ((jacquetFunctor.{uG, max uG uV} (h I) (hU I)).obj A)) :
    alternatingOperator P M U h hU hfl (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      ((-1 : ℤ) ^ Fintype.card ι) • FiniteLengthGrothendieckGroup.ofRepresentation A hA := by
  rw [alternatingOperator_apply, Finset.sum_eq_single Finset.univ]
  · rw [jacquetK0_ofRepresentation, inductionK0_ofRepresentation, Finset.card_univ]
    congr 1
    exact RationalPointFamily.inductionJacquetClass_of_top_bot (h Finset.univ)
      (hU Finset.univ) (isUnimodularModulus_of_eq_bot (hU Finset.univ) hUbot)
      hPtop hUbot A hA _
  · intro I _ hI
    rw [jacquetK0_ofRepresentation, class_eq_zero_of_isZero _ _ (hcusp I hI),
      map_zero, smul_zero]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

end Operator

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- The inside-Levi cuspidal eigenvalue: for an actual finite-length `σ` of the
closed Levi `M J` whose proper inside-Levi Jacquet modules vanish,
`D_{M_J} [σ] = (-1)^|J| [σ]`. The full term uses the ambient decomposition
`P J = M J ⋉ U J`, which gives `(P J).subgroupOf (M J) = ⊤` and
`(U J).subgroupOf (M J) = ⊥`. -/
theorem leviAlternatingOperator_ofObject_of_isCorollaryLeviCuspidal
    (J : Finset ι) (hPJ : IsSemidirectDecomposition (P J) (M J) (U J))
    (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val))
    (σ : FiniteLengthObject.{0, uG, max uG uV} ℂ (M J))
    (hσ : IsCorollaryLeviCuspidal P M U J hM hJ hU σ.val) :
    leviAlternatingOperator P M U J hM hJ hU hfl (FiniteLengthGrothendieckGroup.ofObject σ) =
      ((-1 : ℤ) ^ J.card) • FiniteLengthGrothendieckGroup.ofObject σ := by
  let _ := hM.locallyCompactSpace
  have hPtop : (P (leviIndex J (Finset.univ : Finset J))).subgroupOf (M J) = ⊤ := by
    rw [CuspidalEmbedding.leviIndex_univ]
    exact Subgroup.subgroupOf_eq_top.mpr hPJ.levi_le
  have hUbot : (U (leviIndex J (Finset.univ : Finset J))).subgroupOf (M J) = ⊥ := by
    rw [CuspidalEmbedding.leviIndex_univ]
    exact Subgroup.subgroupOf_eq_bot.mpr hPJ.disjoint_levi_unipotent.symm
  have key := alternatingOperator_ofRepresentation_of_isZero_jacquet
    (fun I : Finset J => (P (leviIndex J I)).subgroupOf (M J))
    (fun I => (M (leviIndex J I)).subgroupOf (M J))
    (fun I => (U (leviIndex J I)).subgroupOf (M J)) hJ
    (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val) hfl hPtop hUbot
    σ.val σ.property hσ
  rw [Fintype.card_coe] at key
  exact key

end Levi

end Langlands.Aubert.General
