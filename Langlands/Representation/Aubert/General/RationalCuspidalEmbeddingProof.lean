import Langlands.Representation.Aubert.General.RationalCuspidalEmbeddingStatement
import Langlands.Representation.Aubert.General.RationalFirstAdjointness
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry
import Langlands.Representation.Aubert.General.JacquetFiniteGeneration
import Langlands.Representation.Smooth.RenardIrreducibleExistenceProof

/-! # Proof of the cuspidal embedding on actual standard rational-point families -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe uG uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General

namespace CuspidalEmbedding

open SmoothRep Jacquet.Localization

section Modulus

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- The Haar modulus of conjugation on a closed subgroup `U` is trivial on
every subgroup of its normalizer which is a limit of compact subgroups. -/
theorem closedNormalizerCharacter_eq_one_of_compactLimit (U W : Subgroup G)
    (hU : IsClosed (U : Set G)) (hWN : W ≤ Subgroup.normalizer (U : Set G))
    (hWc : IsLimitOfCompactSubgroups W) (w : W) :
    HaarModulus.closedNormalizerCharacter U hU ⟨w, hWN w.2⟩ = 1 := by
  obtain ⟨K, hK, hwK⟩ := hWc {w} isCompact_singleton
  let incl : K →* Subgroup.normalizer (U : Set G) :=
    { toFun := fun x => ⟨((x : W) : G), hWN (x : W).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hincl : Continuous incl := by
    change Continuous fun x : K =>
      (⟨((x : W) : G), hWN (x : W).2⟩ : Subgroup.normalizer (U : Set G))
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  let χ := (HaarModulus.closedNormalizerCharacter U hU).comp incl
  have hopen : IsOpen (χ.ker : Set K) :=
    (HaarModulus.isOpen_ker_closedNormalizerCharacter U hU).preimage hincl
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Finite (K ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  let x : K := ⟨w, hwK rfl⟩
  have hx : x ^ Nat.card (K ⧸ χ.ker) ∈ χ.ker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hpow : ((χ x : NNReal)) ^ Nat.card (K ⧸ χ.ker) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, MonoidHom.mem_ker.mp hx, Units.val_one]
  exact Units.ext ((pow_eq_one_iff_of_nonneg (by positivity) Nat.card_pos.ne').mp hpow)

end Modulus

section Jacquet

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] {P M U : Subgroup H}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set H))

/-- A normalized Jacquet module vanishes when every vector of the source lies in
the actual relation span. -/
theorem subsingleton_jacquet_of_forall_mem_relations (B : SmoothRep.{0, uG, uV} ℂ H)
    (hB : ∀ y : B, y ∈ relations B.representation U 1) :
    Subsingleton ((jacquetFunctor.{uG, uV} h hU).obj B) := by
  constructor
  intro a b
  obtain ⟨a, rfl⟩ := mk_surjective B.representation U 1 a
  obtain ⟨b, rfl⟩ := mk_surjective B.representation U 1 b
  exact (mk_eq_iff B.representation U 1 a b).2 (hB _)

/-- The normalized Jacquet functor preserves actual surjections. -/
theorem jacquet_map_surjective {A B : SmoothRep.{0, uG, uV} ℂ H} (f : A ⟶ B)
    (hf : Function.Surjective (hom f)) :
    Function.Surjective (hom ((jacquetFunctor.{uG, uV} h hU).map f)) := by
  intro y
  obtain ⟨b, rfl⟩ := mk_surjective B.representation U 1 y
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨mk A.representation U 1 a,
    normalizedJacquetFunctor_map_mk U M hU h.levi_le_normalizer f a⟩

/-- Vanishing in stages. Let `V` be a fine radical with `V = (M ⊓ V) U` and
on whose part inside `M` the normalizing character `δ_P^{-1/2}` is trivial.
If the `V`-coinvariants of `A` vanish, every vector of the coarse normalized
Jacquet module `r_U A` lies in the relation span for `V ∩ M`. -/
theorem mem_relations_of_subsingleton (V : Subgroup H)
    (hprod : ∀ x ∈ V, ∃ w ∈ M ⊓ V, ∃ n ∈ U, w * n = x)
    (hδ : ∀ w : M, (w : H) ∈ V →
      HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer w = 1)
    (A : SmoothRep.{0, uG, uV} ℂ H)
    (hA : Subsingleton (Coinvariants A.representation V 1))
    (y : (jacquetFunctor.{uG, uV} h hU).obj A) :
    y ∈ relations ((jacquetFunctor.{uG, uV} h hU).obj A).representation
      (V.subgroupOf M) 1 := by
  let J := ((jacquetFunctor.{uG, uV} h hU).obj A).representation
  let Φ : A →ₗ[ℂ] Coinvariants J (V.subgroupOf M) 1 :=
    (mk J (V.subgroupOf M) 1).comp (mk A.representation U 1)
  have hΦ : ∀ (x : V) (b : A),
      Φ (A.representation x b) = ((1 : V →* ℂˣ) x : ℂ) • Φ b := by
    intro x b
    obtain ⟨w, ⟨hwM, hwV⟩, n, hn, hx⟩ := hprod x x.2
    have hnb : mk A.representation U 1 (A.representation n b) =
        mk A.representation U 1 b := by
      simpa using mk_apply_subgroup A.representation U 1 ⟨n, hn⟩ b
    have hact : ∀ z : A, mk A.representation U 1 (A.representation w z) =
        action A.representation U 1 M h.levi_le_normalizer
          (isInvariant_one U M h.levi_le_normalizer) ⟨w, hwM⟩
          (mk A.representation U 1 z) := fun _ => rfl
    have h1 : mk A.representation U 1 (A.representation x b) =
        J ⟨w, hwM⟩ (mk A.representation U 1 b) := by
      change _ = ((HaarModulus.closedInverseHalfCharacter U hU M h.levi_le_normalizer
          ⟨w, hwM⟩ : ℂˣ) : ℂ) • mk A.representation U 1 (A.representation w b)
      rw [hδ ⟨w, hwM⟩ hwV, Units.val_one, one_smul, ← hx, map_mul, Module.End.mul_apply,
        hact, hact, hnb]
    have hw : (⟨w, hwM⟩ : M) ∈ V.subgroupOf M := hwV
    change mk J (V.subgroupOf M) 1 (mk A.representation U 1 (A.representation x b)) =
      ((1 : V →* ℂˣ) x : ℂ) • mk J (V.subgroupOf M) 1 (mk A.representation U 1 b)
    rw [h1]
    have hrel := mk_apply_subgroup J (V.subgroupOf M) 1 ⟨⟨w, hwM⟩, hw⟩
      (mk A.representation U 1 b)
    simpa using hrel
  have hrel : relations A.representation V 1 ≤ LinearMap.ker Φ :=
    (relations_le_ker_iff A.representation V 1 Φ).2 hΦ
  obtain ⟨a, rfl⟩ := mk_surjective A.representation U 1 y
  have ha : a ∈ relations A.representation V 1 :=
    (mk_eq_zero A.representation V 1 a).1 (Subsingleton.elim _ _)
  exact (mk_eq_zero J (V.subgroupOf M) 1 _).1 (hrel ha)

end Jacquet

end CuspidalEmbedding

namespace RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.2.1, Corollary, on the actual standard rational-point families. -/
theorem rationalCuspidalEmbedding : RationalCuspidalEmbeddingStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter _hEndpoints hRoots hU hM hCompact hUc h hL π hπ
  let : Fintype (SimpleRoot i ν) := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have : π.representation.IsIrreducible := hπ
  -- A nonzero vector of `π`.
  obtain ⟨v₀, hv₀⟩ : ∃ x : π, x ≠ 0 := by
    have : Nontrivial π.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (RationalPoint k G.X)) _
    exact exists_ne (0 : π.representation.asModule)
  -- The standard indices with nonzero actual Jacquet module.
  let S : Set (Finset (SimpleRoot i ν)) :=
    {I | Nontrivial ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π)}
  have hbot : ∀ x : RationalPoint k G.X, x ∈ unipotent i ν Finset.univ → x = 1 := by
    intro x hx
    rw [unipotent_univ_eq_bot i ν] at hx
    exact Subgroup.mem_bot.mp hx
  have huniv : Finset.univ ∈ S := by
    refine ⟨⟨Jacquet.Localization.mk π.representation (unipotent i ν Finset.univ) 1 v₀,
      0, ?_⟩⟩
    intro hzero
    apply hv₀
    have hmem := (Jacquet.Localization.mk_eq_zero _ _ _ v₀).1 hzero
    have hle : Jacquet.Localization.relations π.representation
        (unipotent i ν Finset.univ) 1 ≤ ⊥ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨x, b⟩, rfl⟩
      have hx : (x : RationalPoint k G.X) = 1 := hbot x x.2
      simp [hx]
    exact (Submodule.mem_bot ℂ).1 (hle hmem)
  -- A standard index of minimal cardinality with nonzero Jacquet module.
  obtain ⟨I, hI, hImin⟩ :=
    (measure (Finset.card : Finset (SimpleRoot i ν) → ℕ)).wf.has_min S ⟨_, huniv⟩
  have hsmall : ∀ K : Finset I, K ≠ Finset.univ →
      Subsingleton ((jacquetFunctor.{u, max (u + 1) v} (h (leviIndex I K))
        (hU (leviIndex I K))).obj π) := by
    intro K hK
    rw [← not_nontrivial_iff_subsingleton]
    intro hns
    apply hImin (leviIndex I K) hns
    change (leviIndex I K).card < I.card
    rw [card_leviIndex]
    calc K.card < (Finset.univ : Finset I).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.2 hK)
      _ = I.card := by rw [Finset.card_univ, Fintype.card_coe]
  let := (hM I).locallyCompactSpace
  -- Cuspidality of the minimal nonzero Jacquet module.
  have hcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
      ((jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π) := by
    intro K
    have hsub := leviIndex_subset I K.1
    have hWN : unipotent i ν (leviIndex I K.1) ≤
        Subgroup.normalizer (unipotent i ν I : Set (RationalPoint k G.X)) :=
      (unipotent_le_parabolic_of_subset i ν hInter hG hi hν _ I hsub).trans
        (h I).le_normalizer
    apply CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations
    apply CuspidalEmbedding.mem_relations_of_subsingleton (h I) (hU I)
      (unipotent i ν (leviIndex I K.1))
    · intro x hx
      change x ∈ (unipotent i ν (leviIndex I K.1) : Set (RationalPoint k G.X)) at hx
      rw [unipotent_product_of_subset i ν hInter hG hi hν _ I hsub] at hx
      exact Set.mem_mul.mp hx
    · intro w hwV
      apply (Jacquet.inverseHalfCharacter_eq_one _ _).2
      exact CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit
        (unipotent i ν I) (unipotent i ν (leviIndex I K.1)) (hU I) hWN
        (hUc (leviIndex I K.1)) ⟨w, hwV⟩
    · exact hsmall K.1 K.2
  -- Finite generation and an irreducible quotient.
  have hfg : Module.Finite (MonoidAlgebra ℂ (RationalPoint k G.X))
      π.representation.asModule := inferInstance
  have := hCompact I
  let rI := (jacquetFunctor.{u, max (u + 1) v} (h I) (hU I)).obj π
  have : Nontrivial rI := hI
  have : Module.Finite (MonoidAlgebra ℂ (levi i ν I)) rI.representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient (h I) (hU I) π hfg
  have hco : IsCoatomic (Subrepresentation rI.representation) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso
      (ρ := rI.representation)).isCoatomic_iff.mpr inferInstance
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subrepresentation rI.representation, IsCoatom T₀ := by
    rcases hco.eq_top_or_exists_le_coatom ⊥ with hbot' | ⟨T₀, hT₀, -⟩
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (0 : rI)
      apply hy
      have hmem : y ∈ (⊥ : Subrepresentation rI.representation) := by
        rw [hbot']
        exact Submodule.mem_top
      exact hmem
    · exact ⟨T₀, hT₀⟩
  let σ := SmoothRep.quotient rI T₀
  have hσ : σ.IsIrreducible :=
    SmoothRep.RenardIrreducibleExistence.quotient_isIrreducible_of_isCoatom rI T₀ hT₀
  let q : rI ⟶ σ := SmoothRep.mkQ rI T₀
  have hq : Function.Surjective (SmoothRep.hom q) := SmoothRep.mkQ_surjective rI T₀
  -- The quotient is again cuspidal.
  have hσcusp : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU I (hM I) (hL I)
      σ := by
    intro K
    have := hcusp K
    exact (CuspidalEmbedding.jacquet_map_surjective (hL I K.1) _ q hq).subsingleton
  -- First adjointness and irreducibility give the embedding.
  let F := (RationalPointFamily.FirstAdjointness.equiv i ν hStandard hG hi hν I (hU I)
    π σ).symm (SmoothRep.hom q)
  have hF : F ≠ 0 := by
    intro hF0
    have : σ.representation.IsIrreducible := hσ
    have : Nontrivial σ.representation.asModule :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν I)) _
    obtain ⟨s, hs⟩ := exists_ne (0 : σ.representation.asModule)
    obtain ⟨y, hy⟩ := hq s
    apply hs
    have hq0 : SmoothRep.hom q = 0 := by
      have := congrArg (RationalPointFamily.FirstAdjointness.equiv i ν hStandard hG hi hν I
        (hU I) π σ) hF0
      simpa [F] using this
    rw [← hy, hq0]
    rfl
  have hinj : Function.Injective F :=
    (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF
  exact ⟨I, hI, hcusp, σ, hσ, hσcusp, SmoothRep.ofHom F, hinj⟩

end RationalPointFamily

end Langlands.Aubert.General
