import Langlands.Representation.Aubert.General.JacquetCommonConstituent
import Langlands.Representation.Aubert.General.SupportCategoryStatements
import Langlands.Representation.Aubert.General.SupportCategorySums
import Langlands.Representation.Aubert.General.ConjugationComposition
import Langlands.Representation.Aubert.General.CuspidalRemainderProjection
import Langlands.Representation.Aubert.General.RationalLeviCuspidalRemainderTransport
import Langlands.Representation.Aubert.General.RationalCuspidalJacquetSubquotient
import Langlands.Representation.Category.FiniteGenerationExhaustion
import Langlands.Representation.SubrepresentationLattice
import Langlands.Representation.Aubert.General.RationalLeviCuspidalJacquet
import Langlands.Representation.Aubert.General.RationalJacquetCuspidalReduction
import Langlands.Representation.Aubert.General.RationalSupportAssociationInvariance
import Langlands.Representation.Aubert.General.RootAssociationComposition
import Langlands.Representation.Aubert.General.RationalInductionDualityReduction
import Langlands.Representation.CuspidalSupport.RationalFiniteCuspidalEmbeddingReduction
import Langlands.Representation.CuspidalSupport.RationalLeviSplittingFromWhole
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Support stability under induction after Jacquet restriction, by blocks

The generic reduction below derives `SupportCategoryInductionJacquetTarget` for
all smooth objects from an internal support decomposition, cuspidal/remainder
splittings of Jacquet modules, cuspidal-support association and a minimal
cuspidal factorization of nonzero maps between Jacquet modules. Every one of
these inputs remains explicit.

On the actual rational-point families the minimal factorization, compactness,
unimodularity, compact limits, root-association laws, cuspidality transport and
association invariance are discharged from the Library. The Levi Jacquet
splittings follow from the whole-category cuspidal decomposition. The rational
reduction retains exactly the support decomposition, the whole-category
cuspidal decomposition and the association of cuspidal supports.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj MonoidAlgebra

namespace Langlands.Aubert.General

universe uI uG uV uW

open SmoothRep

section Maps

universe uH

variable {H : Type uH} [Group H] [TopologicalSpace H]

/-- The forward map of an isomorphism of smooth representations is injective. -/
theorem hom_hom_injective_of_iso {A B : SmoothRep.{0, uH, uV} ℂ H} (e : A ≅ B) :
    Function.Injective (hom e.hom) := by
  have hinv : Function.LeftInverse (hom e.inv) (hom e.hom) := by
    intro z
    change hom (e.hom ≫ e.inv) z = z
    rw [e.hom_inv_id]
    rfl
  exact hinv.injective

/-- The inverse map of an isomorphism of smooth representations is surjective. -/
theorem hom_inv_surjective_of_iso {A B : SmoothRep.{0, uH, uV} ℂ H} (e : A ≅ B) :
    Function.Surjective (hom e.inv) := by
  intro z
  refine ⟨hom e.hom z, ?_⟩
  change hom (e.hom ≫ e.inv) z = z
  rw [e.hom_inv_id]
  rfl

/-- A surjective intertwiner onto a nonzero representation is nonzero. -/
theorem hom_ne_zero_of_surjective {A B : SmoothRep.{0, uH, uV} ℂ H} [Nontrivial B]
    (f : A ⟶ B) (hf : Function.Surjective (hom f)) : hom f ≠ 0 := by
  intro he
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  obtain ⟨a, rfl⟩ := hf b
  apply hb
  rw [he]
  rfl

/-- An injective intertwiner out of a nonzero representation is nonzero. -/
theorem hom_ne_zero_of_injective {A B : SmoothRep.{0, uH, uV} ℂ H} [Nontrivial A]
    (f : A ⟶ B) (hf : Function.Injective (hom f)) : hom f ≠ 0 := by
  intro he
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  apply ha
  apply hf
  rw [he, map_zero]
  rfl

end Maps

section LeviExactness

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- Levi-in-Levi normalized Jacquet restriction preserves surjective actual
intertwiners. -/
theorem leviNormalizedJacquetFunctor_map_surjective {M Q L N : Subgroup G}
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G)) {X Y : SmoothRep.{0, uG, uV} ℂ M} (p : X ⟶ Y)
    (hp : Function.Surjective (hom p)) :
    Function.Surjective (hom ((leviNormalizedJacquetFunctor hM hLM h hN).map p)) :=
  Jacquet.Localization.map_surjective _ 1 _ h.levi_le_normalizer
    (Jacquet.Localization.isInvariant_one _ _ h.levi_le_normalizer) (hom p) hp

/-- Levi-in-Levi normalized Jacquet restriction preserves injective actual
intertwiners when the unipotent subgroup inside `M` is a limit of compact
subgroups. -/
theorem leviNormalizedJacquetFunctor_map_injective {M Q L N : Subgroup G}
    (hM : IsClosed (M : Set G)) (hLM : L ≤ M)
    (h : IsSemidirectDecomposition (Q.subgroupOf M) (L.subgroupOf M) (N.subgroupOf M))
    (hN : IsClosed (N : Set G))
    (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups (N.subgroupOf M))
    {X Y : SmoothRep.{0, uG, uV} ℂ M} (i : X ⟶ Y) (hi : Function.Injective (hom i)) :
    Function.Injective (hom ((leviNormalizedJacquetFunctor hM hLM h hN).map i)) :=
  Jacquet.Localization.map_injective_of_smooth _ hNc 1 (IsLocallyConstant.const 1) _
    h.levi_le_normalizer (Jacquet.Localization.isInvariant_one _ _ h.levi_le_normalizer)
    (hom i) hi Y.isSmooth

end LeviExactness

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- A nonzero actual intertwiner out of a normalized Jacquet module gives an
irreducible actual subquotient shared by its source and by the normalized
induction of its target. -/
theorem exists_common_irreducible_of_jacquet_map {P M U : Subgroup G}
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hδ : IsUnimodularModulus U hU)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (σ : SmoothRep.{0, uG, max uG uV} ℂ M)
    (s : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation)
    (hs : s ≠ 0) :
    ∃ π : SmoothRep.{0, uG, max uG uV} ℂ G, π.IsIrreducible ∧ IsSubquotient π A ∧
      IsSubquotient π ((normalizedInductionFunctor h hU).obj σ) := by
  classical
  let f : A ⟶ (normalizedInductionFunctor h hU).obj σ :=
    ofHom ((FirstAdjointness.equiv h hU hδ A σ).symm s)
  have hf : hom f ≠ 0 := by
    intro he
    apply hs
    have he' := congrArg (FirstAdjointness.equiv h hU hδ A σ) he
    simpa only [f, hom_ofHom, LinearEquiv.apply_symm_apply, map_zero] using he'
  let B := image f
  let p : A.representation.IntertwiningMap B.representation :=
    { toLinearMap := (hom f).toLinearMap.rangeRestrict
      isIntertwining' := fun g => by
        ext v
        exact Subtype.ext
          (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }
  have hp : Function.Surjective p := by
    rintro ⟨_, v, hv⟩
    exact ⟨v, Subtype.ext hv⟩
  have hB : Nontrivial B := by
    by_contra he
    have : Subsingleton B := not_nontrivial_iff_subsingleton.mp he
    apply hf
    ext v
    exact congrArg Subtype.val (Subsingleton.elim (p v) 0)
  let := hB
  obtain ⟨π, hπ, hπB⟩ :=
    SmoothRep.RenardIrreducibleExistence.exists_irreducible_subquotient B
  have hBA : IsSubquotient B A :=
    SmoothRep.IsQuotient.isSubquotient ⟨ofHom p, hp⟩
  have hBi : IsSubquotient B ((normalizedInductionFunctor h hU).obj σ) :=
    SmoothRep.IsSubrepresentation.isSubquotient
      (subrepresentation_isSubrepresentation (hom f).range)
  exact ⟨π, hπ, smoothSubquotientTransitivity ℂ G A B π hπB hBA,
    smoothSubquotientTransitivity ℂ G _ B π hπB hBi⟩

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- An actual subsingleton representation lies in every support category, since
it has no irreducible actual subquotient. -/
theorem isInSupportCategory_of_subsingleton {κ : Type uI}
    {P M U : Finset κ → Subgroup G} [LocallyCompactSpace G] [NonarchimedeanGroup G]
    {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
    {hU : ∀ I, IsClosed (U I : Set G)}
    {IsAssociate : Finset κ → Finset κ → G → Prop} {I : Finset κ}
    {hM : IsClosed (M I : Set G)}
    {hI : ∀ K : Finset I, IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I))}
    (X : SmoothRep.{0, uG, max uG uV} ℂ G) [Subsingleton X] :
    IsInSupportCategory P M U h hU IsAssociate I hM hI X := by
  intro π hπ hπX
  exfalso
  obtain ⟨B, i, q, hi, hq⟩ := isSubquotient_iff_exists.mp hπX
  have hB (b : B) : b = 0 := hi (Subsingleton.elim (hom i b) (hom i 0))
  have hDz (d : π) : d = 0 := by
    obtain ⟨b, rfl⟩ := hq d
    rw [hB b, map_zero]
  have := hπ
  apply (bot_ne_top : (⊥ : Subrepresentation π.representation) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext d
  rw [hDz d]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

variable {κ : Type uI}
  {P M U : Finset κ → Subgroup G}
  {h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I)}
  {hU : ∀ I, IsClosed (U I : Set G)}
  {hM : ∀ I, IsClosed (M I : Set G)}
  {hL : ∀ (I : Finset κ) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I))
      ((U (leviIndex I J)).subgroupOf (M I))}
  {IsAssociate : Finset κ → Finset κ → G → Prop}

/-- A nonzero actual intertwiner from the Jacquet module of a member of
`Alg({I})` to a cuspidal representation of `M L` forces `L` to be associated to
`I`, with the actual Levi membership certificate at the same point. -/
theorem exists_association_of_cuspidal_jacquet_map
    (hcompact : ∀ K, CompactSpace (Induction.LeftQuotient (P K)))
    (hδ : ∀ K, IsUnimodularModulus (U K) (hU K))
    (hUc : ∀ (L : Finset κ) (J : Finset L),
      Jacquet.Localization.IsLimitOfCompactSubgroups ((U (leviIndex L J)).subgroupOf (M L)))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset κ) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I L J : Finset κ) (n m : G),
      IsAssociate I L n → IsAssociate L J m → IsAssociate I J (m * n))
    {I L : Finset κ} {X : SmoothRep.{0, uG, max uG uV} ℂ G}
    (hX : IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I) X)
    {C : SmoothRep.{0, uG, max uG uV} ℂ (M L)}
    (hC : IsLeviCuspidal P M U hU L (hM L) (hL L) C)
    (q : (jacquetFunctor (h L) (hU L)).obj X ⟶ C) (hq : hom q ≠ 0) :
    ∃ m : G, IsAssociate I L m ∧ ∀ x : G, x ∈ M L ↔ m⁻¹ * x * m ∈ M I := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, hom q y ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hq
    ext y
    exact hn y
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective X.representation (U L) 1 y
  let N : Submodule ℂ[G] X.representation.asModule :=
    Submodule.span (M := X.representation.asModule) ℂ[G]
      {X.representation.asModuleEquiv.symm x}
  let S : Subrepresentation X.representation := Subrepresentation.ofSubmodule' N
  let A := subrepresentation X S
  have hxS : x ∈ S := by
    change X.representation.asModuleEquiv.symm x ∈ N
    exact Submodule.subset_span (Set.mem_singleton _)
  let x' : A := ⟨x, hxS⟩
  let jN : A.representation.asModule →ₗ[ℂ[G]] N :=
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (hom (subtype X S))).codRestrict N (fun w => w.property)
  have hjN : Function.Bijective jN :=
    ⟨fun _ _ he => Subtype.ext (congrArg Subtype.val he),
      fun w => ⟨⟨w.val, w.property⟩, rfl⟩⟩
  have : Module.Finite ℂ[G] N :=
    Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hfinite : Module.Finite ℂ[G] A.representation.asModule :=
    Module.Finite.equiv (LinearEquiv.ofBijective jN hjN).symm
  let qA : (jacquetFunctor (h L) (hU L)).obj A ⟶ C :=
    (jacquetFunctor (h L) (hU L)).map (subtype X S) ≫ q
  have hqA : hom qA (Jacquet.Localization.mk A.representation (U L) 1 x') ≠ 0 := hy
  let := hcompact L
  have hJfinite : Module.Finite ℂ[M L]
      ((jacquetFunctor (h L) (hU L)).obj A).representation.asModule :=
    JacquetFiniteGeneration.finite_of_compactQuotient (h L) (hU L) A hfinite
  obtain ⟨p, hp⟩ := image_isQuotient qA
  have hBfinite : Module.Finite ℂ[M L] (image qA).representation.asModule :=
    Module.Finite.of_surjective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ (hom p)) hp
  have hBnt : Nontrivial (image qA) :=
    ⟨⟨⟨_, _, rfl⟩, 0, fun he => hqA (congrArg Subtype.val he)⟩⟩
  have hBc : IsLeviCuspidal P M U hU L (hM L) (hL L) (image qA) :=
    IsLeviCuspidal.of_isSubquotient (hUc L) hC
      (SmoothRep.IsSubrepresentation.isSubquotient
        (subrepresentation_isSubrepresentation _))
  obtain ⟨ρ, hρ, t, ht⟩ :=
    JacquetCommonConstituent.exists_irreducible_quotient_of_moduleFinite
      (image qA) hBnt hBfinite
  have hρc : IsLeviCuspidal P M U hU L (hM L) (hL L) ρ :=
    IsLeviCuspidal.of_surjective hBc t ht
  let : IsSimpleModule ℂ[M L] ρ.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ.representation).mp hρ
  have hρnt : Nontrivial ρ := IsSimpleModule.nontrivial ℂ[M L] ρ.representation.asModule
  have hs : hom (p ≫ t) ≠ 0 := by
    intro he
    obtain ⟨r, hr⟩ := exists_ne (0 : ρ)
    obtain ⟨b, rfl⟩ := ht r
    obtain ⟨a, rfl⟩ := hp b
    apply hr
    have := congrArg (fun F => F a) he
    simpa using this
  obtain ⟨π, hπ, hπA, hπi⟩ :=
    exists_common_irreducible_of_jacquet_map (h L) (hU L) (hδ L) A ρ (hom (p ≫ t)) hs
  have hπX : IsSubquotient π X :=
    smoothSubquotientTransitivity ℂ G X A π hπA
      (SmoothRep.IsSubrepresentation.isSubquotient (subrepresentation_isSubrepresentation S))
  obtain ⟨J, n, hn, hIJ, σ, hσ, hcσ, hπσ⟩ := hX π hπ hπX
  have hσn : ((conjugationFunctor n hn).obj σ).IsIrreducible :=
    (Langlands.isIrreducible_comp_continuousMulEquiv_iff
      σ.representation (conjugationEquiv n hn)).mpr hσ
  obtain ⟨m, hm, hJL, _⟩ :=
    hassoc π hπ J L ((conjugationFunctor n hn).obj σ) ρ
      hσn (hconjCusp I J n hn hIJ σ hcσ) hρ hρc hπσ hπi
  exact ⟨m * n, hcomp I J L n m hIJ hJL, conjugationMembership_mul n m hn hm⟩

/-- A nonzero actual intertwiner between normalized Jacquet modules along `K`
factors, nontrivially on both sides, through a cuspidal representation of a
smaller standard Levi, given nonzero cuspidal Levi Jacquet modules of nonzero
representations of each Levi and Jacquet restriction in stages. Take such a
Levi Jacquet module `W` of the image `Y`; the stages isomorphism identifies the
induced maps with maps `r_L(A) → W` (surjective) and `W → r_L(B)` (injective). -/
theorem exists_cuspidal_factorization_of_jacquet_map_of_stages
    (hle : ∀ (K : Finset κ) (I : Finset K), M (leviIndex K I) ≤ M K)
    (hNc : ∀ (K : Finset κ) (I : Finset K),
      Jacquet.Localization.IsLimitOfCompactSubgroups ((U (leviIndex K I)).subgroupOf (M K)))
    (hexists : ∀ (K : Finset κ) (τ : SmoothRep.{0, uG, uW} ℂ (M K)), Nontrivial τ →
      ∃ I : Finset K,
        Nontrivial ((leviNormalizedJacquetFunctor (hM K) (hle K I) (hL K I)
          (hU (leviIndex K I))).obj τ) ∧
        IsLeviCuspidal P M U hU (leviIndex K I) (hM (leviIndex K I)) (hL (leviIndex K I))
          ((leviNormalizedJacquetFunctor (hM K) (hle K I) (hL K I)
            (hU (leviIndex K I))).obj τ))
    (hstages : ∀ (K : Finset κ) (I : Finset K),
      jacquetFunctor.{uG, uW} (h K) (hU K) ⋙
          leviNormalizedJacquetFunctor (hM K) (hle K I) (hL K I) (hU (leviIndex K I)) ≅
        jacquetFunctor (h (leviIndex K I)) (hU (leviIndex K I)))
    {K : Finset κ} {A B : SmoothRep.{0, uG, uW} ℂ G}
    (φ : (jacquetFunctor (h K) (hU K)).obj A ⟶ (jacquetFunctor (h K) (hU K)).obj B)
    (hφ : hom φ ≠ 0) :
    ∃ (L : Finset κ) (W : SmoothRep.{0, uG, uW} ℂ (M L)),
      IsLeviCuspidal P M U hU L (hM L) (hL L) W ∧
      (∃ q : (jacquetFunctor (h L) (hU L)).obj A ⟶ W, hom q ≠ 0) ∧
      (∃ j : W ⟶ (jacquetFunctor (h L) (hU L)).obj B, hom j ≠ 0) := by
  classical
  obtain ⟨p, hp⟩ := image_isQuotient φ
  have hY : Nontrivial (image φ) := by
    obtain ⟨y, hy⟩ : ∃ y, hom φ y ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hφ (by ext y; exact hn y)
    exact ⟨⟨⟨_, y, rfl⟩, 0, fun he => hy (congrArg Subtype.val he)⟩⟩
  obtain ⟨I, hInt, hcusp⟩ := hexists K (image φ) hY
  let R := leviNormalizedJacquetFunctor.{uG, uW} (hM K) (hle K I) (hL K I)
    (hU (leviIndex K I))
  let e := hstages K I
  have hRp : Function.Surjective (hom (R.map p)) :=
    leviNormalizedJacquetFunctor_map_surjective (hM K) _ (hL K I) (hU (leviIndex K I)) p hp
  have hRι : Function.Injective (hom (R.map (imageι φ))) :=
    leviNormalizedJacquetFunctor_map_injective (hM K) _ (hL K I) (hU (leviIndex K I))
      (hNc K I) (imageι φ) (subtype_injective _ _)
  let := hInt
  refine ⟨leviIndex K I, R.obj (image φ), hcusp,
    ⟨(e.app A).inv ≫ R.map p, ?_⟩, ⟨R.map (imageι φ) ≫ (e.app B).hom, ?_⟩⟩
  · apply hom_ne_zero_of_surjective
    rw [SmoothRep.hom_comp]
    exact hRp.comp (hom_inv_surjective_of_iso (e.app A))
  · apply hom_ne_zero_of_injective
    rw [SmoothRep.hom_comp]
    exact (hom_hom_injective_of_iso (e.app B)).comp hRι

/-- The block argument for all smooth objects. Every irreducible subquotient of
`i_K r_K(E)` lies in a summand `S_J` of the supplied decomposition. A nonzero
summand gives, by first adjointness and the supplied minimal cuspidal
factorization, nonzero maps `r_L(S_J) → W` and `W → r_L(E)` with `W` cuspidal.
The splitting of `r_L(E)` turns the second into a nonzero map to a cuspidal
component. Association of cuspidal supports, applied twice, associates `J` to
`I`, and association invariance places `S_J` in `Alg({I})`. -/
theorem supportCategoryInductionJacquet_of_decomposition_and_splitting
    (hcompact : ∀ K, CompactSpace (Induction.LeftQuotient (P K)))
    (hδ : ∀ K, IsUnimodularModulus (U K) (hU K))
    (hUc : ∀ (L : Finset κ) (J : Finset L),
      Jacquet.Localization.IsLimitOfCompactSubgroups ((U (leviIndex L J)).subgroupOf (M L)))
    (hdec : SupportCategoryDecompositionTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hsplit : ∀ (X : SmoothRep.{0, uG, max uG uV} ℂ G) (L : Finset κ),
      HasLeviCuspidalRemainderSplitting P M U hU L (hM L) (hL L)
        ((jacquetFunctor (h L) (hU L)).obj X))
    (hminimal : ∀ (K : Finset κ) (A B : SmoothRep.{0, uG, max uG uV} ℂ G)
      (φ : (jacquetFunctor (h K) (hU K)).obj A ⟶ (jacquetFunctor (h K) (hU K)).obj B),
      hom φ ≠ 0 →
      ∃ (L : Finset κ) (W : SmoothRep.{0, uG, max uG uV} ℂ (M L)),
        IsLeviCuspidal P M U hU L (hM L) (hL L) W ∧
        (∃ q : (jacquetFunctor (h L) (hU L)).obj A ⟶ W, hom q ≠ 0) ∧
        (∃ j : W ⟶ (jacquetFunctor (h L) (hU L)).obj B, hom j ≠ 0))
    (hassoc : CuspidalSupportAssociationTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate)
    (hconjCusp : ∀ (I J : Finset κ) (n : G)
      (hn : ∀ x : G, x ∈ M J ↔ n⁻¹ * x * n ∈ M I),
      IsAssociate I J n →
      ∀ σ : SmoothRep.{0, uG, max uG uV} ℂ (M I),
        IsLeviCuspidal P M U hU I (hM I) (hL I) σ →
        IsLeviCuspidal P M U hU J (hM J) (hL J)
          ((conjugationFunctor n hn).obj σ))
    (hcomp : ∀ (I L J : Finset κ) (n m : G),
      IsAssociate I L n → IsAssociate L J m → IsAssociate I J (m * n))
    (hinv : ∀ (I J : Finset κ) (n : G), IsAssociate I J n → IsAssociate J I n⁻¹)
    (hinvariant : SupportCategoryAssociationInvarianceTarget.{uI, uG, uV}
      P M U h hU hM hL IsAssociate) :
    SupportCategoryInductionJacquetTarget.{uI, uG, uV} P M U h hU hM hL IsAssociate := by
  classical
  intro I K E hE
  let F := (inductionJacquetFunctor.{uG, uV} (h K) (hU K)).obj E
  obtain ⟨S, hS, hint⟩ := hdec F
  have hsummand : ∀ J, IsInSupportCategory P M U h hU IsAssociate I (hM I) (hL I)
      (subrepresentation F (S J)) := by
    intro J
    by_cases hnt : Nontrivial (subrepresentation F (S J))
    · let incl := subtype F (S J)
      have hincl : hom incl ≠ 0 := by
        intro he
        obtain ⟨w, hw⟩ := exists_ne (0 : subrepresentation F (S J))
        apply hw
        apply subtype_injective F (S J)
        change hom incl w = hom incl 0
        rw [he, map_zero]
        rfl
      let e := FirstAdjointness.equiv (h K) (hU K) (hδ K) (subrepresentation F (S J))
        ((jacquetFunctor (h K) (hU K)).obj E)
      let φ : (jacquetFunctor (h K) (hU K)).obj (subrepresentation F (S J)) ⟶
          (jacquetFunctor (h K) (hU K)).obj E :=
        ofHom (e (hom incl))
      have hφ : hom φ ≠ 0 := by
        intro he
        apply hincl
        have he' : e (hom incl) = e 0 := by
          rw [map_zero]
          exact he
        exact e.injective he'
      obtain ⟨L, W, hW, ⟨q, hq⟩, ⟨j, hj⟩⟩ := hminimal K _ E φ hφ
      obtain ⟨m₁, hJL, hm₁⟩ :=
        exists_association_of_cuspidal_jacquet_map hcompact hδ hUc hassoc hconjCusp hcomp
          (hS J) hW q hq
      let := (hM L).locallyCompactSpace
      obtain ⟨C, hC, p, hp⟩ := HasCuspidalRemainderSplitting.exists_projection (hsplit E L)
      have hpj : p.comp (hom j) ≠ 0 := fun he => hj (hp W hW (hom j) he)
      have hp0 : hom (ofHom p : (jacquetFunctor (h L) (hU L)).obj E ⟶ C) ≠ 0 := by
        intro he
        apply hpj
        change (hom (ofHom p : (jacquetFunctor (h L) (hU L)).obj E ⟶ C)).comp (hom j) = 0
        rw [he]
        rfl
      obtain ⟨m₂, hIL, hm₂⟩ :=
        exists_association_of_cuspidal_jacquet_map hcompact hδ hUc hassoc hconjCusp hcomp
          hE hC (ofHom p) hp0
      exact hinvariant J I (m₂⁻¹ * m₁) (hcomp J L I m₁ m₂⁻¹ hJL (hinv I L m₂ hIL))
        (conjugationMembership_mul m₁ m₂⁻¹ hm₁ (conjugationMembership_inv m₂ hm₂))
        _ (hS J)
    · have : Subsingleton (subrepresentation F (S J)) :=
        not_nontrivial_iff_subsingleton.mp hnt
      exact isInSupportCategory_of_subsingleton _
  have htop : (⨆ J, S J) = ⊤ := by
    apply Subrepresentation.toSubmodule_injective
    rw [Langlands.Subrepresentation.toSubmodule_iSup]
    let : DecidableEq (Finset κ) := Classical.decEq (Finset κ)
    exact hint.submodule_iSup_eq_top
  have hsum := IsInSupportCategory.iSup S hsummand
  rw [htop] at hsum
  exact hsum.of_isSubquotient
    (SmoothRep.IsQuotient.isSubquotient ⟨subtype F ⊤, fun b => ⟨⟨b, Submodule.mem_top⟩, rfl⟩⟩)

end Generic

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

universe u v

section Minimal

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance supportInductionJacquetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))

include hStandard in
/-- Every nontrivial smooth representation of an actual standard Levi has a
nonzero cuspidal standard Jacquet module. This is the minimal-index argument of
`exists_nonzero_cuspidal_leviJacquet`, which uses irreducibility only to obtain
a nonzero vector. -/
theorem exists_nonzero_cuspidal_leviJacquet_of_nontrivial
    (K : Finset (SimpleRoot i ν))
    (τ : SmoothRep.{0, u, v} ℂ (levi i ν K)) [Nontrivial τ] :
    ∃ I : Finset K,
      Nontrivial ((leviNormalizedJacquetFunctor (hM K)
        (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I)
        (hU (leviIndex K I))).obj τ) ∧
      IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU
        (leviIndex K I) (hM (leviIndex K I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (leviIndex K I))
        ((leviNormalizedJacquetFunctor (hM K)
          (levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν K I)
          (hU (leviIndex K I))).obj τ) := by
  classical
  let := (hM K).locallyCompactSpace
  let h := isSemidirectDecomposition_in_levi i ν hInter hG hi hν K
  let hUK := fun I : Finset K => (hU (leviIndex K I)).preimage
    (continuous_subtype_val : Continuous (fun x : levi i ν K => (x : RationalPoint k G.X)))
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : τ)
  let S : Set (Finset K) :=
    {I | Nontrivial ((jacquetFunctor.{u, v} (h I) (hUK I)).obj τ)}
  have hbot : (unipotent i ν (leviIndex K Finset.univ)).subgroupOf
      (levi i ν K) = ⊥ := by
    rw [CuspidalEmbedding.leviIndex_univ]
    exact (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν K).unipotent_subgroupOf_levi_eq_bot
  have huniv : Finset.univ ∈ S := by
    refine ⟨⟨Jacquet.Localization.mk τ.representation
      ((unipotent i ν (leviIndex K Finset.univ)).subgroupOf (levi i ν K)) 1 v₀,
      0, ?_⟩⟩
    intro hzero
    apply hv₀
    have hmem := (Jacquet.Localization.mk_eq_zero _ _ _ v₀).1 hzero
    have hle : Jacquet.Localization.relations τ.representation
        ((unipotent i ν (leviIndex K Finset.univ)).subgroupOf (levi i ν K)) 1 ≤ ⊥ := by
      apply Submodule.span_le.2
      rintro _ ⟨⟨x, b⟩, rfl⟩
      have hx : (x : levi i ν K) = 1 := Subgroup.mem_bot.mp (hbot ▸ x.property)
      simp only [hx, map_one, Module.End.one_apply, MonoidHom.one_apply,
        Units.val_one, one_smul, sub_self]
      exact Submodule.zero_mem _
    exact (Submodule.mem_bot ℂ).1 (hle hmem)
  obtain ⟨I, hI, hImin⟩ :=
    (measure (Finset.card : Finset K → ℕ)).wf.has_min S ⟨_, huniv⟩
  let A := leviIndex K I
  let rI := (jacquetFunctor.{u, v} (h I) (hUK I)).obj τ
  have hAK : levi i ν A ≤ levi i ν K :=
    levi_le_of_subset i ν hInter hG hi hν A K (leviIndex_subset K I)
  let flat := (SmoothRep.pullbackFunctor (subgroupOfContinuousEquiv hAK).symm).obj rI
  refine ⟨I, hI, ?_⟩
  change IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) hU A
    (hM A) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν A) flat
  let := (hM A).locallyCompactSpace
  intro J
  let J' : Finset K := J.val.map (CuspidalEmbedding.descendantEmbedding K I)
  have hlabels : leviIndex K J' = leviIndex A J.val :=
    CuspidalEmbedding.leviIndex_descendantEmbedding K I J.val
  have hsmall : Subsingleton ((jacquetFunctor.{u, v} (h J') (hUK J')).obj τ) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hns
    apply hImin J' hns
    change J'.card < I.card
    rw [Finset.card_map]
    calc J.val.card < (Finset.univ : Finset A).card :=
          Finset.card_lt_card (Finset.ssubset_univ_iff.2 J.property)
      _ = I.card := by rw [Finset.card_univ, Fintype.card_coe, card_leviIndex]
  have hsmall' : Subsingleton (Jacquet.Localization.Coinvariants τ.representation
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)) 1) := by
    rw [← hlabels]
    exact hsmall
  have hsub := leviIndex_subset A J.val
  have hWN : (unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K) ≤
      Subgroup.normalizer
        ((unipotent i ν A).subgroupOf (levi i ν K) : Set (levi i ν K)) :=
    (Subgroup.subgroupOf_mono (levi i ν K)
      (unipotent_le_parabolic_of_subset i ν hInter hG hi hν _ A hsub)).trans
      (h I).le_normalizer
  have hrels : ∀ y : rI, y ∈ Jacquet.Localization.relations rI.representation
      (((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)).subgroupOf
        ((levi i ν A).subgroupOf (levi i ν K))) 1 := by
    apply CuspidalEmbedding.mem_relations_of_subsingleton (h I) (hUK I)
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K))
    · exact unipotent_product_in_levi_of_subsets i ν hInter hG hi hν
        (leviIndex A J.val) A K hsub (leviIndex_subset K I)
    · intro w hwV
      apply (Jacquet.inverseHalfCharacter_eq_one _ _).2
      exact CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit
        _ _ (hUK I) hWN
        (isLimitOfCompactSubgroups_subgroupOf _ _ (hM K)
          (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
            i ν hStandard hG hi hν (leviIndex A J.val))) ⟨w, hwV⟩
    · exact hsmall'
  have hnested : Subsingleton (Jacquet.Localization.Coinvariants rI.representation
      (((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν K)).subgroupOf
        ((levi i ν A).subgroupOf (levi i ν K))) 1) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ a
    obtain ⟨b, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ b
    exact (Jacquet.Localization.mk_eq_iff _ _ _ a b).2 (hrels _)
  have hflat : Subsingleton (Jacquet.Localization.Coinvariants flat.representation
      ((unipotent i ν (leviIndex A J.val)).subgroupOf (levi i ν A)) 1) :=
    (CuspidalEmbedding.subgroupOfPullbackCoinvariantsEquiv hAK
      (unipotent i ν (leviIndex A J.val)) rI).injective.subsingleton
  exact hflat

end Minimal

/-- Full smooth support stability under actual normalized induction after
actual normalized Jacquet restriction on the actual rational-point families,
conditional on the actual support decomposition (Renard, Théorème VI.7.2), the
literal Levi cuspidal/remainder splittings of Jacquet modules and the
association of cuspidal supports (Renard, Théorème VI.5.4). Quotient
compactness, unimodularity, compact limits, the minimal cuspidal Levi Jacquet
module, Jacquet restriction in stages, the root-association laws, cuspidality
transport and association invariance are discharged from the Library. -/
theorem rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association
    (hdec : RationalSupportCategoryDecompositionStatement.{u, v})
    (hsplit : RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, max (u + 1) v})
    (hassoc : RationalCuspidalSupportAssociationStatement.{u, v}) :
    RationalSupportCategoryInductionJacquetStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  have hUc := standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
    i ν hStandard hG hi hν
  exact supportCategoryInductionJacquet_of_decomposition_and_splitting
    (fun K => compactSpace_leftQuotient_parabolic i ν
      BruhatTits.dynamicParabolicQuotientCompact hStandard hG hi hν K)
    (fun K => standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν K (hU K))
    (fun L J => standardLeviUnipotent_isLimitOfCompactSubgroups i ν hUc L (hM L) J)
    (hdec k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    (hsplit k G hG T i hi ν hν hStandard hInter hRoots hU hM)
    (fun _ _ _ φ hφ => exists_cuspidal_factorization_of_jacquet_map_of_stages
      (fun K I => levi_le_of_subset i ν hInter hG hi hν _ K (leviIndex_subset K I))
      (fun K I => standardLeviUnipotent_isLimitOfCompactSubgroups i ν hUc K (hM K) I)
      (fun K τ hτ => by
        let := hτ
        exact exists_nonzero_cuspidal_leviJacquet_of_nontrivial
          i ν hInter hG hi hν hStandard hU hM K τ)
      (fun K I => standardJacquetStagesIso_of_standardCocharacterStatement.{u, v}
        i ν hInter hG hi hν hStandard hU K I (hM K))
      φ hφ)
    (hassoc k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
    (fun _ _ _ hn hIJ σ hc => isLeviCuspidal_conjugation
      i ν hG hi hν hStandard hInter hRoots hN hZ hU hM hn hIJ σ hc)
    (fun _ _ _ _ _ hIL hLJ => rootAssociation_mul i ν hN hZ hIL hLJ)
    (fun _ _ _ hIJ => rootAssociation_inv i ν hN hZ hIJ)
    (rationalSupportCategoryAssociationInvariance
      k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)

/-- The closed whole-category cuspidal decomposition of Renard VI.3.5 gives the
literal Levi cuspidal/remainder splittings of all actual normalized Jacquet
modules, at the same carrier universe. The intrinsic relative root system of
each standard Levi is the published relative root system theorem. -/
theorem rationalLeviJacquetSplitting_of_wholeDecomposition
    (hwhole : CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, v}) :
    RationalLeviJacquetCuspidalRemainderSplittingStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro A L
  exact hasLeviCuspidalRemainderSplitting_of_wholeStatement hwhole G hG T i hi ν
    hStandard hInter hν hU L (hM L)
    (Langlands.GroupScheme.relativeRootSystem k _
      (standardLeviScheme_isConnectedReductive i ν hStandard
        Langlands.GroupScheme.dynamicCentralizerReductive hG hi hν L)
      T _
      (hi.isMaximalSplitTorus_standardLeviTorusFactor i ν (rootSet i ν L)
        (Standard.isRepresentedBy_leviHom i ν (rootSet i ν L))
        (Standard.isClosedSubgroup_leviHom i ν (rootSet i ν L))))
    _

/-- The actual support decomposition, the closed whole-category cuspidal
decomposition (at carrier universe `max (u + 1) v`) and the association of
cuspidal supports together imply full smooth support stability under actual
normalized induction after actual normalized Jacquet restriction. -/
def RationalSupportCategoryInductionJacquetReductionStatement : Prop :=
  RationalSupportCategoryDecompositionStatement.{u, v} →
    CuspidalSupport.RationalWholeCuspidalCategoryDecompositionStatement.{u, max (u + 1) v} →
    RationalCuspidalSupportAssociationStatement.{u, v} →
    RationalSupportCategoryInductionJacquetStatement.{u, v}

/-- The reduction of induction-Jacquet support stability to decomposition,
the whole-category cuspidal decomposition and association of cuspidal
supports. -/
theorem rationalSupportCategoryInductionJacquetReduction :
    RationalSupportCategoryInductionJacquetReductionStatement.{u, v} :=
  fun hdec hwhole hassoc =>
    rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association
      hdec (rationalLeviJacquetSplitting_of_wholeDecomposition hwhole) hassoc

end RationalPointFamily

end Langlands.Aubert.General
