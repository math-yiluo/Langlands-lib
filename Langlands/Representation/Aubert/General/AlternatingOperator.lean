import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.Contragredient.ExactProof
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTransport
import Langlands.Representation.Jacquet.LocalizationExactnessProof
import Langlands.Representation.Induction.SurjectivityProof
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Parabolic.InductionExactnessProof

/-!
# Exact-K0 adapters and Aubert's unadjusted alternating operator

The actual normalized induction and Jacquet functors of
`Langlands.Aubert.General.Parabolic` induce integer-linear maps of the exact
finite-length smooth Grothendieck groups through the published generic functor
map `SmoothRep.FiniteLengthGrothendieckGroup.map`. These maps take the visible
named hypothesis `ParabolicFiniteLength`, so every map and operator below is
conditional on it. Its two exactness conjuncts are proved here from structural
inputs (a limit of compact subgroups for Jacquet restriction; a Hausdorff group
with cofinal compact open subgroups, a closed parabolic and a continuous
projection for induction), in fact for all short exact sequences. Finite-length
preservation is not proved here.

Aubert's Definition 1.5 (printed p. 2181) is the signed sum
`D_G = ∑_{I ⊆ S} (-1)^{|I|} i_I ∘ r_I`, indexed here by all finite subsets of a
finite index type `ι` (the simple relative roots), for an actual family of
semidirect decompositions `P I = M I ⋉ U I`. The Levi version is the same
operator for the group `M J` with index type `J` and the restricted families,
and the empty index type gives the single term `i_∅ ∘ r_∅`.

Conjugation transports and the smooth contragredient also act on exact K0: the
first unconditionally, the second under the named finite-length hypothesis
`ContragredientPreservesFiniteLength` and compact-open cofinality.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uI uG uV

open SmoothRep

section Maps

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Subgroup G}

/-- Named prerequisite for one actual decomposition, at carrier universe `uV`:
normalized induction and normalized Jacquet restriction preserve finite length
and send actual short exact sequences of finite-length representations to short
exact sequences. -/
def ParabolicFiniteLength (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) : Prop :=
  PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU) ∧
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} h hU) ∧
    PreservesFiniteLength (jacquetFunctor.{uG, uV} h hU) ∧
    PreservesFiniteLengthShortExact (jacquetFunctor.{uG, uV} h hU)

/-- Normalized Jacquet restriction sends every actual short exact sequence of
smooth representations, of any length, to a short exact sequence when `U` is a
limit of compact subgroups, by the published `characterLocalizationExactness`;
the twist does not change the underlying maps. -/
theorem jacquetFunctor_map_isShortExact (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    {A B C : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsShortExact (hom f) (hom g)) :
    IsShortExact (hom ((jacquetFunctor.{uG, uV} h hU).map f))
      (hom ((jacquetFunctor.{uG, uV} h hU).map g)) := by
  obtain ⟨hf, hg, hex⟩ := hfg
  obtain ⟨h1, h2, h3⟩ := (Jacquet.Localization.characterLocalizationExactness
    (G := G) (V := A) (W := B) (X := C)).2 U hUc 1
    (IsLocallyConstant.of_constant _ fun _ _ => by simp) M h.levi_le_normalizer
    (Jacquet.Localization.isInvariant_one U M h.levi_le_normalizer)
    A.representation B.representation C.representation (SmoothRep.hom f) (SmoothRep.hom g)
    hf hg hex B.isSmooth
  exact ⟨h1, h3, h2⟩

/-- The exactness conjunct of `ParabolicFiniteLength` for Jacquet restriction:
the finite-length case of `jacquetFunctor_map_isShortExact`. -/
theorem jacquetFunctor_preservesShortExact (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U) :
    PreservesFiniteLengthShortExact (jacquetFunctor.{uG, uV} h hU) :=
  fun _ _ _ f g _ _ _ hfg => jacquetFunctor_map_isShortExact h hU hUc f g hfg

/-- Normalized induction sends every actual short exact sequence of smooth
representations, of any length, to a short exact sequence, for a closed
parabolic in a Hausdorff group with cofinal compact open subgroups, when the
projection is continuous (so that the inducing representations are smooth). The
proof uses the published injectivity, middle-exactness and surjectivity theorems
for smooth induction. -/
theorem normalizedInductionFunctor_map_isShortExact [T2Space G]
    (hcof : CompactOpenCofinal G) (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection)
    {A B C : SmoothRep.{0, uG, uV} ℂ M} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsShortExact (hom f) (hom g)) :
    IsShortExact (hom ((normalizedInductionFunctor.{uG, uV} h hU).map f))
      (hom ((normalizedInductionFunctor.{uG, uV} h hU).map g)) := by
  obtain ⟨hf, hg, hex⟩ := hfg
  have hsm : ∀ X : SmoothRep.{0, uG, uV} ℂ M, IsSmooth (inducingRepresentation h hU X) :=
    fun X => (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter U hU P h.le_normalizer)).mpr
      (isSmooth_comp h.projection hproj X.isSmooth)
  refine ⟨Induction.smoothInducedMap_injective P _ hf, ?_,
    Induction.smoothInducedMap_range_eq_ker P _ _ hf hex⟩
  exact Induction.smoothInductionSurjectivity G (fun K => (hcof K).imp fun L hL => hL) P hP
    B C _ _ (hsm B) (hsm C) _ hg

/-- The exactness conjunct of `ParabolicFiniteLength` for induction: the
finite-length case of `normalizedInductionFunctor_map_isShortExact`. -/
theorem normalizedInductionFunctor_preservesShortExact [T2Space G]
    (hcof : CompactOpenCofinal G) (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) :
    PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, uV} h hU) :=
  fun _ _ _ f g _ _ _ hfg =>
    normalizedInductionFunctor_map_isShortExact hcof h hU hP hproj f g hfg

/-- The named prerequisite from finite-length preservation alone, with exactness
supplied by `jacquetFunctor_preservesShortExact` and
`normalizedInductionFunctor_preservesShortExact`. -/
theorem ParabolicFiniteLength.of_preservesFiniteLength [T2Space G]
    (hcof : CompactOpenCofinal G) (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) (hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U)
    (hi : PreservesFiniteLength (normalizedInductionFunctor.{uG, uV} h hU))
    (hr : PreservesFiniteLength (jacquetFunctor.{uG, uV} h hU)) :
    ParabolicFiniteLength.{uG, uV} h hU :=
  ⟨hi, normalizedInductionFunctor_preservesShortExact hcof h hU hP hproj, hr,
    jacquetFunctor_preservesShortExact h hU hUc⟩

/-- The exact-K0 map of normalized induction, with saturated carriers
`Type (max uG uV)`, conditional on the supplied finite-length hypotheses. -/
def inductionK0 (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h hU)) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  FiniteLengthGrothendieckGroup.map _ hl hx

/-- The exact-K0 map of normalized Jacquet restriction, with saturated carriers
`Type (max uG uV)`, conditional on the supplied finite-length hypotheses. -/
def jacquetK0 (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h hU)) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ M :=
  FiniteLengthGrothendieckGroup.map _ hl hx

@[simp]
theorem inductionK0_ofRepresentation (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (normalizedInductionFunctor.{uG, max uG uV} h hU))
    (A : SmoothRep.{0, uG, max uG uV} ℂ M) (hA : A.HasFiniteLength) :
    inductionK0 h hU hl hx (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((normalizedInductionFunctor.{uG, max uG uV} h hU).obj A) (hl A hA) :=
  FiniteLengthGrothendieckGroup.map_ofRepresentation _ hl hx A hA

@[simp]
theorem jacquetK0_ofRepresentation (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G))
    (hl : PreservesFiniteLength (jacquetFunctor.{uG, max uG uV} h hU))
    (hx : PreservesFiniteLengthShortExact (jacquetFunctor.{uG, max uG uV} h hU))
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.HasFiniteLength) :
    jacquetK0 h hU hl hx (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation
        ((jacquetFunctor.{uG, max uG uV} h hU).obj A) (hl A hA) :=
  FiniteLengthGrothendieckGroup.map_ofRepresentation _ hl hx A hA

/-- The K0 map of the composite endofunctor `i ∘ r` is the composite of the K0
maps. -/
theorem inductionK0_comp_jacquetK0 (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hfl : ParabolicFiniteLength.{uG, max uG uV} h hU) :
    (inductionK0 h hU hfl.1 hfl.2.1).comp (jacquetK0 h hU hfl.2.2.1 hfl.2.2.2) =
      FiniteLengthGrothendieckGroup.map (inductionJacquetFunctor.{uG, uV} h hU)
        (hfl.2.2.1.comp hfl.1) (PreservesFiniteLengthShortExact.comp hfl.2.2.1 hfl.2.2.2 hfl.2.1) :=
  (FiniteLengthGrothendieckGroup.map_comp _ _ _ _ _ _ _ _).symm

end Maps

section Operator

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI} [Fintype ι]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hfl : ∀ I, ParabolicFiniteLength.{uG, max uG uV} (h I) (hU I))

/-- The `I`-th term `i_I ∘ r_I` on exact K0. -/
def alternatingTerm (I : Finset ι) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  (inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1).comp
    (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2)

/-- The unadjusted alternating operator of Aubert's Definition 1.5:
`D_G = ∑_{I ⊆ S} (-1)^{|I|} i_I ∘ r_I`, the sum over all finite subsets `I` of
the index type, on the exact finite-length Grothendieck group with carriers
`Type (max uG uV)`. It is conditional on the hypotheses `hfl`. -/
def alternatingOperator :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G :=
  ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) • alternatingTerm P M U h hU hfl I

theorem alternatingOperator_apply
    (x : FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ G) :
    alternatingOperator P M U h hU hfl x =
      ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
        inductionK0 (h I) (hU I) (hfl I).1 (hfl I).2.1
          (jacquetK0 (h I) (hU I) (hfl I).2.2.1 (hfl I).2.2.2 x) := by
  rw [alternatingOperator, LinearMap.sum_apply]
  rfl

omit [Fintype ι] in
include hfl in
/-- Normalized induction after normalized Jacquet restriction of a finite-length
representation has finite length, under the named hypotheses. -/
theorem inductionJacquet_hasFiniteLength (I : Finset ι)
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (hA : A.HasFiniteLength) :
    ((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A).HasFiniteLength :=
  (hfl I).1 _ ((hfl I).2.2.1 A hA)

/-- The class formula: on the class of an actual finite-length smooth
representation, `D_G` is the signed sum of the classes of its actual normalized
inductions after normalized Jacquet modules. -/
theorem alternatingOperator_ofRepresentation (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (hA : A.HasFiniteLength) :
    alternatingOperator P M U h hU hfl (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      ∑ I : Finset ι, ((-1 : ℤ) ^ I.card) •
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((inductionJacquetFunctor.{uG, uV} (h I) (hU I)).obj A)
          (inductionJacquet_hasFiniteLength P M U h hU hfl I A hA) := by
  rw [alternatingOperator_apply]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [jacquetK0_ofRepresentation, inductionK0_ofRepresentation]
  rfl

/-- The empty-root-set case: with no simple roots the operator is the single
term `i_∅ ∘ r_∅`, with sign `+1`. -/
theorem alternatingOperator_of_isEmpty [IsEmpty ι] :
    alternatingOperator P M U h hU hfl = alternatingTerm P M U h hU hfl ∅ := by
  rw [alternatingOperator, Fintype.sum_unique]
  simp [Subsingleton.elim (default : Finset ι) ∅]

end Operator

section Levi

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {ι : Type uI}
variable (P M U : Finset ι → Subgroup G)

/-- The index finsets of `J` read as finsets of `ι`. -/
abbrev leviIndex (J : Finset ι) (I : Finset J) : Finset ι :=
  I.map (Function.Embedding.subtype (· ∈ J))

theorem card_leviIndex (J : Finset ι) (I : Finset J) : (leviIndex J I).card = I.card :=
  Finset.card_map _

/-- The Levi version of Aubert's operator on the exact K0 of the closed Levi
`M J`: `D_{M_J} = ∑_{I ⊆ J} (-1)^{|I|} i^{M_J}_{I} ∘ r^{M_J}_{I}`, built from the
restricted decompositions `(P I ⊓ M J) = (M I) ⋉ (U I ⊓ M J)` read inside
`M J`. It is the general operator for the group `M J` and the index type `J`. -/
def leviAlternatingOperator (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)) :
    FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, max uG uV} ℂ (M J) :=
  letI := hM.locallyCompactSpace
  alternatingOperator (fun I : Finset J => (P (leviIndex J I)).subgroupOf (M J))
    (fun I => (M (leviIndex J I)).subgroupOf (M J))
    (fun I => (U (leviIndex J I)).subgroupOf (M J)) hJ
    (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val) hfl

/-- The Levi version is the general alternating sum, with signs `(-1)^{|I|}`
for the index finsets `I` of `J`. -/
theorem leviAlternatingOperator_eq (J : Finset ι) (hM : IsClosed (M J : Set G))
    (hJ : ∀ I : Finset J, IsSemidirectDecomposition ((P (leviIndex J I)).subgroupOf (M J))
      ((M (leviIndex J I)).subgroupOf (M J)) ((U (leviIndex J I)).subgroupOf (M J)))
    (hU : ∀ I, IsClosed (U I : Set G))
    (hfl : letI := hM.locallyCompactSpace
      ∀ I : Finset J, ParabolicFiniteLength.{uG, max uG uV} (hJ I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)) :
    letI := hM.locallyCompactSpace
    leviAlternatingOperator P M U J hM hJ hU hfl =
      ∑ I : Finset J, ((-1 : ℤ) ^ (leviIndex J I).card) •
        alternatingTerm (fun I : Finset J => (P (leviIndex J I)).subgroupOf (M J))
          (fun I => (M (leviIndex J I)).subgroupOf (M J))
          (fun I => (U (leviIndex J I)).subgroupOf (M J)) hJ
          (fun I => (hU (leviIndex J I)).preimage continuous_subtype_val) hfl I := by
  simp only [card_leviIndex]
  rfl

end Levi

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation transport on exact K0, `[σ] ↦ [ᵍσ]`; it is unconditional. -/
def conjugationK0 (g : G) {M N : Subgroup G} (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ M →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ N :=
  FiniteLengthGrothendieckGroup.pullback (conjugationEquiv g hMN)

@[simp]
theorem conjugationK0_ofRepresentation (g : G) {M N : Subgroup G}
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) (A : SmoothRep.{0, uG, uV} ℂ M)
    (hA : A.HasFiniteLength) (hOut : ((conjugationFunctor g hMN).obj A).HasFiniteLength) :
    conjugationK0 g hMN (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation ((conjugationFunctor g hMN).obj A) hOut :=
  FiniteLengthGrothendieckGroup.pullback_ofRepresentation _ A hA hOut

/-- In a locally compact nonarchimedean group, compact open subgroups are cofinal
among the open subgroups: an open subgroup inside a compact neighbourhood of `1`
is closed, hence compact. -/
theorem compactOpenCofinal_of_nonarchimedean (H : Type uG) [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [NonarchimedeanGroup H] : CompactOpenCofinal H := by
  intro K
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : H)
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _
    (Filter.inter_mem hC K.mem_nhds_one)
  exact ⟨V, hCc.of_isClosed_subset V.isClosed (hV.trans Set.inter_subset_left),
    fun x hx => (hV hx).2⟩

/-- Named prerequisite: the smooth contragredient of every finite-length smooth
complex representation of `H` has finite length. -/
def ContragredientPreservesFiniteLength (H : Type uG) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] : Prop :=
  ∀ A : SmoothRep.{0, uG, uV} ℂ H, A.HasFiniteLength → A.contragredient.HasFiniteLength

variable (H : Type uG) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The class function `[A] ↦ [Ã]` of the smooth contragredient. -/
def contragredientClass (hl : ContragredientPreservesFiniteLength.{uG, uV} H) :
    FiniteLengthIsoClass.{0, uG, uV} ℂ H → FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ H :=
  Quotient.lift (s := finiteLengthIsoSetoid ℂ H)
    (fun A => FiniteLengthGrothendieckGroup.ofObject ⟨A.val.contragredient, hl A.val A.property⟩)
    (fun _ _ e => e.elim fun e =>
      (FiniteLengthGrothendieckGroup.ofObject_eq_of_iso (contragredientIso e)).symm)

/-- The contragredient is exact additive: an actual short exact sequence
`0 → A → B → C → 0` gives `0 → C̃ → B̃ → Ã → 0` by the published exactness
theorem `smoothContragredientShortExact`, under compact-open cofinality. -/
theorem isExactAdditive_contragredientClass (hcof : CompactOpenCofinal H)
    (hl : ContragredientPreservesFiniteLength.{uG, uV} H) :
    FiniteLengthGrothendieckGroup.IsExactAdditive ℂ H (contragredientClass H hl) := by
  intro A B C f g hfg
  obtain ⟨hf, hg, hrk⟩ := hfg
  have hex : Function.Exact f g :=
    (LinearMap.exact_iff (f := f.toLinearMap) (g := g.toLinearMap)).mpr hrk.symm
  obtain ⟨hg', hex', hf'⟩ := smoothContragredientShortExact hcof A.val.representation
    B.val.representation C.val.representation A.val.isSmooth B.val.isSmooth f g hf hex hg
  have hses : IsShortExact (A := C.val.contragredient) (B := B.val.contragredient)
      (C := A.val.contragredient) (contragredientMap g) (contragredientMap f) :=
    ⟨hg', hf', ((LinearMap.exact_iff (f := (contragredientMap g).toLinearMap)
      (g := (contragredientMap f).toLinearMap)).mp hex').symm⟩
  change FiniteLengthGrothendieckGroup.ofObject ⟨B.val.contragredient, _⟩ =
    FiniteLengthGrothendieckGroup.ofObject ⟨A.val.contragredient, _⟩ +
      FiniteLengthGrothendieckGroup.ofObject ⟨C.val.contragredient, _⟩
  rw [FiniteLengthGrothendieckGroup.ofObject_shortExact
    (A := ⟨C.val.contragredient, hl C.val C.property⟩)
    (B := ⟨B.val.contragredient, hl B.val B.property⟩)
    (C := ⟨A.val.contragredient, hl A.val A.property⟩) hses, add_comm]

/-- The smooth contragredient on exact K0, `[A] ↦ [Ã]`, conditional on the named
finite-length hypothesis and compact-open cofinality. -/
def contragredientK0 (hcof : CompactOpenCofinal H)
    (hl : ContragredientPreservesFiniteLength.{uG, uV} H) :
    FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ H →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ H :=
  FiniteLengthGrothendieckGroup.lift ℂ H (contragredientClass H hl)
    (isExactAdditive_contragredientClass H hcof hl)

@[simp]
theorem contragredientK0_ofRepresentation (hcof : CompactOpenCofinal H)
    (hl : ContragredientPreservesFiniteLength.{uG, uV} H)
    (A : SmoothRep.{0, uG, uV} ℂ H) (hA : A.HasFiniteLength) :
    contragredientK0 H hcof hl (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      FiniteLengthGrothendieckGroup.ofRepresentation A.contragredient (hl A hA) :=
  FiniteLengthGrothendieckGroup.lift_ofRepresentation ℂ H _ _ A hA

end Transport

end Langlands.Aubert.General
