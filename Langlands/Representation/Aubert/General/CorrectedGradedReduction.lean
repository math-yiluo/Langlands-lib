import Langlands.Representation.Aubert.General.CorrectedGradedInterface
import Langlands.Representation.Aubert.CorrectedSupportOrbitQuotient
import Langlands.Representation.Jacquet.LocalizationExactnessProof

/-!
# Conditional surviving graded transitions

A conditional (helper) proof of `CorrectedGradedTransitionTarget` from the
interface data of `CorrectedGradedInterface`:

* Part A: restriction `R_s` of the functions of `E_J` supported in
  `G_{θ_{i+1}'}` to the cell `P_J m⁻¹ P_I` (`stepRestriction`), with kernel and
  surjectivity;
* Part C: descent of `Θ_s ∘ R_s` to the step `i + 1` of `r_I(E_J)`
  (`gradedMap`, `stepGradedMap`) and the assembled theorem
  `correctedGradedTransitionTarget_of_orbitData`.
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

section Support

variable {P : Finset ι → Subgroup G}
  {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Membership of a coset in the image of a left `Q`-invariant set. -/
theorem quotientMap_mem_image_iff {Q : Subgroup G} {X : Set G}
    (hX : ∀ p ∈ Q, ∀ g ∈ X, p * g ∈ X) (g : G) :
    Induction.quotientMap Q g ∈ Induction.quotientMap Q '' X ↔ g ∈ X := by
  constructor
  · rintro ⟨g', hg', he⟩
    have hr : g * g'⁻¹ ∈ Q := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    simpa using hX _ hr g' hg'
  · intro hg
    exact ⟨g, hg, rfl⟩

namespace SurvivingSupportHypotheses

variable {I s : Finset ι} {i : ℕ} {m : G}

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem groupSupport_subset :
    groupSupport P T cs I s i ⊆ groupSupport P T cs I s (i + 1) :=
  cellSupport_mono (modifiedSupport_monotone cs _ I (Nat.le_succ i))

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The lower support is also left `P_J`-invariant. -/
theorem left_lower (H : SurvivingSupportHypotheses P T cs I s i m) :
    ∀ p ∈ P (Finset.univ \ s), ∀ g ∈ groupSupport P T cs I s i,
      p * g ∈ groupSupport P T cs I s i := by
  intro p hp g hg
  by_contra hpg
  have hmem : p * g ∈ groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i :=
    ⟨H.left_upper p hp g (groupSupport_subset hg), hpg⟩
  rw [H.sdiff_eq] at hmem
  obtain ⟨p', hp', q, hq, he⟩ := hmem
  have hg' : g ∈ groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i := by
    rw [H.sdiff_eq]
    refine ⟨p⁻¹ * p', (P _).mul_mem ((P _).inv_mem hp) hp', q, hq, ?_⟩
    have hg : g = p⁻¹ * (p * g) := by group
    rw [hg, he]
    group
  exact hg'.2 hg

omit [LocallyCompactSpace G] in
/-- The two support sets as an open orbit support pair on `P_J \ G`, with the
new orbit `P_J m⁻¹ P_I`. -/
def supportPair (H : SurvivingSupportHypotheses P T cs I s i m) :
    Geometric.OpenOrbitSupportPair (P (Finset.univ \ s)) (P I) m where
  lower := Induction.quotientMap (P (Finset.univ \ s)) '' groupSupport P T cs I s i
  upper := Induction.quotientMap (P (Finset.univ \ s)) '' groupSupport P T cs I s (i + 1)
  lower_invariant q x hx := by
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g * q, cellSupport_mul_right hg q.2, rfl⟩
  upper_invariant q x hx := by
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g * q, cellSupport_mul_right hg q.2, rfl⟩
  lower_open := isOpenMap_quotient_mk'_mul _ H.isOpen_lower
  upper_open := isOpenMap_quotient_mk'_mul _ H.isOpen_upper
  lower_subset_upper := Set.image_mono groupSupport_subset
  difference := by
    ext x
    induction x using Quotient.inductionOn with
    | h g =>
      change Induction.quotientMap _ g ∈ _ ∧ Induction.quotientMap _ g ∉ _ ↔
        Induction.quotientMap _ g ∈ Geometric.cosetOrbit _ _ m
      rw [quotientMap_mem_image_iff H.left_upper, quotientMap_mem_image_iff H.left_lower]
      change g ∈ groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i ↔ _
      rw [H.sdiff_eq]
      constructor
      · rintro ⟨p, hp, q, hq, rfl⟩
        refine ⟨⟨q, hq⟩, ?_⟩
        apply Quotient.sound
        exact QuotientGroup.rightRel_apply.mpr (by simpa [mul_assoc] using hp)
      · rintro ⟨q, hq⟩
        have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
        exact ⟨_, hr, q, q.2, by group⟩

end SurvivingSupportHypotheses

end Support

section OrbitRestriction

variable [SigmaCompactSpace G] [T2Space G] {Q₁ Q₂ : Subgroup G} {w : G}
  (S : Geometric.OpenOrbitSupportPair Q₁ Q₂ w)
  (hQ₁ : IsClosed (Q₁ : Set G)) (hQ₂ : IsClosed (Q₂ : Set G))
  [CompactSpace (Induction.LeftQuotient Q₁)] (A : Induction.SmoothRep.{0, uG, uV} ℂ Q₁)

/-- Restriction to the new orbit `Q₁ w⁻¹ Q₂` of a smooth section supported in the
upper set of an open orbit support pair: the support quotient projection
followed by `smoothQuotientIso`. -/
def orbitRestriction :
    (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
        S.upper_invariant).representation A.obj ⟶
      (Geometric.orbitPiece.{0, uG, uV} Q₁ Q₂ w).obj A :=
  (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.lower
      S.lower_invariant).quotientProjection
      (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
        S.upper_invariant) A.obj ≫
    (S.smoothQuotientIso hQ₁ hQ₂).hom.app A

/-- The orbit restriction evaluates as `q ↦ f(w⁻¹ q)`. -/
theorem orbitRestriction_eval
    (f : (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
        S.upper_invariant).representation A.obj) (q : Q₂) :
    Induction.eval _ _ ((orbitRestriction S hQ₁ hQ₂ A).hom f).val q =
      Induction.eval Q₁ A.obj.ρ f.val (w⁻¹ * (q : G)) :=
  S.smoothQuotientIso_hom_projection_eval hQ₁ hQ₂ A f q

omit [LocallyCompactSpace G] [SigmaCompactSpace G] [T2Space G]
  [CompactSpace (Induction.LeftQuotient Q₁)] in
/-- Elements of an orbit piece agree when their evaluations agree. -/
theorem orbitPiece_ext {g g' : (Geometric.orbitPiece.{0, uG, uV} Q₁ Q₂ w).obj A}
    (hg : ∀ q : Q₂, Induction.eval _ _ g.val q = Induction.eval _ _ g'.val q) :
    g = g' := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext q
  exact hg q

/-- The orbit restriction vanishes exactly on the sections supported in the
lower set. -/
theorem orbitRestriction_eq_zero_iff
    (f : (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
        S.upper_invariant).representation A.obj) :
    (orbitRestriction S hQ₁ hQ₂ A).hom f = 0 ↔
      ∀ x : G, Induction.eval Q₁ A.obj.ρ f.val x ≠ 0 →
        Induction.quotientMap Q₁ x ∈ S.lower := by
  have hlow := S.restriction_zero_iff_lower A.obj.ρ f.val f.property
  rw [← hlow]
  constructor
  · intro hf q
    have key := orbitRestriction_eval S hQ₁ hQ₂ A f q
    rw [hf] at key
    exact key.symm
  · intro hf
    apply orbitPiece_ext
    intro q
    have key := orbitRestriction_eval S hQ₁ hQ₂ A f q
    exact key.trans (hf q)

/-- The orbit restriction is surjective. -/
theorem orbitRestriction_surjective :
    Function.Surjective (orbitRestriction S hQ₁ hQ₂ A).hom := by
  intro g
  obtain ⟨f, hf⟩ := RepSubfunctor.quotientProjection_surjective
    (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.lower
      S.lower_invariant)
    (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
      S.upper_invariant) A.obj (((S.smoothQuotientIso hQ₁ hQ₂).inv.app A).hom g)
  refine ⟨f, ?_⟩
  have key := congrArg (fun φ => φ.hom g) ((S.smoothQuotientIso hQ₁ hQ₂).inv_hom_id_app A)
  change ((S.smoothQuotientIso hQ₁ hQ₂).hom.app A).hom
    (((Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.lower
      S.lower_invariant).quotientProjection
      (Geometric.rawSmoothSupportSubfunctor.{0, uG, uV} (R := ℂ) Q₁ Q₂ S.upper
        S.upper_invariant) A.obj).hom f) = g
  rw [hf]
  exact key

omit [LocallyCompactSpace G] [SigmaCompactSpace G] [T2Space G]
  [CompactSpace (Induction.LeftQuotient Q₁)] in
theorem eval_smoothInducedMap {V W : Type uV} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ Q₁ V}
    {τ : Representation ℂ Q₁ W} (T : σ.IntertwiningMap τ)
    (f : Induction.SmoothFunctions Q₁ σ) (x : G) :
    Induction.eval Q₁ τ (Induction.smoothInducedMap Q₁ T f) x =
      T (Induction.eval Q₁ σ f x) :=
  rfl

end OrbitRestriction

section ImageDescent

variable {V X W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup W] [Module ℂ W] (π : V →ₗ[ℂ] X) (S : Submodule ℂ V) (L : S →ₗ[ℂ] W)
  (hL : ∀ v : S, π v = 0 → L v = 0)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- A linear map on `S` that vanishes on `ker π` descends to the image `π(S)`. -/
def imageDescent : S.map π →ₗ[ℂ] W :=
  (LinearMap.ker (π.submoduleMap S)).liftQ L
      (fun v hv => LinearMap.mem_ker.mpr (hL v (congrArg Subtype.val (LinearMap.mem_ker.mp hv)))) ∘ₗ
    ((π.submoduleMap S).quotKerEquivOfSurjective (π.submoduleMap_surjective S)).symm.toLinearMap

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem imageDescent_apply (v : S) : imageDescent π S L hL (π.submoduleMap S v) = L v := by
  simp only [imageDescent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem imageDescent_surjective (hsurj : Function.Surjective L) :
    Function.Surjective (imageDescent π S L hL) := by
  intro w
  obtain ⟨v, rfl⟩ := hsurj w
  exact ⟨π.submoduleMap S v, imageDescent_apply π S L hL v⟩

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The kernel of the descended map is the image of a subspace `S' ≤ S` when
`L` vanishes on `S'` and every zero of `L` agrees with an element of `S'` modulo
`ker π`. -/
theorem imageDescent_eq_zero_iff {S' : Submodule ℂ V} (hS'S : S' ≤ S)
    (hS' : ∀ v : S, (v : V) ∈ S' → L v = 0)
    (hker : ∀ v : S, L v = 0 → ∃ v' ∈ S', π v' = π v) (x : S.map π) :
    imageDescent π S L hL x = 0 ↔ (x : X) ∈ S'.map π := by
  obtain ⟨v, rfl⟩ := π.submoduleMap_surjective S x
  rw [imageDescent_apply]
  constructor
  · intro h0
    obtain ⟨v', hv', he⟩ := hker v h0
    exact ⟨v', hv', he⟩
  · rintro ⟨v', hv', he⟩
    have hdiff : L (v - ⟨v', hS'S hv'⟩) = 0 := hL _ (by
      change π ((v : V) - v') = 0
      rw [map_sub, sub_eq_zero]
      exact he.symm)
    rw [map_sub, sub_eq_zero] at hdiff
    rw [hdiff]
    exact hS' _ hv'

end ImageDescent

section Relations

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Relations along `N ≤ Q` are relations of the restriction to `Q`. -/
theorem relations_le_subgroupOf {Q N : Subgroup G} (hNQ : N ≤ Q) (ρ : Representation ℂ G V) :
    Jacquet.Localization.relations ρ N 1 ≤
      Jacquet.Localization.relations (ρ.comp Q.subtype) (N.subgroupOf Q) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨u, v⟩, rfl⟩
  exact Jacquet.Localization.sub_mem_relations (ρ.comp Q.subtype) (N.subgroupOf Q) 1
    ⟨⟨u, hNQ u.2⟩, u.2⟩ v

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Relations of a subrepresentation of the restriction to `Q` are relations
along `N`. -/
theorem relations_subrepresentation_le {Q N : Subgroup G} (ρ : Representation ℂ G V)
    (Sr : Subrepresentation (ρ.comp Q.subtype)) (v : Sr.toSubmodule)
    (hv : v ∈ Jacquet.Localization.relations Sr.toRepresentation (N.subgroupOf Q) 1) :
    (v : V) ∈ Jacquet.Localization.relations ρ N 1 := by
  have hle : Jacquet.Localization.relations Sr.toRepresentation (N.subgroupOf Q) 1 ≤
      (Jacquet.Localization.relations ρ N 1).comap Sr.toSubmodule.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u, w⟩, rfl⟩
    exact Jacquet.Localization.sub_mem_relations ρ N 1 ⟨(u : Q), u.2⟩ (w : V)
  exact hle hv

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- Exactness of localization: a vector of a subrepresentation that is a
relation of the ambient smooth representation is already a relation of the
subrepresentation. -/
theorem mem_relations_subrepresentation [IsTopologicalGroup G] {Q N : Subgroup G}
    (hNQ : N ≤ Q) (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups (N.subgroupOf Q))
    {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (Sr : Subrepresentation (ρ.comp Q.subtype)) (v : Sr.toSubmodule)
    (hv : (v : V) ∈ Jacquet.Localization.relations ρ N 1) :
    v ∈ Jacquet.Localization.relations Sr.toRepresentation (N.subgroupOf Q) 1 := by
  let i : Sr.toRepresentation.IntertwiningMap (ρ.comp Q.subtype) :=
    { toLinearMap := Sr.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  have hinj := Jacquet.Localization.map_injective_of_smooth (N.subgroupOf Q) hNc 1
    (IsLocallyConstant.const (1 : ℂ)) ⊥ bot_le
    (Jacquet.Localization.isInvariant_one (N.subgroupOf Q) ⊥ bot_le) i
    Subtype.val_injective (isSmooth_comp Q.subtype continuous_subtype_val hρ)
  rw [← Jacquet.Localization.mk_eq_zero]
  apply hinj
  rw [map_zero, Jacquet.Localization.map_mk, Jacquet.Localization.mk_eq_zero]
  exact relations_le_subgroupOf hNQ ρ hv

end Relations

section GradedDescent

universe uY

variable {Q L N : Subgroup G} (hQ : IsSemidirectDecomposition Q L N) (hN : IsClosed (N : Set G))
  (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups (N.subgroupOf Q))
  (A : SmoothRep.{0, uG, uV} ℂ G) (Sr : Subrepresentation (A.representation.comp Q.subtype))
  {Y : Type uY} [AddCommGroup Y] [Module ℂ Y] {X : Representation ℂ Q Y}
  (R : Sr.toRepresentation.IntertwiningMap X)
  (B : SmoothRep.{0, uG, uV} ℂ L) (Θ : Y →ₗ[ℂ] B)
  (hΘu : ∀ (u : N) (y : Y), Θ (X ⟨u, hQ.unipotent_le u.2⟩ y) = Θ y)
  (hΘl : ∀ (l : L) (y : Y),
    ((HaarModulus.closedInverseHalfCharacter N hN L hQ.levi_le_normalizer l : ℂˣ) : ℂ) •
      Θ (X ⟨l, hQ.levi_le l.2⟩ y) = B.representation l (Θ y))

omit [LocallyCompactSpace G] in
include hNc hΘu in
theorem graded_wellDefined (v : Sr.toSubmodule) (hv : Jacquet.Localization.mk A.representation N 1 v = 0) :
    (Θ ∘ₗ R.toLinearMap) v = 0 := by
  have h1 := (Jacquet.Localization.mk_eq_zero _ _ _ _).mp hv
  have h2 := mem_relations_subrepresentation hQ.unipotent_le hNc A.isSmooth Sr v h1
  have h3 : Jacquet.Localization.relations Sr.toRepresentation (N.subgroupOf Q) 1 ≤
      LinearMap.ker (Θ ∘ₗ R.toLinearMap) := by
    apply (Jacquet.Localization.relations_le_ker_iff _ _ _ _).mpr
    intro u w
    change Θ (R (Sr.toRepresentation u w)) = ((1 : N.subgroupOf Q →* ℂˣ) u : ℂ) • Θ (R w)
    rw [R.isIntertwining, MonoidHom.one_apply, Units.val_one, one_smul]
    exact hΘu ⟨((u : Q) : G), u.2⟩ (R w)
  exact h3 h2

/-- The graded map `[v] ↦ Θ (R v)` on the image of `Sr` in the normalized
Jacquet module, as a linear map. -/
def gradedLinear :
    (Sr.toSubmodule.map (Jacquet.Localization.mk A.representation N 1)) →ₗ[ℂ] B :=
  imageDescent (Jacquet.Localization.mk A.representation N 1) Sr.toSubmodule
    (Θ ∘ₗ R.toLinearMap) (graded_wellDefined hQ hNc A Sr R B Θ hΘu)

omit [LocallyCompactSpace G] in
theorem gradedLinear_apply (v : Sr.toSubmodule) :
    gradedLinear hQ hNc A Sr R B Θ hΘu
        ((Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule v) =
      Θ (R v) :=
  imageDescent_apply _ _ _ _ v

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] in
theorem subrep_stable :
    ∀ q ∈ Q, ∀ v ∈ Sr.toSubmodule, A.representation q v ∈ Sr.toSubmodule :=
  fun q hq _ hv => Sr.apply_mem_toSubmodule ⟨q, hq⟩ hv

/-- The image `r_N(Sr)` of `Sr` in the normalized Jacquet module, as a smooth
representation of `L`. -/
abbrev gradedSource : SmoothRep.{0, uG, uV} ℂ L :=
  SmoothRep.subrepresentation ((jacquetFunctor.{uG, uV} hQ hN).obj A)
    (jacquetImage hQ hN A Sr.toSubmodule (subrep_stable A Sr))

/-- The action on a class: `l · [v] = δ^{-1/2}(l) [l v]`. -/
theorem gradedSource_apply (l : L) (v : Sr.toSubmodule) :
    (gradedSource hQ hN A Sr).representation l
        ((Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule v) =
      ((HaarModulus.closedInverseHalfCharacter N hN L hQ.levi_le_normalizer l : ℂˣ) : ℂ) •
        (Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule
          (Sr.toRepresentation ⟨l, hQ.levi_le l.2⟩ v) :=
  rfl

include hΘl in
/-- The graded map `β : r_N(Sr) → B`, `[v] ↦ Θ (R v)`. -/
def gradedMap : gradedSource hQ hN A Sr ⟶ B :=
  SmoothRep.ofHom
    { toLinearMap := gradedLinear hQ hNc A Sr R B Θ hΘu
      isIntertwining' := fun l => by
        refine LinearMap.ext fun x => ?_
        obtain ⟨v, rfl⟩ :=
          (Jacquet.Localization.mk A.representation N 1).submoduleMap_surjective Sr.toSubmodule x
        change gradedLinear hQ hNc A Sr R B Θ hΘu ((gradedSource hQ hN A Sr).representation l
            ((Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule v)) =
          B.representation l (gradedLinear hQ hNc A Sr R B Θ hΘu
            ((Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule v))
        rw [gradedSource_apply, map_smul, gradedLinear_apply, gradedLinear_apply,
          R.isIntertwining]
        exact hΘl l (R v) }

theorem gradedMap_mk (v : Sr.toSubmodule) :
    SmoothRep.hom (gradedMap hQ hN hNc A Sr R B Θ hΘu hΘl)
        ((Jacquet.Localization.mk A.representation N 1).submoduleMap Sr.toSubmodule v) =
      Θ (R v) :=
  gradedLinear_apply hQ hNc A Sr R B Θ hΘu v

theorem gradedMap_surjective (hR : Function.Surjective R) (hΘ : Function.Surjective Θ) :
    Function.Surjective (SmoothRep.hom (gradedMap hQ hN hNc A Sr R B Θ hΘu hΘl)) := by
  have key := imageDescent_surjective (Jacquet.Localization.mk A.representation N 1)
    Sr.toSubmodule (Θ ∘ₗ R.toLinearMap) (graded_wellDefined hQ hNc A Sr R B Θ hΘu)
    (hΘ.comp hR)
  exact key

/-- The kernel of `β` is the image of `S' = ker R` when `R` is surjective and the
kernel of `Θ` consists of `N`-relations. -/
theorem gradedMap_eq_zero_iff (hR : Function.Surjective R) {S' : Submodule ℂ A}
    (hS'S : S' ≤ Sr.toSubmodule) (hker : ∀ v : Sr.toSubmodule, R v = 0 ↔ (v : A) ∈ S')
    (hΘker : ∀ y : Y, Θ y = 0 → y ∈ Jacquet.Localization.relations X (N.subgroupOf Q) 1)
    (x : gradedSource hQ hN A Sr) :
    SmoothRep.hom (gradedMap hQ hN hNc A Sr R B Θ hΘu hΘl) x = 0 ↔
      x.1 ∈ S'.map (Jacquet.Localization.mk A.representation N 1) := by
  refine imageDescent_eq_zero_iff (Jacquet.Localization.mk A.representation N 1) Sr.toSubmodule
    (Θ ∘ₗ R.toLinearMap) (graded_wellDefined hQ hNc A Sr R B Θ hΘu) hS'S ?_ ?_ x
  · intro v hv
    change Θ (R v) = 0
    rw [(hker v).mpr hv, map_zero]
  · intro v hv
    have hrel := hΘker (R v) hv
    rw [← Jacquet.Localization.relations_map_of_surjective (N.subgroupOf Q) 1 R hR] at hrel
    obtain ⟨v'', hv'', he⟩ := hrel
    refine ⟨(v : A) - v'', ?_, ?_⟩
    · have hk : R (v - v'') = 0 := by
        rw [map_sub, sub_eq_zero]
        exact he.symm
      exact (hker _).mp hk
    · have h0 : Jacquet.Localization.mk A.representation N 1 (v'' : A) = 0 :=
        (Jacquet.Localization.mk_eq_zero _ _ _ _).mpr
          (relations_subrepresentation_le A.representation Sr v'' hv'')
      rw [map_sub, h0, sub_zero]

end GradedDescent

section Restriction

variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))

include hδ in
/-- With `U_J` unimodular, the normalized coefficient action of `E_J` is the
unnormalized quotient action of `inducingObject`. -/
theorem coefficientRepresentation_eq (E : SmoothRep.{0, uG, max uG uV} ℂ G)
    (s : Finset ι) :
    Complex.coefficientRepresentation (StandardComplex.removedFamily P)
        (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
        (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) E s =
      (inducingObject P M U h E (Finset.univ \ s)).representation :=
  inducingRepresentation_jacquet_eq (h _) (hclosed _) (hδ _) E

/-- The functions of `E_J`, `J = S \ s`, supported in `G_{θ_i'}`, as a
representation of `P_I` by right translation. -/
def stepSubrepresentation (E : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι)
    (i : ℕ) :
    Subrepresentation ((term P M U h hclosed E s).representation.comp (P I).subtype) where
  toSubmodule := inductionStep P M U h hclosed T cs E I s i
  apply_mem_toSubmodule q f hf :=
    inductionStep_stable P M U h hclosed T cs E I s i q q.2 f hf

variable [SigmaCompactSpace G] [T2Space G]
  [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))
  {I s : Finset ι} {i : ℕ} {m : G}
  (H : SurvivingSupportHypotheses P T cs I s i m) (E : SmoothRep.{0, uG, max uG uV} ℂ G)

/-- A function of `E_J` supported in `G_{θ_{i+1}'}`, viewed as a smooth function
for the unnormalized quotient action supported in the upper support set of
`P_J \ G`. -/
def supportInclusion :
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1)).toRepresentation.IntertwiningMap
      ((Geometric.rawSmoothSupportSubfunctor.{0, uG, max uG uV} (R := ℂ)
        (P (Finset.univ \ s)) (P I) H.supportPair.upper
        H.supportPair.upper_invariant).representation
        (inducingObject P M U h E (Finset.univ \ s)).obj).ρ where
  toFun f := ⟨Induction.smoothInducedMap (P (Finset.univ \ s))
      (intertwiningOfEq (coefficientRepresentation_eq P M U h hclosed hδ E s)) f.1,
    fun x hx => ⟨x, f.2 x hx, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

/-- The restriction `R_s` of a function supported in `G_{θ_{i+1}'}` to the new
cell `P_J m⁻¹ P_I`, landing in the orbit piece. -/
def stepRestriction :
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1)).toRepresentation.IntertwiningMap
      ((Geometric.orbitPiece.{0, uG, max uG uV} (P (Finset.univ \ s)) (P I) m).obj
        (inducingObject P M U h E (Finset.univ \ s))).ρ :=
  (orbitRestriction H.supportPair (hPc _) (hPc I)
      (inducingObject P M U h E (Finset.univ \ s))).hom.comp
    (supportInclusion P M U h hclosed hδ T cs H E)

theorem stepRestriction_apply
    (f : stepSubrepresentation P M U h hclosed T cs E I s (i + 1)) :
    stepRestriction P M U h hclosed hδ T cs hPc H E f =
      (orbitRestriction H.supportPair (hPc _) (hPc I)
        (inducingObject P M U h E (Finset.univ \ s))).hom
        (supportInclusion P M U h hclosed hδ T cs H E f) :=
  rfl

/-- Evaluation of `R_s f` through the support inclusion. -/
theorem stepRestriction_eval_inclusion
    (f : stepSubrepresentation P M U h hclosed T cs E I s (i + 1)) (q : P I) :
    Induction.eval _ _ (stepRestriction P M U h hclosed hδ T cs hPc H E f).val q =
      Induction.eval _ (inducingObject P M U h E (Finset.univ \ s)).obj.ρ
        (supportInclusion P M U h hclosed hδ T cs H E f).val (m⁻¹ * (q : G)) := by
  have key := orbitRestriction_eval H.supportPair (hPc _) (hPc I)
    (inducingObject P M U h E (Finset.univ \ s))
    (supportInclusion P M U h hclosed hδ T cs H E f) q
  exact key

/-- `R_s f (q) = f(m⁻¹ q)`. -/
theorem stepRestriction_eval
    (f : stepSubrepresentation P M U h hclosed T cs E I s (i + 1)) (q : P I) :
    Induction.eval _ _ (stepRestriction P M U h hclosed hδ T cs hPc H E f).val q =
      Induction.eval _ _ f.1 (m⁻¹ * (q : G)) := by
  have key := stepRestriction_eval_inclusion P M U h hclosed hδ T cs hPc H E f q
  exact key

/-- The kernel of `R_s` is the step `i`: the functions supported in `G_{θ_i'}`. -/
theorem stepRestriction_eq_zero_iff
    (f : stepSubrepresentation P M U h hclosed T cs E I s (i + 1)) :
    stepRestriction P M U h hclosed hδ T cs hPc H E f = 0 ↔
      f.1 ∈ inductionStep P M U h hclosed T cs E I s i := by
  have key := orbitRestriction_eq_zero_iff H.supportPair (hPc _) (hPc I)
    (inducingObject P M U h E (Finset.univ \ s))
    (supportInclusion P M U h hclosed hδ T cs H E f)
  have e := stepRestriction_apply P M U h hclosed hδ T cs hPc H E f
  rw [e]
  refine key.trans ?_
  change _ ↔ ∀ g : G, Induction.eval _ _ f.1 g ≠ 0 → g ∈ groupSupport P T cs I s i
  exact forall_congr' fun x => imp_congr Iff.rfl (quotientMap_mem_image_iff H.left_lower x)

/-- `R_s` is surjective. -/
theorem stepRestriction_surjective :
    Function.Surjective (stepRestriction P M U h hclosed hδ T cs hPc H E) := by
  intro g
  obtain ⟨f', hf'⟩ := orbitRestriction_surjective H.supportPair (hPc _) (hPc I)
    (inducingObject P M U h E (Finset.univ \ s)) g
  let F := Induction.smoothInducedMap (P (Finset.univ \ s))
    (intertwiningOfEq (coefficientRepresentation_eq P M U h hclosed hδ E s).symm) f'.val
  have hF : F ∈ inductionStep P M U h hclosed T cs E I s (i + 1) := fun x hx =>
    (quotientMap_mem_image_iff H.left_upper x).mp (f'.property x hx)
  refine ⟨⟨F, hF⟩, ?_⟩
  apply orbitPiece_ext
  intro q
  have e1 := stepRestriction_eval P M U h hclosed hδ T cs hPc H E ⟨F, hF⟩ q
  have e2 := orbitRestriction_eval H.supportPair (hPc _) (hPc I)
    (inducingObject P M U h E (Finset.univ \ s)) f' q
  rw [hf'] at e2
  exact e1.trans e2.symm

variable (hNc : Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
  (hU : Antitone U) {w : Group.RelativeWeyl.Weyl T} {K : Finset ι}
  (hK : ∀ x : G, x ∈ M I ↔ m⁻¹ * x * m ∈ M K)
  (D : OrbitJacquetData P M U h hclosed hU T cs I E w m K hK)
  (hKs : K ⊆ Finset.univ \ s)
  (hs : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I w)

/-- The graded map `β_s` at a surviving grade: `[f] ↦ Θ_s (R_s f)` on the step
`i + 1` of `r_I(E_J)`. -/
def stepGradedMap :
    SmoothRep.subrepresentation
        ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed E s))
        (step P M U h hclosed T cs E I s (i + 1)) ⟶
      (conjugationFunctor m hK).obj
        ((jacquetFunctor.{uG, max uG uV} (h K) (hclosed K)).obj E) :=
  gradedMap (h I) (hclosed I) hNc (term P M U h hclosed E s)
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1))
    (stepRestriction P M U h hclosed hδ T cs hPc H E) _ (D.Θ s hKs hs)
    (D.unipotent_invariant s hKs hs) (D.levi_equivariant s hKs hs)

/-- `β_s [f] = Θ_s (R_s f)`. -/
theorem stepGradedMap_mk (f : term P M U h hclosed E s)
    (hf : f ∈ inductionStep P M U h hclosed T cs E I s (i + 1)) :
    SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H E hNc hU hK D hKs hs)
        ⟨Jacquet.Localization.mk (term P M U h hclosed E s).representation (U I) 1 f,
          ⟨f, hf, rfl⟩⟩ =
      D.Θ s hKs hs (stepRestriction P M U h hclosed hδ T cs hPc H E ⟨f, hf⟩) := by
  have key := gradedMap_mk (h I) (hclosed I) hNc (term P M U h hclosed E s)
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1))
    (stepRestriction P M U h hclosed hδ T cs hPc H E) _ (D.Θ s hKs hs)
    (D.unipotent_invariant s hKs hs) (D.levi_equivariant s hKs hs) ⟨f, hf⟩
  exact key

/-- `β_s` is surjective. -/
theorem stepGradedMap_surjective :
    Function.Surjective
      (SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H E hNc hU hK D hKs hs)) := by
  have key := gradedMap_surjective (h I) (hclosed I) hNc (term P M U h hclosed E s)
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1))
    (stepRestriction P M U h hclosed hδ T cs hPc H E) _ (D.Θ s hKs hs)
    (D.unipotent_invariant s hKs hs) (D.levi_equivariant s hKs hs)
    (stepRestriction_surjective P M U h hclosed hδ T cs hPc H E) (D.surjective s hKs hs)
  exact key

/-- The kernel of `β_s` is the step `i`. -/
theorem stepGradedMap_eq_zero_iff
    (x : SmoothRep.subrepresentation
      ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed E s))
      (step P M U h hclosed T cs E I s (i + 1))) :
    SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H E hNc hU hK D hKs hs) x = 0 ↔
      x.1 ∈ (step P M U h hclosed T cs E I s i).toSubmodule := by
  have key := gradedMap_eq_zero_iff (h I) (hclosed I) hNc (term P M U h hclosed E s)
    (stepSubrepresentation P M U h hclosed T cs E I s (i + 1))
    (stepRestriction P M U h hclosed hδ T cs hPc H E) _ (D.Θ s hKs hs)
    (D.unipotent_invariant s hKs hs) (D.levi_equivariant s hKs hs)
    (stepRestriction_surjective P M U h hclosed hδ T cs hPc H E)
    (S' := inductionStep P M U h hclosed T cs E I s i)
    (functionSupport_mono _ SurvivingSupportHypotheses.groupSupport_subset)
    (stepRestriction_eq_zero_iff P M U h hclosed hδ T cs hPc H E)
    (D.ker_le s hKs hs) x
  exact key

/-- For surviving `s ⊆ t`, `β_t ∘ r_I(φ^J_{J'}) = β_s` on the step `i + 1`. -/
theorem stepGradedMap_transition (hP : Monotone P) {t : Finset ι} (hst : s ⊆ t)
    (Ht : SurvivingSupportHypotheses P T cs I t i m) (hKt : K ⊆ Finset.univ \ t)
    (ht : Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ t) I w)
    (x : (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed E s))
    (hx : x ∈ (step P M U h hclosed T cs E I s (i + 1)).toSubmodule) :
    SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc Ht E hNc hU hK D hKt ht)
        ⟨SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
          (transition P M U h hclosed hδ hP hU E hst)) x,
          transition_mem_step E I hst (i + 1) hx⟩ =
      SmoothRep.hom (stepGradedMap P M U h hclosed hδ T cs hPc H E hNc hU hK D hKs hs)
        ⟨x, hx⟩ := by
  obtain ⟨f, hf, rfl⟩ := hx
  have hφf := transition_mem_inductionStep (hδ := hδ) (hP := hP) (hU := hU) E I hst (i + 1) hf
  have et := stepGradedMap_mk P M U h hclosed hδ T cs hPc Ht E hNc hU hK D hKt ht _ hφf
  have es := stepGradedMap_mk P M U h hclosed hδ T cs hPc H E hNc hU hK D hKs hs f hf
  have htr := D.transition s t hst hKs hs hKt ht
    (stepRestriction P M U h hclosed hδ T cs hPc H E ⟨f, hf⟩)
    (stepRestriction P M U h hclosed hδ T cs hPc Ht E ⟨_, hφf⟩) (fun q => by
      have a := stepRestriction_eval P M U h hclosed hδ T cs hPc Ht E ⟨_, hφf⟩ q
      have b := stepRestriction_eval P M U h hclosed hδ T cs hPc H E ⟨f, hf⟩ q
      refine a.trans ?_
      rw [b]
      rfl)
  exact et.trans (htr.trans es.symm)

end Restriction

section Assembly

variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset ι) (K : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I K)).subgroupOf (M I))
      ((M (leviIndex I K)).subgroupOf (M I)) ((U (leviIndex I K)).subgroupOf (M I)))
  (IsAssociate : Finset ι → Finset ι → G → Prop)
  (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))
  [SigmaCompactSpace G] [T2Space G] [∀ J, CompactSpace (Induction.LeftQuotient (P J))]
  (hPc : ∀ J, IsClosed (P J : Set G))

include hPc in
/-- Conditional proof of `CorrectedGradedTransitionTarget`: the support
hypotheses at every surviving grade, orbit Jacquet data for every grade, lift and
`K`, and `U_I ∩ P_I` a limit of compact subgroups give the graded maps
`β_s = Θ_s ∘ R_s`. -/
theorem correctedGradedTransitionTarget_of_orbitData
    (hsupp : ∀ (I s : Finset ι) (i : ℕ) (hi : i < (Support.rankOrderedList cs.length).length)
      (m : Group.RelativeWeyl.normalizer T),
      (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
        (Support.rankOrderedElement cs.length i hi)⁻¹ →
      Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
        (Support.rankOrderedElement cs.length i hi) →
      SurvivingSupportHypotheses P T cs I s i (m : G))
    (hNc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups ((U I).subgroupOf (P I)))
    (hD : ∀ (I : Finset ι) (E : SmoothRep.{0, uG, max uG uV} ℂ G),
      IsInSupportCategory P M U h hclosed IsAssociate I (hM I) (hL I) E →
      ∀ (i : ℕ) (hi : i < (Support.rankOrderedList cs.length).length)
        (m : Group.RelativeWeyl.normalizer T),
        (QuotientGroup.mk m : Group.RelativeWeyl.Weyl T) =
          (Support.rankOrderedElement cs.length i hi)⁻¹ →
      ∀ (K : Finset ι) (hK : ∀ x : G, x ∈ M I ↔ (m : G)⁻¹ * x * m ∈ M K),
        OrbitJacquetData P M U h hclosed hU T cs I E
          (Support.rankOrderedElement cs.length i hi) (m : G) K hK) :
    CorrectedGradedTransitionTarget.{uI, uG, uV} P M U h hclosed hδ hP hU hM hL IsAssociate
      T cs := by
  intro I E hE i hi m hm K hK
  refine ⟨fun s hKs hs => stepGradedMap P M U h hclosed hδ T cs hPc
      (hsupp I s i hi m hm hs) E (hNc I) hU hK (hD I E hE i hi m hm K hK) hKs hs,
    ?_, ?_, ?_⟩
  · intro s hKs hs
    exact stepGradedMap_surjective P M U h hclosed hδ T cs hPc
      (hsupp I s i hi m hm hs) E (hNc I) hU hK (hD I E hE i hi m hm K hK) hKs hs
  · intro s hKs hs x
    exact stepGradedMap_eq_zero_iff P M U h hclosed hδ T cs hPc
      (hsupp I s i hi m hm hs) E (hNc I) hU hK (hD I E hE i hi m hm K hK) hKs hs x
  · intro s t hst hKs hs hKt ht x hx
    exact stepGradedMap_transition P M U h hclosed hδ T cs hPc
      (hsupp I s i hi m hm hs) E (hNc I) hU hK (hD I E hE i hi m hm K hK) hKs hs hP hst
      (hsupp I t i hi m hm ht) hKt ht x hx

end Assembly

end Langlands.Aubert.General.CorrectedFiltration
