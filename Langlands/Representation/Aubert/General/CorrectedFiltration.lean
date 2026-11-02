import Langlands.Representation.Aubert.General.StandardComplex
import Langlands.Representation.Aubert.RankOrderedSupports
import Langlands.Group.RelativeWeylMinimalUniqueProof

/-!
# The corrected support filtration of the general Aubert complex

For the terms `E_J = i_J r_J E` of Worker 194's standard complex and a source
index `I`, this module constructs the support filtration of the normalized
Jacquet modules `r_I(E_J)` used in the 1996 erratum (pp. 4687–4689), with the
two-sided modified supports of Ban–Jantzen (2016, Section 4):

* `functionSupport σ X`: smooth induced functions whose nonzero set lies in `X`;
* `jacquetImage hQ hN A S`: the image of a `Q`-stable subspace in the normalized
  Jacquet module along `Q = L ⋉ N`, an `L`-subrepresentation;
* `cellSupport T B Q θ`: the union of the cells `B n Q` over all lifts
  `n ∈ N_G(T)` of the elements of `θ ⊆ N_G(T)/Z_G(T)`;
* `modifiedSupport W J I i`: the two-sided modified support `θ_i'` for
  `W_J`, `W_I` and the rank-ordered prefixes of the Coxeter length;
* `step`: the filtration step of `r_I(E_J)` at `i`, indexed as in
  `StandardComplex` by the removed roots `s` (so `J = S \ s`).

Proved laws: monotonicity, the zero endpoint, the full endpoint under the
Bruhat covering hypothesis `IsBruhatCover`, preservation of the steps by the
actual transition maps of the complex, and the identification of the indices
where `θ_i'` changes with the minimal double-coset representatives.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

section Functions

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smooth induced functions whose nonzero set lies in `X`. -/
def functionSupport {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ P V) (X : Set G) :
    Submodule ℂ (Induction.SmoothFunctions P σ) where
  carrier := {f | ∀ g : G, Induction.eval P σ f g ≠ 0 → g ∈ X}
  zero_mem' := fun _ hg => (hg rfl).elim
  add_mem' := by
    intro f f' hf hf' g hg
    by_cases hfg : Induction.eval P σ f g = 0
    · apply hf' g
      intro h'
      apply hg
      change Induction.eval P σ f g + Induction.eval P σ f' g = 0
      rw [hfg, h', add_zero]
    · exact hf g hfg
  smul_mem' := by
    intro c f hf g hg
    apply hf g
    intro h'
    apply hg
    change c • Induction.eval P σ f g = 0
    rw [h', smul_zero]

variable {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V)

omit [IsTopologicalGroup G] in
theorem mem_functionSupport {X : Set G} (f : Induction.SmoothFunctions P σ) :
    f ∈ functionSupport σ X ↔ ∀ g : G, Induction.eval P σ f g ≠ 0 → g ∈ X :=
  Iff.rfl

omit [IsTopologicalGroup G] in
theorem functionSupport_mono {X Y : Set G} (hXY : X ⊆ Y) :
    functionSupport σ X ≤ functionSupport σ Y :=
  fun _ hf g hg => hXY (hf g hg)

omit [IsTopologicalGroup G] in
@[simp] theorem functionSupport_empty : functionSupport σ ∅ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_contra hx
    exact hf x hx
  · exact bot_le

omit [IsTopologicalGroup G] in
@[simp] theorem functionSupport_univ : functionSupport σ Set.univ = ⊤ :=
  le_antisymm le_top fun _ _ _ _ => trivial

/-- Right translation by `q` preserves the support condition when `X q ⊆ X`. -/
theorem functionSupport_smoothInduced {X : Set G} {q : G} (hq : ∀ x ∈ X, x * q⁻¹ ∈ X)
    {f : Induction.SmoothFunctions P σ} (hf : f ∈ functionSupport σ X) :
    Induction.smoothInduced P σ q f ∈ functionSupport σ X := by
  intro g hg
  have hgq := hf (g * q) hg
  simpa [mul_assoc] using hq _ hgq

end Functions

section Jacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {Q L N : Subgroup G} (hQ : IsSemidirectDecomposition Q L N)
  (hN : IsClosed (N : Set G))

/-- The image of a `Q`-stable subspace of `A` in the normalized Jacquet module
`r_N(A)`, an actual `L`-subrepresentation. -/
def jacquetImage (A : SmoothRep.{0, uG, uV} ℂ G) (S : Submodule ℂ A)
    (hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S) :
    Subrepresentation ((jacquetFunctor.{uG, uV} hQ hN).obj A).representation where
  toSubmodule := S.map (Jacquet.Localization.mk A.representation N 1)
  apply_mem_toSubmodule m := by
    rintro _ ⟨v, hv, rfl⟩
    change ((normalizedJacquetFunctor N L hN hQ.levi_le_normalizer).obj A).representation m
      (Jacquet.Localization.mk A.representation N 1 v) ∈ _
    rw [normalizedJacquetFunctor_obj_apply]
    exact ⟨_, S.smul_mem _ (hS _ (hQ.levi_le m.2) v hv), map_smul _ _ _⟩

variable {hQ hN}

theorem mem_jacquetImage {A : SmoothRep.{0, uG, uV} ℂ G} {S : Submodule ℂ A}
    {hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S}
    (x : (jacquetFunctor.{uG, uV} hQ hN).obj A) :
    x ∈ (jacquetImage hQ hN A S hS).toSubmodule ↔
      ∃ v ∈ S, Jacquet.Localization.mk A.representation N 1 v = x :=
  Iff.rfl

theorem jacquetImage_mono {A : SmoothRep.{0, uG, uV} ℂ G} {S S' : Submodule ℂ A}
    {hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S}
    {hS' : ∀ q ∈ Q, ∀ v ∈ S', A.representation q v ∈ S'} (hle : S ≤ S') :
    jacquetImage hQ hN A S hS ≤ jacquetImage hQ hN A S' hS' := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, hle hv, rfl⟩

theorem jacquetImage_eq_bot {A : SmoothRep.{0, uG, uV} ℂ G} {S : Submodule ℂ A}
    {hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S} (h0 : S = ⊥) :
    jacquetImage hQ hN A S hS = ⊥ := by
  apply le_antisymm _ bot_le
  rintro _ ⟨v, hv, rfl⟩
  subst h0
  rw [SetLike.mem_coe, Submodule.mem_bot] at hv
  subst hv
  show Jacquet.Localization.mk A.representation N 1 0 ∈
    (⊥ : Submodule ℂ (Jacquet.Localization.Coinvariants A.representation N 1))
  rw [map_zero]
  exact zero_mem _

theorem jacquetImage_eq_top {A : SmoothRep.{0, uG, uV} ℂ G} {S : Submodule ℂ A}
    {hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S} (h1 : S = ⊤) :
    jacquetImage hQ hN A S hS = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective A.representation N 1 x
  exact ⟨v, h1 ▸ Submodule.mem_top, rfl⟩

/-- An intertwiner that maps `S` into `S'` maps the Jacquet image of `S` into that
of `S'` under the actual Jacquet functor. -/
theorem jacquetImage_map {A A' : SmoothRep.{0, uG, uV} ℂ G} (f : A ⟶ A')
    {S : Submodule ℂ A} {S' : Submodule ℂ A'}
    {hS : ∀ q ∈ Q, ∀ v ∈ S, A.representation q v ∈ S}
    {hS' : ∀ q ∈ Q, ∀ v ∈ S', A'.representation q v ∈ S'}
    (hf : ∀ v ∈ S, SmoothRep.hom f v ∈ S') {x : (jacquetFunctor.{uG, uV} hQ hN).obj A}
    (hx : x ∈ (jacquetImage hQ hN A S hS).toSubmodule) :
    SmoothRep.hom ((jacquetFunctor.{uG, uV} hQ hN).map f) x ∈
      (jacquetImage hQ hN A' S' hS').toSubmodule := by
  obtain ⟨v, hv, rfl⟩ := hx
  exact ⟨SmoothRep.hom f v, hf v hv, rfl⟩

end Jacquet

section Cells

variable {G : Type uG} [Group G]

/-- The union of the cells `B n Q` over all lifts `n ∈ N_G(T)` of the elements of
`θ ⊆ N_G(T)/Z_G(T)`. -/
def cellSupport (T B Q : Subgroup G) (θ : Set (Group.RelativeWeyl.Weyl T)) : Set G :=
  {g | ∃ n : Group.RelativeWeyl.normalizer T,
    (QuotientGroup.mk n : Group.RelativeWeyl.Weyl T) ∈ θ ∧
      ∃ b ∈ B, ∃ q ∈ Q, g = b * (n : G) * q}

/-- The Bruhat covering `G = ⋃_{w ∈ W} B n_w Q`: every element of `G` lies in
`B n Q` for some `n ∈ N_G(T)`. -/
def IsBruhatCover (T B Q : Subgroup G) : Prop :=
  ∀ g : G, ∃ n : Group.RelativeWeyl.normalizer T, ∃ b ∈ B, ∃ q ∈ Q, g = b * (n : G) * q

variable {T B Q : Subgroup G}

theorem cellSupport_mul_right {θ : Set (Group.RelativeWeyl.Weyl T)} {g q : G}
    (hg : g ∈ cellSupport T B Q θ) (hq : q ∈ Q) : g * q ∈ cellSupport T B Q θ := by
  obtain ⟨n, hn, b, hb, q', hq', rfl⟩ := hg
  exact ⟨n, hn, b, hb, q' * q, Q.mul_mem hq' hq, by simp [mul_assoc]⟩

theorem cellSupport_mono {θ η : Set (Group.RelativeWeyl.Weyl T)} (hθη : θ ⊆ η) :
    cellSupport T B Q θ ⊆ cellSupport T B Q η := by
  rintro g ⟨n, hn, rest⟩
  exact ⟨n, hθη hn, rest⟩

@[simp] theorem cellSupport_empty : cellSupport T B Q ∅ = ∅ := by
  ext g
  simp [cellSupport]

theorem cellSupport_univ (hcover : IsBruhatCover T B Q) :
    cellSupport T B Q Set.univ = Set.univ := by
  ext g
  obtain ⟨n, b, hb, q, hq, hg⟩ := hcover g
  exact ⟨fun _ => trivial, fun _ => ⟨n, trivial, b, hb, q, hq, hg⟩⟩

end Cells

section Modified

variable {ι : Type uI} {W : Type uG} [Group W] [Fintype W] [DecidableEq W]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx W)

/-- The two-sided modified support `θ_i'` for the target index `J` and the source
index `I`: the largest subset of the `i`-th length-ordered prefix that is left
`W_J`-invariant and right `W_I`-invariant. -/
def modifiedSupport (J I : Finset ι) (i : ℕ) : Set W :=
  Support.modifiedRankSupport (Group.RelativeWeylIndexing.standardSubgroup cs J)
    (Group.RelativeWeylIndexing.standardSubgroup cs I) cs.length i

theorem modifiedSupport_monotone (J I : Finset ι) : Monotone (modifiedSupport cs J I) :=
  Support.modifiedRankSupport_monotone _ _ _

/-- Shrinking the target index enlarges the modified support. -/
theorem modifiedSupport_antitone_target {J J' : Finset ι} (hJ : J' ⊆ J) (I : Finset ι)
    (i : ℕ) : modifiedSupport cs J I i ⊆ modifiedSupport cs J' I i :=
  Support.twoSidedCore_antitone_subgroups _ _
    (Group.RelativeWeylIndexing.standardSubgroup_mono cs hJ) le_rfl _

/-- The modified support changes at `i` exactly when the `i`-th length-ordered
element is the minimal representative of its double coset `W_J w W_I`. -/
theorem mem_modifiedSupport_succ_iff (J I : Finset ι) (i : ℕ)
    (hi : i < (Support.rankOrderedList cs.length).length) :
    Support.rankOrderedElement cs.length i hi ∈ modifiedSupport cs J I (i + 1) ↔
      Group.RelativeWeylIndexing.IsMinimal cs J I
        (Support.rankOrderedElement cs.length i hi) := by
  set w := Support.rankOrderedElement cs.length i hi
  constructor
  · intro hw a ha b hb
    have hne := (Support.modifiedRankSupport_succ_ne_iff _ _ cs.length i hi).mpr hw
    exact Support.modifiedRankSupport_succ_minimal _ _ cs.length i hi hne _
      (DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b, hb, rfl⟩)
  · intro hmin
    apply (Support.mem_twoSidedCore_iff _ _ _ w).mpr
    intro a ha b hb
    by_cases hv : a * w * b = w
    · rw [hv]
      exact Support.rankOrderedElement_mem_succ cs.length i hi
    · have hle := hmin a ha b hb
      have hlt : cs.length w < cs.length (a * w * b) := by
        refine lt_of_le_of_ne hle fun heq => hv ?_
        have hmin' : Group.RelativeWeylIndexing.IsMinimal cs J I (a * w * b) := by
          intro a' ha' b' hb'
          rw [← heq]
          have := hmin (a' * a) ((Group.RelativeWeylIndexing.standardSubgroup cs J).mul_mem ha' ha)
            (b * b') ((Group.RelativeWeylIndexing.standardSubgroup cs I).mul_mem hb hb')
          simpa [mul_assoc] using this
        exact Group.RelativeWeylIndexing.minimalRepresentativeUnique_proof cs J I w
          (a * w * b) w ⟨a, ha, b, hb, rfl⟩
          (Group.RelativeWeylIndexing.mem_doubleCoset_self cs J I w) hmin' hmin
      exact Support.rankOrderedSupport_isRankUpper cs.length (i + 1) w
        (Support.rankOrderedElement_mem_succ cs.length i hi) _ hlt

end Modified

section Standard

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable (P M U : Finset ι → Subgroup G)
  (h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J))
  (hclosed : ∀ J, IsClosed (U J : Set G))
  (hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J))
  (hP : Monotone P) (hU : Antitone U)

/-- The term `E_J = i_J r_J E` of the standard complex at the removed roots `s`,
so that `J = S \ s`. -/
abbrev term (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :=
  Complex.termObject (StandardComplex.removedFamily P) (StandardComplex.removedFamily M)
    (StandardComplex.removedFamily U) (fun s => h (Finset.univ \ s))
    (fun s => hclosed (Finset.univ \ s)) A s

/-- The actual transition map `φ^J_{J'}` of the complex, `J = S \ s ⊇ J' = S \ t`,
as a morphism of smooth representations. -/
abbrev transition (A : SmoothRep.{0, uG, max uG uV} ℂ G) {s t : Finset ι} (hst : s ⊆ t) :
    term P M U h hclosed A s ⟶ term P M U h hclosed A t :=
  SmoothRep.ofHom (Complex.transition (StandardComplex.removedFamily P)
    (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
    (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
    (fun s => hδ (Finset.univ \ s)) (StandardComplex.removedFamily_antitone hP)
    (StandardComplex.removedFamily_monotone hU) A hst)

variable (T : Subgroup G) [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
variable {Mx : CoxeterMatrix ι} (cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T))

/-- The support set `G_{θ_i'} = ⋃_{w ∈ θ_i'} B n_w P_I` of the erratum, with
`B = P ∅` and the modified support for the target `J = S \ s` and source `I`. -/
def groupSupport (I s : Finset ι) (i : ℕ) : Set G :=
  cellSupport T (P ∅) (P I) (modifiedSupport cs (Finset.univ \ s) I i)

/-- The functions in `E_J` supported in `G_{θ_i'}`. -/
def inductionStep (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ) :
    Submodule ℂ (term P M U h hclosed A s) :=
  functionSupport
    (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
      (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
      (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
    (groupSupport P T cs I s i)

theorem inductionStep_stable (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι)
    (i : ℕ) : ∀ q ∈ P I, ∀ f ∈ inductionStep P M U h hclosed T cs A I s i,
      (term P M U h hclosed A s).representation q f ∈
        inductionStep P M U h hclosed T cs A I s i := by
  intro q hq f hf
  exact functionSupport_smoothInduced _
    (fun x hx => cellSupport_mul_right hx ((P I).inv_mem hq)) hf

/-- The filtration step `Ẽ^{θ_i'}_{J,I}` of `r_I(E_J)`: the image in the actual
normalized Jacquet module along `P I` of the functions in `E_J` supported in
`G_{θ_i'}`. -/
def step (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ) :
    Subrepresentation
      ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj
        (term P M U h hclosed A s)).representation :=
  jacquetImage (h I) (hclosed I) (term P M U h hclosed A s)
    (inductionStep P M U h hclosed T cs A I s i)
    (inductionStep_stable P M U h hclosed T cs A I s i)

variable {P M U h hclosed hδ hP hU T cs}

theorem step_monotone (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) :
    Monotone (step P M U h hclosed T cs A I s) := fun _ _ hij =>
  jacquetImage_mono (functionSupport_mono _
    (cellSupport_mono (modifiedSupport_monotone cs _ I hij)))

@[simp] theorem step_zero (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) :
    step P M U h hclosed T cs A I s 0 = ⊥ := by
  apply jacquetImage_eq_bot
  simp [inductionStep, groupSupport, modifiedSupport]

theorem step_length (hcover : IsBruhatCover T (P ∅) (P I))
    (A : SmoothRep.{0, uG, max uG uV} ℂ G) (s : Finset ι) :
    step P M U h hclosed T cs A I s (Support.rankOrderedList cs.length).length = ⊤ := by
  apply jacquetImage_eq_top
  simp [inductionStep, groupSupport, modifiedSupport, cellSupport_univ hcover]

/-- The actual transition maps preserve the supports: `φ^J_{J'}` maps the
functions supported in `G_{θ_i'(J)}` to functions supported in
`G_{θ_i'(J')}`, since `φ` acts pointwise and `θ_i'(J) ⊆ θ_i'(J')`. -/
theorem transition_mem_inductionStep (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I : Finset ι) {s t : Finset ι} (hst : s ⊆ t) (i : ℕ) {f : term P M U h hclosed A s}
    (hf : f ∈ inductionStep P M U h hclosed T cs A I s i) :
    SmoothRep.hom (transition P M U h hclosed hδ hP hU A hst) f ∈
      inductionStep P M U h hclosed T cs A I t i := by
  intro g hg
  have hfg : Induction.eval _ _ f g ≠ 0 := by
    intro h0
    apply hg
    rw [SmoothRep.hom_ofHom]
    refine (Complex.transition_eval (StandardComplex.removedFamily P)
      (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
      (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s))
      (fun s => hδ (Finset.univ \ s)) (StandardComplex.removedFamily_antitone hP)
      (StandardComplex.removedFamily_monotone hU) A hst f g).trans ?_
    have h0' : Induction.eval (StandardComplex.removedFamily P s)
        (inducingRepresentation (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))
          ((jacquetFunctor (h (Finset.univ \ s)) (hclosed (Finset.univ \ s))).obj A)) f g = 0 :=
      h0
    exact (congrArg _ h0').trans (map_zero _)
  exact cellSupport_mono (modifiedSupport_antitone_target cs
    (Finset.sdiff_subset_sdiff_right Finset.univ hst) I i) (hf g hfg)

/-- The actual Jacquet transition `r_I(φ^J_{J'})` maps each filtration step of
`r_I(E_J)` into the same step of `r_I(E_{J'})`. -/
theorem transition_mem_step (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I : Finset ι)
    {s t : Finset ι} (hst : s ⊆ t) (i : ℕ)
    {x : (jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).obj (term P M U h hclosed A s)}
    (hx : x ∈ (step P M U h hclosed T cs A I s i).toSubmodule) :
    SmoothRep.hom ((jacquetFunctor.{uG, max uG uV} (h I) (hclosed I)).map
        (transition P M U h hclosed hδ hP hU A hst)) x ∈
      (step P M U h hclosed T cs A I t i).toSubmodule :=
  jacquetImage_map _ (fun _ hf => transition_mem_inductionStep A I hst i hf) hx

/-- The step does not change at `i` when the `i`-th length-ordered element is not
the minimal representative of its double coset `W_J w W_I`. -/
theorem step_succ_eq (A : SmoothRep.{0, uG, max uG uV} ℂ G) (I s : Finset ι) (i : ℕ)
    (hi : i < (Support.rankOrderedList cs.length).length)
    (hw : ¬ Group.RelativeWeylIndexing.IsMinimal cs (Finset.univ \ s) I
      (Support.rankOrderedElement cs.length i hi)) :
    step P M U h hclosed T cs A I s (i + 1) = step P M U h hclosed T cs A I s i := by
  have heq : modifiedSupport cs (Finset.univ \ s) I (i + 1) =
      modifiedSupport cs (Finset.univ \ s) I i :=
    Support.modifiedRankSupport_succ_eq _ _ cs.length i hi
      (fun hm => hw ((mem_modifiedSupport_succ_iff cs _ I i hi).mp hm))
  simp only [step, inductionStep, groupSupport, heq]

end Standard

end Langlands.Aubert.General.CorrectedFiltration
