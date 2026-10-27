import Langlands.Representation.Induction.CompactLocalSectionSpanningStatement

/-! Compact induction is spanned by right translates of identity-centered
compact double-coset sections. -/

noncomputable section

namespace Langlands.Induction

universe uG uV

section Spanning

variable {G : Type uG} {V : Type uV}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module ℂ V]

/-- The generators of the spanning statement: right translates of compact
double-coset sections centered at `1`. -/
private def localSectionGenerators (H : Subgroup G) (sigma : Representation ℂ H V) :
    Set (CompactFunctions H sigma) :=
  {f | ∃ (g : G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
      (v : V) (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K 1).toSubgroup),
      f = compactInduced H sigma g (compactDoubleCosetSection H sigma K hK 1 v hv)}

private theorem eval_compactInduced (H : Subgroup G) (sigma : Representation ℂ H V)
    (g : G) (s : CompactFunctions H sigma) (y : G) :
    eval H sigma (compactInduced H sigma g s).1 y = eval H sigma s.1 (y * g) :=
  rfl

private theorem eval_sub (H : Subgroup G) (sigma : Representation ℂ H V)
    (f s : CompactFunctions H sigma) (y : G) :
    eval H sigma (f - s).1 y = eval H sigma f.1 y - eval H sigma s.1 y :=
  rfl

/-- The conjugate open subgroup `x K x⁻¹`, consisting of the `y` with `x⁻¹ * y * x ∈ K`. -/
private def conjugateOpenSubgroup (K : OpenSubgroup G) (x : G) : OpenSubgroup G :=
  K.comap (MulAut.conj x⁻¹).toMonoidHom (IsTopologicalGroup.continuous_conj x⁻¹)

private theorem mem_conjugateOpenSubgroup {K : OpenSubgroup G} {x y : G} :
    y ∈ conjugateOpenSubgroup K x ↔ x⁻¹ * y * x ∈ K := by
  simp [conjugateOpenSubgroup]

private theorem isCompact_conjugateOpenSubgroup {K : OpenSubgroup G}
    (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact (conjugateOpenSubgroup K x : Set G) := by
  have he : (conjugateOpenSubgroup K x : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
    ext y
    constructor
    · intro hy
      exact ⟨x⁻¹ * y * x, mem_conjugateOpenSubgroup.mp hy, by group⟩
    · rintro ⟨k, hk, rfl⟩
      apply mem_conjugateOpenSubgroup.mpr
      simpa [mul_assoc] using hk
  rw [he]
  exact hK.image ((continuous_const.mul continuous_id).mul continuous_const)

/-- A vector fixed by `H ∩ x K x⁻¹` is fixed by the identity-centered subgroup for
`x K x⁻¹`. -/
private theorem mem_fixedVectors_conjugate (H : Subgroup G) (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (x : G) {v : V}
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) :
    v ∈ fixedVectors sigma (conjOpenSubgroup H (conjugateOpenSubgroup K x) 1).toSubgroup := by
  intro p
  have hp : x⁻¹ * ((p : H) : G) * x ∈ K := by
    have h := mem_conjOpenSubgroup.mp p.property
    simpa using mem_conjugateOpenSubgroup.mp h
  exact hv ⟨p, mem_conjOpenSubgroup.mpr hp⟩

/-- The translated identity-centered section that reproduces a section centered at `x`. -/
private def translatedSection (H : Subgroup G) (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) :
    CompactFunctions H sigma :=
  compactInduced H sigma x⁻¹
    (compactDoubleCosetSection H sigma (conjugateOpenSubgroup K x)
      (isCompact_conjugateOpenSubgroup hK x) 1 v (mem_fixedVectors_conjugate H sigma K x hv))

private theorem translatedSection_mem (H : Subgroup G) (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) :
    translatedSection H sigma K hK x v hv ∈ localSectionGenerators H sigma :=
  ⟨x⁻¹, conjugateOpenSubgroup K x, isCompact_conjugateOpenSubgroup hK x, v,
    mem_fixedVectors_conjugate H sigma K x hv, rfl⟩

private theorem translatedSection_apply (H : Subgroup G) (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) (p : H) (k : K) :
    eval H sigma (translatedSection H sigma K hK x v hv).1 ((p : G) * x * (k : G)) =
      sigma p v := by
  have hl : x * (k : G) * x⁻¹ ∈ conjugateOpenSubgroup K x := by
    apply mem_conjugateOpenSubgroup.mpr
    simp [mul_assoc]
  rw [translatedSection, eval_compactInduced]
  have he : (p : G) * x * (k : G) * x⁻¹ = (p : G) * 1 * (x * (k : G) * x⁻¹) := by group
  rw [he]
  exact compactDoubleCosetSection_apply H sigma _ _ 1 v _ p ⟨_, hl⟩

private theorem translatedSection_mul (H : Subgroup G) (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) (k : K) (y : G) :
    eval H sigma (translatedSection H sigma K hK x v hv).1 (y * (k : G)) =
      eval H sigma (translatedSection H sigma K hK x v hv).1 y := by
  have hl : x * (k : G) * x⁻¹ ∈ conjugateOpenSubgroup K x := by
    apply mem_conjugateOpenSubgroup.mpr
    simp [mul_assoc]
  rw [translatedSection, eval_compactInduced, eval_compactInduced]
  have he : y * (k : G) * x⁻¹ = y * x⁻¹ * (x * (k : G) * x⁻¹) := by group
  rw [he]
  exact compactDoubleCosetSection_mul H sigma _ _ 1 v _ ⟨_, hl⟩ (y * x⁻¹)

/-- The translated section vanishes off the double coset `H * x * K`. -/
private theorem exists_eq_of_translatedSection_ne_zero (H : Subgroup G)
    (sigma : Representation ℂ H V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G) (v : V)
    (hv : v ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup) {y : G}
    (hy : eval H sigma (translatedSection H sigma K hK x v hv).1 y ≠ 0) :
    ∃ p : H, ∃ k : K, y = (p : G) * x * (k : G) := by
  rw [translatedSection, eval_compactInduced] at hy
  obtain ⟨l, hl, hq⟩ := compactDoubleCosetSection_support_subset H sigma _ _ 1 v _
    ⟨y * x⁻¹, hy, rfl⟩
  have hp : y * x⁻¹ * (1 * l)⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
  refine ⟨⟨_, hp⟩, ⟨x⁻¹ * l * x, mem_conjugateOpenSubgroup.mp hl⟩, ?_⟩
  simp [mul_assoc]

/-- The finite-support decomposition: a right-`K`-invariant compact function whose
nonzero support lies in finitely many double cosets `H * x * K` is a finite sum
of translated identity-centered sections. -/
private theorem mem_span_of_doubleCoset_cover (H : Subgroup G)
    (sigma : Representation ℂ H V) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (t : Finset G) :
    ∀ f : CompactFunctions H sigma,
      (∀ (k : K) (y : G), eval H sigma f.1 (y * (k : G)) = eval H sigma f.1 y) →
      (∀ y : G, eval H sigma f.1 y ≠ 0 →
        ∃ x ∈ t, ∃ p : H, ∃ k : K, y = (p : G) * x * (k : G)) →
      f ∈ Submodule.span ℂ (localSectionGenerators H sigma) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro f _ hs
    have hf : f = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      funext y
      by_contra hy
      obtain ⟨x, hx, -⟩ := hs y hy
      simp at hx
    rw [hf]
    exact Submodule.zero_mem _
  | insert x t _ ih =>
    intro f hfK hs
    have hfx : ∀ (p : H) (k : K), eval H sigma f.1 ((p : G) * x * (k : G)) =
        sigma p (eval H sigma f.1 x) := by
      intro p k
      rw [hfK k, eval_covariant]
    have hv : eval H sigma f.1 x ∈ fixedVectors sigma (conjOpenSubgroup H K x).toSubgroup := by
      intro p
      have hp : x⁻¹ * ((p : H) : G) * x ∈ K := mem_conjOpenSubgroup.mp p.property
      change sigma (p : H) (eval H sigma f.1 x) = eval H sigma f.1 x
      rw [← eval_covariant]
      calc eval H sigma f.1 (((p : H) : G) * x) =
            eval H sigma f.1 (x * (x⁻¹ * ((p : H) : G) * x)) := by simp [mul_assoc]
        _ = eval H sigma f.1 x := hfK ⟨_, hp⟩ x
    set T := translatedSection H sigma K hK x (eval H sigma f.1 x) hv
    have hT : T ∈ Submodule.span ℂ (localSectionGenerators H sigma) :=
      Submodule.subset_span (translatedSection_mem H sigma K hK x _ hv)
    have hg : f - T ∈ Submodule.span ℂ (localSectionGenerators H sigma) := by
      apply ih
      · intro k y
        rw [eval_sub, eval_sub, hfK k, translatedSection_mul]
      · intro y hy
        by_cases hxy : ∃ p : H, ∃ k : K, y = (p : G) * x * (k : G)
        · obtain ⟨p, k, rfl⟩ := hxy
          exfalso
          apply hy
          rw [eval_sub, hfx, translatedSection_apply, sub_self]
        · have hT0 : eval H sigma T.1 y = 0 := by
            by_contra hT0
            exact hxy (exists_eq_of_translatedSection_ne_zero H sigma K hK x _ hv hT0)
          rw [eval_sub, hT0, sub_zero] at hy
          obtain ⟨x', hx', hxy'⟩ := hs y hy
          rcases Finset.mem_insert.mp hx' with rfl | hx'
          · exact absurd hxy' hxy
          · exact ⟨x', hx', hxy'⟩
    simpa using Submodule.add_mem _ hg hT

/-- Compact induction is spanned by right translates of identity-centered compact
double-coset sections, given compact open subgroups in every identity neighborhood. -/
private theorem span_localSectionGenerators_eq_top
    (hbasis : ∀ O : Set G, IsOpen O → (1 : G) ∈ O →
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (H : Subgroup G) (sigma : Representation ℂ H V) :
    Submodule.span ℂ (localSectionGenerators H sigma) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun f => ?_
  obtain ⟨K₀, hK₀⟩ := f.1.property
  obtain ⟨K, hK, hKK₀⟩ := hbasis K₀ K₀.isOpen K₀.one_mem
  have hfK : ∀ (k : K) (y : G), eval H sigma f.1 (y * (k : G)) = eval H sigma f.1 y :=
    fun k y => congrArg (fun F : EquivariantFunctions H sigma => F.1 y)
      (hK₀ ⟨k, hKK₀ k.property⟩)
  have hopen : IsOpenMap (quotientMap H) :=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  obtain ⟨t, ht⟩ := f.2.elim_finite_subcover
    (fun i : G => quotientMap H '' ((fun k => i * k) '' (K : Set G)))
    (fun i => hopen _ (isOpenMap_mul_left i _ K.isOpen))
    (by
      rintro _ ⟨y, -, rfl⟩
      exact Set.mem_iUnion.mpr ⟨y, y, ⟨1, K.one_mem, mul_one y⟩, rfl⟩)
  apply mem_span_of_doubleCoset_cover H sigma K hK t f hfK
  intro y hy
  have hq := ht ⟨y, hy, rfl⟩
  simp only [Set.mem_iUnion] at hq
  obtain ⟨i, hi, _, ⟨k, hk, rfl⟩, hyq⟩ := hq
  have hp : y * (i * k)⁻¹ ∈ H := QuotientGroup.rightRel_apply.mp (Quotient.exact hyq)
  exact ⟨i, hi, ⟨_, hp⟩, ⟨k, hk⟩, by simp [mul_assoc]⟩

end Spanning

/-- Actual compact induction is spanned over `ℂ` by right translates of compact
double-coset sections centered at the identity. -/
theorem compactLocalSectionSpanning : CompactLocalSectionSpanning.{uG, uV} := by
  intro G _ _ _ _ hbasis H _ V _ _ sigma
  exact span_localSectionGenerators_eq_top hbasis H sigma

end Langlands.Induction
