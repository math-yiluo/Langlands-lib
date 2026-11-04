import Langlands.Representation.Aubert.General.CorrectedFiltration

/-!
# Restricting a changing corrected filtration step to its new support

For the corrected support filtration `step` of `r_I(E_J)`, this module proves the
right-exactness reduction used for the graded pieces: if the restrictions to the new
support `G_{θ_{i+1}'} \ G_{θ_i'}` of the functions supported in `G_{θ_{i+1}'}` have
trivial `U_I`-coinvariants, then the step does not change at `i`.

* `restrictTo σ D`: restriction of smooth induced functions to `D`, extended by zero;
* `restrictionImage σ X D`: the restrictions to `D` of the functions supported in `X`;
* `translationRelations Y N`: the span of the differences `φ(· n) - φ`, `φ ∈ Y`, `n ∈ N`.

No openness, closedness or Bruhat-disjointness of the cells is used.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General.CorrectedFiltration

universe uI uG uV

section Restriction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {P : Subgroup G} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V)

/-- Restriction of smooth induced functions to `D`, extended by zero off `D`. -/
def restrictTo (D : Set G) : Induction.SmoothFunctions P σ →ₗ[ℂ] (G → V) where
  toFun f := D.indicator (Induction.eval P σ f)
  map_add' f f' := by
    funext x
    by_cases hx : x ∈ D
    · simp only [Pi.add_apply, Set.indicator_of_mem hx]
      rfl
    · simp only [Pi.add_apply, Set.indicator_of_notMem hx, add_zero]
  map_smul' c f := by
    funext x
    by_cases hx : x ∈ D
    · simp only [Pi.smul_apply, RingHom.id_apply, Set.indicator_of_mem hx]
      rfl
    · simp only [Pi.smul_apply, RingHom.id_apply, Set.indicator_of_notMem hx, smul_zero]

omit [IsTopologicalGroup G] in
theorem restrictTo_apply (D : Set G) (f : Induction.SmoothFunctions P σ) (x : G) :
    restrictTo σ D f x = D.indicator (Induction.eval P σ f) x :=
  rfl

/-- Right translation `φ ↦ φ(· q)` of functions `G → V`. -/
def rightTranslate (q : G) : (G → V) →ₗ[ℂ] (G → V) :=
  LinearMap.funLeft ℂ V (· * q)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem rightTranslate_apply (q : G) (φ : G → V) (x : G) :
    rightTranslate q φ x = φ (x * q) :=
  rfl

/-- Restriction to a set stable under right translation by `q` commutes with the
right translation by `q`. -/
theorem restrictTo_smoothInduced {D : Set G} {q : G} (hD : ∀ x, x * q ∈ D ↔ x ∈ D)
    (f : Induction.SmoothFunctions P σ) :
    restrictTo σ D (Induction.smoothInduced P σ q f) =
      rightTranslate q (restrictTo σ D f) := by
  funext x
  rw [rightTranslate_apply, restrictTo_apply, restrictTo_apply]
  by_cases hx : x ∈ D
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hD x).2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem fun hxq => hx ((hD x).1 hxq)]

/-- The restrictions to `D` of the smooth induced functions supported in `X`. -/
def restrictionImage (X D : Set G) : Submodule ℂ (G → V) :=
  (functionSupport σ X).map (restrictTo σ D)

/-- The span of the right-translation differences `φ(· n) - φ` for `φ ∈ Y` and
`n ∈ N`. For a right `N`-stable `Y` it lies in `Y`
(`translationRelations_le`), and `Y ⧸ translationRelations Y N` is the space of
`N`-coinvariants of `Y`. -/
def translationRelations (Y : Submodule ℂ (G → V)) (N : Subgroup G) :
    Submodule ℂ (G → V) :=
  Submodule.span ℂ {ψ | ∃ φ ∈ Y, ∃ n ∈ N, ψ = rightTranslate n φ - φ}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem translationRelations_le {Y : Submodule ℂ (G → V)} {N : Subgroup G}
    (hY : ∀ n ∈ N, ∀ φ ∈ Y, rightTranslate n φ ∈ Y) : translationRelations Y N ≤ Y := by
  apply Submodule.span_le.2
  rintro _ ⟨φ, hφ, n, hn, rfl⟩
  exact Y.sub_mem (hY n hn φ hφ) hφ

variable {σ}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The difference of two right `N`-stable sets is right `N`-stable in both
directions. -/
theorem mul_mem_sdiff_iff {X X' : Set G} {N : Subgroup G}
    (hX : ∀ x ∈ X, ∀ n ∈ N, x * n ∈ X) (hX' : ∀ x ∈ X', ∀ n ∈ N, x * n ∈ X')
    {n : G} (hn : n ∈ N) (x : G) : x * n ∈ X \ X' ↔ x ∈ X \ X' := by
  constructor
  · rintro ⟨hxX, hxX'⟩
    refine ⟨?_, fun hx => hxX' (hX' x hx n hn)⟩
    simpa using hX (x * n) hxX n⁻¹ (N.inv_mem hn)
  · rintro ⟨hxX, hxX'⟩
    refine ⟨hX x hxX n hn, fun hx => hxX' ?_⟩
    simpa using hX' (x * n) hx n⁻¹ (N.inv_mem hn)

/-- The restriction image is right `N`-stable, so `translationRelations` computes
its `N`-coinvariants. -/
theorem rightTranslate_mem_restrictionImage {X X' : Set G} {N : Subgroup G}
    (hX : ∀ x ∈ X, ∀ n ∈ N, x * n ∈ X) (hX' : ∀ x ∈ X', ∀ n ∈ N, x * n ∈ X')
    {n : G} (hn : n ∈ N) {φ : G → V} (hφ : φ ∈ restrictionImage σ X (X \ X')) :
    rightTranslate n φ ∈ restrictionImage σ X (X \ X') := by
  obtain ⟨g, hg, rfl⟩ := hφ
  refine ⟨Induction.smoothInduced P σ n g, ?_, ?_⟩
  · exact functionSupport_smoothInduced σ (fun x hx => hX x hx n⁻¹ (N.inv_mem hn)) hg
  · exact restrictTo_smoothInduced σ (mul_mem_sdiff_iff hX hX' hn) g

/-- **Right exactness on the new support.** Let `X' , X` be right `N`-stable. If the
restriction of `f ∈ functionSupport σ X` to `X \ X'` is a combination of
right-translation differences of such restrictions, then `f` differs from a function
supported in `X'` by a combination of the differences `n · g - g` with `g` supported
in `X`. -/
theorem exists_lower_of_restrictTo_mem_translationRelations {X X' : Set G}
    {N : Subgroup G} (hX : ∀ x ∈ X, ∀ n ∈ N, x * n ∈ X)
    (hX' : ∀ x ∈ X', ∀ n ∈ N, x * n ∈ X') {f : Induction.SmoothFunctions P σ}
    (hf : f ∈ functionSupport σ X)
    (hres : restrictTo σ (X \ X') f ∈
      translationRelations (restrictionImage σ X (X \ X')) N) :
    ∃ f' ∈ functionSupport σ X', f - f' ∈ Submodule.span ℂ
      {k | ∃ g ∈ functionSupport σ X, ∃ n ∈ N, k = Induction.smoothInduced P σ n g - g} := by
  set K := Submodule.span ℂ
    {k | ∃ g ∈ functionSupport σ X, ∃ n ∈ N, k = Induction.smoothInduced P σ n g - g}
  have hKX : K ≤ functionSupport σ X := by
    apply Submodule.span_le.2
    rintro _ ⟨g, hg, n, hn, rfl⟩
    exact (functionSupport σ X).sub_mem
      (functionSupport_smoothInduced σ (fun x hx => hX x hx n⁻¹ (N.inv_mem hn)) hg) hg
  have hrel : translationRelations (restrictionImage σ X (X \ X')) N ≤
      K.map (restrictTo σ (X \ X')) := by
    apply Submodule.span_le.2
    rintro _ ⟨_, ⟨g, hg, rfl⟩, n, hn, rfl⟩
    refine ⟨Induction.smoothInduced P σ n g - g, Submodule.subset_span ⟨g, hg, n, hn, rfl⟩, ?_⟩
    rw [map_sub, restrictTo_smoothInduced σ (mul_mem_sdiff_iff hX hX' hn)]
  obtain ⟨k, hk, hkf⟩ := hrel hres
  refine ⟨f - k, ?_, by simpa using hk⟩
  intro x hx
  have hxX : x ∈ X := (functionSupport σ X).sub_mem hf (hKX hk) x hx
  by_contra hxX'
  have hzero : restrictTo σ (X \ X') (f - k) x = 0 := by
    rw [map_sub, hkf, sub_self]
    rfl
  rw [restrictTo_apply, Set.indicator_of_mem (show x ∈ X \ X' from ⟨hxX, hxX'⟩)] at hzero
  exact hx hzero

end Restriction

section Standard

variable {ι : Type uI} [LinearOrder ι] [Fintype ι]
variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
variable {P M U : Finset ι → Subgroup G}
  {h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)}
  {hclosed : ∀ J, IsClosed (U J : Set G)}
  {T : Subgroup G} [Fintype (Group.RelativeWeyl.Weyl T)]
  [DecidableEq (Group.RelativeWeyl.Weyl T)]
  {Mx : CoxeterMatrix ι} {cs : CoxeterSystem Mx (Group.RelativeWeyl.Weyl T)}

omit [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G] in
/-- The corrected group supports are right `P_I`-stable. -/
theorem groupSupport_mul_mem (I s : Finset ι) (i : ℕ) :
    ∀ x ∈ groupSupport P T cs I s i, ∀ q ∈ P I, x * q ∈ groupSupport P T cs I s i :=
  fun _ hx _ hq => cellSupport_mul_right hx hq

/-- If the restriction of `f ∈ inductionStep (i + 1)` to the new support
`G_{θ_{i+1}'} \ G_{θ_i'}` lies in the `U_I`-translation relations of the restriction
image, then the class of `f` in the actual Jacquet module `r_I(E_J)` lies in the
lower step. -/
theorem mk_mem_step_of_restrictTo_mem (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I s : Finset ι) (i : ℕ) {f : term P M U h hclosed A s}
    (hf : f ∈ inductionStep P M U h hclosed T cs A I s (i + 1))
    (hres : restrictTo (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
        (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
        (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i) f ∈
      translationRelations (restrictionImage
        (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1))
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i)) (U I)) :
    Jacquet.Localization.mk (term P M U h hclosed A s).representation (U I) 1 f ∈
      (step P M U h hclosed T cs A I s i).toSubmodule := by
  have hstable : ∀ j, ∀ x ∈ groupSupport P T cs I s j, ∀ n ∈ U I,
      x * n ∈ groupSupport P T cs I s j :=
    fun j x hx n hn => groupSupport_mul_mem I s j x hx n ((h I).unipotent_le hn)
  obtain ⟨f', hf', hk⟩ :=
    exists_lower_of_restrictTo_mem_translationRelations (hstable (i + 1)) (hstable i) hf hres
  have hle : Submodule.span ℂ {k : term P M U h hclosed A s |
      ∃ g ∈ inductionStep P M U h hclosed T cs A I s (i + 1), ∃ n ∈ U I,
        k = (term P M U h hclosed A s).representation n g - g} ≤
      Jacquet.Localization.relations (term P M U h hclosed A s).representation (U I) 1 := by
    apply Submodule.span_le.2
    rintro _ ⟨g, -, n, hn, rfl⟩
    have := Jacquet.Localization.sub_mem_relations (term P M U h hclosed A s).representation
      (U I) 1 ⟨n, hn⟩ g
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this
    exact this
  refine ⟨f', hf', ?_⟩
  exact (Jacquet.Localization.mk_eq_iff _ _ _ f' f).2
    (by rw [← neg_sub]; exact Submodule.neg_mem _ (hle hk))

/-- **Right-exactness criterion.** If the restriction image of `inductionStep (i + 1)`
on the new support `G_{θ_{i+1}'} \ G_{θ_i'}` has trivial `U_I`-coinvariants, that is,
it lies in its own `U_I`-translation relations, then the step does not change at `i`. -/
theorem step_succ_eq_of_restrictionImage_le (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I s : Finset ι) (i : ℕ)
    (hres : restrictionImage
        (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1))
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i) ≤
      translationRelations (restrictionImage
        (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1))
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i)) (U I)) :
    step P M U h hclosed T cs A I s (i + 1) = step P M U h hclosed T cs A I s i := by
  refine le_antisymm ?_ (step_monotone A I s (Nat.le_succ i))
  intro x hx
  obtain ⟨f, hf, rfl⟩ := (mem_jacquetImage x).1 hx
  exact mk_mem_step_of_restrictTo_mem A I s i hf (hres ⟨f, hf, rfl⟩)

/-- If the step changes at `i`, some function of `inductionStep (i + 1)` has a
restriction to the new support outside the `U_I`-translation relations, so the
`U_I`-coinvariants of the restriction image are nonzero. -/
theorem exists_restrictTo_not_mem_of_step_succ_ne (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I s : Finset ι) (i : ℕ)
    (hne : step P M U h hclosed T cs A I s (i + 1) ≠ step P M U h hclosed T cs A I s i) :
    ∃ f ∈ inductionStep P M U h hclosed T cs A I s (i + 1),
      restrictTo (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
          (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i) f ∉
        translationRelations (restrictionImage
          (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
            (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
            (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
          (groupSupport P T cs I s (i + 1))
          (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i)) (U I) := by
  by_contra hall
  refine hne (step_succ_eq_of_restrictionImage_le A I s i ?_)
  rintro _ ⟨f, hf, rfl⟩
  by_contra hf'
  exact hall ⟨f, hf, hf'⟩

/-- Contrapositive of `step_succ_eq_of_restrictionImage_le`: a change of the step at
`i` forces nonzero `U_I`-coinvariants of the restriction image on the new support. -/
theorem not_restrictionImage_le_of_step_succ_ne (A : SmoothRep.{0, uG, max uG uV} ℂ G)
    (I s : Finset ι) (i : ℕ)
    (hne : step P M U h hclosed T cs A I s (i + 1) ≠ step P M U h hclosed T cs A I s i) :
    ¬ restrictionImage
        (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1))
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i) ≤
      translationRelations (restrictionImage
        (Complex.coefficientRepresentation (StandardComplex.removedFamily P)
          (StandardComplex.removedFamily M) (StandardComplex.removedFamily U)
          (fun s => h (Finset.univ \ s)) (fun s => hclosed (Finset.univ \ s)) A s)
        (groupSupport P T cs I s (i + 1))
        (groupSupport P T cs I s (i + 1) \ groupSupport P T cs I s i)) (U I) :=
  fun hres => hne (step_succ_eq_of_restrictionImage_le A I s i hres)

end Standard

end Langlands.Aubert.General.CorrectedFiltration
