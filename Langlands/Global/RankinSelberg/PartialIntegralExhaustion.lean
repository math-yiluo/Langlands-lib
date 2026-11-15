import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.RankinSelberg.UnfoldingWhittaker
import Langlands.Global.AdelesSecondCountable
import Langlands.Global.FiniteAdelicGL.RestrictedProduct
import Langlands.Global.AdelicGroupPointTopology

/-! # Exhausting `N_m(𝔸) \ GL_m(𝔸)` by the partial integration domains

The classes `N_m(𝔸) h` whose representative satisfies `h_v ∈ N_m(F_v) GL_m(𝒪_v)` at every
finite place `v ∉ S` form a closed set `unipotentIntegralClasses F m S`. These sets increase
with `S`, and their union is the whole quotient. For an integrable function whose integral
over these sets is multiplied by a factor `c_v` each time a place `v` is added, the full
integral is the partial integral times the infinite product of the `c_v`. See the paired
Markdown.
-/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj Pointwise
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open PrimitiveAdelicHeight (IsUnitriangular)

variable (F : Type u) [Field F] [NumberField F]

/-- The partial integration domain of `partialUnequalWhittakerIntegral` and
`partialDualWhittakerIntegral`: the classes `q ∈ N_m(𝔸) \ GL_m(𝔸)` whose representative
`q.out` lies in `N_m(F_v) GL_m(𝒪_v)` at every finite place `v ∉ S`. -/
def unipotentIntegralClasses (n : ℕ) (S : Finset (FinitePlace F)) :
    Set (WhittakerQuotient F n) :=
  {q | q.out ∈ unipotentIntegralOutside F n S}

variable {F}

/-- `partialUnequalWhittakerIntegral` is the integral over `unipotentIntegralClasses`. -/
theorem partialUnequalWhittakerIntegral_eq_setIntegral {r t : ℕ} (h : t < r)
    (S : Finset (FinitePlace F)) (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ)
    (s : ℂ) :
    partialUnequalWhittakerIntegral F h S W W' s =
      ∫ q in unipotentIntegralClasses F (t + 1) S, unequalWhittakerIntegrand F h W W' s q
        ∂whittakerQuotientMeasure F (t + 1) :=
  rfl

/-- `partialDualWhittakerIntegral` is the integral over `unipotentIntegralClasses`. -/
theorem partialDualWhittakerIntegral_eq_setIntegral {r t : ℕ} (h : t < r)
    (S : Finset (FinitePlace F)) (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ)
    (s : ℂ) :
    partialDualWhittakerIntegral F h S W W' s =
      ∫ q in unipotentIntegralClasses F (t + 1) S, dualWhittakerIntegrand F h W W' s q
        ∂whittakerQuotientMeasure F (t + 1) :=
  rfl

/-- `partialEqualWhittakerIntegral` is the integral over `unipotentIntegralClasses`. -/
theorem partialEqualWhittakerIntegral_eq_setIntegral {r : ℕ} (S : Finset (FinitePlace F))
    (W W' : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) :
    partialEqualWhittakerIntegral F S W W' Φ s =
      ∫ q in unipotentIntegralClasses F (r + 1) S, equalWhittakerIntegrand F W W' Φ s q
        ∂whittakerQuotientMeasure F (r + 1) :=
  rfl

theorem unipotentIntegralOutside_mono {n : ℕ} {S S' : Finset (FinitePlace F)} (h : S ⊆ S') :
    unipotentIntegralOutside F n S ⊆ unipotentIntegralOutside F n S' :=
  fun _ hg v hv => hg v fun hvS => hv (h hvS)

theorem unipotentIntegralClasses_mono {n : ℕ} {S S' : Finset (FinitePlace F)} (h : S ⊆ S') :
    unipotentIntegralClasses F n S ⊆ unipotentIntegralClasses F n S' :=
  fun _ hq => unipotentIntegralOutside_mono h hq

theorem finiteComponent_mul (n : ℕ) (v : FinitePlace F) (g g' : Points F n) :
    finiteComponent F n v (g * g') = finiteComponent F n v g * finiteComponent F n v g' := by
  simp only [finiteComponent, map_mul]

theorem continuous_finiteComponent (n : ℕ) (v : FinitePlace F) :
    Continuous (finiteComponent F n v) :=
  (FiniteAdelicGL.localProjection F n v).continuous.comp
    ((AdelicGL.finite F n).continuous.comp
      (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)

theorem finiteComponent_apply (n : ℕ) (v : FinitePlace F) (g : Points F n) (i j : Fin n) :
    finiteComponent F n v g i j =
      ((GeneralLinearGroupPoints.adelicEquiv F n g :
        Matrix.GeneralLinearGroup (Fin n) (Adeles F)) i j).2 v :=
  rfl

/-- The local components of a point of `N_n(𝔸)` are upper unitriangular. -/
theorem isUnitriangular_finiteComponent {n : ℕ} {u : Points F n}
    (hu : u ∈ unipotentAdelic F n) (v : FinitePlace F) :
    IsUnitriangular ((finiteComponent F n v u : FiniteLocalGL F n v) :
      Matrix (Fin n) (Fin n) (FiniteCompletion F v)) := by
  have h := (Unfolding.mem_unipotentAdelic_iff F u).mp hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change finiteComponent F n v u i j = 0
    rw [finiteComponent_apply, h.1 hij]
    rfl
  · change finiteComponent F n v u i i = 1
    rw [finiteComponent_apply, h.2 i]
    rfl

/-- The upper unitriangular elements of `GL_n(F_v)`. -/
def localUnitriangular (n : ℕ) (v : FinitePlace F) : Set (FiniteLocalGL F n v) :=
  {x | IsUnitriangular (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v))}

theorem isClosed_localUnitriangular (n : ℕ) (v : FinitePlace F) :
    IsClosed (localUnitriangular (F := F) n v) := by
  have hc : Continuous fun x : FiniteLocalGL F n v =>
      (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) := Units.continuous_val
  have hent : ∀ i j, Continuous fun x : FiniteLocalGL F n v =>
      (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hc)
  have : localUnitriangular (F := F) n v =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i),
        {x : FiniteLocalGL F n v |
          (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) i j = 0}) ∩
        ⋂ i : Fin n, {x : FiniteLocalGL F n v |
          (x : Matrix (Fin n) (Fin n) (FiniteCompletion F v)) i i = 1} := by
    ext x
    simp only [localUnitriangular, IsUnitriangular, Matrix.IsUpperTriangular,
      Matrix.BlockTriangular, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [this]
  refine IsClosed.inter (isClosed_iInter fun i => isClosed_iInter fun j =>
    isClosed_iInter fun _ => isClosed_eq (hent i j) continuous_const)
    (isClosed_iInter fun i => isClosed_eq (hent i i) continuous_const)

theorem isUnipotentIntegral_iff (n : ℕ) (v : FinitePlace F) (x : FiniteLocalGL F n v) :
    IsUnipotentIntegral F n v x ↔
      x ∈ localUnitriangular (F := F) n v *
        (FiniteAdelicGL.localIntegral F n v : Set (FiniteLocalGL F n v)) := by
  constructor
  · rintro ⟨k, hk, hdiag, hlow⟩
    refine ⟨x * k, ⟨fun i j hij => hlow i j hij, hdiag⟩, k⁻¹, inv_mem hk, ?_⟩
    simp
  · rintro ⟨y, hy, k, hk, rfl⟩
    refine ⟨k⁻¹, inv_mem hk, ?_, ?_⟩
    · intro i
      simpa using hy.2 i
    · intro i j hij
      simpa using hy.1 hij

theorem isClosed_setOf_isUnipotentIntegral (n : ℕ) (v : FinitePlace F) :
    IsClosed {x : FiniteLocalGL F n v | IsUnipotentIntegral F n v x} := by
  have : {x : FiniteLocalGL F n v | IsUnipotentIntegral F n v x} =
      localUnitriangular (F := F) n v *
        (FiniteAdelicGL.localIntegral F n v : Set (FiniteLocalGL F n v)) := by
    ext x
    exact isUnipotentIntegral_iff n v x
  rw [this]
  exact (isClosed_localUnitriangular n v).mul_right_of_isCompact
    (FiniteAdelicGL.isCompact_localIntegral F n v)

theorem isClosed_unipotentIntegralOutside (n : ℕ) (S : Finset (FinitePlace F)) :
    IsClosed (unipotentIntegralOutside F n S) := by
  have : unipotentIntegralOutside F n S =
      ⋂ v : FinitePlace F, ⋂ (_ : v ∉ S),
        finiteComponent F n v ⁻¹' {x | IsUnipotentIntegral F n v x} := by
    ext g
    simp [unipotentIntegralOutside]
  rw [this]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    (isClosed_setOf_isUnipotentIntegral n v).preimage (continuous_finiteComponent n v)

/-- `N_n(𝔸) · (N_n(F_v) GL_n(𝒪_v) at every v ∉ S) ⊆ (the same set)`. -/
theorem mul_mem_unipotentIntegralOutside {n : ℕ} {S : Finset (FinitePlace F)}
    {u g : Points F n} (hu : u ∈ unipotentAdelic F n)
    (hg : g ∈ unipotentIntegralOutside F n S) :
    u * g ∈ unipotentIntegralOutside F n S := by
  intro v hv
  obtain ⟨k, hk, hdiag, hlow⟩ := hg v hv
  have hgk : IsUnitriangular (((finiteComponent F n v g * k : FiniteLocalGL F n v)) :
      Matrix (Fin n) (Fin n) (FiniteCompletion F v)) := ⟨fun i j hij => hlow i j hij, hdiag⟩
  have hm := (isUnitriangular_finiteComponent hu v).mul hgk
  refine ⟨k, hk, fun i => ?_, fun i j hij => ?_⟩
  · rw [finiteComponent_mul, mul_assoc]
    exact hm.2 i
  · rw [finiteComponent_mul, mul_assoc]
    exact hm.1 hij

theorem mk_mem_unipotentIntegralClasses_iff (n : ℕ) (S : Finset (FinitePlace F))
    (g : Points F n) :
    LeftCosetSpace.mk (unipotentAdelic F n) g ∈ unipotentIntegralClasses F n S ↔
      g ∈ unipotentIntegralOutside F n S := by
  set q := LeftCosetSpace.mk (unipotentAdelic F n) g
  have hq : LeftCosetSpace.mk (unipotentAdelic F n) q.out = q := Quotient.out_eq q
  have h1 : g * q.out⁻¹ ∈ unipotentAdelic F n :=
    (LeftCosetSpace.mk_eq_mk_iff _ _ _).mp hq
  have h2 : q.out * g⁻¹ ∈ unipotentAdelic F n := by
    simpa using inv_mem h1
  change q.out ∈ unipotentIntegralOutside F n S ↔ g ∈ unipotentIntegralOutside F n S
  constructor
  · intro h
    simpa using mul_mem_unipotentIntegralOutside h1 h
  · intro h
    simpa using mul_mem_unipotentIntegralOutside h2 h

theorem preimage_mk_unipotentIntegralClasses (n : ℕ) (S : Finset (FinitePlace F)) :
    LeftCosetSpace.mk (unipotentAdelic F n) ⁻¹' unipotentIntegralClasses F n S =
      unipotentIntegralOutside F n S := by
  ext g
  exact mk_mem_unipotentIntegralClasses_iff n S g

theorem isClosed_unipotentIntegralClasses (n : ℕ) (S : Finset (FinitePlace F)) :
    IsClosed (unipotentIntegralClasses F n S) := by
  rw [← (LeftCosetSpace.isQuotientMap_mk (unipotentAdelic F n)).isClosed_preimage,
    preimage_mk_unipotentIntegralClasses]
  exact isClosed_unipotentIntegralOutside n S

theorem measurableSet_unipotentIntegralClasses (n : ℕ) (S : Finset (FinitePlace F)) :
    MeasurableSet (unipotentIntegralClasses F n S) :=
  (isClosed_unipotentIntegralClasses n S).measurableSet

/-- Every adelic point lies in `N_n(F_v) GL_n(𝒪_v)` at all but finitely many finite places. -/
theorem exists_mem_unipotentIntegralOutside (n : ℕ) (g : Points F n) :
    ∃ A : Finset (FinitePlace F), g ∈ unipotentIntegralOutside F n A := by
  have hev := FiniteAdelicGL.eventually_localIntegral F n
    (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicEquiv F n g))
  refine ⟨(Filter.eventually_cofinite.mp hev).toFinset, fun v hv => ?_⟩
  have hvK : finiteComponent F n v g ∈ FiniteAdelicGL.localIntegral F n v := by
    by_contra hc
    exact hv ((Filter.eventually_cofinite.mp hev).mem_toFinset.mpr hc)
  refine ⟨(finiteComponent F n v g)⁻¹, inv_mem hvK, fun i => ?_, fun i j hij => ?_⟩
  · simp
  · simp [Matrix.one_apply_ne hij.ne']

theorem iUnion_unipotentIntegralClasses (n : ℕ) :
    (⋃ A : Finset (FinitePlace F), unipotentIntegralClasses F n A) = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨A, hA⟩ := exists_mem_unipotentIntegralOutside n q.out
  exact Set.mem_iUnion.mpr ⟨A, hA⟩

/-- **Exhaustion.** Let `f` be integrable on `N_n(𝔸) \ GL_n(𝔸)` for some measure `μ`. Suppose
that adding a place `v ∉ S'` to any finite `S' ⊇ S` multiplies the integral of `f` over
`unipotentIntegralClasses F n S'` by `c_v`. If `∏_(v ∉ S) c_v` converges to `p`, then
`∫ f dμ = p · ∫_(unipotentIntegralClasses F n S) f dμ`. -/
theorem integral_eq_hasProd_mul_setIntegral {n : ℕ} {S : Finset (FinitePlace F)}
    {ν : Measure (WhittakerQuotient F n)} {f : WhittakerQuotient F n → ℂ}
    (hf : Integrable f ν) {c : {v : FinitePlace F // v ∉ S} → ℂ} {p : ℂ}
    (hc : HasProd c p)
    (hstep : ∀ A : Finset (FinitePlace F), S ⊆ A → ∀ v : {v : FinitePlace F // v ∉ S},
      ∀ hv : v.1 ∉ A,
      ∫ q in unipotentIntegralClasses F n (Finset.cons v.1 A hv), f q ∂ν =
        c v * ∫ q in unipotentIntegralClasses F n A, f q ∂ν) :
    ∫ q, f q ∂ν = p * ∫ q in unipotentIntegralClasses F n S, f q ∂ν := by
  classical
  have : Countable (FinitePlace F) := finitePlace_countable F
  let e : {v : FinitePlace F // v ∉ S} ↪ FinitePlace F := Function.Embedding.subtype _
  let s : Finset {v : FinitePlace F // v ∉ S} → Set (WhittakerQuotient F n) := fun B =>
    unipotentIntegralClasses F n (S ∪ B.map e)
  have hmono : Monotone s := fun B B' h =>
    unipotentIntegralClasses_mono (Finset.union_subset_union le_rfl (Finset.map_subset_map.mpr h))
  have hunion : (⋃ B, s B) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨A, hA⟩ := exists_mem_unipotentIntegralOutside n q.out
    refine Set.mem_iUnion.mpr ⟨A.subtype (fun v => v ∉ S), ?_⟩
    refine unipotentIntegralOutside_mono (fun v hv => ?_) hA
    by_cases hvS : v ∈ S
    · exact Finset.mem_union_left _ hvS
    · exact Finset.mem_union_right _
        (Finset.mem_map.mpr ⟨⟨v, hvS⟩, Finset.mem_subtype.mpr hv, rfl⟩)
  have hprod : ∀ B : Finset {v : FinitePlace F // v ∉ S},
      ∫ q in s B, f q ∂ν = (∏ v ∈ B, c v) * ∫ q in unipotentIntegralClasses F n S, f q ∂ν := by
    intro B
    induction B using Finset.induction_on with
    | empty => simp [s]
    | insert a B ha ih =>
      have hnot : a.1 ∉ S ∪ B.map e := by
        simp only [Finset.mem_union, Finset.mem_map, not_or, not_exists, not_and]
        exact ⟨a.2, fun b hb hba => ha (by
          have : b = a := Subtype.ext hba
          exact this ▸ hb)⟩
      have hins : S ∪ (insert a B).map e = insert a.1 (S ∪ B.map e) := by
        rw [Finset.map_insert, Finset.union_insert]
        rfl
      change ∫ q in unipotentIntegralClasses F n (S ∪ (insert a B).map e), f q ∂ν = _
      have h := hstep _ Finset.subset_union_left a hnot
      rw [Finset.cons_eq_insert] at h
      rw [hins, h, Finset.prod_insert ha, mul_assoc]
      exact congrArg (c a * ·) ih
  have hlim1 : Tendsto (fun B => ∫ q in s B, f q ∂ν) atTop (𝓝 (∫ q, f q ∂ν)) := by
    have h := tendsto_setIntegral_of_monotone
      (fun B => measurableSet_unipotentIntegralClasses n _) hmono hf.integrableOn
    rwa [hunion, Measure.restrict_univ] at h
  have hlim2 : Tendsto (fun B => ∫ q in s B, f q ∂ν) atTop
      (𝓝 (p * ∫ q in unipotentIntegralClasses F n S, f q ∂ν)) := by
    have hc' : Tendsto (fun B : Finset {v : FinitePlace F // v ∉ S} => ∏ v ∈ B, c v) atTop
        (𝓝 p) := hc
    simp_rw [hprod]
    exact hc'.mul_const _
  exact tendsto_nhds_unique hlim1 hlim2

end Langlands.Global.RankinSelbergGlobal
