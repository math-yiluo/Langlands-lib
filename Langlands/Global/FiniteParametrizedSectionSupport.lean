import Langlands.Global.AdelicGLStandardCompact
import Langlands.Global.FiniteBlockParabolicCosets
import Langlands.Representation.FiniteKernelSubquotient
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Smooth.Definitions

/-! A finite set of projected sections suffices on a compact-finite cyclic generator. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global

open GeneralLinear FiniteVectors _root_.Representation

variable {F : Type*} [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  {J V : Type*} [AddCommGroup V] [Module ℂ V]
  {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]

/-- The indices for which the projected section has a nonzero value. -/
def sectionEvaluationSupport
    (e : ∀ j : J, standardInfiniteCompact F n → FiniteAdelicGL F n → V →ₗ[ℂ] W j)
    (v : V) : Set J :=
  {j | ∃ k g, e j k g v ≠ 0}

/-- The projected sections of a smooth, compact-finite vector have a common finite
support in the projection indices, given pointwise finite support and covariance. -/
theorem finiteSectionEvaluationSupport
    (κ : Representation ℂ (standardInfiniteCompact F n) V)
    (ρ : Representation ℂ (FiniteAdelicGL F n) V)
    (e : ∀ j : J, standardInfiniteCompact F n → FiniteAdelicGL F n → V →ₗ[ℂ] W j)
    (hpoint : ∀ g v, {j | e j 1 g v ≠ 0}.Finite)
    (hcompact : ∀ j k g v, e j k g v = e j 1 g (κ k v))
    (htrans : ∀ j k g d v, e j k g (ρ d v) = e j k (g * d) v)
    (hcov : ∀ j k (p : AdelicBlockParabolic.Finite F B) g v,
      e j k g v = 0 → e j k (p.val * g) v = 0)
    (v : V) (hκ : IsFiniteVector κ v) (hρ : IsSmoothVector ρ v) :
    (sectionEvaluationSupport e v).Finite := by
  obtain ⟨L, hL⟩ := hρ
  obtain ⟨s, hsfin, hs⟩ := Submodule.fg_def.mp (Module.Finite.iff_fg.mp hκ)
  let reps := finiteBlockParabolicDoubleCosetReps F B L
  let indices : Set J :=
    ⋃ a ∈ (reps : Set (FiniteAdelicGL F n)), ⋃ w ∈ s, {j | e j 1 a w ≠ 0}
  have hindices : indices.Finite :=
    reps.finite_toSet.biUnion fun a _ => hsfin.biUnion fun w _ => hpoint a w
  apply hindices.subset
  rintro j ⟨k, g, hj⟩
  by_contra hn
  obtain ⟨a, ha, p, l, rfl⟩ := finiteBlockParabolicDoubleCosetReps_cover F B L g
  have hspan : orbitSpan κ v ≤ (e j 1 a).ker := by
    rw [← hs, Submodule.span_le]
    intro w hw
    apply LinearMap.mem_ker.mpr
    by_contra hw'
    apply hn
    exact Set.mem_biUnion ha (Set.mem_biUnion hw hw')
  have he : e j k a v = 0 :=
    (hcompact j k a v).trans (hspan (action_mem_orbitSpan κ k v))
  have hl : ρ l.val v = v := hL ⟨l.val, l.property⟩
  rw [← htrans, hl] at hj
  exact hj (hcov j k p a v he)

end Langlands.Global

namespace Langlands

open FiniteVectors _root_.Representation

/-- On a cyclic carrier, a projection whose stable kernel contains the generator
vanishes on the whole carrier. Hence finite support on the generator suffices
for extraction of the simple quotient in one projected representation. -/
theorem exists_subquotient_of_cyclicProjections
    {M G V W J : Type*} [Monoid M] [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {Y : J → Type*} [∀ j, AddCommGroup (Y j)] [∀ j, Module ℂ (Y j)]
    {ρ : Representation ℂ M V} {τ : Representation ℂ M W} [τ.IsIrreducible]
    (α : G →* M) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (σ : ∀ j, Representation ℂ G (Y j))
    (f : ∀ j, Representation.IntertwiningMap (ρ.comp α) (σ j))
    (K : J → Subrepresentation ρ) (hK : ∀ j x, x ∈ K j ↔ f j x = 0)
    (hkill : ∀ x, (∀ j, f j x = 0) → q x = 0)
    (v : V) (hv : orbitSpan ρ v = ⊤) (hfin : {j | f j v ≠ 0}.Finite) :
    ∃ j, Correspondence.IsSubquotientOf (σ j) (τ.comp α) := by
  classical
  let J₀ := {j : J // f j v ≠ 0}
  let : Fintype J₀ := hfin.fintype
  have hkill₀ (x : V) (hx : ∀ j : J₀, f j.val x = 0) : q x = 0 := by
    apply hkill x
    intro j
    by_cases hj : f j v = 0
    · apply (hK j x).mp
      have htop : ⊤ ≤ (K j).toSubmodule :=
        hv ▸ orbitSpan_le ρ v (K j) ((hK j v).mpr hj)
      exact htop (Submodule.mem_top)
    · exact hx ⟨j, hj⟩
  obtain ⟨j, hj⟩ := exists_subquotient_of_finiteProjections α q hq
    (fun j : J₀ => σ j.val) (fun j => f j.val) (fun j => K j.val)
    (fun j => hK j.val) hkill₀
  exact ⟨j.val, hj⟩

end Langlands
