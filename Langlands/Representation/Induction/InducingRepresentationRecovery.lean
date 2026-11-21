import Langlands.Representation.Induction.CompactLocalSection

/-!
# Smooth induction reflects admissibility

When the ambient group has a compact open subgroup basis and the coefficient
ring is Noetherian, evaluate a right-`K`-fixed induced function at `1`. The
section supported on `P * K` gives surjectivity onto the `(P ∩ K)`-fixed
coefficients. See the paired Markdown.
-/

noncomputable section

namespace Langlands.Induction

universe uR uG uX

section SmoothInduction

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type uX} [AddCommGroup X] [Module R X]
variable (P : Subgroup G) (τ : Representation R P X)

section Evaluation

variable [IsTopologicalGroup G]

/-- Evaluation at a single point on the fixed spaces, with the conjugated
fixed-space codomain already used by `fixedEvaluation`. -/
def fixedEvaluationAt (K : OpenSubgroup G) (x : G) :
    fixedVectors (smoothInduced P τ) K.toSubgroup →ₗ[R]
      fixedVectors τ (conjOpenSubgroup P K x).toSubgroup where
  toFun f := ⟨eval P τ f.val x, eval_mem_fixedVectors P τ K x f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- For compact open `K`, evaluation at `1` maps the `K`-fixed vectors of smooth
induction onto the coefficient vectors fixed by `P ∩ K`. -/
theorem fixedEvaluation_one_surjective (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Function.Surjective (fixedEvaluationAt P τ K 1) := by
  classical
  intro v
  let f := compactDoubleCosetSection P τ K hK 1 v.val v.property
  have hf : f.val ∈ fixedVectors (smoothInduced P τ) K.toSubgroup := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact compactDoubleCosetSection_mul P τ K hK 1 v.val v.property ⟨k.val, k.property⟩ g
  refine ⟨⟨f.val, hf⟩, ?_⟩
  apply Subtype.ext
  change eval P τ f.val 1 = v.val
  have h := compactDoubleCosetSection_apply P τ K hK 1 v.val v.property (1 : P) (1 : K)
  change eval P τ f.val ((1 : G) * 1 * 1) = τ 1 v.val at h
  simpa using h

end Evaluation

/-- If the smooth induction of a smooth representation `τ` is admissible, so is
`τ`. This does not require the parabolic quotient to be compact. -/
theorem isAdmissible_of_smoothInduced [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    [IsNoetherianRing R] (hτ : IsSmooth τ) (h : IsAdmissible (smoothInduced P τ)) :
    IsAdmissible τ := by
  classical
  refine ⟨hτ, fun H => ?_⟩
  obtain ⟨U, hU, hUH⟩ := isOpen_induced_iff.mp H.isOpen
  have h1 : (1 : G) ∈ U := by
    have : (1 : P) ∈ Subtype.val ⁻¹' U := by rw [hUH]; exact H.one_mem
    simpa using this
  obtain ⟨K, hK, hKU⟩ := compactOpenSubgroupBasis G U (hU.mem_nhds h1)
  have hle : (conjOpenSubgroup P K 1).toSubgroup ≤ H.toSubgroup := by
    intro q hq
    have hqK : (q : G) ∈ K := by simpa using mem_conjOpenSubgroup.mp hq
    have hqU : q ∈ Subtype.val ⁻¹' U := hKU hqK
    rwa [hUH] at hqU
  have hfixed : fixedVectors τ H.toSubgroup ≤ fixedVectors τ (conjOpenSubgroup P K 1).toSubgroup :=
    fun v hv q => hv ⟨q.val, hle q.property⟩
  have := h.2 K
  have := Module.Finite.of_surjective _ (fixedEvaluation_one_surjective P τ K hK)
  exact Module.Finite.of_injective (Submodule.inclusion hfixed) (Submodule.inclusion_injective hfixed)

end SmoothInduction

/-- Surjective inflation reflects irreducibility: invariance of a subspace
under the target group is equivalent to invariance under the pullback action. -/
theorem isIrreducible_of_comp_surjective {P' : Type*} [Group P'] {M : Type*} [Group M]
    {k : Type uR} [Field k] {Y : Type uX} [AddCommGroup Y] [Module k Y]
    (m : P' →* M) (hm : Function.Surjective m) (Ξ : Representation k M Y)
    (h : Representation.IsIrreducible (Ξ.comp m)) : Ξ.IsIrreducible := by
  let e : Subrepresentation Ξ ≃o Subrepresentation (Ξ.comp m) :=
    { toFun := fun W => ⟨W.toSubmodule, fun p _ hv => W.apply_mem_toSubmodule (m p) hv⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => by
        obtain ⟨p, rfl⟩ := hm g
        exact W.apply_mem_toSubmodule p hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mpr h

end Langlands.Induction
