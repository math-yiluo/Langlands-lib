import Langlands.Global.AdelicGroupLocalPoints

/-! # Local factors inside actual adelic group points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Filter
open scoped CategoryTheory.MonObj RestrictedProduct

namespace Langlands.Global.AdelicGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]

local instance : DecidableEq (Place F) := Classical.decEq _

omit [IsAffine G.X.left] in
private theorem singleFamily_isAdelic (i : Place F) (g : PlaceGroupPoints F G i) :
    IsAdelicFamily F G (Pi.mulSingle i g) := by
  classical
  apply isAdelicFamily_of_eventually_eq F G _ 1
  have hi : ∀ᶠ j : Place F in cofinite, j ≠ i := by simp
  filter_upwards [Sum.inr_injective.tendsto_cofinite.eventually hi] with v hv
  simp [Pi.mulSingle_eq_of_ne hv]

/-- Insert an actual local point at one place and the identity at all other places. -/
def ofPlace (i : Place F) : PlaceGroupPoints F G i →* AdelicGroupPoints F G where
  toFun g := glue F G (Pi.mulSingle i g) (singleFamily_isAdelic F G i g)
  map_one' := by
    apply ext_atPlace F G
    intro j
    simp
  map_mul' g h := by
    apply ext_atPlace F G
    intro j
    simp [Pi.mulSingle_mul]

@[simp] theorem atPlace_ofPlace (i j : Place F) (g : PlaceGroupPoints F G i) :
    atPlace F G j (ofPlace F G i g) = Pi.mulSingle i g j :=
  atPlace_glue F G _ (singleFamily_isAdelic F G i g) j

@[simp] theorem atPlace_ofPlace_same (i : Place F) (g : PlaceGroupPoints F G i) :
    atPlace F G i (ofPlace F G i g) = g := by
  classical
  simp

theorem atPlace_ofPlace_of_ne (i j : Place F) (h : j ≠ i)
    (g : PlaceGroupPoints F G i) : atPlace F G j (ofPlace F G i g) = 1 := by
  classical
  simp [h]

/-- The local insertion is continuous for the existing evaluation topologies. -/
theorem continuous_ofPlace (i : Place F) : Continuous (ofPlace F G i) := by
  classical
  refine (G.continuous_affinePoints_iff _ _).mpr fun a => ?_
  let f : PlaceGroupPoints F G i → AdeleRing (𝓞 F) F := fun g =>
    G.affinePointEvaluation (CommAlgCat.of F (AdeleRing (𝓞 F) F)) (ofPlace F G i g) a
  have hf (j : Place F) : Continuous fun g => adeleProjection F j (f g) := by
    have he : (fun g => adeleProjection F j (f g)) = fun g =>
        G.affinePointEvaluation (placeCompletion F j) (Pi.mulSingle i g j) a := by
      funext g
      exact glue_evaluation F G _ (singleFamily_isAdelic F G i g) a j
    rw [he]
    exact (G.continuous_affinePointEvaluation (placeCompletion F j) a).comp
      ((continuous_apply j).comp (continuous_mulSingle i))
  have hfst : Continuous fun g => (f g).1 := continuous_pi fun w => hf (.inl w)
  have ha : ∀ᶠ v : FinitePlace F in cofinite, ∀ g : PlaceGroupPoints F G i,
      (f g).2 v ∈ v.adicCompletionIntegers F := by
    have hi : ∀ᶠ j : Place F in cofinite, j ≠ i := by simp
    filter_upwards [Sum.inr_injective.tendsto_cofinite.eventually hi,
      eventually_atPlace_evaluation_mem F G 1 a] with v hv ha
    intro g
    have he := glue_evaluation F G (Pi.mulSingle i g) (singleFamily_isAdelic F G i g) a (.inr v)
    change (f g).2 v = _ at he
    rw [he, Pi.mulSingle_eq_of_ne hv]
    simpa using ha
  let S : Set (FinitePlace F) := {v | ∀ g : PlaceGroupPoints F G i,
    (f g).2 v ∈ v.adicCompletionIntegers F}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr ha
  let f' : PlaceGroupPoints F G i →
      Πʳ v : FinitePlace F, [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 S] :=
    fun g => ⟨fun v => (f g).2 v, eventually_principal.mpr fun v hv => hv g⟩
  have hf' : Continuous f' :=
    RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun v => hf (.inr v)
  exact hfst.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf')

/-- The local insertion is a continuous group homomorphism. -/
def ofPlaceContinuous (i : Place F) : PlaceGroupPoints F G i →ₜ* AdelicGroupPoints F G where
  toMonoidHom := ofPlace F G i
  continuous_toFun := continuous_ofPlace F G i

/-- Each local group embeds as a closed subgroup of the actual adelic group. -/
theorem isClosedEmbedding_ofPlace (i : Place F) :
    Topology.IsClosedEmbedding (ofPlace F G i) :=
  Function.LeftInverse.isClosedEmbedding (atPlace_ofPlace_same F G i)
    (atPlace F G i).continuous (continuous_ofPlace F G i)

/-- The image consists exactly of points equal to the identity at other places. -/
theorem mem_range_ofPlace_iff (i : Place F) (g : AdelicGroupPoints F G) :
    g ∈ (ofPlace F G i).range ↔ ∀ j, j ≠ i → atPlace F G j g = 1 := by
  constructor
  · rintro ⟨h, rfl⟩ j hj
    exact atPlace_ofPlace_of_ne F G i j hj h
  · intro h
    refine ⟨atPlace F G i g, ?_⟩
    apply ext_atPlace F G
    intro j
    by_cases hj : j = i
    · subst j
      exact atPlace_ofPlace_same F G i _
    · rw [atPlace_ofPlace_of_ne F G i j hj, h j hj]

/-- Each local factor is normal in the actual adelic group. -/
instance range_ofPlace_normal (i : Place F) : (ofPlace F G i).range.Normal where
  conj_mem g hg h := by
    rw [mem_range_ofPlace_iff] at hg ⊢
    intro j hj
    simp [hg j hj]

/-- Local factors at distinct places commute. -/
theorem ofPlace_commute (i j : Place F) (hij : i ≠ j)
    (g : PlaceGroupPoints F G i) (h : PlaceGroupPoints F G j) :
    Commute (ofPlace F G i g) (ofPlace F G j h) := by
  change _ * _ = _ * _
  apply ext_atPlace F G
  intro k
  simp only [map_mul]
  by_cases hk : k = i
  · subst k
    rw [atPlace_ofPlace_of_ne F G j i hij]
    simp
  · rw [atPlace_ofPlace_of_ne F G i k hk]
    simp

end Langlands.Global.AdelicGroupPoints
