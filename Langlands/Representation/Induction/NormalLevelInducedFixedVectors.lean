import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Plancherel.NormalizedCompactPicture
import Langlands.BruhatTits.SpecialCompact.SmallSubgroupPredicates

/-! # Induced fixed vectors at a prescribed normal level -/

noncomputable section

namespace Langlands.Induction

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
  [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module R V]

omit [CommRing R] [AddCommGroup V] [Module R V] in
/-- A point normalizing the level leaves its coefficient stabilizer unchanged. -/
theorem conjOpenSubgroup_eq_comap_of_mem_normalizer
    (P : Subgroup G) (K : OpenSubgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    (conjOpenSubgroup P K x).toSubgroup = K.toSubgroup.comap P.subtype := by
  ext p
  rw [OpenSubgroup.mem_toSubgroup, mem_conjOpenSubgroup, Subgroup.mem_comap]
  exact ((Subgroup.mem_normalizer_iff'' (H := K.toSubgroup) (g := x)).mp
    hx (p : G)).symm

/-- Restriction to a subgroup normalizing the level takes values in the one
literal intersection fixed space. -/
def normalLevelEvaluation (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (K₀ : Subgroup G)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set G)) :
    fixedVectors (smoothInduced P σ) K.toSubgroup →ₗ[R]
      (K₀ → fixedVectors σ (K.toSubgroup.comap P.subtype)) where
  toFun f k := ⟨eval P σ f.val k, by
    rw [← conjOpenSubgroup_eq_comap_of_mem_normalizer P K (hnormal k.property)]
    exact eval_mem_fixedVectors P σ K k f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A factorization `G = P K₀` makes restriction injective on fixed sections. -/
theorem normalLevelEvaluation_injective (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (K₀ : Subgroup G)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set G))
    (hfactor : ∀ x : G, ∃ p : P, ∃ k : K₀, x = (p : G) * (k : G)) :
    Function.Injective (normalLevelEvaluation P σ K K₀ hnormal) := by
  intro f g hfg
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  obtain ⟨p, k, rfl⟩ := hfactor x
  change eval P σ f.val ((p : G) * (k : G)) =
    eval P σ g.val ((p : G) * (k : G))
  rw [eval_covariant, eval_covariant]
  exact congrArg (σ p) (congrArg (fun a => (a k).val) hfg)

/-- At a compact open level normalized by `K₀`, with `G = P K₀`, induced
fixed vectors are nonzero exactly when the coefficient intersection fixed
vectors are nonzero. Neither compactness nor openness of `K₀` is needed. -/
theorem nontrivial_fixedVectors_smoothInduced_iff
    (P : Subgroup G) (σ : Representation R P V)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (K₀ : Subgroup G)
    (hnormal : K₀ ≤ Subgroup.normalizer (K : Set G))
    (hfactor : ∀ x : G, ∃ p : P, ∃ k : K₀, x = (p : G) * (k : G)) :
    Nontrivial (fixedVectors (smoothInduced P σ) K.toSubgroup) ↔
      Nontrivial (fixedVectors σ (K.toSubgroup.comap P.subtype)) := by
  constructor
  · intro h
    let := h
    obtain ⟨f, hf⟩ := exists_ne
      (0 : fixedVectors (smoothInduced P σ) K.toSubgroup)
    let ev := normalLevelEvaluation P σ K K₀ hnormal
    have hne : ev f ≠ 0 := fun he =>
      hf (normalLevelEvaluation_injective P σ K K₀ hnormal hfactor
        (he.trans ev.map_zero.symm))
    have hex : ∃ k : K₀, ev f k ≠ 0 := by
      by_contra hn
      apply hne
      funext k
      exact not_ne_iff.mp (not_exists.mp hn k)
    obtain ⟨k, hk⟩ := hex
    exact ⟨⟨ev f k, 0, hk⟩⟩
  · intro h
    let := h
    obtain ⟨v, hv⟩ := exists_ne
      (0 : fixedVectors σ (K.toSubgroup.comap P.subtype))
    let w : fixedVectors σ (conjOpenSubgroup P K 1).toSubgroup :=
      ⟨v.val, by
        rw [conjOpenSubgroup_eq_comap_of_mem_normalizer P K
          (show (1 : G) ∈ Subgroup.normalizer (K : Set G) from
            (Subgroup.normalizer (K : Set G)).one_mem)]
        exact v.property⟩
    let f := fixedDoubleCosetSection P σ K hK 1 w
    refine ⟨⟨f, 0, ?_⟩⟩
    intro hf
    apply hv
    apply Subtype.ext
    have he := fixedDoubleCosetSection_eval_self P σ K hK 1 w
    change eval P σ f.val 1 = v.val at he
    rw [hf] at he
    exact he.symm

end Langlands.Induction
