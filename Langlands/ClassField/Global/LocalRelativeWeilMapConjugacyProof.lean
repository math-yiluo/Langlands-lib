import Langlands.ClassField.Global.LocalRelativeWeilMapStatement
import Langlands.ClassField.Global.H1VanishingProof
import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction

/-!
# Conjugacy of local-to-relative Weil maps

Two local-to-relative Weil maps `W_{F_v} → W_{E/F}` for the same place `w` and the same
reciprocity candidate differ by a crossed homomorphism into `C_E`. It is trivial on
the image of `W_{E_w}`, hence factors through the decomposition group, and it is a
coboundary because `H¹` of the idele class group vanishes (Tate 1979, §1.5).
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

namespace RelativeWeilGroup

section Completion

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]

/-- An automorphism of the closure of `F_v` fixing the image of `E` fixes the image of
`E_w`: `E_w` is spanned over `F_v` by `E`. -/
theorem completionClosureEmbedding_fixed_of_global
    (σ : Field.absoluteGaloisGroup (padicField v).Carrier)
    (h : ∀ x : E, AlgEquiv.toAlgHom σ
        (completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x)) =
      completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x))
    (z : w.adicCompletion E) :
    AlgEquiv.toAlgHom σ (completionClosureEmbedding v w z) =
      completionClosureEmbedding v w z := by
  classical
  let q : FinitePlacesAbove E v := ⟨w, inferInstance⟩
  have key : ∀ t, AlgEquiv.toAlgHom σ (completionClosureEmbedding v w
      (finiteTensorMap (L := E) v t q)) =
      completionClosureEmbedding v w (finiteTensorMap (L := E) v t q) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      rw [finiteTensorMap_tmul, map_mul, map_mul]
      congr 1
      swap
      · exact h y
      have ha := completionClosureEmbedding_algebraMap v w a
      change AlgEquiv.toAlgHom σ (completionClosureEmbedding v w
        (algebraMap (v.adicCompletion F) (w.adicCompletion E) a)) =
        completionClosureEmbedding v w
          (algebraMap (v.adicCompletion F) (w.adicCompletion E) a)
      rw [ha]
      exact σ.commutes a
    | add s t hs ht' =>
      simp only [map_add, Pi.add_apply]
      rw [hs, ht']
  obtain ⟨t, ht⟩ := finiteTensorMap_surjective (L := E) v
    (Function.update (0 : (r : FinitePlacesAbove E v) → r.1.adicCompletion E) q z)
  have hz : finiteTensorMap (L := E) v t q = z := by
    rw [ht, Function.update_self]
  rw [← hz]
  exact key t

/-- A local Weil element whose Galois image fixes the image of `E` lies in the image of
`W_{E_w}`. -/
theorem mem_range_completionWeilMap_of_fixes (g : Weil.Local.localWeilGroup (padicField v))
    (h : ∀ x : E, AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) g)
        (completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x)) =
      completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x)) :
    g ∈ (completionWeilMap v w).toMonoidHom.range := by
  rw [Weil.Local.extensionWeilMap_range, Subgroup.mem_comap, Weil.Local.extensionGaloisMap_range]
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun y hy => ?_
  obtain ⟨z, rfl⟩ := (Weil.Local.mem_extensionIntermediateField _ _ _ y).mp hy
  exact completionClosureEmbedding_fixed_of_global v w _ h z

end Completion

section Conjugacy

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}
  {v : Langlands.Global.FinitePlace F} {w : Langlands.Global.FinitePlace E}
  [w.asIdeal.LiesOver v.asIdeal]

/-- Two maps satisfying the Galois condition at `w` have the same Galois images. -/
theorem projection_eq_of_isLocalRelativeWeilMap
    {e e' : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w)}
    {ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap v w e ι) (hι' : IsLocalRelativeWeilMap v w e' ι')
    (g : Weil.Local.localWeilGroup (padicField v)) :
    projection c F E (ι' g) = projection c F E (ι g) := by
  apply AlgEquiv.ext
  intro x
  apply ((completionClosureEmbedding v w).comp (algebraMap E (w.adicCompletion E))).injective
  simp only [RingHom.comp_apply]
  rw [hι'.2.1 g x, hι.2.1 g x]

end Conjugacy

end RelativeWeilGroup

open RelativeWeilGroup in
/-- **Conjugacy of local-to-relative Weil maps** (Tate 1979, §1.5): two local-to-relative
Weil maps for the same place and the same reciprocity candidate are conjugate by an
element of `C_E`. -/
theorem localRelativeWeilMapConjugacy : LocalRelativeWeilMapConjugacyStatement.{u} := by
  intro F E _ _ _ _ _ _ c v w _ e ι ι' hι hι'
  have hproj := projection_eq_of_isLocalRelativeWeilMap hι hι'
  -- The quotient `α g = ι' g (ι g)⁻¹` lies in `C_E`.
  have hker : ∀ g, ∃ a, inclusion c F E a = ι' g * (ι g)⁻¹ := fun g => by
    have : ι' g * (ι g)⁻¹ ∈ (projection c F E).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hproj, mul_inv_cancel]
    rw [← exact] at this
    exact this
  choose α hα using hker
  -- `α` is a crossed homomorphism for the action through the Galois image of `ι`.
  have hcoc : ∀ g h, α (g * h) =
      α g * ideleClassEquiv (projection c F E (ι g)).toRingEquiv (α h) := by
    intro g h
    apply inclusion_injective c F E
    rw [map_mul, ← conjugation]
    simp only [hα, map_mul]
    group
  -- `α` is trivial on the image of `W_{E_w}`.
  have hH : ∀ y, α (completionWeilMap v w y) = 1 := fun y => by
    apply inclusion_injective c F E
    rw [hα, hι.2.2 y, hι'.2.2 y, mul_inv_cancel, map_one]
  -- Hence `α` is trivial on the kernel of the Galois image.
  have hkerτ : ∀ g, projection c F E (ι g) = 1 → α g = 1 := by
    intro g hg
    obtain ⟨y, rfl⟩ := mem_range_completionWeilMap_of_fixes v w g (fun x => by
      have hx := hι.2.1 g x
      rw [hg, AlgEquiv.one_apply] at hx
      exact hx.symm)
    exact hH y
  -- So `α` only depends on the Galois image.
  have hfac : ∀ g g', projection c F E (ι g) = projection c F E (ι g') → α g = α g' := by
    intro g g' hgg
    have h1 : projection c F E (ι (g⁻¹ * g')) = 1 := by
      simp only [map_mul, map_inv, hgg, inv_mul_cancel]
    have h2 := hcoc g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hkerτ _ h1, map_one] at h2
    exact (h2.trans (mul_one (M := IdeleClassGroup (𝓞 E) E) _)).symm
  -- Descend to the decomposition group `Gal(E/K)`, `K` the fixed field of the image.
  let D : Subgroup (E ≃ₐ[F] E) := ((projection c F E).comp ι.toMonoidHom).range
  let K : IntermediateField F E := IntermediateField.fixedField D
  have hK : K.fixingSubgroup = D := IntermediateField.fixingSubgroup_fixedField D
  have hlift : ∀ σ : E ≃ₐ[K] E, ∃ g, projection c F E (ι g) = σ.restrictScalars F := by
    intro σ
    have hσ : σ.restrictScalars F ∈ K.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩
    rw [hK] at hσ
    obtain ⟨g, hg⟩ := hσ
    exact ⟨g, hg⟩
  choose lift hlift using hlift
  let f : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E := fun σ => α (lift σ)
  have hf : ∀ σ σ', f (σ * σ') = f σ * relativeIdeleClassAut K E σ (f σ') := by
    intro σ σ'
    have h1 : f (σ * σ') = α (lift σ * lift σ') := hfac _ _ (by
      rw [hlift, map_mul, map_mul, hlift, hlift]
      rfl)
    rw [h1, hcoc, hlift]
    rfl
  -- `H¹(Gal(E/K), C_E) = 0`.
  have := ideleClassH1Vanishing.{u} K E
  let B := relativeIdeleClassRepresentation K E
  let φ : (E ≃ₐ[K] E) → B := fun σ =>
    (Additive.ofMul (f σ) : Additive (IdeleClassGroup (𝓞 E) E))
  have hmem : φ ∈ groupCohomology.cocycles₁ B := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro σ σ'
    exact congrArg Additive.ofMul ((hf σ σ').trans (mul_comm (f σ) _))
  have hzero : groupCohomology.H1π B ⟨_, hmem⟩ = 0 := Subsingleton.elim _ _
  rw [groupCohomology.H1π_eq_zero_iff] at hzero
  obtain ⟨d, hd⟩ := hzero
  let c0 : IdeleClassGroup (𝓞 E) E := Additive.toMul (α := IdeleClassGroup (𝓞 E) E) d
  have hdσ : ∀ σ, f σ = relativeIdeleClassAut K E σ c0 / c0 := fun σ => by
    have h := congrArg (Additive.toMul (α := IdeleClassGroup (𝓞 E) E)) (congrFun hd σ)
    exact h.symm
  -- Every `α g` is a coboundary.
  have hαg : ∀ g, α g = ideleClassEquiv (projection c F E (ι g)).toRingEquiv c0 / c0 := by
    intro g
    have hmemK : projection c F E (ι g) ∈ K.fixingSubgroup := by
      rw [hK]
      exact ⟨g, rfl⟩
    let σ : E ≃ₐ[K] E := IntermediateField.fixingSubgroupEquiv K ⟨_, hmemK⟩
    have hσ : σ.restrictScalars F = projection c F E (ι g) :=
      congrArg Subtype.val ((IntermediateField.fixingSubgroupEquiv K).symm_apply_apply ⟨_, hmemK⟩)
    have h1 : f σ = α g := hfac _ _ (by rw [hlift, hσ])
    rw [← h1, hdσ σ, ← hσ]
    rfl
  refine ⟨c0⁻¹, fun g => ?_⟩
  have h1 : ι' g = inclusion c F E (α g) * ι g := by rw [hα, inv_mul_cancel_right]
  have hconj := conjugation c F E (ι g) c0
  rw [h1, hαg g]
  calc inclusion c F E (ideleClassEquiv (projection c F E (ι g)).toRingEquiv c0 / c0) * ι g
      = inclusion c F E c0⁻¹ * (ι g * inclusion c F E c0 * (ι g)⁻¹) * ι g := by
        rw [hconj, ← map_mul, div_eq_mul_inv]
        congr 2
        exact mul_comm (G := IdeleClassGroup (𝓞 E) E) _ _
    _ = inclusion c F E c0⁻¹ * ι g * (inclusion c F E c0⁻¹)⁻¹ := by
        rw [map_inv, inv_inv]
        group

end Langlands.ClassField.Global
