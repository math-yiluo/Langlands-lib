import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.CompactCompletionAction
import Langlands.Representation.Smooth.CompactCompletionMaps

/-!
# The compact-open completion of the smooth contragredient

A functional on a smooth representation gives a family of smooth functionals
by precomposing with each compact average. A compatible family recovers a
functional by evaluation at a level fixing the vector.
-/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

private theorem average_smoothDual_apply (K : CompactOpenSubgroup G)
    (ℓ : SmoothDual ρ) (v : V) :
    (Compact.averageMap (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
      K.1 K.2 ℓ).1 v = ℓ.1 (Compact.averageMap ρ hρ K.1 K.2 v) := by
  let w := Compact.averageMap ρ hρ K.1 K.2 v
  let h := isSmooth_smoothContragredient ρ
  have hw := Compact.averageMap_mem_fixedVectors ρ hρ K.1 K.2 v
  have havg := Compact.averageMap_mem_fixedVectors (smoothContragredient ρ) h K.1 K.2 ℓ
  change smoothDualPairing ρ
    (Compact.averageMap (smoothContragredient ρ) h K.1 K.2 ℓ) v = ℓ.1 w
  rw [← Jacquet.smoothDualPairing_averageMap ρ hρ K.1 K.2 havg v]
  change ((smoothDualPairing ρ).flip w)
    (Compact.averageMap (smoothContragredient ρ) h K.1 K.2 ℓ) = ℓ.1 w
  apply Jacquet.map_averageMap_of_forall_eq
  intro k
  change ℓ.1 (ρ (k : G)⁻¹ w) = ℓ.1 w
  exact congrArg ℓ.1 (hw k⁻¹)

private def dualComponent (ℓ : Module.Dual ℂ V) (K : CompactOpenSubgroup G) :
    SmoothDual ρ :=
  ⟨ℓ.comp (Compact.averageMap ρ hρ K.1 K.2), K.1, fun k => by
    apply LinearMap.ext
    intro v
    change ℓ (Compact.averageMap ρ hρ K.1 K.2 (ρ (k : G)⁻¹ v)) =
      ℓ (Compact.averageMap ρ hρ K.1 K.2 v)
    exact congrArg ℓ (Jacquet.averageMap_apply_of_mem ρ hρ K.1 K.2
      (K.1.inv_mem k.property) v)⟩

private def dualFamily : ρ.dual.IntertwiningMap
    (representation (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)) where
  toLinearMap :=
    { toFun := fun ℓ => ⟨dualComponent ρ hρ ℓ, by
        intro K L hLK
        apply Subtype.ext
        apply LinearMap.ext
        intro v
        rw [average_smoothDual_apply ρ hρ]
        change ℓ (Compact.averageMap ρ hρ L.1 L.2 (Compact.averageMap ρ hρ K.1 K.2 v)) =
          ℓ (Compact.averageMap ρ hρ K.1 K.2 v)
        exact congrArg ℓ (Compact.averageMap_id ρ hρ L.1 L.2 _
          (fun l => Compact.averageMap_mem_fixedVectors ρ hρ K.1 K.2 v
            ⟨l, hLK l.property⟩))⟩
      map_add' := fun ℓ m => by
        apply Subtype.ext
        funext K
        apply Subtype.ext
        rfl
      map_smul' := fun c ℓ => by
        apply Subtype.ext
        funext K
        apply Subtype.ext
        rfl }
  isIntertwining' g := by
    apply LinearMap.ext
    intro ℓ
    apply Subtype.ext
    funext K
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change ℓ (ρ g⁻¹ (Compact.averageMap ρ hρ K.1 K.2 v)) =
      ℓ (Compact.averageMap ρ hρ (K.conj g⁻¹).1 (K.conj g⁻¹).2 (ρ g⁻¹ v))
    rw [averageMap_translate ρ hρ]
    simp [CompactOpenSubgroup.conj_mul]

omit [IsTopologicalGroup G] in
include hρ in
private theorem exists_compact_fixer (hcof : CompactOpenCofinal G) (v : V) :
    ∃ K : CompactOpenSubgroup G, v ∈ fixedVectors ρ K.1.toSubgroup := by
  obtain ⟨U, hu⟩ := hρ v
  obtain ⟨K, hK, hKU⟩ := hcof U
  exact ⟨⟨K, hK⟩, fun k => hu ⟨k, hKU k.property⟩⟩

include hρ in
private theorem family_eval_eq_of_le
    (x : completion (smoothContragredient ρ) (isSmooth_smoothContragredient ρ))
    {K L : CompactOpenSubgroup G} (hLK : L.1 ≤ K.1)
    {v : V} (hv : v ∈ fixedVectors ρ K.1.toSubgroup) :
    (x.1 K).1 v = (x.1 L).1 v := by
  rw [← x.property K L hLK, average_smoothDual_apply ρ hρ,
    Compact.averageMap_id ρ hρ K.1 K.2 v hv]

/-- Precomposition with the compact averages realizes the algebraic dual as
the completion of the smooth contragredient, equivariantly for translation. -/
def dualCompletionEquiv (hcof : CompactOpenCofinal G) :
    ρ.dual.Equiv
      (representation (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)) :=
  (dualFamily ρ hρ).ofBijective (by
    constructor
    · intro ℓ m h
      apply LinearMap.ext
      intro v
      obtain ⟨K, hK⟩ := exists_compact_fixer ρ hρ hcof v
      have he := congrArg
        (fun x : completion (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) =>
          (x.1 K).1 v) h
      change ℓ (Compact.averageMap ρ hρ K.1 K.2 v) =
        m (Compact.averageMap ρ hρ K.1 K.2 v) at he
      rwa [Compact.averageMap_id ρ hρ K.1 K.2 v hK] at he
    · intro x
      choose J hJ using exists_compact_fixer ρ hρ hcof
      let value (v : V) := (x.1 (J v)).1 v
      have hvalue (v : V) (K : CompactOpenSubgroup G)
          (hv : v ∈ fixedVectors ρ K.1.toSubgroup) : value v = (x.1 K).1 v :=
        (family_eval_eq_of_le ρ hρ x
          (L := (J v).inf K) inf_le_left (hJ v)).trans
          (family_eval_eq_of_le ρ hρ x (L := (J v).inf K) inf_le_right hv).symm
      let ℓ : Module.Dual ℂ V :=
        { toFun := value
          map_add' := fun v w => by
            let K := (J v).inf (J w)
            have hv : v ∈ fixedVectors ρ K.1.toSubgroup :=
              fun k => hJ v ⟨k, k.property.1⟩
            have hw : w ∈ fixedVectors ρ K.1.toSubgroup :=
              fun k => hJ w ⟨k, k.property.2⟩
            rw [hvalue (v + w) K ((fixedVectors ρ K.1.toSubgroup).add_mem hv hw),
              hvalue v K hv, hvalue w K hw, map_add]
          map_smul' := fun c v => by
            rw [hvalue (c • v) (J v) ((fixedVectors ρ (J v).1.toSubgroup).smul_mem c (hJ v))]
            exact (x.1 (J v)).1.map_smul c v }
      refine ⟨ℓ, ?_⟩
      apply Subtype.ext
      funext K
      apply Subtype.ext
      apply LinearMap.ext
      intro v
      change value (Compact.averageMap ρ hρ K.1 K.2 v) = (x.1 K).1 v
      rw [hvalue _ K (Compact.averageMap_mem_fixedVectors ρ hρ K.1 K.2 v)]
      have hx : x.1 K ∈ fixedVectors (smoothContragredient ρ) K.1.toSubgroup :=
        x.property K K le_rfl ▸ Compact.averageMap_mem_fixedVectors
          (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K.1 K.2 (x.1 K)
      exact Jacquet.smoothDualPairing_averageMap ρ hρ K.1 K.2 hx v)

@[simp]
theorem dualCompletionEquiv_apply (hcof : CompactOpenCofinal G)
    (ℓ : Module.Dual ℂ V) (K : CompactOpenSubgroup G) (v : V) :
    ((dualCompletionEquiv ρ hρ hcof ℓ).1 K).1 v =
      ℓ (Compact.averageMap ρ hρ K.1 K.2 v) :=
  rfl

/-- The recovered functional evaluates a family at any index fixing the vector. -/
theorem dualCompletionEquiv_symm_apply (hcof : CompactOpenCofinal G)
    (x : completion (smoothContragredient ρ) (isSmooth_smoothContragredient ρ))
    (K : CompactOpenSubgroup G) {v : V} (hv : v ∈ fixedVectors ρ K.1.toSubgroup) :
    (dualCompletionEquiv ρ hρ hcof).symm x v = (x.1 K).1 v := by
  let E := dualCompletionEquiv ρ hρ hcof
  have he := congrArg
    (fun y : completion (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) =>
      (y.1 K).1 v) (E.apply_symm_apply x)
  simpa only [E, dualCompletionEquiv_apply, Compact.averageMap_id ρ hρ K.1 K.2 v hv]
    using he

/-- Pullback along an intertwiner agrees with the componentwise completion
map on smooth contragredients. -/
theorem dualCompletionEquiv_natural (hcof : CompactOpenCofinal G)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (f : ρ.IntertwiningMap σ) (ℓ : Module.Dual ℂ W) :
    map (isSmooth_smoothContragredient σ) (isSmooth_smoothContragredient ρ)
      (contragredientMap f) (dualCompletionEquiv σ hσ hcof ℓ) =
      dualCompletionEquiv ρ hρ hcof (dualIntertwining f ℓ) := by
  apply Subtype.ext
  funext K
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change ℓ (Compact.averageMap σ hσ K.1 K.2 (f v)) =
    ℓ (f (Compact.averageMap ρ hρ K.1 K.2 v))
  exact congrArg ℓ
    ((LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K.1 K.2 f) v).symm)

end Langlands.CompactCompletion
