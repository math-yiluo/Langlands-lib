import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Smooth.CompactCompletionFixed
import Langlands.Representation.Smooth.CompactCompletionMaps

/-!
# The smooth part of the compact-open completion

Compact averaging embeds a smooth representation in its completion. A smooth
family is recovered from its component at any compact open subgroup fixing it.
-/

noncomputable section

namespace Langlands.CompactCompletion

open Langlands.HarishChandraSchwartz (CompactOpenSubgroup)

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

private def averageFamily : ρ.IntertwiningMap (representation ρ hρ) where
  toLinearMap :=
    { toFun := fun v => ⟨fun K => Compact.averageMap ρ hρ K.1 K.2 v,
        fun K L hLK =>
          Jacquet.averageMap_averageMap_of_le ρ hρ K.1 L.1 K.2 L.2 hLK v⟩
      map_add' := fun v w => by
        apply Subtype.ext
        funext K
        exact (Compact.averageMap ρ hρ K.1 K.2).map_add v w
      map_smul' := fun c v => by
        apply Subtype.ext
        funext K
        exact (Compact.averageMap ρ hρ K.1 K.2).map_smul c v }
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext K
    exact averageMap_translate ρ hρ g K v

private theorem averageFamily_component_eq (K : CompactOpenSubgroup G)
    (x : completion ρ hρ) (hx : x ∈ completionFixed ρ hρ K.1.toSubgroup) :
    averageFamily ρ hρ (x.1 K) = x := by
  apply Subtype.ext
  funext L
  obtain ⟨J, hJ, hJle⟩ :=
    cofinal_fixed_components_of_fixed ρ hρ K.1.toSubgroup K.2 x hx (K.inf L)
  have hJK : J.1 ≤ K.1 := hJle.trans inf_le_left
  have hJL : J.1 ≤ L.1 := hJle.trans inf_le_right
  have he : x.1 J = x.1 K :=
    (Compact.averageMap_id ρ hρ K.1 K.2 (x.1 J) hJ).symm.trans (x.property K J hJK)
  change Compact.averageMap ρ hρ L.1 L.2 (x.1 K) = x.1 L
  rw [← he]
  exact x.property L J hJL

/-- The canonical equivariant identification of a smooth representation with
the smooth vectors in its compact-open completion. -/
def smoothCompletionEquiv (hcof : CompactOpenCofinal G) :
    ρ.Equiv (smoothPart (representation ρ hρ)) :=
  (smoothLift hρ (averageFamily ρ hρ)).ofBijective (by
    constructor
    · intro v w h
      obtain ⟨U, hU⟩ := hρ (v - w)
      obtain ⟨K, hK, hKU⟩ := hcof U
      have hvw : v - w ∈ fixedVectors ρ K.toSubgroup :=
        fun k => hU ⟨k, hKU k.property⟩
      have he := congrArg (fun x : smoothVectors (representation ρ hρ) =>
        x.1.1 ⟨K, hK⟩) h
      change Compact.averageMap ρ hρ K hK v = Compact.averageMap ρ hρ K hK w at he
      apply sub_eq_zero.mp
      rw [← Compact.averageMap_id ρ hρ K hK (v - w) hvw, map_sub, he, sub_self]
    · intro x
      obtain ⟨U, hU⟩ := x.property
      obtain ⟨K, hK, hKU⟩ := hcof U
      let J : CompactOpenSubgroup G := ⟨K, hK⟩
      have hx : x.1 ∈ completionFixed ρ hρ J.1.toSubgroup :=
        fun k hk => congrArg Subtype.val (hU ⟨k, hKU hk⟩)
      exact ⟨x.1.1 J, Subtype.ext (averageFamily_component_eq ρ hρ J x.1 hx)⟩)

@[simp]
theorem smoothCompletionEquiv_apply (hcof : CompactOpenCofinal G)
    (v : V) (K : CompactOpenSubgroup G) :
    (smoothCompletionEquiv ρ hρ hcof v).1.1 K =
      Compact.averageMap ρ hρ K.1 K.2 v :=
  rfl

/-- At an index fixing a smooth family, its component is the recovered vector. -/
theorem smoothCompletionEquiv_symm_apply (hcof : CompactOpenCofinal G)
    (x : smoothVectors (representation ρ hρ)) (K : CompactOpenSubgroup G)
    (hx : x.1 ∈ completionFixed ρ hρ K.1.toSubgroup) :
    (smoothCompletionEquiv ρ hρ hcof).symm x = x.1.1 K := by
  let e := smoothCompletionEquiv ρ hρ hcof
  have he : e (x.1.1 K) = x :=
    Subtype.ext (averageFamily_component_eq ρ hρ K x.1 hx)
  exact e.injective ((e.apply_symm_apply x).trans he.symm)

/-- Completion of an intertwiner agrees with its action on the original
vectors under the smooth-part comparison. -/
theorem smoothCompletionEquiv_natural (hcof : CompactOpenCofinal G)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ) (f : ρ.IntertwiningMap σ) (v : V) :
    map hρ hσ f (smoothCompletionEquiv ρ hρ hcof v).1 =
      (smoothCompletionEquiv σ hσ hcof (f v)).1 := by
  apply Subtype.ext
  funext K
  exact LinearMap.congr_fun (Compact.averageMap_commute ρ σ hρ hσ K.1 K.2 f) v

end Langlands.CompactCompletion
