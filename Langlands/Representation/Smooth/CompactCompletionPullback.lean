import Langlands.Representation.Smooth.CompactCompletion
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# Compact-open completions under a topological group isomorphism

Pullback reindexes compact open subgroups and preserves their actual orbit
averages. It therefore gives a linear equivalence of compatible families.
-/

noncomputable section

namespace Langlands

open HarishChandraSchwartz

universe uG uH uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {H : Type uH} [Group H] [TopologicalSpace H]

namespace CompactCompletion

/-- Preimage of a compact open subgroup under a topological group isomorphism. -/
def compactIndexComap (e : H ≃ₜ* G) (K : CompactOpenSubgroup G) :
    CompactOpenSubgroup H :=
  ⟨K.1.comap e.toMonoidHom e.continuous,
    e.toHomeomorph.isCompact_preimage.mpr K.2⟩

@[simp]
theorem mem_compactIndexComap (e : H ≃ₜ* G) (K : CompactOpenSubgroup G) (h : H) :
    h ∈ (compactIndexComap e K).1 ↔ e h ∈ K.1 :=
  Iff.rfl

/-- Preimages preserve inclusion of compact indices. -/
theorem compactIndexComap_mono (e : H ≃ₜ* G) {K L : CompactOpenSubgroup G}
    (hKL : K.1 ≤ L.1) :
    (compactIndexComap e K).1 ≤ (compactIndexComap e L).1 :=
  fun _ hk => hKL hk

@[simp]
theorem compactIndexComap_symm_comap (e : H ≃ₜ* G) (K : CompactOpenSubgroup G) :
    compactIndexComap e.symm (compactIndexComap e K) = K := by
  apply Subtype.ext
  apply OpenSubgroup.ext
  intro g
  change e (e.symm g) ∈ K.1 ↔ g ∈ K.1
  rw [e.apply_symm_apply]

@[simp]
theorem compactIndexComap_comap_symm (e : H ≃ₜ* G) (J : CompactOpenSubgroup H) :
    compactIndexComap e (compactIndexComap e.symm J) = J := by
  apply Subtype.ext
  apply OpenSubgroup.ext
  intro h
  change e.symm (e h) ∈ J.1 ↔ h ∈ J.1
  rw [e.symm_apply_apply]

/-- Compact indices on isomorphic topological groups correspond by preimage. -/
def compactIndexEquiv (e : H ≃ₜ* G) :
    CompactOpenSubgroup G ≃ CompactOpenSubgroup H where
  toFun := compactIndexComap e
  invFun := compactIndexComap e.symm
  left_inv := compactIndexComap_symm_comap e
  right_inv := compactIndexComap_comap_symm e

end CompactCompletion

variable [IsTopologicalGroup G] [IsTopologicalGroup H]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

namespace Compact

/-- Pullback has the same normalized average at corresponding compact indices.
The equality follows from equality of the actual orbit sets. -/
theorem averageMap_comp_equiv (e : H ≃ₜ* G) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hcomp : IsSmooth (ρ.comp e.toMonoidHom))
    (J : CompactOpenSubgroup H) :
    averageMap (ρ.comp e.toMonoidHom) hcomp J.1 J.2 =
      averageMap ρ hρ (CompactCompletion.compactIndexComap e.symm J).1
        (CompactCompletion.compactIndexComap e.symm J).2 := by
  ext v
  change orbitMean ((ρ.comp e.toMonoidHom).comp J.1.toSubgroup.subtype) v =
    orbitMean (ρ.comp
      (CompactCompletion.compactIndexComap e.symm J).1.toSubgroup.subtype) v
  have horbit :
      orbit ((ρ.comp e.toMonoidHom).comp J.1.toSubgroup.subtype) v =
        orbit (ρ.comp
          (CompactCompletion.compactIndexComap e.symm J).1.toSubgroup.subtype) v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨⟨e (h : H), ?_⟩, rfl⟩
      change e.symm (e (h : H)) ∈ J.1
      rw [e.symm_apply_apply]
      exact h.property
    · rintro ⟨g, rfl⟩
      refine ⟨⟨e.symm (g : G), g.property⟩, ?_⟩
      change ρ (e (e.symm (g : G))) v = ρ (g : G) v
      rw [e.apply_symm_apply]
  exact congrArg (fun S : Set V => (Nat.card S : ℂ)⁻¹ • ∑ᶠ x : S, x.val) horbit

end Compact

namespace CompactCompletion

/-- Completion commutes with pullback along a topological group isomorphism,
by reindexing its compatible families. -/
def pullbackEquiv (e : H ≃ₜ* G) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hcomp : IsSmooth (ρ.comp e.toMonoidHom)) :
    completion ρ hρ ≃ₗ[ℂ] completion (ρ.comp e.toMonoidHom) hcomp where
  toFun v := ⟨fun J => v.val (compactIndexComap e.symm J), by
    intro J L hLJ
    rw [Compact.averageMap_comp_equiv e ρ hρ hcomp J]
    exact v.property _ _ (compactIndexComap_mono e.symm hLJ)⟩
  invFun w := ⟨fun K => w.val (compactIndexComap e K), by
    intro K L hLK
    have hw := w.property (compactIndexComap e K) (compactIndexComap e L)
      (compactIndexComap_mono e hLK)
    rw [Compact.averageMap_comp_equiv e ρ hρ hcomp,
      compactIndexComap_symm_comap] at hw
    exact hw⟩
  left_inv v := by
    apply Subtype.ext
    funext K
    exact congrArg v.val (compactIndexComap_symm_comap e K)
  right_inv w := by
    apply Subtype.ext
    funext J
    exact congrArg w.val (compactIndexComap_comap_symm e J)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem pullbackEquiv_apply (e : H ≃ₜ* G) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hcomp : IsSmooth (ρ.comp e.toMonoidHom))
    (v : completion ρ hρ) (J : CompactOpenSubgroup H) :
    (pullbackEquiv e ρ hρ hcomp v).val J =
      v.val (compactIndexComap e.symm J) :=
  rfl

@[simp]
theorem pullbackEquiv_symm_apply (e : H ≃ₜ* G) (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (hcomp : IsSmooth (ρ.comp e.toMonoidHom))
    (w : completion (ρ.comp e.toMonoidHom) hcomp) (K : CompactOpenSubgroup G) :
    ((pullbackEquiv e ρ hρ hcomp).symm w).val K =
      w.val (compactIndexComap e K) :=
  rfl

end CompactCompletion

end Langlands
