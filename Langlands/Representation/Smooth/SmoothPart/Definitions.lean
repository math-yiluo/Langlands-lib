import Langlands.Representation.Smooth.Definitions
import Mathlib.RepresentationTheory.Subrepresentation

/-! # The smooth part of an algebraic representation

Construction fields are proved directly from the open-subgroup definition.
Only the foundational smoothness definitions are a project dependency.
-/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} {G : Type uG} {V : Type uV} {W : Type uW}
variable [CommRing R] [Group G] [TopologicalSpace G]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- The submodule of vectors fixed by some open subgroup. -/
def smoothVectors (ρ : Representation R G V) : Submodule R V where
  carrier := {v | IsSmoothVector ρ v}
  zero_mem' := ⟨⊤, (fixedVectors ρ (⊤ : OpenSubgroup G).toSubgroup).zero_mem⟩
  add_mem' := by
    intro v w hv hw
    obtain ⟨K, hK⟩ := hv
    obtain ⟨L, hL⟩ := hw
    refine ⟨K ⊓ L, ?_⟩
    change ∀ k : (K ⊓ L : OpenSubgroup G), ρ (k : G) (v + w) = v + w
    intro k
    have hkv : ρ (k : G) v = v := hK ⟨(k : G), k.property.1⟩
    have hkw : ρ (k : G) w = w := hL ⟨(k : G), k.property.2⟩
    rw [map_add, hkv, hkw]
  smul_mem' := by
    intro a v hv
    obtain ⟨K, hK⟩ := hv
    exact ⟨K, (fixedVectors ρ K.toSubgroup).smul_mem a hK⟩

variable [IsTopologicalGroup G]

/-- The smooth vectors, bundled as a Mathlib subrepresentation. -/
def smoothSubrepresentation (ρ : Representation R G V) : Subrepresentation ρ where
  toSubmodule := smoothVectors ρ
  apply_mem_toSubmodule := by
    intro g v hv
    obtain ⟨K, hK⟩ := hv
    let cg : G →* G := (MulAut.conj g⁻¹).toMonoidHom
    have hcg : Continuous cg := IsTopologicalGroup.continuous_conj g⁻¹
    refine ⟨K.comap cg hcg, ?_⟩
    change ∀ k : K.comap cg hcg, ρ (k : G) (ρ g v) = ρ g v
    intro k
    apply (ρ.inv_apply_eq_iff (g := g)).mp
    have hk := hK ⟨cg (k : G), k.property⟩
    change ρ (g⁻¹ * (k : G) * (g⁻¹)⁻¹) v = v at hk
    simpa only [inv_inv, map_mul, Module.End.mul_apply] using hk

/-- Restriction of the representation to its smooth vectors. -/
def smoothPart (ρ : Representation R G V) : Representation R G (smoothVectors ρ) :=
  (smoothSubrepresentation ρ).toRepresentation

/-- The canonical inclusion of the smooth part. -/
def smoothInclusion (ρ : Representation R G V) : (smoothPart ρ).IntertwiningMap ρ where
  toLinearMap := (smoothVectors ρ).subtype
  isIntertwining' _ := by
    ext v
    rfl

variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Restrict the codomain of an intertwiner from a smooth representation. -/
def smoothLift (hσ : IsSmooth σ) (f : σ.IntertwiningMap ρ) :
    σ.IntertwiningMap (smoothPart ρ) where
  toLinearMap := f.toLinearMap.codRestrict (smoothVectors ρ) (by
    intro v
    obtain ⟨K, hK⟩ := hσ v
    refine ⟨K, ?_⟩
    change ∀ k : K, ρ (k : G) (f v) = f v
    intro k
    rw [← f.isIntertwining]
    exact congrArg f (hK k))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change f (σ g v) = ρ g (f v)
    exact congrArg (fun m : W →ₗ[R] V => m v) (f.isIntertwining' g)

/-- Restrict an intertwiner to the smooth parts of its source and target. -/
def smoothMap (f : ρ.IntertwiningMap σ) :
    (smoothPart ρ).IntertwiningMap (smoothPart σ) :=
  smoothLift (by
    intro v
    obtain ⟨K, hK⟩ := v.property
    refine ⟨K, ?_⟩
    intro k
    apply Subtype.ext
    exact hK k) (f.comp (smoothInclusion ρ))

/-- The smooth-part inclusion is an equivalence when the original action is smooth. -/
def smoothEquiv (hρ : IsSmooth ρ) : (smoothPart ρ).Equiv ρ :=
  (smoothInclusion ρ).ofBijective
    ⟨Subtype.val_injective, fun v => ⟨⟨v, hρ v⟩, rfl⟩⟩

end Langlands
