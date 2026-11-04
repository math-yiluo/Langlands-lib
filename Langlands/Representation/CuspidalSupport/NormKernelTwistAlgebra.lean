import Langlands.Analysis.EndomorphismPowerBound
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Twist.SubquotientProof
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Algebra for twisting from a nonzero restricted intertwiner

The finite-dimensional space used below is the span of one orbit. The ambient
representation and the full space of restricted intertwiners may be infinite-dimensional.
-/

noncomputable section

namespace Langlands.CuspidalSupport

universe uG uV uW uX

section Orbit

variable {G : Type uG} [Group G]
  {X : Type uX} [AddCommGroup X] [Module ℂ X]

/-- A scalar action of a normal finite-index subgroup makes each orbit span
finite-dimensional. -/
theorem finiteDimensional_orbitSpan (ρ : Representation ℂ G X)
    (K : Subgroup G) [K.Normal] [K.FiniteIndex]
    (hscalar : ∀ k : K, ∃ c : ℂ, ∀ x : X, ρ k x = c • x) (x : X) :
    FiniteDimensional ℂ (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule := by
  let T := Submodule.span ℂ (Set.range fun q : G ⧸ K => ρ q.out x)
  have hT : (FiniteVectors.orbitSubrepresentation ρ x).toSubmodule = T := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      obtain ⟨k, hk, hg⟩ := FiniteIndexRestriction.exists_mem_mul_out K g
      obtain ⟨c, hc⟩ := hscalar ⟨k, hk⟩
      change ρ g x ∈ T
      rw [hg, map_mul, Module.End.mul_apply, hc]
      exact T.smul_mem c (Submodule.subset_span ⟨_, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨q, rfl⟩
      exact Submodule.subset_span ⟨q.out, rfl⟩
  rw [hT]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

/-- Commuting operators with a scalar finite-index subgroup admit a nonzero
common eigenvector in the orbit span of any nonzero vector. -/
theorem exists_eigencharacter_of_finiteIndex_scalar (ρ : Representation ℂ G X)
    (K : Subgroup G) [K.Normal] [K.FiniteIndex]
    (hscalar : ∀ k : K, ∃ c : ℂ, ∀ x : X, ρ k x = c • x)
    (hcomm : ∀ g h, Commute (ρ g) (ρ h)) {x : X} (hx : x ≠ 0) :
    ∃ (y : X) (χ : G →* ℂˣ), y ≠ 0 ∧ ∀ g, ρ g y = (χ g : ℂ) • y := by
  let S := FiniteVectors.orbitSubrepresentation ρ x
  have : FiniteDimensional ℂ S.toSubmodule :=
    finiteDimensional_orbitSpan ρ K hscalar x
  have : Nontrivial S.toSubmodule :=
    ⟨⟨⟨x, FiniteVectors.self_mem_orbitSpan ρ x⟩, 0, fun h => hx (congrArg Subtype.val h)⟩⟩
  have hc : ∀ g h, Commute (S.toRepresentation g) (S.toRepresentation h) := by
    intro g h
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    exact LinearMap.congr_fun (hcomm g h).eq (s : X)
  obtain ⟨y, hy, heig⟩ :=
    EndomorphismBound.exists_common_eigenvector S.toRepresentation hc
  obtain ⟨χ, hχ⟩ :=
    EndomorphismBound.exists_character_of_forall_eigen S.toRepresentation hy heig
  exact ⟨y, χ, fun h => hy (Subtype.ext h), fun g => congrArg Subtype.val (hχ g)⟩

end Orbit

section RestrictedHom

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
  (H : Subgroup G) [H.Normal]

/-- The conjugation representation on the restricted Hom space, realized as
the `H`-invariants in the ambient linear-Hom representation. -/
abbrev restrictedHomConjugation :=
  (Representation.linHom ρ σ).toInvariants H

theorem restrictedHomConjugation_trivial (h : H)
    (f : Representation.invariants ((Representation.linHom ρ σ).comp H.subtype)) :
    restrictedHomConjugation ρ σ H h f = f := by
  exact Subtype.ext (f.property h)

/-- Since the action kills `H`, a commutative quotient makes its operators commute. -/
theorem restrictedHomConjugation_commute (hcomm : commutator G ≤ H) (g h : G) :
    Commute (restrictedHomConjugation ρ σ H g) (restrictedHomConjugation ρ σ H h) := by
  have : IsMulCommutative (G ⧸ H) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
  let q := (Representation.linHom ρ σ).quotientToInvariants H
  have hq : ∀ a : G, q (a : G ⧸ H) = restrictedHomConjugation ρ σ H a := by
    intro a
    exact LinearMap.ext (Representation.ofQuotient_coe_apply _ _ a)
  change _ * _ = _ * _
  rw [← hq g, ← hq h, ← map_mul, ← map_mul, mul_comm']

/-- Scalar central actions induce a scalar action on the restricted Hom space. -/
theorem restrictedHomConjugation_center_scalar
    (hρ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v, ρ z v = c • v)
    (hσ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ w, σ z w = c • w)
    (z : Subgroup.center G) :
    ∃ c : ℂ, ∀ f, restrictedHomConjugation ρ σ H z f = c • f := by
  obtain ⟨a, ha⟩ := hρ z⁻¹
  obtain ⟨b, hb⟩ := hσ z
  change ∀ v, ρ (z : G)⁻¹ v = a • v at ha
  refine ⟨b * a, fun f => ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  change σ z (f.val (ρ (z : G)⁻¹ v)) = (b * a) • f.val v
  rw [ha, map_smul, hb, smul_smul]

theorem restrictedHomConjugation_supCenter_scalar
    (hρ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v, ρ z v = c • v)
    (hσ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ w, σ z w = c • w)
    (k : (H ⊔ Subgroup.center G : Subgroup G)) :
    ∃ c : ℂ, ∀ f, restrictedHomConjugation ρ σ H k f = c • f := by
  obtain ⟨h, hh, z, hz, heq⟩ := Subgroup.mem_sup_of_normal_right.mp k.property
  obtain ⟨c, hc⟩ := restrictedHomConjugation_center_scalar ρ σ H hρ hσ ⟨z, hz⟩
  refine ⟨c, fun f => ?_⟩
  rw [← heq, map_mul, Module.End.mul_apply]
  rw [restrictedHomConjugation_trivial ρ σ H ⟨h, hh⟩, hc]

/-- A simultaneous eigenvector of conjugation is an intertwiner in the
direction of the scalar twist used in the target statement. -/
def intertwinerOfConjugationEigenvector
    (f : V →ₗ[ℂ] W) (χ : G →* ℂˣ)
    (hf : ∀ g, Representation.linHom ρ σ g f = (χ g : ℂ) • f) :
    Representation.IntertwiningMap (Langlands.twist χ ρ) σ where
  toLinearMap := f
  isIntertwining' g := by
    ext v
    have h := LinearMap.congr_fun (hf g) (ρ g v)
    change σ g (f (ρ g⁻¹ (ρ g v))) = (χ g : ℂ) • f (ρ g v) at h
    rw [Representation.inv_self_apply] at h
    change f ((χ g : ℂ) • ρ g v) = σ g (f v)
    rw [map_smul]
    exact h.symm

/-- A nonzero restricted intertwiner supplies a nonzero twisted intertwiner
when the subgroup contains the commutator and its product with the centre
has finite index. The resulting character is trivial on the subgroup. -/
theorem exists_twistIntertwiningMap_of_restrictedHom_nonzero
    [(H ⊔ Subgroup.center G : Subgroup G).FiniteIndex]
    (hcomm : commutator G ≤ H)
    (hρ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ v, ρ z v = c • v)
    (hσ : ∀ z : Subgroup.center G, ∃ c : ℂ, ∀ w, σ z w = c • w)
    (f : Representation.IntertwiningMap (ρ.comp H.subtype) (σ.comp H.subtype))
    (hf : f ≠ 0) :
    ∃ χ : G →* ℂˣ, H ≤ χ.ker ∧
      ∃ t : Representation.IntertwiningMap (Langlands.twist χ ρ) σ, t ≠ 0 := by
  let e := Representation.invariantsEquivIntertwiningMap
    (ρ.comp H.subtype) (σ.comp H.subtype)
  let x : Representation.invariants ((Representation.linHom ρ σ).comp H.subtype) :=
    e.symm f
  have hx : x ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact congrArg Subtype.val h
  obtain ⟨y, χ, hy, heig⟩ :=
    exists_eigencharacter_of_finiteIndex_scalar
      (restrictedHomConjugation ρ σ H) (H ⊔ Subgroup.center G)
      (restrictedHomConjugation_supCenter_scalar ρ σ H hρ hσ)
      (restrictedHomConjugation_commute ρ σ H hcomm) hx
  refine ⟨χ, ?_, intertwinerOfConjugationEigenvector ρ σ y.val χ
    (fun g => congrArg Subtype.val (heig g)), ?_⟩
  · intro h hh
    change χ h = 1
    apply Units.ext
    change (χ h : ℂ) = 1
    apply smul_left_injective ℂ hy
    calc
      (χ h : ℂ) • y = restrictedHomConjugation ρ σ H h y := (heig h).symm
      _ = y := restrictedHomConjugation_trivial ρ σ H ⟨h, hh⟩ y
      _ = (1 : ℂ) • y := (one_smul ℂ y).symm
  · intro ht
    apply hy
    apply Subtype.ext
    exact congrArg
      (fun t : Representation.IntertwiningMap (Langlands.twist χ ρ) σ =>
        t.toLinearMap) ht

end RestrictedHom

end Langlands.CuspidalSupport
