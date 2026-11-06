import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Lie.WeightSupportGalois
import Langlands.GroupScheme.Absolute.CocharacterAveraging
import Mathlib.Logic.Equiv.Set

/-! # The ordinary Galois permutation of actual root indices -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u v

namespace Langlands.GroupScheme

variable (k E : Type u) [Field k] [Field E] [Algebra k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The ordinary character Galois action as an integral linear equivalence. -/
def characterLattice.galoisEquiv (σ : E ≃ₐ[k] E) :
    characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) ≃ₗ[ℤ]
      characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) where
  toLinearMap := characterLattice.galoisRepresentation k E T σ
  invFun := characterLattice.galoisRepresentation k E T σ⁻¹
  left_inv x := Representation.inv_self_apply _ σ x
  right_inv x := Representation.self_inv_apply _ σ x

/-- The ordinary cocharacter Galois action as an integral linear equivalence. -/
def cocharacterLattice.galoisEquiv (σ : E ≃ₐ[k] E) :
    cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) ≃ₗ[ℤ]
      cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T) where
  toLinearMap := cocharacterLattice.galoisRepresentation k E T σ
  invFun := cocharacterLattice.galoisRepresentation k E T σ⁻¹
  left_inv x := Representation.inv_self_apply _ σ x
  right_inv x := Representation.self_inv_apply _ σ x

variable {T}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance baseChangeAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k E))
  infer_instance

/-- Ordinary Galois transport preserves precisely the actual nonzero adjoint weights. -/
theorem mem_roots_galois_iff (σ : E ≃ₐ[k] E)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :
    characterLattice.galoisRepresentation k E T σ χ ∈
        roots ((GroupScheme.baseChange (algebraBaseMap k E)).map i) ↔
      χ ∈ roots ((GroupScheme.baseChange (algebraBaseMap k E)).map i) := by
  have hz := (characterLattice.galoisEquiv k E T σ).map_eq_zero_iff (x := χ)
  rw [mem_roots, mem_roots]
  exact and_congr (not_congr hz) (RelativeRoot.weightSpace_galois_ne_bot_iff k E i σ χ)

variable {J : Type v}
    {P : RootDatum J
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))
      (cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T))}

/-- The ordinary Galois permutation of the indices of a supplied actual root datum. -/
def IsRootDatumOf.galoisRootIndexEquiv
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) : Equiv.Perm J :=
  (Equiv.ofInjective P.root P.root.injective).trans
    ((Equiv.subtypeEquiv (characterLattice.galoisEquiv k E T σ).toEquiv
      (by
        intro χ
        change χ ∈ Set.range P.root ↔
          characterLattice.galoisRepresentation k E T σ χ ∈ Set.range P.root
        rw [hP.2.1]
        exact (mem_roots_galois_iff k E i σ χ).symm)).trans
      (Equiv.ofInjective P.root P.root.injective).symm)

@[simp]
theorem IsRootDatumOf.galoisRootIndexEquiv_root
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    (σ : E ≃ₐ[k] E) (j : J) :
    P.root (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP σ j) =
      characterLattice.galoisRepresentation k E T σ (P.root j) := by
  change P.root ((Equiv.ofInjective P.root P.root.injective).symm _) = _
  exact congrArg Subtype.val
    ((Equiv.ofInjective P.root P.root.injective).apply_symm_apply _)

/-- These ordinary root-index permutations satisfy the Galois group law. -/
def IsRootDatumOf.galoisRootIndexAction
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P) :
    (E ≃ₐ[k] E) →* Equiv.Perm J where
  toFun := IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP
  map_one' := by
    ext j
    apply P.root.injective
    rw [IsRootDatumOf.galoisRootIndexEquiv_root, map_one]
    rfl
  map_mul' σ τ := by
    ext j
    apply P.root.injective
    change P.root (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP (σ * τ) j) =
      P.root (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP σ
        (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP τ j))
    simp only [IsRootDatumOf.galoisRootIndexEquiv_root, map_mul, Module.End.mul_apply]

/-- The index action also preserves the root set of any descended map from the same torus. -/
theorem IsRootDatumOf.galoisRootIndexEquiv_mem_roots_iff
    (hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map i) P)
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (j : T.toGrp ⟶ H) (σ : E ≃ₐ[k] E) (a : J) :
    P.root (IsRootDatumOf.galoisRootIndexEquiv (T := T) (P := P) k E i hP σ a) ∈
        roots ((GroupScheme.baseChange (algebraBaseMap k E)).map j) ↔
      P.root a ∈ roots ((GroupScheme.baseChange (algebraBaseMap k E)).map j) := by
  rw [IsRootDatumOf.galoisRootIndexEquiv_root]
  exact mem_roots_galois_iff k E j σ (P.root a)

end Langlands.GroupScheme
