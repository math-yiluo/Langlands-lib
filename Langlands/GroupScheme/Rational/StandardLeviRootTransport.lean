import Langlands.GroupScheme.Rational.RootFiniteness
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Torus.CocharacterAction

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Postcomposition by a torus automorphism on cocharacters. -/
abbrev cocharacterAut (σ : T ≅ T) : cocharacterLattice T ≃ₗ[ℤ] cocharacterLattice T :=
  RealTorusSpace.cocharacterAut σ

@[simp] theorem cocharacterAut_apply (σ : T ≅ T) (zeta : cocharacterLattice T) :
    cocharacterAut σ zeta = zeta ≫ σ.hom :=
  rfl

/-- The character and cocharacter actions of the same automorphism preserve the pairing. -/
theorem latticePairing_characterAut_cocharacterAut (σ : T ≅ T)
    (α : characterLattice T) (zeta : cocharacterLattice T) :
    latticePairing T (characterAut σ α) (cocharacterAut σ zeta) =
      latticePairing T α zeta :=
  RealTorusSpace.latticePairing_aut σ α zeta

/-- Transporting the exact rationally encoded root sets transports the actual character sets.
No assertion about their linear spans is used. -/
theorem weylAction_image_eq_of_relativeWeylAction_image_eq
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hT : IsSplitTorus T.toGrp) {J J' : Set (characterLattice T)}
    (hJ : J ⊆ relativeRoots i) (hJ' : J' ⊆ relativeRoots i)
    (n : normalizerPoints i)
    (h : relativeWeylAction i (QuotientGroup.mk n) ''
        {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} =
      {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J}) :
    weylAction i n '' J' = J := by
  apply Set.Subset.antisymm
  · rintro _ ⟨α, hα, rfl⟩
    have hx : (⟨toRat α, toRat_mem_ratSpan (hJ' hα)⟩ : relativeRootSpan i) ∈
        {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J'} :=
      ⟨α, hα, rfl⟩
    have hy := Set.mem_image_of_mem (relativeWeylAction i (QuotientGroup.mk n)) hx
    rw [h] at hy
    obtain ⟨β, hβ, heq⟩ := hy
    have heq' : toRat β = toRat (weylAction i n α) := heq
    exact hT.character_toRat_injective heq' ▸ hβ
  · intro β hβ
    have hy : (⟨toRat β, toRat_mem_ratSpan (hJ hβ)⟩ : relativeRootSpan i) ∈
        {x : relativeRootSpan i | (x : ℚ ⊗[ℤ] characterLattice T) ∈ toRat '' J} :=
      ⟨β, hβ, rfl⟩
    rw [← h] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨α, hα, hαx⟩ := hx
    refine ⟨α, hα, hT.character_toRat_injective ?_⟩
    calc
      toRat (weylAction i n α) = ratAut (weylAction i n) (toRat α) := rfl
      _ = ratAut (weylAction i n) (x : ℚ ⊗[ℤ] characterLattice T) :=
        congrArg _ hαx
      _ = toRat β := congrArg Subtype.val hxy

/-- Annihilation of a transported character set is equivalent to annihilation before transport. -/
theorem annihilates_image_iff (σ : T ≅ T)
    {J J' : Set (characterLattice T)} (h : characterAut σ '' J' = J)
    (zeta : cocharacterLattice T) :
    (∀ α ∈ J, latticePairing T α (cocharacterAut σ zeta) = 0) ↔
      ∀ α ∈ J', latticePairing T α zeta = 0 := by
  constructor
  · intro hzeta α hα
    have := hzeta (characterAut σ α) (h ▸ Set.mem_image_of_mem _ hα)
    rwa [latticePairing_characterAut_cocharacterAut] at this
  · intro hzeta α hα
    obtain ⟨β, hβ, rfl⟩ := h.symm ▸ hα
    rw [latticePairing_characterAut_cocharacterAut]
    exact hzeta β hβ

/-- Conjugation by a normalizing point on a cocharacter of the torus. -/
theorem groupHom_cocharacterAut_comp (i : T.toGrp ⟶ G)
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    CommGroupScheme.groupHom (cocharacterAut (normalizingAut i n) zeta) ≫ i =
      (CommGroupScheme.groupHom zeta ≫ i) ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom := by
  change (CommGroupScheme.groupHom zeta ≫
    CommGroupScheme.groupHom (normalizingAut i n).hom) ≫ i = _
  rw [Category.assoc, ← isNormalizingPoint_normalizingAut, ← Category.assoc]

end Langlands.GroupScheme
