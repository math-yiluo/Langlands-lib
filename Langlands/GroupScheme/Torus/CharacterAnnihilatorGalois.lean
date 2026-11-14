import Langlands.GroupScheme.Torus.HomKernelDiagonalizable
import Langlands.GroupScheme.Descent.GaloisSubgroupTransport

/-! # Full character annihilators and Galois transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.characterLattice

section Annihilator

variable {k : Type u} [CommRing k] [IsDomain k]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The full subgroup functor cut out by a submodule of actual characters. -/
def annihilatorSubgroupFunctor (L : Submodule ℤ (characterLattice T)) :
    SubgroupFunctor T.toGrp where
  carrier U :=
    { carrier := {x | ∀ χ ∈ L, pointCharacters T U x (.ofAdd χ) = 1}
      one_mem' := by
        intro χ hχ
        rw [map_one]
        rfl
      mul_mem' := by
        intro x y hx hy χ hχ
        rw [map_mul]
        change pointCharacters T U x (.ofAdd χ) *
          pointCharacters T U y (.ofAdd χ) = 1
        rw [hx χ hχ, hy χ hχ, one_mul]
      inv_mem' := by
        intro x hx χ hχ
        rw [map_inv]
        change (pointCharacters T U x (.ofAdd χ))⁻¹ = 1
        rw [hx χ hχ, inv_one] }
  comp_mem a x hx χ hχ := by
    rw [pointCharacters_naturality, hx χ hχ, map_one]

omit [IsDomain k] in
@[simp]
theorem mem_annihilatorSubgroupFunctor (L : Submodule ℤ (characterLattice T))
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X) :
    x ∈ (annihilatorSubgroupFunctor T L).carrier U ↔
      ∀ χ ∈ L, pointCharacters T U x (.ofAdd χ) = 1 :=
  Iff.rfl

variable {T} {Q : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The full kernel of a morphism into a split torus is the annihilator of
the integral image of its actual character pullback. -/
theorem range_kernel_eq_annihilator (f : T.toGrp ⟶ Q.toGrp)
    (hQ : IsSplitTorus Q.toGrp) :
    SubgroupFunctor.range (kernelι f) =
      annihilatorSubgroupFunctor T (comapHom f).toIntLinearMap.range := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, mem_annihilatorSubgroupFunctor]
  constructor
  · intro hx χ hχ
    obtain ⟨ψ, rfl⟩ := hχ
    change pointCharacters T U x (.ofAdd (comapHom f ψ)) = 1
    rw [← pointCharacters_comp_hom, hx, map_one]
    rfl
  · intro hx
    apply (pointCharactersEquiv Q hQ U).injective
    apply MonoidHom.ext
    intro ψ
    change pointCharacters Q U (x ≫ f.hom.hom) (.ofAdd ψ.toAdd) =
      pointCharacters Q U 1 (.ofAdd ψ.toAdd)
    rw [map_one, pointCharacters_comp_hom]
    exact hx _ ⟨ψ.toAdd, rfl⟩

end Annihilator

section Galois

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (L : Submodule ℤ
      (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))

/-- Canonical transport of the full annihilator agrees with the annihilator
of the transported integral character submodule. -/
theorem descentTransport_annihilatorSubgroupFunctor (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.descentTransport (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) T.toGrp
        (annihilatorSubgroupFunctor _ L) =
      annihilatorSubgroupFunctor _ (L.map (galoisRepresentation k K T σ)) := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_descentTransport_iff_descentPoint,
    mem_annihilatorSubgroupFunctor, mem_annihilatorSubgroupFunctor]
  constructor
  · intro hx χ hχ
    obtain ⟨ψ, hψ, rfl⟩ := hχ
    rw [pointCharacters_apply, galoisRepresentation_points]
    exact hx ψ hψ
  · intro hx χ hχ
    have h := hx (galoisRepresentation k K T σ χ) ⟨χ, hχ, rfl⟩
    rw [pointCharacters_apply, galoisRepresentation_points] at h
    exact h

/-- A Galois-stable integral submodule cuts out an invariant full subgroup
functor, without saturation or reduction. -/
theorem descentTransport_annihilatorSubgroupFunctor_eq (σ : K ≃ₐ[k] K)
    (hL : L.map (galoisRepresentation k K T σ) = L) :
    SubgroupFunctor.descentTransport (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) T.toGrp
        (annihilatorSubgroupFunctor _ L) =
      annihilatorSubgroupFunctor _ L := by
  rw [descentTransport_annihilatorSubgroupFunctor, hL]

/-- Any represented annihilator of a stable integral character submodule has
the same full range as its canonical Galois translate. -/
theorem range_galoisTranslate_eq_of_annihilator
    {H : GroupScheme (Spec (CommRingCat.of K))}
    (i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj T.toGrp)
    (hi : SubgroupFunctor.range i = annihilatorSubgroupFunctor _ L)
    (σ : K ≃ₐ[k] K)
    (hL : L.map (galoisRepresentation k K T σ) = L) :
    SubgroupFunctor.range
        ((GroupScheme.baseChange (galoisBaseMap k K σ)).map i ≫
          (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
            (galoisBaseMap_over k K σ) T.toGrp).hom) =
      SubgroupFunctor.range i := by
  rw [← SubgroupFunctor.descentTransport_range, hi]
  exact descentTransport_annihilatorSubgroupFunctor_eq T L σ hL

end Galois

end Langlands.GroupScheme.characterLattice
