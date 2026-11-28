import Langlands.GroupScheme.GaloisCocycle
import Langlands.GroupScheme.Torus.FieldCocycleDescent
import Langlands.GroupScheme.Torus.GaloisInvariantLatticesProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.FieldTheory.Galois.Basic

/-! # Descent of a rank-one torus across a Galois extension of odd degree -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An odd-order group acts trivially on a lattice isomorphic to `ℤ`. -/
theorem rankOneLattice_fixed_of_odd_card {Γ M : Type*} [Group Γ] [AddCommGroup M]
    [Module ℤ M] (ρ : Representation ℤ Γ M) (e : M ≃ₗ[ℤ] ℤ)
    (hodd : Odd (Nat.card Γ)) (σ : Γ) (x : M) : ρ σ x = x := by
  let c := e.conjRingEquiv
  let a := c (ρ σ) 1
  have hscalar : c (ρ σ) = algebraMap ℤ (Module.End ℤ ℤ) a := by
    apply LinearMap.ext_ring
    rw [Module.algebraMap_end_apply, smul_eq_mul, mul_one]
  have hpow : (ρ σ) ^ Nat.card Γ = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have ha_pow : a ^ Nat.card Γ = 1 := by
    have h := congrArg c hpow
    rw [map_pow, map_one, hscalar, ← map_pow] at h
    simpa only [Module.algebraMap_end_apply, smul_eq_mul, mul_one, Module.End.one_apply] using
      DFunLike.congr_fun h (1 : ℤ)
  have ha : a = 1 :=
    (hodd.strictMono_pow (R := ℤ)).injective (by simpa only [one_pow] using ha_pow)
  have hρ : ρ σ = 1 := c.injective (by rw [hscalar, ha, map_one, map_one])
  exact DFunLike.congr_fun hρ x

/-- If an affine commutative group over `k` becomes `𝔾ₘ` over a finite Galois
extension `L/k` of odd degree, its `L`-characters are invariant and the group
is isomorphic to `𝔾ₘ` over `k`. -/
def RankOneTorusOddDegreeDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (Q : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom Q.X.hom],
    Odd (Module.finrank k L) →
    Nonempty ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj Q ≅
      Gm (Spec (CommRingCat.of L))) →
    (∀ σ χ, characterLattice.galoisRepresentation k L Q σ χ = χ) ∧
      Nonempty (Q ≅ Gm (Spec (CommRingCat.of k)))

/-- The trivial action on the rank-one character lattice descends the splitting
character to an isomorphism over the ground field. -/
theorem rankOneTorusOddDegreeDescent : RankOneTorusOddDegreeDescentStatement.{u} := by
  intro k L _ _ _ _ _ Q _ hodd ⟨e⟩
  let b := algebraBaseMap k L
  have hcard : Odd (Nat.card (L ≃ₐ[k] L)) := by
    rwa [IsGalois.card_aut_eq_finrank]
  have hfix (σ : L ≃ₐ[k] L) (χ : characterLattice ((CommGroupScheme.baseChange b).obj Q)) :
      characterLattice.galoisRepresentation k L Q σ χ = χ :=
    rankOneLattice_fixed_of_odd_card (characterLattice.galoisRepresentation k L Q)
      ((characterLattice.congr e).trans (gmEndEquiv L)).toIntLinearEquiv hcard σ χ
  obtain ⟨χ, hχ⟩ := (galoisInvariantLattices k L Q).1.2 ⟨e.hom, fun σ => hfix σ e.hom⟩
  have hχ_bc : (CommGroupScheme.baseChange b).map χ ≫ (Gm.commBaseChangeIso b).hom = e.hom :=
    congrArg Subtype.val hχ
  let f := e ≪≫ (Gm.commBaseChangeIso b).symm
  have hf : (CommGroupScheme.baseChange b).map χ = f.hom := by
    apply (cancel_mono (Gm.commBaseChangeIso b).hom).mp
    simpa only [f, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using hχ_bc
  let : Surjective b := (fieldExtension_fpqc k L).1
  let : Flat b := (fieldExtension_fpqc k L).2.1
  let : QuasiCompact b := (fieldExtension_fpqc k L).2.2
  let : IsIso ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom χ)) := by
    change IsIso (CommGroupScheme.groupHom ((CommGroupScheme.baseChange b).map χ))
    rw [hf]
    exact (MultiplicativeTypeGaloisExactness.grpIso f).isIso_hom
  let : IsIso (CommGroupScheme.groupHom χ) := isIso_of_baseChange b _
  exact ⟨hfix, ⟨CommGroupScheme.isoOfGroupIso (asIso (CommGroupScheme.groupHom χ))⟩⟩

section FixedField

variable {k L : Type u} [Field k] [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
  (P : Subgroup (L ≃ₐ[k] L)) (hP : Nat.card P = 7)
  (Q : CommGroupScheme (Spec (CommRingCat.of (IntermediateField.fixedField P))))
  [IsAffineHom Q.X.hom]

local notation "E" => IntermediateField.fixedField P

include hP

/-- Over the fixed field of a subgroup of order seven, an affine quotient torus
that is isomorphic to `𝔾ₘ` over `L` is already split and all its `L`-characters
are fixed by `Gal(L/E)`. -/
theorem rankOneTorus_descent_fixedField_card_seven
    (hsplit : Nonempty ((CommGroupScheme.baseChange (algebraBaseMap E L)).obj Q ≅
      Gm (Spec (CommRingCat.of L)))) :
    (∀ σ χ, characterLattice.galoisRepresentation E L Q σ χ = χ) ∧
      Nonempty (Q ≅ Gm (Spec (CommRingCat.of E))) := by
  apply rankOneTorusOddDegreeDescent E L Q _ hsplit
  rw [IntermediateField.finrank_fixedField_eq_card, hP]
  decide

/-- The rank-one quotient has trivial cocycles on the degree-seven cover of
the fixed field. -/
theorem rankOneTorus_cocycle_isTrivial_fixedField_card_seven
    (hsplit : Nonempty ((CommGroupScheme.baseChange (algebraBaseMap E L)).obj Q ≅
      Gm (Spec (CommRingCat.of L))))
    (ξ : Cocycle Q.toGrp (GaloisCocycle.cover E L)) : ξ.IsTrivial := by
  obtain ⟨e⟩ := (rankOneTorus_descent_fixedField_card_seven P hP Q hsplit).2
  let : IsAffineHom (GaloisCocycle.cover E L).hom := by
    change IsAffineHom (algebraBaseMap E L)
    unfold algebraBaseMap
    infer_instance
  let : Flat (GaloisCocycle.cover E L).hom := (fieldExtension_fpqc E L).2.1
  let : Surjective (GaloisCocycle.cover E L).hom := (fieldExtension_fpqc E L).1
  apply Cocycle.isTrivial_of_isSplitTorus_overField _ ξ
  exact IsSplitTorus.of_iso (MultiplicativeTypeGaloisExactness.grpIso e) isSplitTorus_gm

end FixedField

end Langlands.GroupScheme
