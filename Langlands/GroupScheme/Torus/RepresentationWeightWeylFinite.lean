import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Torus.WeylImageTransport
import Langlands.GroupTheory.FiniteGeneratorAction

/-! # Full Weyl-image finiteness from representation weight stability -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RepresentationWeightWeylFinite

open splitTorus CharacterRestrictionFiniteIndex

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] (I : Type u) [Fintype I] [DecidableEq I]

local notation "𝕋" => commGroupScheme (Spec (CommRingCat.of k)) I

/-- The actual integral character action of a standard-torus automorphism,
written in exponent coordinates. -/
def exponentAut (σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
    commGroupScheme (Spec (CommRingCat.of k)) I) : (I → ℤ) ≃+ (I → ℤ) :=
  ((characterLatticeEquiv k I).symm.trans (characterAut σ).toAddEquiv).trans
    (characterLatticeEquiv k I)

omit [DecidableEq I] in
@[simp]
theorem characterLatticeEquiv_symm_exponentAut
    (σ : commGroupScheme (Spec (CommRingCat.of k)) I ≅
      commGroupScheme (Spec (CommRingCat.of k)) I) (m : I → ℤ) :
    (characterLatticeEquiv k I).symm (exponentAut I σ m) =
      characterAut σ ((characterLatticeEquiv k I).symm m) :=
  (characterLatticeEquiv k I).symm_apply_apply _

variable {G : GroupScheme (Spec (CommRingCat.of k))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- The actual algebraic characters whose exponent weight matrices are nonzero. -/
def weightCharacters :
    Set (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :=
  (characterLatticeEquiv k I).symm '' {m : I → ℤ | weight ρ I j m ≠ 0}

/-- Only finitely many actual representation weight characters occur. -/
theorem finite_weightCharacters : (weightCharacters I ρ j).Finite := by
  have hs : {m : I → ℤ | weight ρ I j m ≠ 0}.Finite :=
    (weightSupport ρ I j).finite_toSet.subset fun m hm => by
      by_contra h
      exact hm (weight_eq_zero ρ I j h)
  exact hs.image _

/-- A monomorphic composite representation makes the actual weight characters
generate the entire integral character group. -/
theorem closure_weightCharacters_eq_top
    (hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left) :
    AddSubgroup.closure (weightCharacters I ρ j) = ⊤ := by
  change AddSubgroup.closure
    ((characterLatticeEquiv k I).symm.toAddMonoidHom ''
      {m : I → ℤ | weight ρ I j m ≠ 0}) = ⊤
  rw [← AddMonoidHom.map_closure, closure_weights_eq_top ρ I j hmono]
  exact AddSubgroup.map_top_of_surjective _ (characterLatticeEquiv k I).symm.surjective

/-- If normalizing points preserve the nonzero representation weights in
exponent coordinates, their image on the full integral character lattice is finite. -/
theorem finite_weylImage_of_weight_stable [Mono j.hom.hom.left]
    (hmono : Mono (j.hom.hom ≫ ρ.hom.hom).left)
    (hstable : ∀ (n : normalizerPoints (T := 𝕋) j) (m : I → ℤ), weight ρ I j m ≠ 0 →
      weight ρ I j (exponentAut I (normalizingAut (T := 𝕋) j n) m) ≠ 0) :
    Finite (weylImage (T := commGroupScheme (Spec (CommRingCat.of k)) I) j) := by
  apply Langlands.GroupTheory.FiniteGeneratorAction.finite_linear_range_of_preserves_generating_set
    (weylAction (T := 𝕋) j) (weightCharacters I ρ j) ?_
    (finite_weightCharacters I ρ j) (closure_weightCharacters_eq_top I ρ j hmono)
  intro n χ hχ
  obtain ⟨m, hm, rfl⟩ := hχ
  refine ⟨exponentAut I (normalizingAut (T := 𝕋) j n) m, hstable n m hm, ?_⟩
  exact characterLatticeEquiv_symm_exponentAut I (normalizingAut (T := 𝕋) j n) m

end Langlands.GroupScheme.RepresentationWeightWeylFinite
