import Langlands.GroupScheme.Torus.MultiplicativeTypeAbsoluteEquivalenceProof
import Langlands.GroupScheme.Torus.LatticeBaseInvariants

/-! # Recovering an isomorphism from absolute characters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace characterLattice

variable {k : Type u} [Field k]

local notation "Ω" => SeparableClosure k
local notation "BC" => CommGroupScheme.baseChange (algebraBaseMap k Ω)

/-- An equivariant equivalence of the actual absolute character lattices gives
an isomorphism of the groups of multiplicative type in the reverse direction. -/
def isoOfEquivariantAbsoluteEquiv
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsMultiplicativeType T.toGrp) (hU : IsMultiplicativeType U.toGrp)
    (e : characterLattice ((BC).obj T) ≃ₗ[ℤ] characterLattice ((BC).obj U))
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) χ, e (galoisRepresentation k Ω T σ χ) =
      galoisRepresentation k Ω U σ (e χ)) : U ≅ T := by
  let X := MultiplicativeTypeGroup.characterFunctor k
  let A : MultiplicativeTypeGroup k := ⟨T, hT⟩
  let B : MultiplicativeTypeGroup k := ⟨U, hU⟩
  let : X.IsEquivalence := multiplicativeTypeAbsoluteEquivalence k
  let e' : ((X.obj (op A)).representation).Equiv ((X.obj (op B)).representation) :=
    Representation.Equiv.mk e (fun σ => LinearMap.ext (he σ))
  let i : X.obj (op A) ≅ X.obj (op B) :=
    FGDiscreteGaloisModule.toRep.preimageIso (Rep.mkIso e')
  exact (MultiplicativeTypeGroup.inclusion k).mapIso (X.preimageIso i).unop

/-- Every geometric character of a diagonalizable group is the base change
of the evaluation character of its unique integral parameter. -/
def diagonalizableAbsoluteEquiv (M : Type u) [AddCommGroup M] :
    M ≃+ characterLattice ((BC).obj (Diagonalizable.groupScheme (CommRingCat.of k) M)) :=
  (DiagonalizableCharacter.evalCharacterEquiv Ω M).trans
    (characterLattice.congr (Diagonalizable.commBaseChangeIso (algebraBaseMap k Ω) M)).symm

theorem diagonalizableAbsoluteEquiv_apply (M : Type u) [AddCommGroup M] (m : M) :
    diagonalizableAbsoluteEquiv (k := k) M m =
      characterLattice.baseChange (algebraBaseMap k Ω) _
        (DiagonalizableCharacter.evalCharacter (CommRingCat.of k) M m) := by
  rw [MultiplicativeTypeAbsoluteEquivalence.baseChange_evalCharacter]
  rfl

/-- The absolute action on these evaluation characters is trivial. -/
theorem galoisRepresentation_diagonalizableAbsoluteEquiv
    (M : Type u) [AddCommGroup M] (σ : Ω ≃ₐ[k] Ω) (m : M) :
    galoisRepresentation k Ω (Diagonalizable.groupScheme (CommRingCat.of k) M) σ
        (diagonalizableAbsoluteEquiv (k := k) M m) = diagonalizableAbsoluteEquiv (k := k) M m := by
  rw [diagonalizableAbsoluteEquiv_apply]
  exact galoisRepresentation_baseChange k Ω _ σ _

/-- A constant action on the characters of a group of multiplicative type
identifies the group with the diagonalizable group of the character module. -/
def isoOfConstantAbsoluteEquiv {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsMultiplicativeType T.toGrp) {M : Type u} [AddCommGroup M] [AddGroup.FG M]
    (e : M ≃+ characterLattice ((BC).obj T))
    (he : ∀ (σ : Ω ≃ₐ[k] Ω) (m : M), galoisRepresentation k Ω T σ (e m) = e m) :
    T ≅ Diagonalizable.groupScheme (CommRingCat.of k) M := by
  let D := Diagonalizable.groupScheme (CommRingCat.of k) M
  have hD : IsMultiplicativeType D.toGrp :=
    ⟨Ω, inferInstance, inferInstance, M, inferInstance, inferInstance,
      ⟨Diagonalizable.baseChangeIso (algebraBaseMap k Ω) M⟩⟩
  let eq := (diagonalizableAbsoluteEquiv (k := k) M).symm.trans e
  apply isoOfEquivariantAbsoluteEquiv hD hT eq.toIntLinearEquiv
  intro σ χ
  obtain ⟨m, rfl⟩ := (diagonalizableAbsoluteEquiv (k := k) M).surjective χ
  rw [galoisRepresentation_diagonalizableAbsoluteEquiv]
  change e ((diagonalizableAbsoluteEquiv (k := k) M).symm
      (diagonalizableAbsoluteEquiv (k := k) M m)) =
    galoisRepresentation k Ω T σ
      (e ((diagonalizableAbsoluteEquiv (k := k) M).symm
        (diagonalizableAbsoluteEquiv (k := k) M m)))
  rw [AddEquiv.symm_apply_apply, he]

end characterLattice

end Langlands.GroupScheme
