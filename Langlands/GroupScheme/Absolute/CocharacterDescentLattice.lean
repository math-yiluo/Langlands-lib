import Langlands.GroupScheme.Absolute.CocharacterDescentGroup
import Langlands.GroupScheme.Absolute.CocharacterAveraging

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GaloisCocharacterDescent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Base change of an actual cocharacter, with the canonical Gm identification. -/
def baseChangeCocharacter
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G :=
  (Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
    (GroupScheme.baseChange (algebraBaseMap k K)).map χ

/-- A cocharacter is determined by its base change along any field extension. -/
theorem baseChangeCocharacter_injective :
    Function.Injective (baseChangeCocharacter k K G) := by
  let := faithful_algebraPullback k K
  intro χ ψ h
  apply (GroupScheme.baseChange (algebraBaseMap k K)).map_injective
  exact (cancel_epi (Gm.baseChangeIso (algebraBaseMap k K)).inv).mp h

variable [FiniteDimensional k K] [IsGalois k K] [IsAffineHom G.X.hom]
  (ν : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
    (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
  (hν : IsInvariant k K G ν)

include hν in
/-- An invariant cocharacter has a unique descent over the original field. -/
theorem existsUnique_descent :
    ∃! χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      baseChangeCocharacter k K G χ = ν := by
  refine ⟨descend k K G ν hν, baseChange_descend k K G ν hν, ?_⟩
  intro χ hχ
  apply baseChangeCocharacter_injective k K G
  exact hχ.trans (baseChange_descend k K G ν hν).symm

end GaloisCocharacterDescent

namespace cocharacterLattice

section BaseChange

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (T : CommGroupScheme S)

/-- Base change of cocharacters as an additive map of the actual lattices. -/
def baseChange :
    cocharacterLattice T →+
      cocharacterLattice ((CommGroupScheme.baseChange b).obj T) where
  toFun ν := (Gm.commBaseChangeIso b).inv ≫ (CommGroupScheme.baseChange b).map ν
  map_zero' := by simp
  map_add' ν ν' := by simp [Functor.map_add, Preadditive.comp_add]

theorem groupHom_baseChange (ν : cocharacterLattice T) :
    CommGroupScheme.groupHom (baseChange b T ν) =
      (Gm.baseChangeIso b).inv ≫
        (GroupScheme.baseChange b).map (CommGroupScheme.groupHom ν) := rfl

end BaseChange

section Descent

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
  (hν : ∀ σ : K ≃ₐ[k] K, galoisRepresentation k K T σ ν = ν)

/-- A fixed lattice cocharacter descends through the actual group-scheme construction. -/
def descend : cocharacterLattice T :=
  Additive.ofMul
    (GaloisCocharacterDescent.descend k K T.toGrp (CommGroupScheme.groupHom ν)
      (fun σ => congrArg CommGroupScheme.groupHom (hν σ)))

/-- Extending a descended lattice cocharacter recovers the given fixed element. -/
theorem baseChange_descend :
    baseChange (algebraBaseMap k K) T (descend k K T ν hν) = ν := by
  change (Gm.baseChangeIso (algebraBaseMap k K)).inv ≫
    (GroupScheme.baseChange (algebraBaseMap k K)).map
      (GaloisCocharacterDescent.descend k K T.toGrp (CommGroupScheme.groupHom ν)
        (fun σ => congrArg CommGroupScheme.groupHom (hν σ))) =
      CommGroupScheme.groupHom ν
  exact GaloisCocharacterDescent.baseChange_descend k K T.toGrp _ _

end Descent

end cocharacterLattice

namespace CocharacterAveraging

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffineHom T.X.hom]
  (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))

/-- The integral orbit sum as an actual cocharacter over the original field. -/
def descendedOrbitSum : cocharacterLattice T :=
  cocharacterLattice.descend k K T (galoisOrbitSum k K T ν)
    (galoisOrbitSum_fixed k K T ν)

/-- Base change of the descended orbit sum is exactly the original orbit sum. -/
theorem baseChange_descendedOrbitSum :
    cocharacterLattice.baseChange (algebraBaseMap k K) T (descendedOrbitSum k K T ν) =
      galoisOrbitSum k K T ν :=
  cocharacterLattice.baseChange_descend k K T _ _

/-- Descent of the orbit sum preserves every stable nonnegative character condition. -/
theorem descendedOrbitSum_nonneg_iff
    (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) χ,
      characterLattice.galoisRepresentation k K T σ χ ∈ Φ ↔ χ ∈ Φ)
    (hcone : ∀ (σ : K ≃ₐ[k] K) χ,
      (characterLattice.galoisRepresentation k K T σ χ ∈ Φ ∧
        0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (characterLattice.galoisRepresentation k K T σ χ) ν) ↔
      (χ ∈ Φ ∧ 0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        χ ν))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hχ : χ ∈ Φ) :
    0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
        (cocharacterLattice.baseChange (algebraBaseMap k K) T (descendedOrbitSum k K T ν)) ↔
      0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν := by
  rw [baseChange_descendedOrbitSum]
  exact galoisOrbitSum_nonneg_iff k K T ν Φ hΦ hcone χ hχ

end CocharacterAveraging

end Langlands.GroupScheme
