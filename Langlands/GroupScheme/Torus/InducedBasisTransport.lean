import Langlands.GroupScheme.Torus.CharacterRestriction
import Langlands.GroupScheme.Torus.InducedPermutationBasis
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic

/-! # Transport of an induced-torus permutation basis to a prescribed splitting field -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
namespace Langlands.GroupScheme

namespace characterLattice

variable {k E M : Type u} [Field k] [Field E] [Field M]
  [Algebra k E] [Algebra k M]

/-- A field embedding gives a map between the corresponding tests over `Spec k`. -/
def fieldTestMap (e : E →ₐ[k] M) :
    Over.mk (algebraBaseMap k M) ⟶ Over.mk (algebraBaseMap k E) :=
  Over.homMk (Spec.map (CommRingCat.ofHom e.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k E)) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact e.comp_algebraMap)

/-- Character restriction respects compatible field automorphisms. -/
theorem restriction_galois
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (e : E →ₐ[k] M)
    (σ : E ≃ₐ[k] E) (τ : M ≃ₐ[k] M)
    (h : ∀ x, τ (e x) = e (σ x))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T)) :
    restriction T (fieldTestMap e) (galoisRepresentation k E T σ χ) =
      galoisRepresentation k M T τ (restriction T (fieldTestMap e) χ) := by
  rw [galoisRepresentation_apply, galoisRepresentation_apply,
    ← restriction_endomorphism, ← restriction_endomorphism,
    ← restriction_comp, ← restriction_comp]
  apply congrArg (fun a : Over.mk (algebraBaseMap k M) ⟶
    Over.mk (algebraBaseMap k E) => restriction T a χ)
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) =
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom e.toRingHom)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun x => (h x).symm

/-- Restriction along an embedding into an extension is bijective for a split torus. -/
theorem field_restriction_bijective
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (e : E →ₐ[k] M)
    (hT : IsSplitTorus (GaloisPointComparison.baseChanged k E T.toGrp)) :
    Function.Bijective (restriction T (fieldTestMap e)) :=
  restriction_bijective T (fieldTestMap e) hT

end characterLattice

/-- Every integral basis of the character lattice of a split torus has finite index. -/
theorem IsSplitTorus.finite_character_basis
    {K I : Type u} [Field K]
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    (hT : IsSplitTorus T.toGrp) (b : Module.Basis I ℤ (characterLattice T)) :
    Finite I := by
  obtain ⟨J, hJ, ⟨e⟩⟩ := hT
  let : Finite J := hJ
  let f := (characterLattice.congr (CommGroupScheme.isoOfGroupIso e)).trans
    (splitTorus.characterLatticeEquiv K J)
  let : Module.Finite ℤ (characterLattice T) :=
    Module.Finite.equiv f.toIntLinearEquiv.symm
  exact Module.Finite.finite_basis b

/-- An induced torus has a finite permuted character basis over every prescribed
finite Galois splitting field, in the original universe. -/
theorem IsInducedTorus.exists_permuted_basis
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsInducedTorus T)
    (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (hL : IsSplitTorus (GaloisPointComparison.baseChanged k L T.toGrp)) :
    ∃ (I : Type u) (_ : Finite I)
      (b : Module.Basis I ℤ
        (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))),
      ∀ (σ : L ≃ₐ[k] L) (i : I), ∃ j : I,
        characterLattice.galoisRepresentation k L T σ (b i) = b j := by
  classical
  obtain ⟨E, hEF, hEA, hEfin, hEgal, hE, I, b, hb⟩ := hT
  let : Field E := hEF
  let : Algebra k E := hEA
  let : FiniteDimensional k E := hEfin
  let : IsGalois k E := hEgal
  let Ω := AlgebraicClosure k
  let eE : E →ₐ[k] Ω := IsAlgClosed.lift
  let eL : L →ₐ[k] Ω := IsAlgClosed.lift
  let : Algebra E Ω := eE.toRingHom.toAlgebra
  let : IsScalarTower k E Ω :=
    IsScalarTower.of_algebraMap_eq' eE.comp_algebraMap.symm
  let : Algebra L Ω := eL.toRingHom.toAlgebra
  let : IsScalarTower k L Ω :=
    IsScalarTower.of_algebraMap_eq' eL.comp_algebraMap.symm
  let rE := characterLattice.restriction T (characterLattice.fieldTestMap eE)
  let rL := characterLattice.restriction T (characterLattice.fieldTestMap eL)
  let aE := AddEquiv.ofBijective rE
    (characterLattice.field_restriction_bijective T eE hE)
  let aL := AddEquiv.ofBijective rL
    (characterLattice.field_restriction_bijective T eL hL)
  let bL := b.map (aE.trans aL.symm).toIntLinearEquiv
  have hbL (i : I) : rL (bL i) = rE (b i) := by
    change aL (aL.symm (aE (b i))) = aE (b i)
    exact aL.apply_symm_apply _
  refine ⟨I, hE.finite_character_basis b, bL, ?_⟩
  intro σ i
  let τ : Ω ≃ₐ[k] Ω := σ.liftNormal Ω
  let ρ : E ≃ₐ[k] E := τ.restrictNormal E
  have hτL (x : L) : τ (eL x) = eL (σ x) := by
    change τ (algebraMap L Ω x) = algebraMap L Ω (σ x)
    exact σ.liftNormal_commutes Ω x
  have hτE (x : E) : τ (eE x) = eE (ρ x) := by
    change τ (algebraMap E Ω x) = algebraMap E Ω (τ.restrictNormal E x)
    exact (τ.restrictNormal_commutes E x).symm
  obtain ⟨j, hj⟩ := hb ρ i
  refine ⟨j, (characterLattice.field_restriction_bijective T eL hL).injective ?_⟩
  calc
    rL (characterLattice.galoisRepresentation k L T σ (bL i)) =
        characterLattice.galoisRepresentation k Ω T τ (rL (bL i)) :=
      characterLattice.restriction_galois T eL σ τ hτL _
    _ = characterLattice.galoisRepresentation k Ω T τ (rE (b i)) :=
      congrArg _ (hbL i)
    _ = rE (characterLattice.galoisRepresentation k E T ρ (b i)) :=
      (characterLattice.restriction_galois T eE ρ τ hτE _).symm
    _ = rE (b j) := congrArg rE hj
    _ = rL (bL j) := (hbL j).symm

end Langlands.GroupScheme
