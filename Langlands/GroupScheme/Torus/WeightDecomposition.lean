import Langlands.GroupScheme.Torus.UniversalAdjointCoefficients
import Langlands.GroupScheme.Torus.Weights
import Langlands.LinearAlgebra.FinsuppDecomposition

/-! # Weight decomposition of the actual adjoint representation -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.splitTorus

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I]
variable {A : Type u} [CommRing A] [Algebra k A]

omit [DecidableEq I] in
/-- The character-lattice coordinates evaluate as the exponent monomial on every test algebra. -/
theorem characterValue_characterLatticeEquiv_symm (m : I → ℤ)
    (t : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
    Lie.characterValue ((characterLatticeEquiv k I).symm m) t =
      exponentValue I (algebraPointsEquiv I A t) (Multiplicative.ofAdd m) := by
  let q := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv
  change q (Gm.pointsEquiv _ _ (t ≫
    (CommGroupScheme.groupHom ((characterLatticeEquiv k I).symm m)).hom.hom)) = _
  rw [pointsEquiv_characterLatticeEquiv_symm, map_prod]
  simp only [map_zpow]
  rfl

/-- The exponent monomial evaluated at the universal point is its group-algebra monomial. -/
theorem exponentValue_universalPoint (m : I → ℤ) :
    exponentValue I (algebraPointsEquiv I _ (universalPoint (R := CommRingCat.of k) I))
      (Multiplicative.ofAdd m) = exponentUnit I m := by
  rw [algebraPointsEquiv_universalPoint]
  let f := (AddMonoidAlgebra.of k (I → ℤ)).toHomUnits
  let h : (I → ℤ) →+ Additive (AddMonoidAlgebra k (I → ℤ))ˣ :=
    { toFun := fun n => Additive.ofMul (f (Multiplicative.ofAdd n))
      map_zero' := congrArg Additive.ofMul (map_one f)
      map_add' := fun n p => congrArg Additive.ofMul
        (map_mul f (Multiplicative.ofAdd n) (Multiplicative.ofAdd p)) }
  have hm : (∑ j : I, m j • Pi.single j (1 : ℤ)) = m := by
    ext j
    simp [Pi.single_apply]
  have hh := congrArg Additive.toMul (map_sum h (fun j => m j • Pi.single j (1 : ℤ)) Finset.univ)
  rw [hm] at hh
  simp only [map_zsmul] at hh
  simpa [h, f, exponentValue, exponentUnit] using hh.symm

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)

/-- Universal coefficients reindexed by the actual character lattice. -/
def characterAdjointCoefficients :
    Additive (lieKernel G k) →ₗ[k]
      (characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) →₀
        Additive (lieKernel G k)) :=
  (Finsupp.lmapDomain _ k (characterLatticeEquiv k I).symm).comp
    (universalAdjointCoefficients I G i)

@[simp] theorem characterAdjointCoefficients_apply
    (X : Additive (lieKernel G k))
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterAdjointCoefficients k I G i X χ =
      universalAdjointCoefficients I G i X (characterLatticeEquiv k I χ) := by
  change Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalAdjointCoefficients I G i X) χ = _
  simpa only [AddEquiv.symm_apply_apply] using
    Finsupp.mapDomain_apply_of_injective (characterLatticeEquiv k I).symm.injective
      (universalAdjointCoefficients I G i X) (characterLatticeEquiv k I χ)

/-- Each character-indexed coefficient lies in its all-test-algebra weight space. -/
theorem characterAdjointCoefficients_mem (X : Additive (lieKernel G k))
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I)) :
    characterAdjointCoefficients k I G i X χ ∈ weightSpace i χ := by
  rw [characterAdjointCoefficients_apply]
  intro A _ _ t
  have h := universalAdjointCoefficients_weight I G i (algebraPointsEquiv I A t) X
    (characterLatticeEquiv k I χ)
  rw [MulEquiv.symm_apply_apply, ← characterValue_characterLatticeEquiv_symm k I,
    AddEquiv.symm_apply_apply] at h
  exact h

/-- A vector in one character weight space has its universal coefficients concentrated there. -/
theorem universalAdjointCoefficients_of_mem_weightSpace (m : I → ℤ)
    (X : Additive (lieKernel G k))
    (hX : X ∈ weightSpace i ((characterLatticeEquiv k I).symm m)) :
    universalAdjointCoefficients I G i X = Finsupp.single m X := by
  apply universalAdjointCoefficients_of_monomial
  have h := (mem_weightSpace.mp hX) _ (universalPoint (R := CommRingCat.of k) I)
  rw [characterValue_characterLatticeEquiv_symm, exponentValue_universalPoint] at h
  exact h

/-- On its own weight space the coefficient family is the corresponding singleton. -/
theorem characterAdjointCoefficients_of_mem_weightSpace
    (χ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I))
    (X : Additive (lieKernel G k)) (hX : X ∈ weightSpace i χ) :
    characterAdjointCoefficients k I G i X = Finsupp.single χ X := by
  change Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalAdjointCoefficients I G i X) = _
  have hX' : X ∈ weightSpace i ((characterLatticeEquiv k I).symm
      (characterLatticeEquiv k I χ)) := by simpa only [AddEquiv.symm_apply_apply] using hX
  rw [universalAdjointCoefficients_of_mem_weightSpace k I G i _ X hX',
    Finsupp.mapDomain_single, AddEquiv.symm_apply_apply]

/-- Character-indexed coefficients sum to the original vector. -/
theorem characterAdjointCoefficients_sum (X : Additive (lieKernel G k)) :
    (characterAdjointCoefficients k I G i X).sum (fun _ y => y) = X := by
  change (Finsupp.mapDomain (characterLatticeEquiv k I).symm
    (universalAdjointCoefficients I G i X)).sum (fun _ y => y) = X
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  exact universalAdjointCoefficients_sum I G i X

open Classical in
/-- The actual Lie algebra is the internal direct sum of its split-torus character weight spaces. -/
theorem isInternal_weightSpace : DirectSum.IsInternal
    (weightSpace (T := commGroupScheme (Spec (CommRingCat.of k)) I) i) := by
  classical
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ (characterAdjointCoefficients k I G i)
  · exact characterAdjointCoefficients_mem k I G i
  · intro χ X
    exact characterAdjointCoefficients_of_mem_weightSpace k I G i χ X X.property
  · exact characterAdjointCoefficients_sum k I G i

end Langlands.GroupScheme.splitTorus


namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {R : CommRingCat.{u}} {T T' : CommGroupScheme (Spec R)}

namespace characterLattice

/-- Pull characters back along an isomorphism of the underlying actual group schemes. -/
def comapIso (e : T.toGrp ≅ T'.toGrp) : characterLattice T' ≃+ characterLattice T where
  toFun χ := Additive.ofMul e.hom ≫ χ
  invFun χ := Additive.ofMul e.inv ≫ χ
  left_inv χ := by
    change Additive.ofMul (e.inv ≫ e.hom ≫ χ.toMul) = χ
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    rfl
  right_inv χ := by
    change Additive.ofMul (e.hom ≫ e.inv ≫ χ.toMul) = χ
    rw [← Category.assoc, e.hom_inv_id, Category.id_comp]
    rfl
  map_add' χ ψ := by simp only [Preadditive.comp_add]

end characterLattice

variable {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]

/-- Character weight spaces agree under reparametrization by a torus isomorphism. -/
theorem weightSpace_comapIso (e : T.toGrp ≅ T'.toGrp) (i : T.toGrp ⟶ G)
    (χ : characterLattice T') :
    weightSpace i (characterLattice.comapIso e χ) = weightSpace (e.inv ≫ i) χ := by
  ext X
  constructor
  · intro h A _ _ t
    have h' := (mem_weightSpace.mp h) A (t ≫ e.inv.hom.hom)
    change adjoint G A ((t ≫ e.inv.hom.hom) ≫ i.hom.hom) _ =
      (Lie.characterValue ((Additive.ofMul e.hom : T ⟶ T') ≫ χ)
        (t ≫ e.inv.hom.hom) : A) • _ at h'
    rw [Lie.characterValue_comp] at h'
    change adjoint G A ((t ≫ e.inv.hom.hom) ≫ i.hom.hom) _ =
      (Lie.characterValue χ ((t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom) : A) • _ at h'
    have ht : (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = t := by
      rw [Category.assoc]
      change t ≫ (e.inv ≫ e.hom).hom.hom = t
      rw [e.inv_hom_id]
      exact Category.comp_id t
    rw [ht] at h'
    exact h'
  · intro h A _ _ t
    have h' := (mem_weightSpace.mp h) A (t ≫ e.hom.hom.hom)
    change adjoint G A (((t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom) ≫ i.hom.hom) _ =
      (Lie.characterValue χ (t ≫ e.hom.hom.hom) : A) • _ at h'
    have ht : (t ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = t := by
      rw [Category.assoc]
      change t ≫ (e.hom ≫ e.inv).hom.hom = t
      rw [e.hom_inv_id]
      exact Category.comp_id t
    rw [ht] at h'
    change adjoint G A (t ≫ i.hom.hom) _ =
      (Lie.characterValue ((Additive.ofMul e.hom : T ⟶ T') ≫ χ) t : A) • _
    rw [Lie.characterValue_comp]
    exact h'

open Classical in
/-- The actual Lie algebra decomposes into character weight spaces for any split torus. -/
theorem isInternal_weightSpace_of_isSplitTorus
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) : DirectSum.IsInternal (weightSpace i) := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let q := splitTorus.characterAdjointCoefficients k I G (e.inv ≫ i)
  let p := (Finsupp.lmapDomain (Additive (lieKernel G k)) k c).comp q
  have hp (X : Additive (lieKernel G k))
      (χ : characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)) :
      p X (c χ) = q X χ := by
    exact Finsupp.mapDomain_apply_of_injective c.injective (q X) χ
  apply Langlands.LinearAlgebra.isInternal_of_finsupp _ p
  · intro X χ
    obtain ⟨ψ, rfl⟩ := c.surjective χ
    rw [hp]
    rw [weightSpace_comapIso]
    exact splitTorus.characterAdjointCoefficients_mem k I G (e.inv ≫ i) X ψ
  · intro χ X
    have hX : (X : Additive (lieKernel G k)) ∈
        weightSpace (e.inv ≫ i) (c.symm χ) := by
      rw [← weightSpace_comapIso
        (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e i]
      change (X : Additive (lieKernel G k)) ∈ weightSpace i (c (c.symm χ))
      simpa only [AddEquiv.apply_symm_apply] using X.property
    change Finsupp.mapDomain c (q (X : Additive (lieKernel G k))) =
      Finsupp.single χ (X : Additive (lieKernel G k))
    rw [splitTorus.characterAdjointCoefficients_of_mem_weightSpace k I G (e.inv ≫ i)
      (c.symm χ) X hX, Finsupp.mapDomain_single, AddEquiv.apply_symm_apply]
  · intro X
    change (Finsupp.mapDomain c (q X)).sum (fun _ y => y) = X
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
    exact splitTorus.characterAdjointCoefficients_sum k I G (e.inv ≫ i) X

end Langlands.GroupScheme
