import Langlands.GroupScheme.Lie.StableSubspaceDeterminant
import Langlands.GroupScheme.Torus.WeightDecomposition

/-! # Weight spaces of a central split torus are stable

Let `a : T ⟶ M` be a central homomorphism from a split torus and `l : M ⟶ G` a homomorphism to
an affine group scheme locally of finite type over a field. Every weight space of `T` acting on
`Lie(G)` through `a ≫ l` is stable, after every scalar extension, under the adjoint operators
of the points of `M`. The proof reads off weights from the coefficients of the universal adjoint
action over the group algebra `A[ℤ^I]`. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

set_option maxHeartbeats 800000

namespace splitTorus

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom]
  (I : Type u) [Fintype I] [DecidableEq I] (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
  (A : Type u) [CommRing A] [Algebra k A]

/-- The universal point of the split torus over the group algebra `A[ℤ^I]`. -/
def extendedUniversalPoint :
    Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) (AddMonoidAlgebra A (I → ℤ)) :=
  Lie.affineMap _ (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A))
    (universalPoint (R := CommRingCat.of k) I)

/-- A character of the split torus takes its exponent monomial at the universal point. -/
theorem characterValue_extendedUniversalPoint (n : I → ℤ) :
    (Lie.characterValue ((characterLatticeEquiv k I).symm n)
        (extendedUniversalPoint I A) : AddMonoidAlgebra A (I → ℤ)) =
      AddMonoidAlgebra.single n 1 := by
  rw [characterValue_characterLatticeEquiv_symm, extendedUniversalPoint,
    algebraPointsEquiv_naturality]
  have hmap (v : I → (AddMonoidAlgebra k (I → ℤ))ˣ) :
      exponentValue I (fun j => Units.map
        (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)).toMonoidHom (v j))
          (Multiplicative.ofAdd n) =
        Units.map (AddMonoidAlgebra.mapAlgHom (I → ℤ) (Algebra.ofId k A)).toMonoidHom
          (exponentValue I v (Multiplicative.ofAdd n)) := by
    simp only [exponentValue, MonoidHom.coe_mk, OneHom.coe_mk, map_prod, map_zpow]
  rw [hmap, exponentValue_universalPoint]
  simp

/-- The universal adjoint action on an extended Lie vector. -/
def extendedUniversalAdjoint (y : Additive (lieKernel G A)) :
    Additive (lieKernel G (AddMonoidAlgebra A (I → ℤ))) :=
  adjoint G _ (extendedUniversalPoint I A ≫ i.hom.hom)
    (lieKernelMapLinear G (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) y)

/-- A vector over `A` has universal weight `n` when the universal point acts on it by the
monomial `n`. -/
def HasUniversalWeight (n : I → ℤ) (y : Additive (lieKernel G A)) : Prop :=
  extendedUniversalAdjoint G I i A y =
    AddMonoidAlgebra.single n (1 : A) •
      lieKernelMapLinear G (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) y

variable {G I i A}

theorem HasUniversalWeight.add {n : I → ℤ} {y z : Additive (lieKernel G A)}
    (hy : HasUniversalWeight G I i A n y) (hz : HasUniversalWeight G I i A n z) :
    HasUniversalWeight G I i A n (y + z) := by
  unfold HasUniversalWeight extendedUniversalAdjoint at *
  rw [map_add, map_add, hy, hz, smul_add]

theorem HasUniversalWeight.smul {n : I → ℤ} {y : Additive (lieKernel G A)} (c : A)
    (hy : HasUniversalWeight G I i A n y) : HasUniversalWeight G I i A n (c • y) := by
  unfold HasUniversalWeight extendedUniversalAdjoint at *
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, hy, smul_comm]

theorem HasUniversalWeight.zero (n : I → ℤ) : HasUniversalWeight G I i A n 0 := by
  unfold HasUniversalWeight extendedUniversalAdjoint
  rw [map_zero, map_zero, smul_zero]

variable (A) in
/-- An actual weight vector over `k` has the corresponding universal weight over `A`. -/
theorem hasUniversalWeight_of_mem_weightSpace (n : I → ℤ) {w : Additive (lieKernel G k)}
    (hw : w ∈ weightSpace i ((characterLatticeEquiv k I).symm n)) :
    HasUniversalWeight G I i A n (lieKernelMapLinear G (Algebra.ofId k A) w) := by
  unfold HasUniversalWeight extendedUniversalAdjoint
  rw [Lie.lieKernelMapLinear_base, hw (AddMonoidAlgebra A (I → ℤ)) (extendedUniversalPoint I A),
    characterValue_extendedUniversalPoint]

/-- The `m`-th coefficient of the universal adjoint action detects a universal weight. -/
theorem kernelCoefficient_of_hasUniversalWeight {n : I → ℤ} {y : Additive (lieKernel G A)}
    (hy : HasUniversalWeight G I i A n y) (m : I → ℤ) :
    Lie.kernelCoefficient G A (I → ℤ) m (extendedUniversalAdjoint G I i A y) =
      if n = m then y else 0 := by
  rw [hy]
  have h := Lie.kernelCoefficient_monomial G m n (1 : A) y
  rw [one_smul] at h
  refine h.trans ?_
  split_ifs <;> rfl

/-- A point commuting with the universal torus point preserves universal weights. -/
theorem HasUniversalWeight.map_adjoint {n : I → ℤ} {y : Additive (lieKernel G A)}
    (hy : HasUniversalWeight G I i A n y) (g : Lie.AffinePoints G A)
    (hg : Commute (Lie.affineMap G (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) g)
      (extendedUniversalPoint I A ≫ i.hom.hom)) :
    HasUniversalWeight G I i A n (adjoint G A g y) := by
  unfold HasUniversalWeight extendedUniversalAdjoint at *
  have hc := congrArg (fun φ : Module.End _ _ => φ
    (lieKernelMapLinear G (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) y))
    (hg.map (adjoint G (AddMonoidAlgebra A (I → ℤ)))).eq
  simp only [Module.End.mul_apply] at hc
  rw [adjoint_naturality, ← hc, hy, LinearMap.map_smul, ← adjoint_naturality]

/-- The projection to universal weight `m` by the `m`-th universal coefficient. -/
def universalWeightProjection (m : I → ℤ) (y : Additive (lieKernel G A)) :
    Additive (lieKernel G A) :=
  Lie.kernelCoefficient G A (I → ℤ) m (extendedUniversalAdjoint G I i A y)

theorem universalWeightProjection_add (m : I → ℤ) (y z : Additive (lieKernel G A)) :
    universalWeightProjection (G := G) (i := i) m (y + z) =
      universalWeightProjection (i := i) m y + universalWeightProjection (i := i) m z := by
  unfold universalWeightProjection extendedUniversalAdjoint
  rw [map_add, map_add, map_add]

variable [LocallyOfFiniteType G.X.hom]

/-- Every vector projects into the extended weight space of the given weight. -/
theorem universalWeightProjection_mem (m : I → ℤ) (y : Additive (lieKernel G A)) :
    universalWeightProjection (i := i) m y ∈
      LinearMap.range (Lie.subspaceExtension G
        (weightSpace i ((characterLatticeEquiv k I).symm m)) A) := by
  classical
  obtain ⟨s, rfl⟩ := (Lie.kernelScalarExtension G A).surjective y
  induction s using TensorProduct.inductionOn with
  | tmul c v =>
    rw [Lie.kernelScalarExtension_tmul]
    have hv : v ∈ ⨆ ψ : characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I),
        weightSpace i ψ := by
      rw [(isInternal_weightSpace k I G i).submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction
      (weightSpace (T := commGroupScheme (Spec (CommRingCat.of k)) I) i)
      (motive := fun v => universalWeightProjection (i := i) m
        (c • lieKernelMapLinear G (Algebra.ofId k A) v) ∈
          LinearMap.range (Lie.subspaceExtension G
            (weightSpace i ((characterLatticeEquiv k I).symm m)) A)) hv ?_ ?_ ?_
    · intro ψ w hw
      have hw' : w ∈ weightSpace i
          ((characterLatticeEquiv k I).symm (characterLatticeEquiv k I ψ)) := by
        simpa only [AddEquiv.symm_apply_apply] using hw
      have hu := (hasUniversalWeight_of_mem_weightSpace A _ hw').smul c
      unfold universalWeightProjection
      rw [kernelCoefficient_of_hasUniversalWeight hu]
      split_ifs with h
      · rw [h] at hw'
        exact ⟨c ⊗ₜ ⟨w, hw'⟩, Lie.subspaceExtension_tmul G _ c ⟨w, hw'⟩⟩
      · exact Submodule.zero_mem _
    · rw [map_zero, smul_zero]
      unfold universalWeightProjection extendedUniversalAdjoint
      rw [map_zero, map_zero, map_zero]
      exact Submodule.zero_mem _
    · intro v w hv hw
      rw [map_add, smul_add, universalWeightProjection_add]
      exact Submodule.add_mem _ hv hw
  | add s t hs ht =>
    rw [map_add, universalWeightProjection_add]
    exact Submodule.add_mem _ hs ht

/-- A point commuting with the universal torus point preserves the extended weight spaces. -/
theorem adjoint_mem_range_of_commute (m : I → ℤ) (g : Lie.AffinePoints G A)
    (hg : Commute (Lie.affineMap G (IsScalarTower.toAlgHom k A (AddMonoidAlgebra A (I → ℤ))) g)
      (extendedUniversalPoint I A ≫ i.hom.hom))
    (x : A ⊗[k] weightSpace i ((characterLatticeEquiv k I).symm m)) :
    adjoint G A g (Lie.subspaceExtension G _ A x) ∈
      LinearMap.range (Lie.subspaceExtension G
        (weightSpace i ((characterLatticeEquiv k I).symm m)) A) := by
  have hx : HasUniversalWeight G I i A m (Lie.subspaceExtension G _ A x) := by
    induction x using TensorProduct.inductionOn with
    | tmul c w =>
      rw [Lie.subspaceExtension_tmul]
      exact (hasUniversalWeight_of_mem_weightSpace A m w.property).smul c
    | add x y hx hy =>
      rw [map_add]
      exact hx.add hy
  have h := kernelCoefficient_of_hasUniversalWeight (hx.map_adjoint g hg) m
  simp only [↓reduceIte] at h
  rw [← h]
  exact universalWeightProjection_mem m _

end splitTorus

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

/-- **Stability of central weight spaces.** For a central homomorphism `a : T ⟶ M` from a split
torus and `l : M ⟶ G`, each weight space of `T` in `Lie(G)` for `a ≫ l` is stable under the
adjoint operators of the points of `M` after every scalar extension. -/
theorem isAdjointStable_weightSpace_of_isCentral
    {M : GroupScheme (Spec (CommRingCat.of k))} (l : M ⟶ G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (a : T.toGrp ⟶ M)
    (hT : IsSplitTorus T.toGrp) (ha : IsCentral a) (χ : characterLattice T) :
    Lie.IsAdjointStable G (weightSpace (a ≫ l) χ) l := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  let c := characterLattice.comapIso
    (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e
  let n := splitTorus.characterLatticeEquiv k I (c.symm χ)
  have hχ : weightSpace (a ≫ l) χ =
      weightSpace (e.inv ≫ a ≫ l) ((splitTorus.characterLatticeEquiv k I).symm n) := by
    rw [AddEquiv.symm_apply_apply, ← weightSpace_comapIso]
    simp only [c, AddEquiv.apply_symm_apply]
  rw [hχ]
  intro A _ _ m x
  refine splitTorus.adjoint_mem_range_of_commute (i := e.inv ≫ a ≫ l) n (m ≫ l.hom.hom) ?_ x
  -- the universal torus point is central in `M`
  let B := AddMonoidAlgebra A (I → ℤ)
  let tB : Lie.AffinePoints T.toGrp B :=
    splitTorus.extendedUniversalPoint (k := k) I A ≫ e.inv.hom.hom
  let mB : Lie.AffinePoints M B :=
    Lie.affineMap M (IsScalarTower.toAlgHom k A B) m
  have hcent : Commute (tB ≫ a.hom.hom) mB := by
    have h := ha _ tB
    rw [mem_center] at h
    simpa only [Category.id_comp] using h _ (𝟙 _) mB
  have hl : Commute ((tB ≫ a.hom.hom) ≫ l.hom.hom) (mB ≫ l.hom.hom) := by
    have := congrArg (fun z => z ≫ l.hom.hom) hcent.eq
    simp only [MonObj.mul_comp] at this
    exact this
  have h1 : Lie.affineMap G (IsScalarTower.toAlgHom k A B) (m ≫ l.hom.hom) = mB ≫ l.hom.hom := by
    simp only [mB, Lie.affineMap_apply, Category.assoc]
  have h2 : splitTorus.extendedUniversalPoint (k := k) I A ≫ (e.inv ≫ a ≫ l).hom.hom =
      (tB ≫ a.hom.hom) ≫ l.hom.hom := by
    simp only [tB, Grp.comp_hom_hom, Category.assoc]
  rw [h1, h2]
  exact hl.symm

end Langlands.GroupScheme
