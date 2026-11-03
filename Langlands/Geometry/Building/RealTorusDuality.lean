import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.Geometry.Building.SplitRealTorusSpace
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Perfect real pairings and character kernels of actual split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {A T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- The actual lattice pairing is natural for character restriction and
cocharacter postcomposition. -/
theorem latticePairing_map (f : A ⟶ T) (χ : characterLattice T)
    (ν : cocharacterLattice A) :
    latticePairing T χ (ν ≫ f) =
      latticePairing A (characterRestrict (CommGroupScheme.groupHom f) χ) ν := by
  change gmEndEquiv k ((ν ≫ f) ≫ χ) = gmEndEquiv k (ν ≫ (f ≫ χ))
  rw [Category.assoc]

/-- Naturality of the published real pairing for actual morphisms. -/
theorem pair_cocharacterMapReal (f : A ⟶ T) (x : Vstar T) (v : V A) :
    pair T x (cocharacterMapReal f v) =
      pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) v := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    induction v using TensorProduct.inductionOn with
    | tmul s ν =>
      change pair T (r ⊗ₜ[ℤ] χ) (s ⊗ₜ[ℤ] (ν ≫ f)) =
        pair A (r ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) χ) (s ⊗ₜ[ℤ] ν)
      simp only [pair_tmul_tmul, latticePairing_map]
    | add v w hv hw => simp only [map_add, hv, hw]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The published real pairing on a coordinate split torus is perfect. -/
theorem split_isPerfPair (I : Type u) [Finite I] :
    (pair (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)).IsPerfPair := by
  classical
  let := Fintype.ofFinite I
  have : (dotProductEquiv ℝ I :
      (I → ℝ) →ₗ[ℝ] Module.Dual ℝ (I → ℝ)).IsPerfPair :=
    LinearMap.IsPerfPair.of_bijective _ (dotProductEquiv ℝ I).bijective
  refine LinearMap.IsPerfPair.congr
    (p := (dotProductEquiv ℝ I : (I → ℝ) →ₗ[ℝ] Module.Dual ℝ (I → ℝ)))
    (splitCharacterCoordinates k I)
    (splitCocharacterCoordinates k I) (pair _) ?_
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro v
  rw [LinearMap.compl₁₂_apply, pair_eq_sum]
  change (∑ j, splitCharacterCoordinates k I ((splitCharacterCoordinates k I).symm x) j *
    splitCocharacterCoordinates k I ((splitCocharacterCoordinates k I).symm v) j) = _
  simp only [LinearEquiv.apply_symm_apply]
  rfl

/-- The full published real character and cocharacter spaces of every actual
split torus form a perfect pairing. -/
theorem isPerfPair_of_isSplitTorus (hT : IsSplitTorus T.toGrp) :
    (pair T).IsPerfPair := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have := split_isPerfPair (k := k) I
  refine LinearMap.IsPerfPair.congr
    (p := pair (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I))
    (LinearEquiv.baseChange ℤ ℝ _ _ (characterLattice.congr eC).toIntLinearEquiv)
    (LinearEquiv.baseChange ℤ ℝ _ _ (cocharacterLattice.congr eC).toIntLinearEquiv)
    (pair T) ?_
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro v
  exact pair_congr eC.symm x v

/-- The actual real character space identified with the dual of the actual
real cocharacter space by the published pairing. -/
def characterDualEquiv (hT : IsSplitTorus T.toGrp) :
    Vstar T ≃ₗ[ℝ] Module.Dual ℝ (V T) := by
  letI := isPerfPair_of_isSplitTorus hT
  exact (pair T).toPerfPair

@[simp] theorem characterDualEquiv_apply (hT : IsSplitTorus T.toGrp)
    (x : Vstar T) (v : V T) :
    characterDualEquiv hT x v = pair T x v := rfl

/-- The cocharacters annihilated by a real character subspace. -/
def cocharacterAnnihilator (W : Submodule ℝ (Vstar T)) : Submodule ℝ (V T) :=
  W.dualAnnihilator.comap (pair T).flip

/-- The characters annihilating a real cocharacter subspace. -/
def characterAnnihilator (N : Submodule ℝ (V T)) : Submodule ℝ (Vstar T) :=
  N.dualAnnihilator.comap (pair T)

@[simp] theorem mem_cocharacterAnnihilator (W : Submodule ℝ (Vstar T)) (v : V T) :
    v ∈ cocharacterAnnihilator W ↔ ∀ x ∈ W, pair T x v = 0 := by
  simp only [cocharacterAnnihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator,
    LinearMap.flip_apply]

@[simp] theorem mem_characterAnnihilator (N : Submodule ℝ (V T)) (x : Vstar T) :
    x ∈ characterAnnihilator N ↔ ∀ v ∈ N, pair T x v = 0 := by
  simp only [characterAnnihilator, Submodule.mem_comap, Submodule.mem_dualAnnihilator]

/-- Double annihilation recovers every real character subspace of a split torus. -/
theorem characterAnnihilator_cocharacterAnnihilator
    (hT : IsSplitTorus T.toGrp) (W : Submodule ℝ (Vstar T)) :
    characterAnnihilator (cocharacterAnnihilator W) = W := by
  have hp := isPerfPair_of_isSplitTorus hT
  ext x
  constructor
  · intro hx
    rw [← Subspace.dualAnnihilator_dualCoannihilator_eq (W := W)]
    rw [Submodule.mem_dualCoannihilator]
    intro φ hφ
    obtain ⟨v, hv⟩ := hp.bijective_right.surjective φ
    have hvW : v ∈ cocharacterAnnihilator W := by
      rw [mem_cocharacterAnnihilator]
      intro y hy
      change ((pair T).flip v) y = 0
      rw [hv]
      exact (Submodule.mem_dualAnnihilator φ).mp hφ y hy
    have h := (mem_characterAnnihilator _ _).mp hx v hvW
    change ((pair T).flip v) x = 0 at h
    rwa [hv] at h
  · intro hx
    rw [mem_characterAnnihilator]
    intro v hv
    exact (mem_cocharacterAnnihilator _ _).mp hv x hx

/-- The simultaneous integral-root annihilator is the annihilator of their
span in the published full real character space. -/
theorem rootAnnihilator_eq_cocharacterAnnihilator (R : Set (characterLattice T)) :
    rootAnnihilator T R =
      cocharacterAnnihilator
        (Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' R)) := by
  ext v
  rw [mem_rootAnnihilator, mem_cocharacterAnnihilator]
  constructor
  · intro hv
    have hspan :
        Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' R) ≤
          ((pair T).flip v).ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨α, hα, rfl⟩
      change pair T (1 ⊗ₜ[ℤ] α) v = 0
      rw [← eval_eq_pair]
      exact hv α hα
    exact fun x hx => hspan hx
  · intro hv α hα
    rw [eval_eq_pair]
    exact hv _ (Submodule.subset_span ⟨α, hα, rfl⟩)

/-- The real restriction kernel is the character annihilator of the actual
real cocharacter image. -/
theorem ker_restrictReal_eq_characterAnnihilator_range
    (hA : IsSplitTorus A.toGrp) (f : A ⟶ T) :
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker =
      characterAnnihilator (cocharacterMapReal f).range := by
  have hp := isPerfPair_of_isSplitTorus hA
  ext x
  rw [LinearMap.mem_ker, mem_characterAnnihilator]
  constructor
  · rintro hx v ⟨vA, rfl⟩
    rw [pair_cocharacterMapReal, hx, map_zero, LinearMap.zero_apply]
  · intro hx
    apply hp.bijective_left.injective
    apply LinearMap.ext
    intro v
    change pair A (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x) v = 0
    rw [← pair_cocharacterMapReal]
    exact hx _ ⟨v, rfl⟩

/-- Once the actual cocharacter image has been identified with the root
annihilator, the real character restriction kernel is the actual root span. -/
theorem ker_restrictReal_eq_relativeRootSpanReal_of_range
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus T.toGrp)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (f : A ⟶ T)
    (himage : (cocharacterMapReal f).range = relativeCentralDirections i) :
    (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).ker =
      relativeRootSpanReal i := by
  rw [ker_restrictReal_eq_characterAnnihilator_range hA f, himage,
    relativeCentralDirections, rootAnnihilator_eq_cocharacterAnnihilator,
    characterAnnihilator_cocharacterAnnihilator hT]
  rfl

end Langlands.GroupScheme.RealTorusSpace
