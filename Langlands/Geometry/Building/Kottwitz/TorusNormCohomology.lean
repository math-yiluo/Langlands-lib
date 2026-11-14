import Langlands.GroupScheme.Torus.SplitCoverCocycleVanishing
import Langlands.GroupScheme.GaloisPointTower
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.Cohomology.Tate.SpliceRepresentatives

/-! # Norm surjectivity and norm kernels for split tori over dimension-one fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped MonoidalCategory CategoryTheory.MonObj

namespace Langlands.Geometry.Building.Kottwitz

open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPoint
open Langlands.GroupScheme.TorusPointsTensorGalois

set_option backward.isDefEq.respectTransparency false


section TateLowDegree

variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

/-- Vanishing degree-zero Tate cohomology makes every invariant vector a norm. -/
theorem exists_norm_of_tateZero (A : Rep.{u} R G) (hA : IsZero (tateCohomology A 0))
    (a : A) (ha : a ∈ A.ρ.invariants) : ∃ b : A, A.ρ.norm b = a := by
  have h0 : Langlands.Tate.zeroClass A ⟨a, ha⟩ = 0 := by
    have : Subsingleton (tateCohomology A 0) := ModuleCat.subsingleton_of_isZero hA
    exact Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (Langlands.Tate.zeroClass_eq_zero_iff _).mp h0
  exact ⟨b, congrArg Subtype.val hb⟩

/-- Vanishing degree-minus-one Tate cohomology makes every norm-zero vector a boundary. -/
theorem exists_d₁₀_of_tateMinusOne (A : Rep.{u} R G) (hA : IsZero (tateCohomology A (-1)))
    (a : A) (ha : A.ρ.norm a = 0) : ∃ c : G →₀ A, groupHomology.d₁₀ A c = a := by
  have hex : (tateComplex A).ExactAt (-1) :=
    ((tateComplex A).exactAt_iff_isZero_homology (-1)).mpr hA
  rw [HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)] at hex
  obtain ⟨x₁, hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex
    ((groupHomology.chainsIso₀ A).inv a) (Langlands.Tate.normZero_tate_cycle A a ha)
  refine ⟨(groupHomology.chainsIso₁ A).hom x₁, ?_⟩
  have h := ConcreteCategory.congr_hom (groupHomology.comp_d₁₀_eq A) x₁
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
  rw [h]
  change (groupHomology.chainsIso₀ A).hom ((tateComplex A).d (-2) (-1) x₁) = a
  rw [show (tateComplex A).d (-2) (-1) x₁ = (groupHomology.chainsIso₀ A).inv a from hx₁]
  exact Iso.inv_hom_id_apply _ _

/-- An additive invariant functional kills the norm kernel when `Ĥ⁻¹` vanishes. -/
theorem invariant_eq_zero_of_tateMinusOne (A : Rep.{u} R G)
    (hA : IsZero (tateCohomology A (-1)))
    {X : Type*} [AddCommGroup X] (φ : A →+ X) (hφ : ∀ (g : G) (a : A), φ (A.ρ g a) = φ a)
    (a : A) (ha : A.ρ.norm a = 0) : φ a = 0 := by
  obtain ⟨c, rfl⟩ := exists_d₁₀_of_tateMinusOne A hA a ha
  clear ha
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, add_zero]
  | single g m => rw [groupHomology.d₁₀_single, map_sub, hφ, sub_self]

end TateLowDegree

section Cohomology

variable (k K L : Type u) [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- Relative automorphisms, viewed as automorphisms over the coefficient field `k`. -/
def relativeAutHom : (L ≃ₐ[K] L) →* (L ≃ₐ[k] L) where
  toFun σ := σ.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The original coefficient points over `L` with the relative Galois action. -/
abbrev relativePointRepresentation : Rep.{u} (ULift.{u} ℤ) (L ≃ₐ[K] L) :=
  Rep.res (relativeAutHom k K L)
    (GaloisCocycle.pointRepresentation (G := T.toGrp) (k := k) (L := L))

theorem relativePointRepresentation_apply (σ : L ≃ₐ[K] L)
    (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    (relativePointRepresentation k K L T).ρ σ (Additive.ofMul x) =
      Additive.ofMul (relativeConjugate k K L T.toGrp σ x) := rfl

/-- Restricting the unit representation over `k` gives the unit representation over `K`. -/
def resUnitsIso :
    Rep.res (relativeAutHom k K L) (Langlands.ClassFieldTheory.Local.unitsRepresentation k L) ≅
      Langlands.ClassFieldTheory.Local.unitsRepresentation K L :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl _ _) (fun _ => rfl))

section ResTensor

attribute [-instance] ULift.module

/-- Restriction commutes with the tensor product of representations. -/
def resTensorIso (A B : Rep.{u} (ULift.{u} ℤ) (L ≃ₐ[k] L)) :
    Rep.res (relativeAutHom k K L) (A ⊗ B) ≅
      Rep.res (relativeAutHom k K L) A ⊗ Rep.res (relativeAutHom k K L) B :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl _ _) (fun _ => rfl))

end ResTensor

variable [FiniteDimensional K L] [IsGalois K L]

/-- The relative point representation of a split torus is a free twist of the units. -/
def relativePointTensorIso (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    Langlands.ClassFieldTheory.Local.unitsRepresentation K L ⊗
        Rep.res (relativeAutHom k K L) (latticeRepresentation k L T) ≅
      relativePointRepresentation k K L T :=
  (MonoidalCategory.whiskerRightIso (resUnitsIso k K L).symm _) ≪≫
    (resTensorIso k K L _ _).symm ≪≫
      (Rep.resFunctor (relativeAutHom k K L)).mapIso (tensorPointIso k L T hT)

/-- All Tate cohomology of the relative point representation of a split torus vanishes. -/
theorem relativePoint_tate_isZero
    (hK : Langlands.FieldTheory.HasDimensionLEOne K)
    (hT : IsSplitTorus (baseChanged k L T).toGrp) (n : ℤ) :
    IsZero (tateCohomology (relativePointRepresentation k K L T) n) := by
  let : Module.Free (ULift.{u} ℤ) (latticeRepresentation k L T) :=
    latticeRepresentation_free k L T hT
  let : Module.Free (ULift.{u} ℤ)
      (Rep.res (relativeAutHom k K L) (latticeRepresentation k L T)) :=
    inferInstanceAs (Module.Free (ULift.{u} ℤ) (latticeRepresentation k L T))
  let : Module.Flat (ULift.{u} ℤ)
      (Rep.res (relativeAutHom k K L) (latticeRepresentation k L T)) := Module.Flat.of_free
  have hz := Langlands.Tate.FreeTensor.tensor_isZero
    (Langlands.ClassFieldTheory.Local.unitsRepresentation K L)
    (Rep.res (relativeAutHom k K L) (latticeRepresentation k L T))
    hK.finite_units_cohomologicallyTrivial n
  have e := (tateCohomologyFunctor n).mapIso (relativePointTensorIso k K L T hT)
  exact hz.of_iso e.symm

variable [IsAffine T.X.left]

/-- The representation norm of a point is the extension of its relative norm. -/
theorem relativePoint_norm_apply (x : affinePoints T.toGrp (CommAlgCat.of k L)) :
    (relativePointRepresentation k K L T).ρ.norm (Additive.ofMul x) =
      Additive.ofMul (relativeExtend k K L T.toGrp (relativeNorm k K L T x)) := by
  rw [relativeExtend_norm, ofMul_prod]
  simp only [Representation.norm, LinearMap.sum_apply]
  rfl

/-- KP 11.1.1 input: the relative norm of a split torus over a dimension-one field is onto. -/
theorem relativeNorm_surjective
    (hK : Langlands.FieldTheory.HasDimensionLEOne K)
    (hT : IsSplitTorus (baseChanged k L T).toGrp) :
    Function.Surjective (relativeNorm k K L T) := by
  intro y
  have hinv : (Additive.ofMul (relativeExtend k K L T.toGrp y) :
      relativePointRepresentation k K L T) ∈
        (relativePointRepresentation k K L T).ρ.invariants := fun σ =>
    congrArg Additive.ofMul (relativeConjugate_extend k K L T.toGrp σ y)
  obtain ⟨b, hb⟩ := exists_norm_of_tateZero _
    (relativePoint_tate_isZero k K L T hK hT 0) _ hinv
  refine ⟨Additive.toMul b, relativeExtend_injective k K L T.toGrp ?_⟩
  have h := relativePoint_norm_apply k K L T (Additive.toMul b)
  exact Additive.ofMul.injective (h.symm.trans hb)

/-- KP 11.1.1 input: a relatively invariant additive functional kills the relative norm kernel. -/
theorem invariant_eq_zero_of_relativeNorm_eq_one
    (hK : Langlands.FieldTheory.HasDimensionLEOne K)
    (hT : IsSplitTorus (baseChanged k L T).toGrp)
    {X : Type*} [AddCommGroup X]
    (φ : Additive (affinePoints T.toGrp (CommAlgCat.of k L)) →+ X)
    (hφ : ∀ (σ : L ≃ₐ[K] L) x,
      φ (Additive.ofMul (relativeConjugate k K L T.toGrp σ x)) = φ (Additive.ofMul x))
    (x : affinePoints T.toGrp (CommAlgCat.of k L)) (hx : relativeNorm k K L T x = 1) :
    φ (Additive.ofMul x) = 0 := by
  refine invariant_eq_zero_of_tateMinusOne (relativePointRepresentation k K L T)
    (relativePoint_tate_isZero k K L T hK hT (-1)) φ (fun σ a => hφ σ (Additive.toMul a))
    (Additive.ofMul x) ?_
  rw [relativePoint_norm_apply, hx, map_one]
  rfl

end Cohomology

section Transitivity

variable (k K L M : Type u) [Field k] [Field K] [Field L] [Field M]
  [Algebra k K] [Algebra k L] [Algebra k M] [Algebra K L] [Algebra K M] [Algebra L M]
  [IsScalarTower k K L] [IsScalarTower k K M] [IsScalarTower k L M] [IsScalarTower K L M]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]

/-- Extension of coefficient points is transitive in a tower. -/
theorem relativeExtend_relativeExtend (x : G.affinePoints (CommAlgCat.of k K)) :
    relativeExtend k L M G (relativeExtend k K L G x) = relativeExtend k K M G x := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeExtend]
  exact (IsScalarTower.algebraMap_apply K L M _).symm

/-- Extension intertwines a relative automorphism with its restriction. -/
theorem relativeExtend_relativeConjugate [Normal K L] (σ : M ≃ₐ[K] M)
    (x : G.affinePoints (CommAlgCat.of k L)) :
    relativeExtend k L M G (relativeConjugate k K L G (σ.restrictNormal L) x) =
      relativeConjugate k K M G σ (relativeExtend k L M G x) := by
  apply (coordinates k G M).injective
  ext a
  simp only [coordinates_relativeExtend, coordinates_relativeConjugate]
  exact σ.restrictNormal_commutes L _

variable [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
  [IsGalois K L] [IsGalois K M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- Relative norms compose in a finite Galois tower over an arbitrary coefficient field. -/
theorem relativeNorm_relativeNorm (x : affinePoints T.toGrp (CommAlgCat.of k M)) :
    relativeNorm k K L T (relativeNorm k L M T x) = relativeNorm k K M T x := by
  apply relativeExtend_injective k K M T.toGrp
  calc
    relativeExtend k K M T.toGrp (relativeNorm k K L T (relativeNorm k L M T x)) =
        relativeExtend k L M T.toGrp
          (relativeExtend k K L T.toGrp (relativeNorm k K L T (relativeNorm k L M T x))) :=
      (relativeExtend_relativeExtend k K L M T.toGrp _).symm
    _ = ∏ τ : L ≃ₐ[K] L, relativeConjugate k K M T.toGrp (τ.liftNormal M)
          (relativeExtend k L M T.toGrp (relativeNorm k L M T x)) := by
      rw [relativeExtend_norm, map_prod]
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      simpa only [AlgEquiv.restrict_liftNormal] using
        relativeExtend_relativeConjugate k K L M T.toGrp (τ.liftNormal M) _
    _ = ∏ τ : L ≃ₐ[K] L, ∏ σ : M ≃ₐ[L] M,
          relativeConjugate k K M T.toGrp (τ.liftNormal M * σ.restrictScalars K) x := by
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      rw [relativeExtend_norm, map_prod]
      refine Finset.prod_congr rfl (fun σ _ => ?_)
      rw [relativeConjugate_mul]
      rfl
    _ = ∏ θ : M ≃ₐ[K] M, relativeConjugate k K M T.toGrp θ x := by
      simpa only [Fintype.prod_prod_type, towerAutEquiv_apply] using
        (towerAutEquiv K L M).prod_comp (fun θ => relativeConjugate k K M T.toGrp θ x)
    _ = relativeExtend k K M T.toGrp (relativeNorm k K M T x) :=
      (relativeExtend_norm k K M T x).symm

end Transitivity

end Langlands.Geometry.Building.Kottwitz
