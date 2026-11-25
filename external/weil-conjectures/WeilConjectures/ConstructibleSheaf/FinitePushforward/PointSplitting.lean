/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Unramified.Field
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Constructible sheaves become constant over finite separable extensions of residue fields

Step 3 of the proof of Stacks 09Z6: for a constructible sheaf `C` and a point `x`, there is a
point `v` of an étale scheme over the residue field of the stratum through `x`, mapping to `x`,
with `κ(v) / κ(x)` finite separable, over which `C` becomes constant
(`AlgebraicGeometry.Scheme.exists_isConstant_upperStar_of_isConstructibleSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The residue field maps of a preimmersion are bijective. -/
lemma Scheme.Hom.bijective_residueFieldMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f]
    (x : X) : Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, fun a ↦ ?_⟩
  obtain ⟨b, rfl⟩ := X.residue_surjective x a
  obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
  exact ⟨Y.residue _ c, by
    rw [← ConcreteCategory.comp_apply, Scheme.residue_residueFieldMap, ConcreteCategory.comp_apply]⟩

namespace Scheme

variable {Λ : Type (u + 1)} [Ring Λ]

/-- **A constructible sheaf is constant on an étale neighbourhood of a point with finite
separable residue field extension.** For a constructible sheaf `C` of `Λ`-modules on `X` and a
point `x`, there is a morphism `w : W ⟶ X` and a point `v ↦ x` such that `κ(v) / κ(x)` is finite
separable and `w^* C` is constant: `W` is a member of an étale cover of `Spec κ(z)` trivialising
the restriction of `C` to the stratum through `x`, where `z ↦ x`. This is Step 3 of the proof of
Stacks 09Z6. -/
theorem exists_isConstant_upperStar_of_isConstructibleSheaf {X : Scheme.{u}}
    (C : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf C] (x : X) :
    ∃ (W : Scheme.{u}) (w : W ⟶ X) (v : W), w.base v = x ∧ (w.residueFieldMap v).hom.Finite ∧
      (letI := (w.residueFieldMap v).hom.toAlgebra;
        Algebra.IsSeparable (X.residueField (w.base v)) (W.residueField v)) ∧
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) w).obj C).IsConstant W.smallEtaleTopology := by
  obtain ⟨S, hS⟩ := ‹IsConstructibleSheaf C›.exists_stratification
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
  rw [← S.range_immersion i] at hi
  obtain ⟨z, rfl⟩ := hi
  have := hS i
  have := S.isImmersion i
  let D := S.domain i
  let ι := S.immersion i
  let p := D.fromSpecResidueField z
  have hG := IsFiniteLocallyConstantSheaf.upperStar p ((Etale.upperStar _ ι).obj C)
  obtain ⟨⟨𝒰, h𝒰⟩⟩ := hG.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
  obtain ⟨pt⟩ : Nonempty (Spec (.of (D.residueField z))) := inferInstance
  have : JointlySurjective etalePrecoverage.{u} :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨j, v, hv⟩ := 𝒰.exists_eq pt
  have hpι : IsPreimmersion (p ≫ ι) := inferInstance
  have e1 := (p ≫ ι).bijective_residueFieldMap (𝒰.f j v)
  have : Etale (𝒰.f j) := 𝒰.map_prop j
  have h2 := (𝒰.f j).finite_residueFieldMap v
  have hcomp := Scheme.residueFieldMap_comp (𝒰.f j) (p ≫ ι) v
  refine ⟨𝒰.X j, 𝒰.f j ≫ p ≫ ι, v, ?_, ?_, ?_, ?_⟩
  · change ι.base (p.base (𝒰.f j v)) = ι.base z
    rw [fromSpecResidueField_apply]
  · rw [hcomp]
    exact h2.comp (RingHom.Finite.of_surjective _ e1.2)
  · rw [hcomp]
    let : Algebra ((𝒰.X j).residueField v) ((𝒰.X j).residueField v) := Algebra.id _
    let : Algebra ((Spec (.of (D.residueField z))).residueField ((𝒰.f j).base v))
        ((𝒰.X j).residueField v) := ((𝒰.f j).residueFieldMap v).hom.toAlgebra
    have : Algebra.IsSeparable ((Spec (.of (D.residueField z))).residueField ((𝒰.f j).base v))
        ((𝒰.X j).residueField v) := inferInstance
    let : Algebra (X.residueField ((𝒰.f j ≫ p ≫ ι).base v)) ((𝒰.X j).residueField v) :=
      ((p ≫ ι).residueFieldMap ((𝒰.f j).base v) ≫ (𝒰.f j).residueFieldMap v).hom.toAlgebra
    refine Algebra.IsSeparable.of_equiv_equiv (RingEquiv.ofBijective _ e1).symm
      (RingEquiv.refl _) ?_
    ext a
    change ((𝒰.f j).residueFieldMap v) (((p ≫ ι).residueFieldMap ((𝒰.f j).base v))
      ((RingEquiv.ofBijective _ e1).symm a)) = ((𝒰.f j).residueFieldMap v) a
    congr 1
    exact (RingEquiv.ofBijective _ e1).apply_symm_apply a
  · have hc := h𝒰 j
    rw [isConstant_over_iff_upperStar] at hc
    have : ((Etale.upperStar _ (𝒰.f j)).obj ((Etale.upperStar _ ι ⋙ Etale.upperStar _ p).obj
      C)).IsConstant (𝒰.X j).smallEtaleTopology := hc
    exact Sheaf.isConstant_congr _
      ((Etale.upperStar _ (𝒰.f j)).mapIso ((Etale.upperStarComp _ p ι).app C).symm ≪≫
        ((Etale.upperStarComp _ (𝒰.f j) (p ≫ ι)).app C).symm)

end Scheme

end AlgebraicGeometry
