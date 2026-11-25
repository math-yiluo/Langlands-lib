/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionIdeal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatAffineBasis
import WeilConjectures.AlgebraicGeometry.Morphisms.TraceDiscriminantAffineRestriction
import WeilConjectures.AlgebraicGeometry.AffineCoverIdealStalk

/-!
# Local lifting of a discriminant generator

## References

* Stacks Project, Tag 0BVH, construction before Lemma 49.3.1
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

private theorem basis_basicOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U : Y.affineOpens) :
    letI := (f.app U.1).hom.toAlgebra
    ∀ (n : ℕ) (_b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (r : Γ(Y, U.1)),
      letI := (f.app (Y.basicOpen r)).hom.toAlgebra
      Nonempty (Module.Basis (Fin n) Γ(Y, Y.basicOpen r) Γ(X, f ⁻¹ᵁ Y.basicOpen r)) := by
  let := (f.app U.1).hom.toAlgebra
  intro n b r
  let A := Γ(Y, U.1)
  let B := Γ(X, f ⁻¹ᵁ U.1)
  let Ar := Γ(Y, Y.basicOpen r)
  let Br := Γ(X, f ⁻¹ᵁ Y.basicOpen r)
  let := (f.app (Y.basicOpen r)).hom.toAlgebra
  let : Algebra A Ar :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom.toAlgebra
  have : IsLocalization.Away r Ar := U.2.isLocalization_basicOpen r
  let : Algebra B Br := (X.presheaf.map
    (homOfLE (f.preimage_mono (Y.basicOpen_le r))).op).hom.toAlgebra
  have : IsLocalization.Away (algebraMap A B r) Br :=
    (U.2.preimage f).isLocalization_of_eq_basicOpen (algebraMap A B r) _
      (Scheme.preimage_basicOpen f r)
  let : Algebra A Br := ((algebraMap B Br).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Br := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Ar Br := IsScalarTower.of_algebraMap_eq' (by
    ext a
    exact (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (f.naturality (homOfLE (Y.basicOpen_le r)).op)) a).symm)
  have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers r)) Br := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap A B r) Br)
  exact ⟨b.localizationLocalization Ar (.powers r) Br⟩

private theorem exists_affine_basis_le
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1) :
    ∃ V : Y.affineOpens, V.1 ≤ U.1 ∧ y ∈ V.1 ∧
      (letI := (f.app V.1).hom.toAlgebra
       ∃ n : ℕ, Nonempty (Module.Basis (Fin n) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1))) := by
  obtain ⟨W, hyW, n, ⟨b⟩⟩ := exists_affine_basis_of_finite_flat f y
  obtain ⟨r, s, hrs, hyr⟩ :=
    exists_basicOpen_le_affine_inter W.2 U.2 y ⟨hyW, hy⟩
  refine ⟨Y.affineBasicOpen r, hrs.trans_le (Y.basicOpen_le s), hyr, n, ?_⟩
  exact basis_basicOpen f W n b r

private theorem discr_germ_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (U V : Y.affineOpens)
    (y : Y) (hyU : y ∈ U.1) (hyV : y ∈ V.1) :
    letI := (f.app U.1).hom.toAlgebra
    letI := (f.app V.1).hom.toAlgebra
    ∀ (n m : ℕ)
      (b : Module.Basis (Fin n) Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))
      (c : Module.Basis (Fin m) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)),
      (Ideal.span {Algebra.discr Γ(Y, U.1) b}).map
          (Y.presheaf.germ U.1 y hyU).hom =
        (Ideal.span {Algebra.discr Γ(Y, V.1) c}).map
          (Y.presheaf.germ V.1 y hyV).hom := by
  let := (f.app U.1).hom.toAlgebra
  let := (f.app V.1).hom.toAlgebra
  intro n m b c
  obtain ⟨r, s, hrs, hyr⟩ :=
    exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hyU, hyV⟩
  let W := Y.affineBasicOpen r
  have hWU : W.1 ≤ U.1 := Y.basicOpen_le r
  have hWV : W.1 ≤ V.1 := hrs.trans_le (Y.basicOpen_le s)
  let := (f.app W.1).hom.toAlgebra
  obtain ⟨d⟩ := basis_basicOpen f U n b r
  have hU := trace_discriminant_span_map_affine_restriction f U W hWU n n b d
  have hV := trace_discriminant_span_map_affine_restriction f V W hWV m n c d
  have he := congrArg (Ideal.map (Y.presheaf.germ W.1 y hyr).hom) (hU.trans hV.symm)
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, TopCat.Presheaf.germ_res] using he

/-- A discriminant generator on a free affine subchart belongs to the stalk extension
of the explicit intersection ideal on the larger affine chart. -/
theorem traceDiscriminantSectionIdeal_germ_generator_mem
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U V : Y.affineOpens)
    (h : V.1 ≤ U.1) (y : Y) (hy : y ∈ V.1) :
    letI := (f.app V.1).hom.toAlgebra
    ∀ (n : ℕ) (b : Module.Basis (Fin n) Γ(Y, V.1) Γ(X, f ⁻¹ᵁ V.1)),
      Y.presheaf.germ V.1 y hy (Algebra.discr Γ(Y, V.1) b) ∈
        (traceDiscriminantSectionIdeal f U).map (Y.presheaf.germ U.1 y (h hy)).hom := by
  classical
  let := (f.app V.1).hom.toAlgebra
  intro n b
  let ι := Σ W : {W : Y.affineOpens // W.1 ≤ U.1}, Σ m : ℕ,
    (letI := (f.app W.1.1).hom.toAlgebra
     Module.Basis (Fin m) Γ(Y, W.1.1) Γ(X, f ⁻¹ᵁ W.1.1))
  let O : ι → Y.affineOpens := fun i ↦ i.1.1
  let hO : ∀ i, (O i).1 ≤ U.1 := fun i ↦ i.1.2
  let J : ∀ i, Ideal Γ(Y, (O i).1) := fun i ↦
    letI := (f.app i.1.1.1).hom.toAlgebra
    Ideal.span {Algebra.discr Γ(Y, i.1.1.1) i.2.2}
  have hcover : ∀ z : Y, z ∈ U.1 → ∃ i, z ∈ (O i).1 := by
    intro z hz
    obtain ⟨W, hW, hzW, m, ⟨c⟩⟩ := exists_affine_basis_le f U z hz
    exact ⟨⟨⟨W, hW⟩, m, c⟩, hzW⟩
  have hcompat : ∀ i j (z : Y) (hi : z ∈ (O i).1) (hj : z ∈ (O j).1),
      (J i).map (Y.presheaf.germ (O i).1 z hi).hom =
        (J j).map (Y.presheaf.germ (O j).1 z hj).hom := by
    intro i j z hi hj
    exact discr_germ_eq f i.1.1 j.1.1 z hi hj i.2.1 j.2.1 i.2.2 j.2.2
  have he := affineCoverIdeal_map_germ U O hO J hcover hcompat ⟨⟨V, h⟩, n, b⟩ y hy
  have hI : (⨅ i, (J i).comap (Y.presheaf.map (homOfLE (hO i)).op).hom) =
      traceDiscriminantSectionIdeal f U := by
    ext a
    simp only [traceDiscriminantSectionIdeal, Ideal.mem_iInf]
    constructor
    · intro ha W hW m c
      exact ha ⟨⟨W, hW⟩, m, c⟩
    · intro ha i
      exact ha i.1.1 i.1.2 i.2.1 i.2.2
  rw [hI] at he
  rw [he]
  exact Ideal.mem_map_of_mem (Y.presheaf.germ V.1 y hy).hom
    (Ideal.mem_span_singleton_self (Algebra.discr Γ(Y, V.1) b))

end AlgebraicGeometry.Scheme
