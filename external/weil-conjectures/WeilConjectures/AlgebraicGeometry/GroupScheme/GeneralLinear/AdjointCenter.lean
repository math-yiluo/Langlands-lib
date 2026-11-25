/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Center
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Adjoint

/-!
# The centre is the kernel of the adjoint representation

Let `G` be a connected group scheme of finite type over an algebraically closed field `k` of
characteristic zero. Then the centre of `G` is the kernel of the adjoint representation
`Ad : G ⟶ GL(Lie G)` (`AlgebraicGeometry.GrpObj.centerIsoKerAdjoint`), and its Lie algebra and that
of its identity component are the centre of `Lie(G)`.

Both `Z(G)` and `ker Ad` are reduced by Cartier's theorem, so it suffices to compare their rational
points (`AlgebraicGeometry.exists_comp_eq_of_forall_points`). A central rational point `z` has
trivial conjugation `c_z`, so `Ad(z) = d(c_z) = 1`. Conversely, if `Ad(h) = d(c_h) = 1` then
`Lie(C_G(h)) = Lie(G)`, so the closed subgroup scheme `C_G(h)` is all of `G`, `G` being connected
(`AlgebraicGeometry.GrpObj.isIso_left_of_differential_bijective`), and `h` is central. Then
`Lie(Z(G)) = Lie(ker Ad) = ker(ad) = 𝔷(Lie G)`, and `Lie(Z(G)°) = Lie(Z(G))` since `Z(G)° ⟶ Z(G)`
is an open immersion.

## Main statements

- `AlgebraicGeometry.GrpObj.centerIsoKerAdjoint`: `Z(G) ≅ ker Ad`, over `G`.
- `AlgebraicGeometry.GrpObj.mem_range_differential_centerι_iff`: `Lie(Z(G)) = 𝔷(Lie G)`.
- `AlgebraicGeometry.GrpObj.mem_range_differential_identityComponent_center_iff`:
  `Lie(Z(G)°) = 𝔷(Lie G)`.

## Blueprint

- `lemma-stable-subspaces-center`, `lemma-stable-subspaces-center--2`: `Lie(Z(G)°) = 𝔷(Lie G)` for a
connected algebraic group.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

open GeneralLinearGroup

variable {k : Type u} [Field k]

/-- A morphism of group schemes whose composite with a monomorphism of group schemes is a
homomorphism is itself a homomorphism. -/
theorem isMonHom_of_comp {Z K H : Over (Spec (.of k))} [GrpObj Z] [GrpObj K] [GrpObj H]
    (u : Z ⟶ K) (j : K ⟶ H) [IsMonHom j] [Mono j] [IsMonHom (u ≫ j)] : IsMonHom u where
  one_hom := (cancel_mono j).1 (by rw [Category.assoc, IsMonHom.one_hom (u ≫ j), IsMonHom.one_hom])
  mul_hom := (cancel_mono j).1 (by
    rw [Category.assoc, IsMonHom.mul_hom (u ≫ j), Category.assoc, IsMonHom.mul_hom,
      tensorHom_comp_tensorHom_assoc])

variable [IsAlgClosed k] [CharZero k] {G : Over (Spec (.of k))} [GrpObj G]
  [LocallyOfFiniteType G.hom] {I : Type u} [Fintype I] [DecidableEq I]
  (b : Module.Basis I k (Lie G))

/-- The conjugation by a central rational point is the identity. -/
theorem conjBy_centerι_eq [IsReduced G.left] (z : 𝟙_ (Over (Spec (.of k))) ⟶ center G) :
    conjBy G (z ≫ centerι G) = 𝟙 G := by
  refine ext_of_forall_points fun p ↦ ?_
  have h := centerι_comp_commute z p
  rw [toUnit_unit, Category.id_comp] at h
  rw [comp_conjBy, toUnit_unit, Category.id_comp, Category.id_comp, Category.comp_id, ← h,
    mul_inv_cancel_right]

/-- A central rational point is in the kernel of the adjoint representation. -/
theorem centerι_comp_adjoint (z : 𝟙_ (Over (Spec (.of k))) ⟶ center G) :
    (z ≫ centerι G) ≫ adjoint b = 1 := by
  have := isReduced_of_charZero G
  apply homGLEquiv_injective I (𝟙_ _)
  rw [homGLEquiv_comp_adjoint, map_one]
  refine Units.ext ?_
  rw [coe_adjointHom, adjointMatrix_unit, differential_congr (conjBy_centerι_eq z), differential_id]
  change (LinearMap.toMatrix b b LinearMap.id).map _ = 1
  rw [LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]

/-- **A rational point in the kernel of `Ad` is central**: if `Ad(h) = d(c_h) = 1`, the closed
subgroup scheme `C_G(h)` has the Lie algebra of `G`, hence is `G`, `G` being connected. -/
theorem exists_comp_centerι_of_comp_adjoint [QuasiCompact G.hom] [ConnectedSpace G.left]
    (h : 𝟙_ (Over (Spec (.of k))) ⟶ G) (hh : h ≫ adjoint b = 1) :
    ∃ z : 𝟙_ (Over (Spec (.of k))) ⟶ center G, z ≫ centerι G = h := by
  have hd : (differential (conjBy G h) : Lie G →ₗ[k] Lie G) = LinearMap.id := by
    have hm := homGLEquiv_comp_adjoint_unit b h
    rw [hh, map_one, Units.val_one] at hm
    have hσ : Function.Injective (Scheme.ΓSpecIso (.of k)).inv :=
      ((Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv).injective
    apply (LinearMap.toMatrix b b).injective
    apply Matrix.map_injective hσ
    change ((LinearMap.toMatrix b b) _).map _ = ((LinearMap.toMatrix b b) LinearMap.id).map _
    rw [← hm, LinearMap.toMatrix_id, Matrix.map_one _ (map_zero _) (map_one _)]
  have hbij : Function.Bijective (differential (centralizerι h)) :=
    ⟨differential_injective _, fun x ↦ (mem_range_differential_centralizerι_iff h x).2
      (LinearMap.congr_fun hd x)⟩
  have : IsIso (centralizerι h).left := isIso_left_of_differential_bijective _ hbij
  have : IsIso ((Over.forget _).map (centralizerι h)) := this
  have : IsIso (centralizerι h) := isIso_of_reflects_iso _ (Over.forget _)
  refine (exists_comp_centerι_iff h).2 fun g ↦ ?_
  have hg := (exists_comp_centralizerι_iff h g).1 ⟨g ≫ inv (centralizerι h), by simp⟩
  rw [toUnit_unit, Category.id_comp] at hg ⊢
  exact hg.symm

theorem exists_center_comp_kerι :
    ∃ u : center G ⟶ CategoryTheory.GrpObj.ker (adjoint b),
      u ≫ CategoryTheory.GrpObj.kerι (adjoint b) = centerι G := by
  have := isReduced_of_charZero (center G)
  have := isClosedImmersion_kerι (adjoint b)
  refine exists_comp_eq_of_forall_points _ (centerι G) fun z ↦
    ⟨CategoryTheory.GrpObj.kerLift (adjoint b) (z ≫ centerι G) ?_,
      CategoryTheory.GrpObj.kerLift_kerι _ _ _⟩
  rw [centerι_comp_adjoint, Hom.one_def]

theorem exists_kerι_comp_center [QuasiCompact G.hom] [ConnectedSpace G.left] :
    ∃ v : CategoryTheory.GrpObj.ker (adjoint b) ⟶ center G,
      v ≫ centerι G = CategoryTheory.GrpObj.kerι (adjoint b) := by
  have : LocallyOfFiniteType (CategoryTheory.GrpObj.ker (adjoint b)).hom := by
    rw [← Over.w (CategoryTheory.GrpObj.kerι (adjoint b))]
    have := isClosedImmersion_kerι (adjoint b)
    infer_instance
  have := isReduced_of_charZero (CategoryTheory.GrpObj.ker (adjoint b))
  refine exists_comp_eq_of_forall_points (centerι G) _ fun q ↦
    exists_comp_centerι_of_comp_adjoint b _ ?_
  rw [Category.assoc, CategoryTheory.GrpObj.kerι_comp, ← Category.assoc,
    toUnit_unique (q ≫ toUnit _) (toUnit _), ← Hom.one_def]

variable [QuasiCompact G.hom] [ConnectedSpace G.left]

/-- **The centre is the kernel of the adjoint representation.** For a connected group scheme of
finite type over an algebraically closed field of characteristic zero, `Z(G) = ker Ad` as closed
subgroup schemes of `G`. (blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def centerIsoKerAdjoint : center G ≅ CategoryTheory.GrpObj.ker (adjoint b) where
  hom := (exists_center_comp_kerι b).choose
  inv := (exists_kerι_comp_center b).choose
  hom_inv_id := (cancel_mono (centerι G)).1 (by
    rw [Category.assoc, (exists_kerι_comp_center b).choose_spec,
      (exists_center_comp_kerι b).choose_spec, Category.id_comp])
  inv_hom_id := (cancel_mono (CategoryTheory.GrpObj.kerι (adjoint b))).1 (by
    rw [Category.assoc, (exists_center_comp_kerι b).choose_spec,
      (exists_kerι_comp_center b).choose_spec, Category.id_comp])

@[reassoc (attr := simp)]
theorem centerIsoKerAdjoint_hom_kerι :
    (centerIsoKerAdjoint b).hom ≫ CategoryTheory.GrpObj.kerι (adjoint b) = centerι G :=
  (exists_center_comp_kerι b).choose_spec

@[reassoc (attr := simp)]
theorem centerIsoKerAdjoint_inv_centerι :
    (centerIsoKerAdjoint b).inv ≫ centerι G = CategoryTheory.GrpObj.kerι (adjoint b) :=
  (exists_kerι_comp_center b).choose_spec

instance : IsMonHom (centerIsoKerAdjoint b).hom := by
  have : IsMonHom ((centerIsoKerAdjoint b).hom ≫ CategoryTheory.GrpObj.kerι (adjoint b)) := by
    rw [centerIsoKerAdjoint_hom_kerι]
    infer_instance
  exact isMonHom_of_comp _ (CategoryTheory.GrpObj.kerι (adjoint b))

instance : IsMonHom (centerIsoKerAdjoint b).inv := by
  have : IsMonHom ((centerIsoKerAdjoint b).inv ≫ centerι G) := by
    rw [centerIsoKerAdjoint_inv_centerι]
    infer_instance
  exact isMonHom_of_comp _ (centerι G)

/-- **The Lie algebra of the centre** of a connected group scheme of finite type over an
algebraically closed field of characteristic zero is the centre of its Lie algebra:
`Lie(Z(G)) = Lie(ker Ad) = ker(ad) = 𝔷(Lie G)`. (blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_centerι_iff (x : Lie G) :
    x ∈ (differential (centerι G)).range ↔ x ∈ LieAlgebra.center k (Lie G) := by
  classical
  let b := Module.Free.chooseBasis k (Lie G)
  rw [← mem_range_differential_kerι_adjoint_iff b]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨differential (centerIsoKerAdjoint b).hom y, ?_⟩
    change ((differential (CategoryTheory.GrpObj.kerι (adjoint b))).comp
      (differential (centerIsoKerAdjoint b).hom)) y = _
    rw [← differential_comp, differential_congr (centerIsoKerAdjoint_hom_kerι b)]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨differential (centerIsoKerAdjoint b).inv y, ?_⟩
    change ((differential (centerι G)).comp (differential (centerIsoKerAdjoint b).inv)) y = _
    rw [← differential_comp, differential_congr (centerIsoKerAdjoint_inv_centerι b)]
    rfl

/-- **The Lie algebra of the identity component of the centre** of a connected group scheme of
finite type over an algebraically closed field of characteristic zero is the centre of its Lie
algebra: `Lie(Z(G)°) = Lie(Z(G)) = 𝔷(Lie G)`. (blueprint: `lemma-stable-subspaces-center--2`) -/
theorem mem_range_differential_identityComponent_center_iff (x : Lie G) :
    x ∈ (differential (identityComponentι (center G) ≫ centerι G)).range ↔
      x ∈ LieAlgebra.center k (Lie G) := by
  rw [← mem_range_differential_centerι_iff, differential_comp]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨y', rfl⟩ := (differential_identityComponentι_bijective (center G)).2 y
    exact ⟨y', rfl⟩

end AlgebraicGeometry.GrpObj
