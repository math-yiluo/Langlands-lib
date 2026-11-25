/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Separated
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.GrpEqLocus

/-!
# Lie algebras of kernels, equalizers and centralizers

Let `f, g : G ⟶ H` be homomorphisms of group schemes over a field `k`. A tangent vector of `G`,
a point `v : Spec k[ε] ⟶ G` reducing to the identity, is tangent to the kernel `ker f` (the
fibre of `f` over the identity) if and only if `v ≫ f` is the identity point, that is if
`df(v) = 0`: the Lie algebra of the kernel is the kernel of the differential. In the same way
the Lie algebra of the equalizer `eqLocus f g` of `f` and `g` is the subspace on which `df` and
`dg` agree. The equalizer is a closed subgroup scheme, since `H` is separated.

For a rational point `g` of `G`, the centralizer `C_G(g)` is the equalizer of the conjugation
`c_g : x ↦ g x g⁻¹` and the identity. Its Lie algebra is the subspace of `Lie(G)` fixed by the
adjoint action `Ad(g) = d(c_g)` of `g`.

## Main definitions

- `AlgebraicGeometry.GrpObj.centralizer`: the centralizer `C_G(g)` of a rational point, with its
  inclusion `AlgebraicGeometry.GrpObj.centralizerι`.
- `AlgebraicGeometry.GrpObj.lieEquivKer`: `Lie(ker f) ≃ ker(df)`.

## Main statements

- `AlgebraicGeometry.GrpObj.mem_range_differential_kerι_iff`: `Lie(ker f) = ker(df)` inside
  `Lie(G)`.
- `AlgebraicGeometry.GrpObj.mem_range_differential_eqLocusι_iff`: the Lie algebra of the
  equalizer of `f` and `g` is the subspace on which `df = dg`.
- `AlgebraicGeometry.GrpObj.isClosedImmersion_eqLocusι`: the equalizer is a closed subscheme.
- `AlgebraicGeometry.GrpObj.mem_range_differential_centralizerι_iff`: the Lie algebra of
  `C_G(g)` is the subspace fixed by `d(c_g)`.

## Blueprint

- `lemma-stable-subspaces-center`: the kernel of `Ad` and the centralizers of points, with their Lie
algebras.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {k : Type u} [Field k] {G H : Over (Spec (.of k))} [GrpObj G] [GrpObj H]

theorem lieEquivTangent_zero : lieEquivTangent G 0 = 1 := by
  rw [← lieEquivTangent_symm_one (G := G), Equiv.apply_symm_apply]

/-- The differential of the trivial homomorphism is zero. -/
theorem differential_apply_eq_zero (f : G ⟶ H) [IsMonHom f] (hf : f = 1) (x : Lie G) :
    differential f x = 0 := by
  apply (lieEquivTangent H).injective
  rw [lieEquivTangent_differential, lieEquivTangent_zero]
  exact Subtype.ext (by rw [coe_kerPost, hf, MonObj.comp_one]; rfl)

/-! ### The kernel of a homomorphism -/

section Kernel

variable (f : G ⟶ H) [IsMonHom f]

theorem differential_differential_kerι (x : Lie (GrpObj.ker f)) :
    differential f (differential (GrpObj.kerι f) x) = 0 := by
  rw [← LieHom.comp_apply, ← differential_comp]
  exact differential_apply_eq_zero _ (by rw [GrpObj.kerι_comp, Hom.one_def]) x

/-- A tangent vector `x` of `G` with `df(x) = 0` is tangent to the kernel of `f`: its point
`Spec k[ε] ⟶ G` composed with `f` is the identity, so it factors through `ker f`. -/
theorem exists_differential_kerι_eq {x : Lie G} (hx : differential f x = 0) :
    ∃ y : Lie (GrpObj.ker f), differential (GrpObj.kerι f) y = x := by
  set p := lieEquivTangent G x
  have hp : p.1 ≫ f = toUnit _ ≫ η[H] := by
    have h := lieEquivTangent_differential f x
    rw [hx, lieEquivTangent_zero] at h
    rw [← Hom.one_def]
    exact (congrArg Subtype.val h).symm
  set q := GrpObj.kerLift f p.1 hp
  have hq : q ∈ pointsKer (GrpObj.ker f) (aug₁ (k := k)) := by
    rw [mem_pointsKer]
    apply (cancel_mono (GrpObj.kerι f)).1
    rw [MonObj.one_comp]
    change (_ ≫ q) ≫ GrpObj.kerι f = 1
    rw [Category.assoc, GrpObj.kerLift_kerι]
    exact mem_pointsKer.1 p.2
  refine ⟨(lieEquivTangent _).symm ⟨q, hq⟩, (lieEquivTangent G).injective ?_⟩
  rw [lieEquivTangent_differential, Equiv.apply_symm_apply]
  exact Subtype.ext (GrpObj.kerLift_kerι _ _ _)

/-- **The Lie algebra of a kernel.** The tangent vectors of `G` tangent to the kernel of a
homomorphism `f` are those killed by `df`: `Lie(ker f) = ker(df)`.
(blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_kerι_iff (x : Lie G) :
    x ∈ (differential (GrpObj.kerι f)).range ↔ differential f x = 0 := by
  refine ⟨?_, fun hx ↦ (LieHom.mem_range _ _).2 (exists_differential_kerι_eq f hx)⟩
  rintro ⟨y, rfl⟩
  exact differential_differential_kerι f y

theorem range_differential_kerι :
    (differential (GrpObj.kerι f)).range = (differential f).ker.toLieSubalgebra :=
  LieSubalgebra.ext _ _ fun x ↦ (mem_range_differential_kerι_iff f x).trans
    LieHom.mem_ker.symm

/-- The Lie algebra of the kernel of `f` is the kernel of `df`, through the injective
differential of the inclusion `ker f ⟶ G`. (blueprint: `lemma-stable-subspaces-center`) -/
noncomputable def lieEquivKer : Lie (GrpObj.ker f) ≃ₗ⁅k⁆ (differential f).ker :=
  (LieEquiv.ofInjective _ (differential_injective (GrpObj.kerι f))).trans
    (LieEquiv.ofEq _ _ (congrArg (fun L : LieSubalgebra k (Lie G) ↦ (L : Set (Lie G)))
      (range_differential_kerι f)))

@[simp]
theorem coe_lieEquivKer_apply (y : Lie (GrpObj.ker f)) :
    (lieEquivKer f y : Lie G) = differential (GrpObj.kerι f) y :=
  rfl

end Kernel

/-! ### The equalizer of two homomorphisms -/

section EqLocus

variable (f g : G ⟶ H) [IsMonHom f] [IsMonHom g]

theorem differential_differential_eqLocusι (x : Lie (GrpObj.eqLocus f g)) :
    differential f (differential (GrpObj.eqLocusι f g) x) =
      differential g (differential (GrpObj.eqLocusι f g) x) := by
  rw [← LieHom.comp_apply, ← LieHom.comp_apply, ← differential_comp, ← differential_comp,
    differential_congr (GrpObj.eqLocusι_comp_eq f g)]

/-- A tangent vector `x` of `G` with `df(x) = dg(x)` is tangent to the equalizer of `f` and `g`:
its point `v : Spec k[ε] ⟶ G` satisfies `v ≫ f = v ≫ g`. -/
theorem exists_differential_eqLocusι_eq {x : Lie G} (hx : differential f x = differential g x) :
    ∃ y : Lie (GrpObj.eqLocus f g), differential (GrpObj.eqLocusι f g) y = x := by
  set p := lieEquivTangent G x
  have hp : p.1 ≫ f = p.1 ≫ g := by
    have h := congrArg (lieEquivTangent H) hx
    rw [lieEquivTangent_differential, lieEquivTangent_differential] at h
    exact congrArg Subtype.val h
  set q := GrpObj.eqLocusLift f g p.1 hp
  have hq : q ∈ pointsKer (GrpObj.eqLocus f g) (aug₁ (k := k)) := by
    rw [mem_pointsKer]
    apply (cancel_mono (GrpObj.eqLocusι f g)).1
    rw [MonObj.one_comp]
    change (_ ≫ q) ≫ GrpObj.eqLocusι f g = 1
    rw [Category.assoc, GrpObj.eqLocusLift_eqLocusι]
    exact mem_pointsKer.1 p.2
  refine ⟨(lieEquivTangent _).symm ⟨q, hq⟩, (lieEquivTangent G).injective ?_⟩
  rw [lieEquivTangent_differential, Equiv.apply_symm_apply]
  exact Subtype.ext (GrpObj.eqLocusLift_eqLocusι f g p.1 hp)

/-- **The Lie algebra of an equalizer.** The tangent vectors of `G` tangent to the equalizer of
two homomorphisms `f` and `g` are those on which `df` and `dg` agree.
(blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_eqLocusι_iff (x : Lie G) :
    x ∈ (differential (GrpObj.eqLocusι f g)).range ↔ differential f x = differential g x := by
  refine ⟨?_, fun hx ↦ (LieHom.mem_range _ _).2 (exists_differential_eqLocusι_eq f g hx)⟩
  rintro ⟨y, rfl⟩
  exact differential_differential_eqLocusι f g y

end EqLocus

omit [GrpObj G] in
/-- The equalizer of two morphisms into a group scheme over a field is a closed subscheme: it is
the base change of the diagonal of `H`, a closed immersion since `H` is separated. -/
theorem isClosedImmersion_eqLocusι (f g : G ⟶ H) :
    IsClosedImmersion (GrpObj.eqLocusι f g).left := by
  have hd : IsClosedImmersion (lift (𝟙 H) (𝟙 H)).left := by
    have : Limits.pullback.diagonal H.hom = (lift (𝟙 H) (𝟙 H)).left := by
      ext <;> simp
    rw [← this]
    infer_instance
  exact MorphismProperty.of_isPullback
    ((IsPullback.of_hasPullback (lift f g) (lift (𝟙 H) (𝟙 H))).map (Over.forget _)).flip hd

/-! ### Centralizers of rational points -/

section Centralizer

variable (g : 𝟙_ (Over (Spec (.of k))) ⟶ G)

/-- The centralizer `C_G(g)` of a rational point `g` of a group scheme `G` over `k`: the
equalizer of the conjugation `c_g : x ↦ g x g⁻¹` and the identity of `G`, a closed subgroup
scheme. (blueprint: `lemma-stable-subspaces-center`) -/
noncomputable abbrev centralizer : Over (Spec (.of k)) :=
  GrpObj.eqLocus (conjBy G g) (𝟙 G)

/-- The inclusion `C_G(g) ⟶ G` of the centralizer. -/
noncomputable abbrev centralizerι : centralizer g ⟶ G :=
  GrpObj.eqLocusι (conjBy G g) (𝟙 G)

instance : IsClosedImmersion (centralizerι g).left :=
  isClosedImmersion_eqLocusι _ _

/-- The `X`-points of the centralizer of `g` are the `X`-points of `G` commuting with `g`. -/
theorem exists_comp_centralizerι_iff {X : Over (Spec (.of k))} (x : X ⟶ G) :
    (∃ l : X ⟶ centralizer g, l ≫ centralizerι g = x) ↔
      (toUnit X ≫ g) * x = x * (toUnit X ≫ g) := by
  rw [GrpObj.exists_comp_eqLocusι_iff, comp_conjBy, Category.comp_id,
    show toUnit X ≫ g⁻¹ = (toUnit X ≫ g)⁻¹ by rw [Hom.inv_def, Hom.inv_def, Category.assoc],
    mul_inv_eq_iff_eq_mul]

/-- **The Lie algebra of a centralizer.** The Lie algebra of the centralizer `C_G(g)` of a
rational point `g` is the subspace of `Lie(G)` fixed by the adjoint action `d(c_g)` of `g`.
(blueprint: `lemma-stable-subspaces-center`) -/
theorem mem_range_differential_centralizerι_iff (x : Lie G) :
    x ∈ (differential (centralizerι g)).range ↔ differential (conjBy G g) x = x := by
  rw [mem_range_differential_eqLocusι_iff, differential_id, LieHom.id_apply]

end Centralizer

end AlgebraicGeometry.GrpObj
