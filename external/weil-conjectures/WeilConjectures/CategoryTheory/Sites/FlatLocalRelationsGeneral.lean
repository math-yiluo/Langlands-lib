/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The relation criterion for flatness over an arbitrary commutative ring

`WeilConjectures.CategoryTheory.Sites.FlatLocalRelations` proves that a sheaf of modules over a
Noetherian commutative ring is flat if and only if it has locally trivial relations
(`CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations`). Noetherianity is only used there to
resolve the kernel of a matrix `e : R^s ⟶ R^q` by a finite free module. Here we instead tensor
the exact sequence `ker e ⟶ R^s ⟶ R^q` with the sheaf: a section of `F ⊗ ker e` is locally a
finite sum `∑ₘ zₘ ⊗ kₘ` of pure tensors, and the vectors `kₘ ∈ ker e` form the columns of the
matrix `b` trivializing the relations. This removes the Noetherian hypothesis.

We also show that restriction along a cocontinuous functor preserves locally trivial relations
(`CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp`).

## Main results

- `CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat'`: relations between sections of a
  flat sheaf of modules over any commutative ring are locally trivial.
- `CategoryTheory.Sheaf.flat_iff_hasLocallyTrivialRelations'`: the relation criterion for
  flatness over any commutative ring.
- `CategoryTheory.Presheaf.HasLocallyTrivialRelations.comp`: restriction along a cocontinuous
  functor preserves locally trivial relations.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite MonoidalCategory

open scoped TensorProduct

namespace CategoryTheory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]

omit [EssentiallySmall.{u + 1} C] in
/-- **Restriction along a cocontinuous functor preserves locally trivial relations.** If
`G : C ⥤ D` is cocontinuous and `P` has locally trivial relations on `D`, then so has the
restriction `G.op ⋙ P`: a covering sieve of `G V` pulls back to a covering sieve of `V`. -/
lemma Presheaf.HasLocallyTrivialRelations.comp {D : Type (u + 1)} [Category.{u} D]
    {K : GrothendieckTopology D} {P : Dᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (hP : Presheaf.HasLocallyTrivialRelations K P) (G : C ⥤ D) [G.IsCocontinuous J K] :
    Presheaf.HasLocallyTrivialRelations J (G.op ⋙ P) := by
  intro V s q y e he
  obtain ⟨T, hT, hfac⟩ := hP (V := G.obj V) y e he
  exact ⟨T.functorPullback G, G.cover_lift J K hT, fun W f hf ↦ hfac (G.map f) hf⟩

variable [J.HasSheafCompose (forget (ModuleCat.{u + 1} R))]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} R)]

/-- **Linear relations between sections of a flat sheaf are locally trivial**, over an arbitrary
commutative ring `R`. Let `F` be a flat sheaf of `R`-modules and let `y : Fin s → F(V)` satisfy
the relations `∑ⱼ eₗⱼ yⱼ = 0`. Then locally on `V` there are a matrix `b` with `e * b = 0` and
sections `z` with `yⱼ = ∑ₘ bⱼₘ zₘ`.

Compared to `CategoryTheory.Sheaf.hasLocallyTrivialRelations_of_flat`, the exact sequence
`ker e ⟶ R^s ⟶ R^q` is tensored with `F`, and the columns of `b` are the vectors `kₘ ∈ ker e`
of a local preimage `∑ₘ zₘ ⊗ kₘ` of `∑ⱼ yⱼ ⊗ eⱼ`. -/
theorem Sheaf.hasLocallyTrivialRelations_of_flat' {F : Sheaf J (ModuleCat.{u + 1} R)}
    (hF : ObjectProperty.flat F) : Presheaf.HasLocallyTrivialRelations J F.obj := by
  intro V s q y e he
  classical
  -- the exact sequence `ker e ⟶ R^s ⟶ R^q`
  let φ := e.mulVecLin
  let S₀ := ShortComplex.moduleCatMkOfKerLERange (ModuleCat.ofHom (LinearMap.ker φ).subtype)
    (ModuleCat.ofHom φ) (by simp)
  have hS₀ : S₀.Exact :=
    ShortComplex.Exact.moduleCat_of_range_eq_ker _ _ (Submodule.range_subtype _)
  -- tensoring with `F` keeps it exact, and computes the sheafification of `F(-) ⊗ -`
  have : PreservesFiniteLimits (tensorLeft F) := hF.tensorLeft.1
  have : PreservesFiniteColimits (tensorLeft F) := hF.tensorLeft.2
  let Φ : ModuleCat.{u + 1} R ⥤ Sheaf J (ModuleCat.{u + 1} R) :=
    Functor.const Cᵒᵖ ⋙ tensorLeft F.obj ⋙ presheafToSheaf J _
  let eΦ : constantSheaf J (ModuleCat.{u + 1} R) ⋙ tensorLeft F ≅ Φ :=
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
        (asIso ((sheafificationAdjunction J _).counit.app F)).symm) ≪≫
      Functor.isoWhiskerLeft (Functor.const Cᵒᵖ)
        (Sheaf.presheafToSheafCompTensorLeftIso F.obj)
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits (constantSheaf J (ModuleCat.{u + 1} R)) :=
    comp_preservesFiniteColimits _ _
  have hS : (S₀.map Φ).Exact :=
    (ShortComplex.exact_iff_of_iso (S₀.mapNatIso eΦ)).1
      ((hS₀.map (constantSheaf J _)).map (tensorLeft F))
  let Sp := S₀.map (Functor.const Cᵒᵖ ⋙ tensorLeft F.obj)
  -- the section `∑ⱼ yⱼ ⊗ eⱼ` of `F(V) ⊗ R^s` is killed by `e`
  let x : Sp.X₂.obj (op V) := ∑ j, y j ⊗ₜ[R] (Pi.single j 1 : Fin s → R)
  have hx : Sp.g.app (op V) x = 0 := by
    refine (TensorProduct.piScalarRight R R _ (Fin q)).injective ?_
    ext l
    change TensorProduct.piScalarRight R R _ (Fin q) (φ.lTensor _ x) l = 0
    rw [TensorProduct.piScalarRight_lTensor_mulVecLin, TensorProduct.piScalarRight_sum_tmul_single]
    simpa using he l
  refine ⟨_, Presheaf.imageSieve_mem_of_exact_map_presheafToSheaf hS x hx, ?_⟩
  rintro W f ⟨z₀, hz₀⟩
  -- write the local preimage as `∑ₘ zₘ ⊗ kₘ`
  obtain ⟨t, z, k, hzk⟩ :=
    TensorProduct.exists_sum_tmul_eq (R := R) (M := F.obj.obj (op W)) (N := LinearMap.ker φ) z₀
  let b : Matrix (Fin s) (Fin t) R := Matrix.of fun j m ↦ ((k m : LinearMap.ker φ) : Fin s → R) j
  have heb : e * b = 0 := by
    ext l m
    have := congrFun (LinearMap.mem_ker.1 (k m).2) l
    simp only [φ, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    simpa [b, Matrix.mul_apply] using this
  refine ⟨t, b, z, heb, fun j ↦ ?_⟩
  have hz := congrArg (fun w ↦ TensorProduct.piScalarRight R R _ (Fin s) w j) hz₀
  change TensorProduct.piScalarRight R R _ (Fin s)
      ((LinearMap.ker φ).subtype.lTensor _ z₀) j =
    TensorProduct.piScalarRight R R _ (Fin s)
      (TensorProduct.map (F.obj.map f.op).hom LinearMap.id x) j at hz
  have hrhs : TensorProduct.piScalarRight R R _ (Fin s)
      (TensorProduct.map (F.obj.map f.op).hom LinearMap.id x) j = F.obj.map f.op (y j) := by
    simp [x, map_sum, Pi.single_apply]
  rw [← hrhs, ← hz, hzk]
  simp [map_sum, b]

/-- **Relation criterion for flatness of sheaves of modules**, over an arbitrary commutative
ring: a sheaf of modules is flat if and only if linear relations between its sections are
locally trivial. -/
theorem Sheaf.flat_iff_hasLocallyTrivialRelations' (F : Sheaf J (ModuleCat.{u + 1} R)) :
    ObjectProperty.flat F ↔ Presheaf.HasLocallyTrivialRelations J F.obj :=
  ⟨Sheaf.hasLocallyTrivialRelations_of_flat', fun h ↦ ObjectProperty.prop_of_iso _
    (asIso ((sheafificationAdjunction J _).counit.app F))
    (Presheaf.flat_presheafToSheaf_obj_of_hasLocallyTrivialRelations h)⟩

end CategoryTheory
