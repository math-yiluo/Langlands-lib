/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Sites.CoversTop.Over

/-! # Kernel finiteness from a chosen local generating family

Source: Stacks Project, Modules, Lemma 01BY (2), proof, second paragraph;
Lemma 01B7 (1) and Definition 01B5.
(blueprint: lem-weil-pbc-finite-type-kernel-local-generators).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

-- The site and coefficient universes are independent, and the site need not be small.
private theorem finiteType_of_epi.{v, w}
    {C : Type v} [Category.{w} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F G : SheafOfModules.{u} R} (p : F ⟶ G) [Epi p] [F.IsFiniteType] :
    G.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  let d : G.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := by
        have : Epi (p.over (q.X i)) :=
          inferInstanceAs (Epi ((SheafOfModules.pushforward
            (F := Over.forget (q.X i)) (𝟙 (R.over (q.X i)))).map p))
        exact (q.generators i).ofEpi (p.over (q.X i)) }
  exact ⟨d, ⟨fun i ↦ by
    have := hq.isFiniteType i
    dsimp only [d]
    infer_instance⟩⟩

private theorem over_preserves_kernel
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) {F H : SheafOfModules.{u} R}
    (φ : F ⟶ H) (V : C) :
    PreservesLimit (parallelPair φ 0) (SheafOfModules.overFunctor R V) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel φ)
  apply isLimitOfReflects (SheafOfModules.forget (R.over V))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  let E := SheafOfModules.evaluation R (Opposite.op W.unop.left)
  let T := ModuleCat.restrictScalars
    (RingCat.Hom.hom (𝟙 (R.obj.obj (Opposite.op W.unop.left))))
  exact isLimitOfPreserves (E ⋙ T) (kernelIsKernel φ)

-- A commutative square with epi on the source and mono on the target induces an epi
-- on kernels; the old composite/identity square is just a special case.
private theorem epi_kernel_of_epi
    {C : Type*} [Category C] [Abelian C] {A B D E : C}
    (p : A ⟶ B) [Epi p] (g : A ⟶ D) (f : B ⟶ E)
    (j : D ⟶ E) [Mono j] (comm : g ≫ j = p ≫ f) :
    Epi (kernel.map g f p j comm) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro Z z
  obtain ⟨Z', q, hq, a, ha⟩ :=
    surjective_up_to_refinements_of_epi p (z ≫ kernel.ι f)
  have hz : a ≫ g = 0 := by
    apply (cancel_mono j).mp
    calc
      (a ≫ g) ≫ j = a ≫ (p ≫ f) := by rw [Category.assoc, comm]
      _ = (a ≫ p) ≫ f := (Category.assoc _ _ _).symm
      _ = (q ≫ z ≫ kernel.ι f) ≫ f := by rw [ha]
      _ = 0 ≫ j := by simp only [Category.assoc, kernel.condition, comp_zero, zero_comp]
  refine ⟨Z', q, hq, kernel.lift g a hz, ?_⟩
  apply (cancel_mono (kernel.ι f)).mp
  simp [ha]

private theorem finiteType_of_cover.{v}
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V W, HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ V W, ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type v}
    (V : I → C) (hV : J.CoversTop V)
    (h : ∀ i, (M.over (V i)).IsFiniteType) : M.IsFiniteType := by
  classical
  choose D hD using fun i ↦
    @SheafOfModules.IsFiniteType.exists_localGeneratorsData _ _ _ _ _ _ (M.over (V i)) (h i)
  let q : SheafOfModules.LocalGeneratorsData.{max u v} M :=
    { I := (i : I) × (D i).I
      X ij := ((D ij.1).X ij.2).left
      coversTop := hV.over (fun i ↦ (D i).coversTop)
      generators ij := by
        letI e := SheafOfModules.pushforwardPushforwardEquivalence.{u}
          (Over.iteratedSliceEquiv ((D ij.1).X ij.2))
          (S := (R.over (V ij.1)).over ((D ij.1).X ij.2))
          (R := R.over ((D ij.1).X ij.2).left) (𝟙 _) (𝟙 _)
          (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
        exact (((D ij.1).generators ij.2).map e.inverse (Iso.refl _)).ofEpi
          (e.fullyFaithfulFunctor.preimageIso
            (by exact e.counitIso.app ((M.over (V ij.1)).over ((D ij.1).X ij.2)))).hom }
  have hq : q.IsFiniteType := ⟨fun ij ↦ by
    have := (hD ij.1).isFiniteType ij.2
    dsimp only [q]
    infer_instance⟩
  -- Shrinking the covering index allows covers in any universe.
  exact ⟨q.shrink, ⟨fun i ↦ hq.isFiniteType i.2.choose⟩⟩

private theorem finiteType_kernel_of_local_generators
    {C : Type u} [SmallCategory C] [HasBinaryProducts C] [HasPullbacks C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V W, HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ V W, ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    {F H : SheafOfModules.{u} R} (φ : F ⟶ H)
    (q : SheafOfModules.LocalGeneratorsData.{u} F)
    (h : ∀ i, (kernel ((q.generators i).π ≫ φ.over (q.X i))).IsFiniteType) :
    (kernel φ).IsFiniteType := by
  have hlocal (i : q.I) : ((kernel φ).over (q.X i)).IsFiniteType := by
    have : HasBinaryProducts (Over (q.X i)) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    have : (SheafOfModules.overFunctor.{u} R (q.X i)).Additive :=
      Functor.Additive.mk (by intros; rfl)
    let p := (q.generators i).π
    let f := φ.over (q.X i)
    have : (kernel (p ≫ f)).IsFiniteType := h i
    let k := kernel.map (p ≫ f) f p (𝟙 _) (by simp)
    have : Epi k := epi_kernel_of_epi p (p ≫ f) f (𝟙 _) (by simp)
    have : (kernel f).IsFiniteType := finiteType_of_epi k
    have := over_preserves_kernel R φ (q.X i)
    exact finiteType_of_epi
      (PreservesKernel.iso (SheafOfModules.overFunctor R (q.X i)) φ).inv
  exact finiteType_of_cover (kernel φ) q.X q.coversTop hlocal

/-- If the kernels of the composites with a chosen local free epimorphism are
finite type, then the original kernel is finite type. No coherence assumption
or finiteness assumption on the chosen generating families is needed.
Source: Stacks Project, Modules, Lemma 01BY (2), proof, second paragraph;
Lemma 01B7 (1) and Definition 01B5.
(blueprint: lem-weil-pbc-finite-type-kernel-local-generators).

Proof: On the cover q.X, put p = (q.generators i).π and L = kernel (p ≫ φ.over _).
The morphism kernel.ι (p ≫ φ.over _) ≫ p factors through kernel (φ.over _).
This factor is epi: a section killed by φ locally lifts through the epi p;
each lift is killed by the composite and therefore lies in L. As L is finite
type, its quotient kernel (φ.over _) is finite type by pushing forward local
finite generators. Restriction computes kernels sectionwise, so this is the
restriction of kernel φ. Refine the cover q.X by the finite generating covers
of these local kernels. Cover transitivity makes this a cover of U, and
forgetting the intermediate slice identifies its finite families with local
finite generators of kernel φ. Thus kernel φ is finite type. Empty covers of
an empty open and zero generating families satisfy the same argument. -/
theorem finiteType_kernel_local_generators (X : RingedSpace.{u})
    (U : Opens X) {F H : SheafOfModules.{u} ((moduleRings X).over U)}
    (φ : F ⟶ H) (q : SheafOfModules.LocalGeneratorsData.{u, u, u, u} F)
    (h : ∀ i : q.I, (kernel ((q.generators i).π ≫ φ.over (q.X i))).IsFiniteType) :
    (kernel φ).IsFiniteType := by
  classical
  let R := (moduleRings X).over U
  let J := (Opens.grothendieckTopology X).over U
  have : ∀ V : Over U, HasSheafify (J.over V) AddCommGrpCat.{u} :=
    fun V ↦ inferInstance
  have : ∀ V : Over U, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun V ↦ inferInstance
  have : ∀ (V : Over U) (W : Over V),
      HasSheafify ((J.over V).over W) AddCommGrpCat.{u} := fun V W ↦ inferInstance
  have : ∀ (V : Over U) (W : Over V),
      ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    fun V W ↦ inferInstance
  have : ∀ V : Over U, HasWeakSheafify (J.over V) AddCommGrpCat.{u} :=
    fun V ↦ inferInstance
  have : ∀ (V : Over U) (W : Over V),
      HasWeakSheafify ((J.over V).over W) AddCommGrpCat.{u} := fun V W ↦ inferInstance
  exact finiteType_kernel_of_local_generators R φ q h

end AlgebraicGeometry.RingedSpace
