/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! # Finite type submodules and kernels of coherent modules

Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-finite-type-sub-kernel).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

private theorem finiteType_of_epi
    {C : Type u} [SmallCategory C] [HasBinaryProducts C] {J : GrothendieckTopology C}
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

private theorem mono_over (X : RingedSpace.{u})
    {K G : SheafOfModules.{u} (moduleRings X)} (i : K ⟶ G) [Mono i]
    (U : TopologicalSpace.Opens X) : Mono (i.over U) := by
  constructor
  intro Z f g h
  ext W x
  let E := SheafOfModules.evaluation (moduleRings X) (Opposite.op W.unop.left)
  have hi : Function.Injective (E.map i) :=
    (ModuleCat.mono_iff_injective (E.map i)).mp inferInstance
  apply hi
  exact congrArg (fun m ↦ m.val.app W x) h

private theorem over_preserves_kernel (X : RingedSpace.{u})
    {F G : SheafOfModules.{u} (moduleRings X)} (φ : F ⟶ G) (U : TopologicalSpace.Opens X) :
    PreservesLimit (parallelPair φ 0) (SheafOfModules.overFunctor (moduleRings X) U) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel φ)
  apply isLimitOfReflects (SheafOfModules.forget ((moduleRings X).over U))
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  let E := SheafOfModules.evaluation (moduleRings X) (Opposite.op W.unop.left)
  let T := ModuleCat.restrictScalars
    (RingCat.Hom.hom (𝟙 ((moduleRings X).obj.obj (Opposite.op W.unop.left))))
  exact isLimitOfPreserves (E ⋙ T) (kernelIsKernel φ)

private theorem epi_kernel_of_epi
    {C : Type*} [Category C] [Abelian C] {A B D : C}
    (p : A ⟶ B) [Epi p] (f : B ⟶ D) :
    Epi (kernel.map (p ≫ f) f p (𝟙 D) (by simp)) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro Z z
  obtain ⟨Z', q, hq, a, ha⟩ :=
    surjective_up_to_refinements_of_epi p (z ≫ kernel.ι f)
  have hz : a ≫ (p ≫ f) = 0 := by
    calc
      a ≫ (p ≫ f) = (a ≫ p) ≫ f := (Category.assoc _ _ _).symm
      _ = (q ≫ z ≫ kernel.ι f) ≫ f := by rw [ha]
      _ = 0 := by simp only [Category.assoc, kernel.condition, comp_zero]
  refine ⟨Z', q, hq, kernel.lift (p ≫ f) a hz, ?_⟩
  apply (cancel_mono (kernel.ι f)).mp
  simp [ha]

private theorem exists_epi_fin
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M : SheafOfModules.{u} R} (σ : M.GeneratingSections) [σ.IsFiniteType] :
    ∃ (n : ℕ) (p : SheafOfModules.free (R := R) (ULift.{u} (Fin n)) ⟶ M), Epi p := by
  classical
  let indexFintype : Fintype σ.I := Fintype.ofFinite _
  let e := (SheafOfModules.freeFunctor (R := R)).mapIso
    ((Equiv.ulift.trans (Fintype.equivFin σ.I).symm).toIso)
  exact ⟨Fintype.card σ.I, e.hom ≫ σ.π, inferInstance⟩

private theorem finiteType_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V W, HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ V W, ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (M : SheafOfModules.{u} R) {I : Type u}
    (V : I → C) (hV : J.CoversTop V)
    (h : ∀ i, (M.over (V i)).IsFiniteType) : M.IsFiniteType := by
  classical
  choose D hD using fun i ↦
    @SheafOfModules.IsFiniteType.exists_localGeneratorsData _ _ _ _ _ _ (M.over (V i)) (h i)
  let q : M.LocalGeneratorsData :=
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
  refine ⟨q, ⟨fun ij ↦ ?_⟩⟩
  have := (hD ij.1).isFiniteType ij.2
  dsimp only [q]
  infer_instance

private theorem finiteType_kernel
    {C : Type u} [SmallCategory C] [HasBinaryProducts C] [HasPullbacks C]
    {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V, HasSheafify (J.over V) AddCommGrpCat.{u}]
    [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V W, HasSheafify ((J.over V).over W) AddCommGrpCat.{u}]
    [∀ V W, ((J.over V).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U, (SheafOfModules.overFunctor.{u} R U).Additive]
    {F G : SheafOfModules.{u} R} (φ : F ⟶ G) [F.IsFiniteType]
    (hG : ∀ (U : C) (n : ℕ)
      (f : SheafOfModules.free (R := R.over U) (ULift.{u} (Fin n)) ⟶ G.over U),
      (kernel f).IsFiniteType)
    (hlim : ∀ U, PreservesLimit (parallelPair φ 0) (SheafOfModules.overFunctor R U)) :
    (kernel φ).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  have hlocal (i : q.I) : ((kernel φ).over (q.X i)).IsFiniteType := by
    have : HasBinaryProducts (Over (q.X i)) :=
      Over.ConstructProducts.over_binaryProduct_of_pullback
    have hσ : (q.generators i).IsFiniteType := hq.isFiniteType i
    obtain ⟨n, p, hp⟩ := exists_epi_fin.{u} (q.generators i)
    have : Epi p := hp
    let f := φ.over (q.X i)
    have : (kernel (p ≫ f)).IsFiniteType := hG (q.X i) n (p ≫ f)
    let k := kernel.map (p ≫ f) f p (𝟙 _) (by simp)
    have : Epi k := epi_kernel_of_epi p f
    have : (kernel f).IsFiniteType := finiteType_of_epi.{u} k
    have := hlim (q.X i)
    exact finiteType_of_epi.{u}
      (PreservesKernel.iso (SheafOfModules.overFunctor R (q.X i)) φ).inv
  exact finiteType_of_cover.{u} (kernel φ) q.X q.coversTop hlocal

/-- A finite type submodule of a coherent module is coherent, and the kernel of a
map from a finite type module to a coherent module is finite type.
Source: Stacks Project, Modules, Lemma 01BY
(blueprint: lem-weil-pbc-coherent-finite-type-sub-kernel).
Proof, following Stacks 01BY (1), (2):
1. Restriction preserves monomorphisms and kernels, as checked by evaluating on sections.
2. For a map from a finite free module into `K`, compose with the monomorphism into `G`.
   Coherence of `G` makes the composite kernel finite type. `kernelCompMono` identifies it
   with the original kernel, giving coherence of `K`.
3. Choose finite local generating sections of `F` and reindex each finite index set by
   `ULift (Fin n)` to obtain a finite free epimorphism `p` onto the restriction of `F`.
   Coherence of `G` makes the kernel of `p ≫ φ.over U` finite type.
4. The induced map from that kernel onto `kernel (φ.over U)` is epi. Mathlib's abelian
   refinement criterion proves this: refine any map into the latter kernel so that its
   image in `F.over U` lifts through `p`; the lift factors through the composite kernel.
5. Push finite local generating sections through this epimorphism. Transport across the
   kernel restriction isomorphism and flatten the covering of coverings using the
   iterated-slice equivalence. This gives finite local generators of `kernel φ`.
All auxiliary results are proved here from Mathlib; no holed image or lifting theorem
is used.
-/
theorem coherent_finiteType_submodule_kernel
    (X : RingedSpace.{u}) :
    (∀ (K G : SheafOfModules.{u} (moduleRings X))
      (i : K ⟶ G) [Mono i],
      K.IsFiniteType → IsCoherent X G → IsCoherent X K) ∧
    (∀ (F G : SheafOfModules.{u} (moduleRings X))
      (φ : F ⟶ G),
      F.IsFiniteType → IsCoherent X G → (kernel φ).IsFiniteType) := by
  constructor
  · intro K G i hi hK hG
    refine ⟨hK, ?_⟩
    intro U n f
    have : Mono (i.over U) := mono_over X i U
    have : (kernel (f ≫ i.over U)).IsFiniteType := hG.2 U n (f ≫ i.over U)
    exact finiteType_of_epi.{u} (kernelCompMono f (i.over U)).hom
  · intro F G φ hF hG
    have : F.IsFiniteType := hF
    exact finiteType_kernel φ hG.2 (fun U ↦ over_preserves_kernel X φ U)

end AlgebraicGeometry.RingedSpace
