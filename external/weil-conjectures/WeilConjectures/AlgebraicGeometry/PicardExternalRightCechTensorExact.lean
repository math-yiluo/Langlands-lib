/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PicardExternalRightCechModels
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Topology.Sheaves.CechComparison
import WeilConjectures.Algebra.Homology.FirstQuadrantExtendedTotalExact
import Mathlib.RingTheory.Flat.CategoryTheory
@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private lemma scalar_cech_map_proj
    {k : Type w} [Field k] {Y : Scheme.{w}}
    (g : Y ⟶ Spec (CommRingCat.of k)) {κ : Type w} (V : κ → Y.Opens)
    {A B : Y.Modules} (a : A ⟶ B) (n : ℕ) (t : Fin (n + 1) → κ)
    (x : ((picardCechFunctor g V).obj A).X n) :
    TopCat.Presheaf.cechComplexFunctorπ V (scalarSheaf g B).obj n t
      (((picardCechFunctor g V).map a).f n x) =
    scalarHomApp g a (Opposite.op (∏ᶜ fun l ↦ V (t l)))
      (TopCat.Presheaf.cechComplexFunctorπ V (scalarSheaf g A).obj n t x) := by
  exact congrArg (fun h ↦ h x)
    (TopCat.Presheaf.cechComplexFunctor_map_f_π V
      (scalarSheaf g A).obj (scalarHom g a).hom n t)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Affine quasi-coherent sections make the scalar right Cech sequence short exact.
Source: Stacks Project, Varieties, Tag 0BED, coefficient diagram after
`equation-kunneth-on-cech`, right-variable section argument.

Proof: every Cech tuple intersection is affine by repeated use of the affine
relative diagonal criterion. Sections preserve kernels, while vanishing of
positive cohomology for the first quasi-coherent term on an affine gives
surjectivity. Restriction of scalars to the field preserves the resulting
short exact sequence. The finite product over tuples is therefore short exact
in each Cech degree, and the degreewise criterion gives the claim. -/
private theorem picard_right_cech_sections_exact
    {k : Type w} [Field k] {Y : Scheme.{w}}
    (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal g)]
    {κ : Type w} [Finite κ]
    (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j))
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardCechFunctor g V)).ShortExact := by
  classical
  let : (SheafOfModules.toSheaf.{w} Y.ringCatSheaf).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{w} Y.ringCatSheaf) := by
    apply preservesFiniteLimits_of_reflects_of_preserves _
      (sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{w})
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{w} Y.ringCatSheaf) :=
    SheafOfModules.preservesFiniteColimits_toSheaf Y.ringCatSheaf
  let B := S.map (SheafOfModules.toSheaf.{w} Y.ringCatSheaf)
  have hB : B.ShortExact := hS.map_of_exact (SheafOfModules.toSheaf.{w} Y.ringCatSheaf)
  have hinf (n : ℕ) (t : Fin (n + 1) → κ) : IsAffineOpen (⨅ l, V (t l)) := by
    induction n with
    | zero => simpa using hV (t 0)
    | succ n ih =>
      have he : (⨅ l, V (t l)) = V (t 0) ⊓ ⨅ l : Fin (n + 1), V (t l.succ) := by
        apply le_antisymm
        · exact le_inf (iInf_le _ 0) (le_iInf fun l ↦ iInf_le _ l.succ)
        · apply le_iInf
          intro l
          exact Fin.cases inf_le_left (fun i ↦ inf_le_right.trans (iInf_le _ i)) l
      rw [he]
      exact (isAffineHom_diagonal_iff (f := g)).mp inferInstance ⊤ (isAffineOpen_top _)
        _ (by simp) _ (by simp) (hV (t 0)) (ih (fun i ↦ t i.succ))
  have hprod (n : ℕ) (t : Fin (n + 1) → κ) :
      IsAffineOpen (∏ᶜ fun l ↦ V (t l)) := by
    have he : (∏ᶜ fun l ↦ V (t l)) = ⨅ l, V (t l) :=
      le_antisymm (TopCat.Presheaf.piObj_le_iInf V t)
        (TopCat.Presheaf.iInf_le_piObj V t)
    rw [he]
    exact hinf n t
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let W (t : Fin (n + 1) → κ) := Opposite.op (∏ᶜ fun l ↦ V (t l))
  let P₁ := (scalarSheaf g S.X₁).obj
  let P₂ := (scalarSheaf g S.X₂).obj
  let P₃ := (scalarSheaf g S.X₃).obj
  have hsurj (t : Fin (n + 1) → κ) : Function.Surjective (scalarHomApp g S.g (W t)) :=
    surjective_app_of_cechAcyclicOnAffines hB
      (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) (hprod n t)
  have hinj (t : Fin (n + 1) → κ) : Function.Injective (scalarHomApp g S.f (W t)) :=
    TopCat.Sheaf.injective_app_f hB (W t)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    have ht (t : Fin (n + 1) → κ) :
        scalarHomApp g S.g (W t) (TopCat.Presheaf.cechComplexFunctorπ V P₂ n t x) = 0 := by
      calc
        _ = TopCat.Presheaf.cechComplexFunctorπ V P₃ n t
            (((picardCechFunctor g V).map S.g).f n x) :=
          (scalar_cech_map_proj g V S.g n t x).symm
        _ = TopCat.Presheaf.cechComplexFunctorπ V P₃ n t 0 := congrArg _ hx
        _ = 0 := map_zero _
    have hex (t : Fin (n + 1) → κ) : ∃ a : P₁.obj (W t),
        scalarHomApp g S.f (W t) a = TopCat.Presheaf.cechComplexFunctorπ V P₂ n t x :=
      TopCat.Sheaf.exists_app_f_eq hB (W t)
        (TopCat.Presheaf.cechComplexFunctorπ V P₂ n t x) (ht t)
    choose a ha using hex
    refine ⟨(ModuleCat.piIsoPi (fun t ↦ P₁.obj (W t))).inv a, ?_⟩
    apply TopCat.Presheaf.cechComplexFunctor_ext V P₂
    intro t
    calc
      _ = scalarHomApp g S.f (W t)
          (TopCat.Presheaf.cechComplexFunctorπ V P₁ n t
            ((ModuleCat.piIsoPi (fun t ↦ P₁.obj (W t))).inv a)) :=
        scalar_cech_map_proj g V S.f n t _
      _ = scalarHomApp g S.f (W t) (a t) := congrArg _
        (TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv V P₁ a t)
      _ = _ := ha t
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    apply TopCat.Presheaf.cechComplexFunctor_ext V P₁
    intro t
    apply hinj t
    calc
      _ = TopCat.Presheaf.cechComplexFunctorπ V P₂ n t
          (((picardCechFunctor g V).map S.f).f n x) :=
        (scalar_cech_map_proj g V S.f n t x).symm
      _ = TopCat.Presheaf.cechComplexFunctorπ V P₂ n t
          (((picardCechFunctor g V).map S.f).f n y) := congrArg _ hxy
      _ = _ := scalar_cech_map_proj g V S.f n t y
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    choose a ha using fun t ↦ hsurj t (TopCat.Presheaf.cechComplexFunctorπ V P₃ n t x)
    refine ⟨(ModuleCat.piIsoPi (fun t ↦ P₂.obj (W t))).inv a, ?_⟩
    apply TopCat.Presheaf.cechComplexFunctor_ext V P₃
    intro t
    calc
      _ = scalarHomApp g S.g (W t)
          (TopCat.Presheaf.cechComplexFunctorπ V P₂ n t
            ((ModuleCat.piIsoPi (fun t ↦ P₂.obj (W t))).inv a)) :=
        scalar_cech_map_proj g V S.g n t _
      _ = scalarHomApp g S.g (W t) (a t) := congrArg _
        (TopCat.Presheaf.cechComplexFunctorπ_piIsoPi_inv V P₂ a t)
      _ = _ := ha t

private instance tensorComplex_zero
    {k : Type w} [Field k] (C : CochainComplex (ModuleCat.{w} k) ℕ) :
    ((Functor.map₂HomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).obj C).PreservesZeroMorphisms := by
  constructor
  intro A B
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  change HomologicalComplex.ιMapBifunctor C A _ _ p q n hpq ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 C) (0 : A ⟶ B) _ _).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_total_extension_shortExact
    {k : Type w} [Field k] (C : CochainComplex (ModuleCat.{w} k) ℕ)
    (S : ShortComplex (CochainComplex (ModuleCat.{w} k) ℕ)) (hS : S.ShortExact) :
    (S.map (((Functor.map₂HomologicalComplex
      (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (ComplexShape.up ℕ)).obj C) ⋙
      ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{w} k))).ShortExact := by
  classical
  let G := (Functor.mapBifunctorHomologicalComplex
    (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).obj C
  have : G.PreservesZeroMorphisms := by
    constructor
    intro A B
    ext p q
    simp [G]
  let T := S.map G
  have hT : T.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro p
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro q
    let M := C.X p
    have hs := hS.map_of_exact (HomologicalComplex.eval _ _ q)
    change (S.map
      (HomologicalComplex.eval _ _ q)).map
        (CategoryTheory.MonoidalCategory.tensorLeft M) |>.ShortExact
    exact hs.map_of_exact (CategoryTheory.MonoidalCategory.tensorLeft M)
  have ht := HomologicalComplex₂.shortExact_extended_total T hT
  have hid := (Functor.mapBifunctorHomologicalComplex
    (CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat.{w} k))
      (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map_id C
  apply ShortComplex.shortExact_of_iso _ ht
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  all_goals
    dsimp only [Iso.refl_hom]
    simp only [Category.comp_id, Category.id_comp]
    dsimp only [T, ShortComplex.map, Functor.comp_map, Functor.map₂HomologicalComplex]
    simp only [HomologicalComplex.mapBifunctorMap, hid, NatTrans.id_app,
      Category.id_comp]
    rfl

/-- Tensoring a scalar right Cech short exact sequence with fixed left cochains,
then totalizing and extending by zero, remains short exact.
Source: Stacks Project, Varieties, Tag 0BED, the tensor-total construction after
`equation-kunneth-on-cech`.

Proof: tensoring over the field is exact. In every total degree only finitely
many bidegrees occur, so the direct sum of the degreewise short exact sequences
is short exact. The totalization maps are these direct sums, and extension by
zero adds zero short exact sequences in negative degrees. The degreewise
criterion for short exact complexes finishes the argument. -/
private theorem picard_right_tensor_total_shortExact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ Spec (CommRingCat.of k))
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens) (F : X.Modules)
    (S : ShortComplex Y.Modules)
    (hC : (S.map (picardCechFunctor g V)).ShortExact) :
    (S.map (picardRightTensorCechFunctor f g U V F)).ShortExact := by
  exact tensor_total_extension_shortExact ((picardCechFunctor f U).obj F)
    (S.map (picardCechFunctor g V)) hC

/-- The tensor-total Cech sequence is short exact in the right coefficient.
Source: Stacks Project, Varieties, Tag 0BED, the coefficient diagram following
equation-kunneth-on-cech, applied in the right variable.
(blueprint: lem-sc-picard-external-right-cech-exact-tensor).

Proof: In Cech degree q, every tuple has q+1 entries, so its intersection
is nonempty as a family of opens. Repeated use of the affine diagonal criterion
makes that intersection affine. Sections of S there are short exact: sections
preserve kernels, and quasi-coherent affine vanishing of H^1 of S.X₁ gives
surjectivity onto sections of S.X₃. Restriction of scalars to k preserves this.
The finite product over the tuples is therefore short exact, proving degreewise
short exactness of the scalar Cech sequence. Fix a total degree n. Tensor each
sequence in degree q with the fixed k-vector space of F-cochains in degree p,
for p+q=n. All k-vector spaces are flat, so this preserves short exactness.
The finite direct sum over these pairs remains short exact. These are exactly
the terms and maps of picardRightTensorCechFunctor, by the natural tensor-total
construction. Extension from natural to integer degrees keeps these terms and
puts the zero sequence in negative degrees. Degreewise short exactness implies
short exactness of complexes. Empty index types give empty products (zero
modules) in every Cech degree; zero coefficients also give zero terms. Thus
neither a cover hypothesis nor a nonemptiness assumption is needed. -/
theorem picardExternal_right_cech_tensor_exact
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [IsAffineHom (pullback.diagonal f)] [IsAffineHom (pullback.diagonal g)]
    {ι κ : Type w} [Finite ι] [Finite κ]
    (U : ι → X.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (F : X.Modules) [F.IsQuasicoherent]
    (S : ShortComplex Y.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (picardRightTensorCechFunctor f g U V F)).ShortExact := by
  have _ := hU
  apply picard_right_tensor_total_shortExact f g U V F S
  exact picard_right_cech_sections_exact g V hV S hS
end AlgebraicGeometry.Scheme.Modules
