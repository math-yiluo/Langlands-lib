/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Comparing boundaries after extension by zero

Source: Stacks Project, Homology, Tag 0117; Derived Categories, Tag 014Q.
(blueprint: lem-sc-p1-nat-complex-derived-boundary).
-/

@[expose] public section

universe v u w

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

namespace CategoryTheory

/-- The canonical identification of derived homology of the extension by zero of
an `ℕ`-indexed complex with its original homology. This is the composite of
localization's homology identification and extension's homology identification.

Source: Stacks Project, Derived Categories, Tag 014Q; Homology, Tag 0117.
(blueprint: lem-sc-p1-nat-complex-derived-boundary). -/
noncomputable def natComplexDerivedHomologyIso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : CochainComplex C ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor C (n : ℤ)).obj
        (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)) ≅ K.homology n :=
  (DerivedCategory.homologyFunctorFactors C (n : ℤ)).app _ ≪≫
    K.extendHomologyIso ComplexShape.embeddingUpNat rfl

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

private theorem integer_boundary (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n : ℤ) :
    DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS) n (n+1) rfl ≫
      (DerivedCategory.homologyFunctorFactors C (n+1)).hom.app S.X₁ =
    (DerivedCategory.homologyFunctorFactors C n).hom.app S.X₃ ≫ hS.δ n (n+1) rfl := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hc := CochainComplex.mappingCone.homologySequenceδ_triangleh hS n (n+1) rfl
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at hc
  have hcc := congrArg
    (fun f ↦ (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).inv.app _ ≫
      f ≫ (HomotopyCategory.homologyFunctorFactors C (.up ℤ) (n+1)).hom.app _) hc
  dsimp only [CochainComplex.mappingCone.triangle, Pretriangulated.Triangle.mk] at hcc
  simp only [assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app] at hcc
  erw [comp_id, comp_id] at hcc
  apply (cancel_epi ((DerivedCategory.homologyFunctor C n).map
    (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))).1
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  change (DerivedCategory.homologyFunctor C n).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
      (DerivedCategory.homologyFunctor C 0).shiftMap
        (DerivedCategory.triangleOfSESδ hS) n (n+1) (by omega) ≫ _ = _
  have hs := Functor.shiftMap_comp' (DerivedCategory.homologyFunctor C 0)
    (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))
    (DerivedCategory.triangleOfSESδ hS) n (n+1) (by omega)
  simp only [DerivedCategory.shift_homologyFunctor] at hs
  erw [← reassoc_of% hs, DerivedCategory.descShortComplex_triangleOfSESδ]
  erw [DerivedCategory.shiftMap_homologyFunctor_map_Q _ n (n+1) (by omega)]
  erw [assoc, assoc, Iso.inv_hom_id_app, comp_id]
  simpa only [CochainComplex.mappingCone.triangle, Pretriangulated.Triangle.mk, assoc] using
    congrArg (fun f ↦ (DerivedCategory.homologyFunctorFactors C n).hom.app _ ≫ f) hcc

omit [HasDerivedCategory C] in
private theorem extension_shortExact (S : ShortComplex (CochainComplex C ℕ))
    (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingUpNat.extendFunctor C)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).mpr
  intro k
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    let e : ((S.map (ComplexShape.embeddingUpNat.extendFunctor C)).map
        (eval C (.up ℤ) (n : ℤ))) ≅ S.map (eval C (.up ℕ) n) :=
      ShortComplex.isoMk (S.X₁.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₂.extendXIso ComplexShape.embeddingUpNat rfl)
        (S.X₃.extendXIso ComplexShape.embeddingUpNat rfl)
        (by dsimp; simp [extendMap_f]) (by dsimp; simp [extendMap_f])
    exact ShortComplex.shortExact_of_iso e.symm ((shortExact_iff_degreewise_shortExact S).mp hS n)
  · have hz (K : CochainComplex C ℕ) : IsZero ((K.extend ComplexShape.embeddingUpNat).X k) :=
      isZero_extend_X K _ k (by intro n hn; dsimp at hn; omega)
    let T := (S.map (ComplexShape.embeddingUpNat.extendFunctor C)).map (eval C (.up ℤ) k)
    have : IsIso T.g := by
      rw [(hz S.X₂).eq_of_src T.g 0]
      exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hz S.X₂, hz S.X₃⟩
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso T (hz S.X₁) inferInstance).shortExact

omit [HasDerivedCategory C] in
private theorem extendOpcycles_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (n : ℕ) :
    opcyclesMap (extendMap f ComplexShape.embeddingUpNat) (n : ℤ) ≫
      (L.extendOpcyclesIso ComplexShape.embeddingUpNat rfl).hom =
    (K.extendOpcyclesIso ComplexShape.embeddingUpNat rfl).hom ≫ opcyclesMap f n := by
  apply (cancel_epi ((K.extend ComplexShape.embeddingUpNat).pOpcycles (n : ℤ))).1
  simp only [p_opcyclesMap_assoc, pOpcycles_extendOpcyclesIso_hom_assoc]
  rw [pOpcycles_extendOpcyclesIso_hom, p_opcyclesMap]
  rw [extendMap_f f ComplexShape.embeddingUpNat (i := n) (i' := (n : ℤ)) rfl]
  simp only [assoc, Iso.inv_hom_id_assoc]

omit [HasDerivedCategory C] in
private theorem extendOpcyclesToCycles (K : CochainComplex C ℕ) (n : ℕ) :
    (K.extendOpcyclesIso ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
        K.opcyclesToCycles n (n+1) =
      (K.extend ComplexShape.embeddingUpNat).opcyclesToCycles (n : ℤ) (↑(n+1)) ≫
        (K.extendCyclesIso ComplexShape.embeddingUpNat (j := n+1) rfl).hom := by
  apply (cancel_epi ((K.extend ComplexShape.embeddingUpNat).pOpcycles (n : ℤ))).1
  apply (cancel_mono (K.iCycles (n+1))).1
  simp only [assoc, pOpcycles_extendOpcyclesIso_hom_assoc,
    pOpcycles_opcyclesToCycles_iCycles, extendCyclesIso_hom_iCycles]
  erw [pOpcycles_opcyclesToCycles_iCycles_assoc,
    extend_d_eq K ComplexShape.embeddingUpNat (i := n) (j := n+1) rfl rfl]
  simp only [assoc, Iso.inv_hom_id, comp_id]

omit [HasDerivedCategory C] in
private theorem extension_boundary (S : ShortComplex (CochainComplex C ℕ))
    (hS : S.ShortExact)
    (hExt : (S.map (ComplexShape.embeddingUpNat.extendFunctor C)).ShortExact) (n : ℕ) :
    hExt.δ (n : ℤ) (↑(n+1)) (by dsimp) ≫
        (S.X₁.extendHomologyIso ComplexShape.embeddingUpNat (j := n+1) rfl).hom =
      (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).hom ≫
        hS.δ n (n+1) rfl := by
  let φ : HomologySequence.snakeInput hExt (n : ℤ) (↑(n+1)) (by dsimp) ⟶
      HomologySequence.snakeInput hS n (n+1) rfl :=
    { f₀ :=
        { τ₁ := (S.X₁.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          τ₂ := (S.X₂.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          τ₃ := (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          comm₁₂ := (extendHomologyIso_hom_naturality S.f _ rfl).symm
          comm₂₃ := (extendHomologyIso_hom_naturality S.g _ rfl).symm }
      f₁ :=
        { τ₁ := (S.X₁.extendOpcyclesIso ComplexShape.embeddingUpNat rfl).hom
          τ₂ := (S.X₂.extendOpcyclesIso ComplexShape.embeddingUpNat rfl).hom
          τ₃ := (S.X₃.extendOpcyclesIso ComplexShape.embeddingUpNat rfl).hom
          comm₁₂ := (extendOpcycles_naturality S.f n).symm
          comm₂₃ := (extendOpcycles_naturality S.g n).symm }
      f₂ :=
        { τ₁ := (S.X₁.extendCyclesIso ComplexShape.embeddingUpNat rfl).hom
          τ₂ := (S.X₂.extendCyclesIso ComplexShape.embeddingUpNat rfl).hom
          τ₃ := (S.X₃.extendCyclesIso ComplexShape.embeddingUpNat rfl).hom
          comm₁₂ := (extendCyclesIso_hom_naturality S.f _ rfl).symm
          comm₂₃ := (extendCyclesIso_hom_naturality S.g _ rfl).symm }
      f₃ :=
        { τ₁ := (S.X₁.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          τ₂ := (S.X₂.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          τ₃ := (S.X₃.extendHomologyIso ComplexShape.embeddingUpNat rfl).hom
          comm₁₂ := (extendHomologyIso_hom_naturality S.f _ rfl).symm
          comm₂₃ := (extendHomologyIso_hom_naturality S.g _ rfl).symm }
      comm₀₁ := by
        ext <;> exact extendHomologyIso_hom_homologyι _ _ rfl
      comm₁₂ := by
        ext <;> exact extendOpcyclesToCycles _ n
      comm₂₃ := by
        ext <;> exact (homologyπ_extendHomologyIso_hom _ _ rfl).symm }
  exact ShortComplex.SnakeInput.naturality_δ φ

/-- Extension by zero preserves a short exact sequence of nonnegative cochain
complexes, and its derived triangle boundary is the original snake boundary under
`natComplexDerivedHomologyIso`.

Source: Stacks Project, Homology, Tag 0117; Derived Categories, Tag 014Q.
(blueprint: lem-sc-p1-nat-complex-derived-boundary).

Proof:
1. Check exactness degreewise. In a nonnegative degree the extended row is
isomorphic, through `extendXIso`, to the original short exact row. In a negative
degree all three terms are zero. Thus the extended sequence is short exact.
2. For an integer-indexed short exact sequence use its cone triangle. The map
from the cone to the third complex is a quasi-isomorphism. The formula
`CochainComplex.mappingCone.homologySequenceδ_triangleh` identifies the cone
boundary with the snake boundary after this quasi-isomorphism. Localizing and
cancelling that isomorphism gives the same formula for `triangleOfSES`.
3. In degrees n and n+1, the cycles and opcycles identifications of extension
commute with the snake diagram: the differentials and the two sequence maps
are transported by `extendXIso`. Naturality of the snake boundary identifies the
extended boundary with the original boundary. This holds also for n=0: the
incoming differential in degree -1 is zero, just as it is for the initial degree
of the original complex. Compose with `homologyFunctorFactors` to obtain the
asserted equation. The cone uses its third map minus the projection, so the
boundary here has the same sign as the snake boundary.
-/
theorem natComplex_boundary_derived
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℕ)) (hS : S.ShortExact) :
    ∃ hExt : (S.map (ComplexShape.embeddingUpNat.extendFunctor C)).ShortExact,
      ∀ n : ℕ,
        DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hExt)
            (n : ℤ) (n + 1) (by omega) ≫
            (natComplexDerivedHomologyIso S.X₁ (n + 1)).hom =
          (natComplexDerivedHomologyIso S.X₃ n).hom ≫ hS.δ n (n + 1) rfl := by
  let hExt := extension_shortExact S hS
  refine ⟨hExt, ?_⟩
  intro n
  simp only [natComplexDerivedHomologyIso, Iso.trans_hom, assoc]
  erw [reassoc_of% integer_boundary _ hExt (n : ℤ), extension_boundary S hS hExt n]
  rfl

end CategoryTheory
