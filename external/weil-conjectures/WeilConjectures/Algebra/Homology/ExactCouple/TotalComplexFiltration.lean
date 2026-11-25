/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import WeilConjectures.Algebra.Homology.ExactCouple.FilteredComplex
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The column filtration of the total complex of a double complex

Let `K` be a double complex indexed by `ℤ × ℤ` (a `HomologicalComplex₂ C (up ℤ) (up ℤ)`) which
has a total complex `Tot K`, with `(Tot K)ⁿ = ⨁_{p + q = n} K^{p, q}` and differential
`d = d_I + (-1)ᵖ d_II`. The total complexes of the double complexes `K^{≥ p, •}` of the columns of
index `≥ p` form a decreasing filtration of `Tot K` by subcomplexes, the *first filtration*
(`HomologicalComplex₂.columnFiltration`), and the graded piece `grᵖ Tot K` is the total complex
of the column `K^{p, •}`, that is the column shifted by `p` with differential `(-1)ᵖ d_II`.

Consequently, the exact couple of this filtered complex
(`CategoryTheory.DecreasingFiltration.exactCouple`) has `E₁^{p, n} = Hⁿ(grᵖ) ≅ H^{n - p}(K^{p, •})`
(`HomologicalComplex₂.columnFiltrationE₁Iso`), and under these identifications the differential
`d₁` is the morphism induced in vertical cohomology by the horizontal differential `d_I`
(`HomologicalComplex₂.columnFiltrationE₁Iso_d`).

## Main definitions

- `HomologicalComplex₂.columnFiltration`: the filtration of `Tot K` by the columns.
- `HomologicalComplex₂.columnShortComplex`: the short exact sequence
  `0 ⟶ Tot K^{≥ p + 1, •} ⟶ Tot K^{≥ p, •} ⟶ Tot K^{p, •} ⟶ 0`.
- `HomologicalComplex₂.columnFiltrationE₁Iso`: the identification `E₁^{p, p + q} ≅ H^q(K^{p, •})`.

## Main statements

- `HomologicalComplex₂.columnFiltrationE₁Iso_d`: the differential `d₁` is induced by `d_I`.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Abelian C]

section

variable {ι₁ ι₂ ι : Type*} [DecidableEq ι] {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c : ComplexShape ι} [TotalComplexShape c₁ c₂ c]

/-- A morphism of double complexes whose components are split monomorphisms induces
monomorphisms between the objects of the total complexes. -/
lemma mono_total_map_f {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]
    (φ : K ⟶ L) (h : ∀ x y, IsSplitMono ((φ.f x).f y)) (n : ι) : Mono ((total.map φ c).f n) := by
  have : (total.map φ c).f n ≫
      L.totalDesc (fun x y h ↦ retraction ((φ.f x).f y) ≫ K.ιTotal c x y n h) = 𝟙 _ := by
    ext x y h
    simp
  exact mono_of_mono_fac this

/-- A morphism of double complexes whose components are split monomorphisms induces a
monomorphism of total complexes. -/
lemma mono_total_map {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c] [L.HasTotal c]
    (φ : K ⟶ L) (h : ∀ x y, IsSplitMono ((φ.f x).f y)) : Mono (total.map φ c) :=
  HomologicalComplex.mono_of_mono_f _ (mono_total_map_f φ h)

end

variable (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) [K.HasTotal (up ℤ)]

/-- The double complex `K^{≥ p, •}` formed by the columns of `K` of index `≥ p`. -/
noncomputable abbrev columnsGE (p : ℤ) : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  K.stupidTrunc (embeddingUpIntGE p)

/-- The inclusion `K^{≥ p, •} ⟶ K`. -/
noncomputable abbrev ιColumnsGE (p : ℤ) : K.columnsGE p ⟶ K :=
  K.ιStupidTrunc (embeddingUpIntGE p)

omit [K.HasTotal (up ℤ)] in
/-- The inclusion `K^{≥ p, •} ⟶ K` is an isomorphism on the columns of index `≥ p`. -/
lemma isIso_ιColumnsGE_f (p x : ℤ) (hx : p ≤ x) : IsIso ((K.ιColumnsGE p).f x) :=
  K.isIso_ιStupidTrunc_f (embeddingUpIntGE p) (i := (x - p).toNat) (by
    simp only [embeddingUpIntGE_f]
    omega)

omit [K.HasTotal (up ℤ)] in
/-- The inclusion `K^{≥ p, •} ⟶ K` is an isomorphism on the objects of the columns of index
`≥ p`. -/
lemma isIso_ιColumnsGE_f_f (p x y : ℤ) (hx : p ≤ x) : IsIso (((K.ιColumnsGE p).f x).f y) := by
  have := K.isIso_ιColumnsGE_f p x hx
  infer_instance

omit [K.HasTotal (up ℤ)] in
/-- The columns of index `< p` of `K^{≥ p, •}` vanish. -/
lemma isZero_columnsGE_X (p x : ℤ) (hx : x < p) : IsZero ((K.columnsGE p).X x) :=
  K.isZero_stupidTrunc_X _ x (fun i hi ↦ by
    simp only [embeddingUpIntGE_f] at hi
    omega)

omit [K.HasTotal (up ℤ)] in
/-- The objects of the columns of index `< p` of `K^{≥ p, •}` vanish. -/
lemma isZero_columnsGE_X_X (p x y : ℤ) (hx : x < p) : IsZero (((K.columnsGE p).X x).X y) :=
  (HomologicalComplex.eval _ _ y).map_isZero (K.isZero_columnsGE_X p x hx)

/-- The inclusion of total complexes `Tot K^{≥ p, •} ⟶ Tot K`. -/
noncomputable def totalιColumnsGE (p : ℤ) : (K.columnsGE p).total (up ℤ) ⟶ K.total (up ℤ) :=
  total.map (K.ιColumnsGE p) (up ℤ)

omit [K.HasTotal (up ℤ)] in
/-- The components of the inclusion `K^{≥ p, •} ⟶ K` are split monomorphisms. -/
lemma isSplitMono_ιColumnsGE_f_f (p x y : ℤ) : IsSplitMono (((K.ιColumnsGE p).f x).f y) := by
  by_cases hx : p ≤ x
  · have := K.isIso_ιColumnsGE_f_f p x y hx
    infer_instance
  · exact IsSplitMono.mk' ⟨0, (K.isZero_columnsGE_X_X p x y (by omega)).eq_of_src _ _⟩

/-- The inclusion `Tot K^{≥ p, •} ⟶ Tot K` is a monomorphism. -/
instance (p : ℤ) : Mono (K.totalιColumnsGE p) :=
  mono_total_map _ (K.isSplitMono_ιColumnsGE_f_f p)

/-- The components of the inclusion `Tot K^{≥ p, •} ⟶ Tot K` are monomorphisms. -/
instance (p n : ℤ) : Mono ((K.totalιColumnsGE p).f n) :=
  mono_total_map_f _ (K.isSplitMono_ιColumnsGE_f_f p) n

/-- The inclusion `Tot K^{≥ p, •} ⟶ Tot K` on the summands. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalιColumnsGE (p x y n : ℤ) (h : x + y = n) :
    (K.columnsGE p).ιTotal (up ℤ) x y n h ≫ (K.totalιColumnsGE p).f n =
      ((K.ιColumnsGE p).f x).f y ≫ K.ιTotal (up ℤ) x y n h :=
  ιTotal_map _ _ _ _ _ _ _ _

/-- The inclusion `K^{≥ p + 1, •} ⟶ K^{≥ p, •}`. -/
noncomputable abbrev columnsGEMap (p : ℤ) : K.columnsGE (p + 1) ⟶ K.columnsGE p :=
  K.mapStupidTruncGE (embeddingUpIntGE_monotone (p + 1) p (by omega))

omit [K.HasTotal (up ℤ)] in
/-- The inclusions `K^{≥ p + 1, •} ⟶ K^{≥ p, •} ⟶ K` compose to the inclusion. -/
@[reassoc (attr := simp)]
lemma columnsGEMap_ιColumnsGE (p : ℤ) :
    K.columnsGEMap p ≫ K.ιColumnsGE p = K.ιColumnsGE (p + 1) :=
  K.mapStupidTruncGE_fac _

/-- The inclusions `Tot K^{≥ p + 1, •} ⟶ Tot K^{≥ p, •} ⟶ Tot K` compose to the inclusion. -/
lemma total_map_columnsGEMap_comp (p : ℤ) :
    total.map (K.columnsGEMap p) (up ℤ) ≫ K.totalιColumnsGE p = K.totalιColumnsGE (p + 1) := by
  rw [totalιColumnsGE, totalιColumnsGE, ← total.map_comp, columnsGEMap_ιColumnsGE]

/-- The **first filtration** of the total complex of a double complex `K`: `Fᵖ Tot K` is the
total complex of the double complex `K^{≥ p, •}` of the columns of index `≥ p`, that is
`Fᵖ (Tot K)ⁿ = ⨁_{i ≥ p} K^{i, n - i}`. It is a filtration by subcomplexes.

(blueprint: `def-sp-double-complex-total`, `det-def-groth-ss`) -/
noncomputable def columnFiltration : DecreasingFiltration (K.total (up ℤ)) where
  F p := Subobject.mk (K.totalιColumnsGE p)
  F_succ_le p := Subobject.mk_le_mk_of_comm (total.map (K.columnsGEMap p) (up ℤ))
    (K.total_map_columnsGEMap_comp p)

/-- The `p`-th step of the column filtration is `Tot K^{≥ p, •}`. -/
lemma columnFiltration_F (p : ℤ) :
    K.columnFiltration.F p = Subobject.mk (K.totalιColumnsGE p) := rfl


/-! ### The graded pieces of the column filtration -/

omit [K.HasTotal (up ℤ)] in
lemma stupidTruncXIso_hom_eq (p : ℤ) :
    (K.stupidTruncXIso (embeddingUpIntGE p) (i := 0) (by simp)).hom =
      (K.ιColumnsGE p).f p := by
  refine Eq.trans ?_
    (HomologicalComplex.ιStupidTruncf'_eq K (embeddingUpIntGE p) (i := 0) (i' := p) (by simp)).symm
  simp [HomologicalComplex.stupidTruncXIso, HomologicalComplex.restrictionXIso]

/-- The projection `K^{≥ p, •} ⟶ K^{p, •}` to the double complex concentrated in the
column `p`. -/
noncomputable def toSingleColumn (p : ℤ) :
    K.columnsGE p ⟶ (singleColumn C (up ℤ) (up ℤ) p).obj (K.X p) :=
  HomologicalComplex.mkHomToSingle ((K.ιColumnsGE p).f p) (fun x hx ↦
    (K.isZero_columnsGE_X p x (by
      simp at hx
      omega)).eq_of_src _ _)

omit [K.HasTotal (up ℤ)] in
/-- The projection `K^{≥ p, •} ⟶ K^{p, •}` on the column `p`. -/
lemma toSingleColumn_f_f (p y : ℤ) :
    ((K.toSingleColumn p).f p).f y =
      ((K.ιColumnsGE p).f p).f y ≫ (singleColumnXXIso (up ℤ) (K.X p) p y).inv := by
  simp only [toSingleColumn, HomologicalComplex.mkHomToSingle_f]
  rfl

omit [K.HasTotal (up ℤ)] in
/-- The projection `K^{≥ p, •} ⟶ K^{p, •}` agrees with the one of
`CochainComplex.shortComplexStupidFiltrationGE`. -/
lemma stupidFiltrationGEObjToSingle_eq (p : ℤ) :
    CochainComplex.stupidFiltrationGEObjToSingle K p = K.toSingleColumn p := by
  apply HomologicalComplex.to_single_hom_ext
  dsimp only [CochainComplex.stupidFiltrationGEObjToSingle, toSingleColumn]
  rw [HomologicalComplex.mkHomToSingle_f, HomologicalComplex.mkHomToSingle_f,
    ← stupidTruncXIso_hom_eq]

omit [K.HasTotal (up ℤ)] in
/-- The composite `K^{≥ p + 1, •} ⟶ K^{≥ p, •} ⟶ K^{p, •}` vanishes. -/
@[reassoc (attr := simp)]
lemma columnsGEMap_toSingleColumn (p : ℤ) : K.columnsGEMap p ≫ K.toSingleColumn p = 0 := by
  apply HomologicalComplex.to_single_hom_ext
  exact (K.isZero_columnsGE_X (p + 1) p (by omega)).eq_of_src _ _

/-- The short exact sequence `0 ⟶ K^{≥ p + 1, •} ⟶ K^{≥ p, •} ⟶ K^{p, •} ⟶ 0` of double
complexes. -/
noncomputable def columnsShortComplex₂ (p : ℤ) :
    ShortComplex (HomologicalComplex₂ C (up ℤ) (up ℤ)) :=
  ShortComplex.mk (K.columnsGEMap p) (K.toSingleColumn p) (K.columnsGEMap_toSingleColumn p)

/-- The short exact sequence `0 ⟶ Tot K^{≥ p + 1, •} ⟶ Tot K^{≥ p, •} ⟶ Tot K^{p, •} ⟶ 0`,
where `K^{p, •}` is the double complex concentrated in the column `p`. -/
noncomputable def columnShortComplex (p : ℤ) : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (total.map (K.columnsGEMap p) (up ℤ)) (total.map (K.toSingleColumn p) (up ℤ))
    (by rw [← total.map_comp, columnsGEMap_toSingleColumn, total.map_zero])

/-- The first morphism of `HomologicalComplex₂.columnShortComplex`. -/
lemma columnShortComplex_f (p : ℤ) :
    (K.columnShortComplex p).f = total.map (K.columnsGEMap p) (up ℤ) := rfl


/-- The second morphism of `HomologicalComplex₂.columnShortComplex`. -/
lemma columnShortComplex_g (p : ℤ) :
    (K.columnShortComplex p).g = total.map (K.toSingleColumn p) (up ℤ) := rfl

/-- The first term of the stupid filtration short complex has a total complex. -/
instance (p q : ℤ) (h : p + 1 = q) :
    HomologicalComplex₂.HasTotal (CochainComplex.shortComplexStupidFiltrationGE K p q h).X₁
      (up ℤ) :=
  inferInstanceAs (HomologicalComplex₂.HasTotal (K.columnsGE q) (up ℤ))

/-- The second term of the stupid filtration short complex has a total complex. -/
instance (p q : ℤ) (h : p + 1 = q) :
    HomologicalComplex₂.HasTotal (CochainComplex.shortComplexStupidFiltrationGE K p q h).X₂
      (up ℤ) :=
  inferInstanceAs (HomologicalComplex₂.HasTotal (K.columnsGE p) (up ℤ))

/-- The third term of the stupid filtration short complex has a total complex. -/
instance (p q : ℤ) (h : p + 1 = q) :
    HomologicalComplex₂.HasTotal (CochainComplex.shortComplexStupidFiltrationGE K p q h).X₃
      (up ℤ) :=
  inferInstanceAs
    (HomologicalComplex₂.HasTotal ((singleColumn C (up ℤ) (up ℤ) p).obj (K.X p)) (up ℤ))

/-- The sequence `0 ⟶ Tot K^{≥ p + 1, •} ⟶ Tot K^{≥ p, •} ⟶ Tot K^{p, •} ⟶ 0` is short exact
(it is degreewise split). -/
lemma columnShortComplex_shortExact (p : ℤ) : (K.columnShortComplex p).ShortExact := by
  let S := CochainComplex.shortComplexStupidFiltrationGE K p (p + 1) rfl
  have hS : (total.shortComplex S (up ℤ)).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _ (fun n ↦
      (total.shortComplexSplitting _ (up ℤ) ((GradedObject.shortComplexSplittingEquiv _).symm
        (fun xy ↦ (CochainComplex.shortComplexStupidFiltrationGESplitting K p (p + 1) rfl
          xy.1).map (HomologicalComplex.eval C (up ℤ) xy.2))) n).shortExact)
  refine ShortComplex.shortExact_of_iso (S₁ := total.shortComplex S (up ℤ))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_) hS
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (congrArg (fun φ ↦ total.map φ (up ℤ)) (K.stupidFiltrationGEObjToSingle_eq p)).symm

/-- The first morphism of `HomologicalComplex₂.columnShortComplex` is compatible with the
inclusions into `Tot K`. -/
@[reassoc (attr := simp)]
lemma columnShortComplex_f_comp (p : ℤ) :
    (K.columnShortComplex p).f ≫ K.totalιColumnsGE p = K.totalιColumnsGE (p + 1) :=
  K.total_map_columnsGEMap_comp p

/-- The projection `Tot K^{≥ p, •} ⟶ Tot K^{p, •}` on the summands of the column `p`. -/
@[reassoc]
lemma ιTotal_columnShortComplex_g (p y n : ℤ) (h : p + y = n) :
    (K.columnsGE p).ιTotal (up ℤ) p y n h ≫ (K.columnShortComplex p).g.f n =
      ((K.ιColumnsGE p).f p).f y ≫ (singleColumnXXIso (up ℤ) (K.X p) p y).inv ≫
        ((singleColumn C (up ℤ) (up ℤ) p).obj (K.X p)).ιTotal (up ℤ) p y n h := by
  rw [columnShortComplex_g, ιTotal_map, toSingleColumn_f_f, Category.assoc]

/-! ### The comparison with the short exact sequences of the filtration -/

/-- The isomorphism between the subobject `Fᵖ Tot K` and `Tot K^{≥ p, •}`. -/
noncomputable def columnFiltrationPieceIso (p : ℤ) :
    Subobject.underlying.obj (K.columnFiltration.F p) ≅ (K.columnsGE p).total (up ℤ) :=
  Subobject.underlyingIso (K.totalιColumnsGE p)

/-- The isomorphism `Fᵖ Tot K ≅ Tot K^{≥ p, •}` is compatible with the inclusions. -/
@[reassoc (attr := simp)]
lemma columnFiltrationPieceIso_hom_comp (p : ℤ) :
    (K.columnFiltrationPieceIso p).hom ≫ K.totalιColumnsGE p = (K.columnFiltration.F p).arrow :=
  Subobject.underlyingIso_hom_comp_eq_mk _

/-- The isomorphism `Fᵖ Tot K ≅ Tot K^{≥ p, •}` is compatible with the inclusions. -/
@[reassoc (attr := simp)]
lemma columnFiltrationPieceIso_inv_comp (p : ℤ) :
    (K.columnFiltrationPieceIso p).inv ≫ (K.columnFiltration.F p).arrow = K.totalιColumnsGE p :=
  Subobject.underlyingIso_arrow _

/-- The isomorphisms `Fᵖ Tot K ≅ Tot K^{≥ p, •}` are compatible with the inclusions
`Fᵖ⁺¹ ⊆ Fᵖ`. -/
@[reassoc]
lemma ofLE_comp_columnFiltrationPieceIso_hom (p : ℤ) :
    Subobject.ofLE _ _ (K.columnFiltration.F_succ_le p) ≫ (K.columnFiltrationPieceIso p).hom =
    (K.columnFiltrationPieceIso (p + 1)).hom ≫ (K.columnShortComplex p).f := by
  rw [← cancel_mono (K.totalιColumnsGE p), Category.assoc, Category.assoc,
    columnShortComplex_f_comp, columnFiltrationPieceIso_hom_comp,
    columnFiltrationPieceIso_hom_comp, Subobject.ofLE_arrow]

/-- The isomorphisms `Fᵖ Tot K ≅ Tot K^{≥ p, •}` are compatible with the inclusions
`Fᵖ⁺¹ ⊆ Fᵖ`. -/
@[reassoc]
lemma columnShortComplex_f_comp_columnFiltrationPieceIso_inv (p : ℤ) :
    (K.columnShortComplex p).f ≫ (K.columnFiltrationPieceIso p).inv =
      (K.columnFiltrationPieceIso (p + 1)).inv ≫
        Subobject.ofLE _ _ (K.columnFiltration.F_succ_le p) := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← K.ofLE_comp_columnFiltrationPieceIso_hom p,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The morphism from the short exact sequence `0 ⟶ Fᵖ⁺¹ ⟶ Fᵖ ⟶ grᵖ ⟶ 0` of the column
filtration to the short exact sequence `HomologicalComplex₂.columnShortComplex`. It is an
isomorphism. -/
noncomputable def columnFiltrationSesHom (p : ℤ) :
    K.columnFiltration.ses p ⟶ K.columnShortComplex p where
  τ₁ := (K.columnFiltrationPieceIso (p + 1)).hom
  τ₂ := (K.columnFiltrationPieceIso p).hom
  τ₃ := cokernel.desc _ ((K.columnFiltrationPieceIso p).hom ≫ (K.columnShortComplex p).g) (by
    rw [K.ofLE_comp_columnFiltrationPieceIso_hom_assoc, (K.columnShortComplex p).zero,
      comp_zero])
  comm₁₂ := (K.ofLE_comp_columnFiltrationPieceIso_hom p).symm
  comm₂₃ := (cokernel.π_desc _ _ _).symm

/-- The first component of `HomologicalComplex₂.columnFiltrationSesHom`. -/
lemma columnFiltrationSesHom_τ₁ (p : ℤ) :
    (K.columnFiltrationSesHom p).τ₁ = (K.columnFiltrationPieceIso (p + 1)).hom := rfl

/-- The second component of `HomologicalComplex₂.columnFiltrationSesHom`. -/
lemma columnFiltrationSesHom_τ₂ (p : ℤ) :
    (K.columnFiltrationSesHom p).τ₂ = (K.columnFiltrationPieceIso p).hom := rfl


/-- The third component of `HomologicalComplex₂.columnFiltrationSesHom`. -/
@[reassoc (attr := simp)]
lemma π_columnFiltrationSesHom_τ₃ (p : ℤ) :
    cokernel.π _ ≫ (K.columnFiltrationSesHom p).τ₃ =
      (K.columnFiltrationPieceIso p).hom ≫ (K.columnShortComplex p).g :=
  cokernel.π_desc _ _ _

/-- The graded piece `grᵖ Tot K` is isomorphic to the total complex `Tot K^{p, •}` of the
column `p`. -/
lemma isIso_columnFiltrationSesHom_τ₃ (p : ℤ) : IsIso (K.columnFiltrationSesHom p).τ₃ := by
  have hS := K.columnShortComplex_shortExact p
  have : Epi (K.columnShortComplex p).g := hS.epi_g
  let ψ : (K.columnShortComplex p).X₃ ⟶ K.columnFiltration.gr p :=
    hS.gIsCokernel.desc (CokernelCofork.ofπ
    ((K.columnFiltrationPieceIso p).inv ≫ cokernel.π _) (by
      rw [K.columnShortComplex_f_comp_columnFiltrationPieceIso_inv_assoc, cokernel.condition,
        comp_zero]))
  have hψ : (K.columnShortComplex p).g ≫ ψ =
      (K.columnFiltrationPieceIso p).inv ≫ cokernel.π _ :=
    hS.gIsCokernel.fac _ WalkingParallelPair.one
  refine ⟨ψ, ?_, ?_⟩
  · rw [← cancel_epi (cokernel.π (Subobject.ofLE _ _ (K.columnFiltration.F_succ_le p))),
      π_columnFiltrationSesHom_τ₃_assoc, hψ, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · rw [← cancel_epi (K.columnShortComplex p).g, reassoc_of% hψ,
      π_columnFiltrationSesHom_τ₃, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The isomorphism `Hⁿ(grᵖ Tot K) ≅ Hⁿ(Tot K^{p, •})` between the cohomology of the graded
pieces of the column filtration and the cohomology of the total complexes of the columns. -/
noncomputable def columnFiltrationGrHomologyIso (p n : ℤ) :
    (K.columnFiltration.gr p).homology n ≅ (K.columnShortComplex p).X₃.homology n :=
  have := K.isIso_columnFiltrationSesHom_τ₃ p
  asIso (HomologicalComplex.homologyMap (K.columnFiltrationSesHom p).τ₃ n)

/-! ### The cohomology of the total complex of a column -/

omit [K.HasTotal (up ℤ)] in
/-- The differential of the total complex of a double complex concentrated in the column `x`:
it is `(-1)ˣ` times the differential of the column. -/
@[reassoc]
lemma singleColumnObjTotalXIso_inv_d (L : CochainComplex C ℤ) (x y y' n n' : ℤ)
    (hy : y + 1 = y') (h : x + y = n) (h' : x + y' = n') :
    (singleColumnObjTotalXIso L x y n h).inv ≫
        (((singleColumn C (up ℤ) (up ℤ) x).obj L).total (up ℤ)).d n n' =
      x.negOnePow • (L.d y y' ≫ (singleColumnObjTotalXIso L x y' n' h').inv) := by
  rw [singleColumnObjTotalXIso_inv, Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
    singleColumn_d₁, zero_add, singleColumn_d₂ _ _ _ _ _ _ y y' hy n' h',
    singleColumnObjTotalXIso_inv]
  simp

omit [K.HasTotal (up ℤ)] in
/-- The identification `(Tot L^{p, •})ⁿ ≅ L^q` intertwines the incoming differentials up to
the sign `(-1)ᵖ`. -/
lemma singleColumnObjTotalXIso_comm₁ (L : CochainComplex C ℤ) (p q n : ℤ) (hn : p + q = n) :
    (p.negOnePow • (singleColumnObjTotalXIso L p (q - 1) (n - 1) (by omega)).hom) ≫
        L.d (q - 1) q =
      (((singleColumn C (up ℤ) (up ℤ) p).obj L).total (up ℤ)).d (n - 1) n ≫
        (singleColumnObjTotalXIso L p q n hn).hom := by
  rw [← cancel_epi (singleColumnObjTotalXIso L p (q - 1) (n - 1) (by omega)).inv,
    singleColumnObjTotalXIso_inv_d_assoc L p (q - 1) q (n - 1) n (by omega) (by omega) hn]
  simp

omit [K.HasTotal (up ℤ)] in
/-- The identification `(Tot L^{p, •})ⁿ ≅ L^q` intertwines the outgoing differentials up to
the sign `(-1)ᵖ`. -/
lemma singleColumnObjTotalXIso_comm₂ (L : CochainComplex C ℤ) (p q n : ℤ) (hn : p + q = n) :
    (singleColumnObjTotalXIso L p q n hn).hom ≫ L.d q (q + 1) =
      (((singleColumn C (up ℤ) (up ℤ) p).obj L).total (up ℤ)).d n (n + 1) ≫
        (p.negOnePow • (singleColumnObjTotalXIso L p (q + 1) (n + 1) (by omega)).hom) := by
  rw [← cancel_epi (singleColumnObjTotalXIso L p q n hn).inv,
    singleColumnObjTotalXIso_inv_d_assoc L p q (q + 1) n (n + 1) rfl hn (by omega)]
  simp [smul_smul, Int.units_mul_self]

omit [K.HasTotal (up ℤ)] in
/-- The isomorphism `Hⁿ(Tot L^{p, •}) ≅ H^q(L)` for `p + q = n`, where `L^{p, •}` is the double
complex concentrated in the column `p` given by a cochain complex `L`. On cocycles, it is induced
by the identification `(Tot L^{p, •})ⁿ ≅ L^q` (without sign). -/
noncomputable def singleColumnTotalHomologyIso (L : CochainComplex C ℤ) (p q n : ℤ)
    (hn : p + q = n) :
    (((singleColumn C (up ℤ) (up ℤ) p).obj L).total (up ℤ)).homology n ≅ L.homology q :=
  HomologicalComplex.homologyIsoSc' _ (n - 1) n (n + 1) (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (ShortComplex.isoMk
      ((singleColumnObjTotalXIso L p (q - 1) (n - 1) (by omega)).unitsSMul p.negOnePow)
      (singleColumnObjTotalXIso L p q n hn)
      ((singleColumnObjTotalXIso L p (q + 1) (n + 1) (by omega)).unitsSMul p.negOnePow)
      (singleColumnObjTotalXIso_comm₁ L p q n hn) (singleColumnObjTotalXIso_comm₂ L p q n hn)) ≪≫
    (L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).symm

omit [K.HasTotal (up ℤ)] in
/-- `HomologicalComplex₂.singleColumnTotalHomologyIso` sends the class of a cocycle `x` of
`Tot L^{p, •}` to the class of the corresponding cocycle of `L`. -/
@[reassoc]
lemma liftCycles_singleColumnTotalHomologyIso_hom (L : CochainComplex C ℤ) (p q n : ℤ)
    (hn : p + q = n) {A : C} (x : A ⟶ L.X q) (hx : x ≫ L.d q (q + 1) = 0) :
    (((singleColumn C (up ℤ) (up ℤ) p).obj L).total (up ℤ)).liftCycles
        (x ≫ (singleColumnObjTotalXIso L p q n hn).inv) (n + 1) (by simp) (by
          rw [Category.assoc, singleColumnObjTotalXIso_inv_d L p q (q + 1) n (n + 1) rfl hn
            (by omega), Linear.comp_units_smul, reassoc_of% hx, zero_comp, smul_zero]) ≫
      (((singleColumn C (up ℤ) (up ℤ) p).obj L).total (up ℤ)).homologyπ n ≫
        (singleColumnTotalHomologyIso L p q n hn).hom =
      L.liftCycles x (q + 1) (by simp) hx ≫ L.homologyπ q := by
  simp only [singleColumnTotalHomologyIso, Iso.trans_hom, Iso.symm_hom,
    ShortComplex.homologyMapIso_hom, HomologicalComplex.π_homologyIsoSc'_hom_assoc,
    ShortComplex.homologyπ_naturality_assoc, HomologicalComplex.π_homologyIsoSc'_inv]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles q)]
  simp

/-! ### The `E₁`-page and the differential `d₁` -/

/-- The connecting homomorphism of the short exact sequence
`0 ⟶ Tot K^{≥ p + 1, •} ⟶ Tot K^{≥ p, •} ⟶ Tot K^{p, •} ⟶ 0`, followed by the projection to
`Tot K^{p + 1, •}`, is the morphism `H^q(K^{p, •}) ⟶ H^q(K^{p + 1, •})` induced by the
horizontal differential, under the identifications `Hⁿ(Tot K^{p, •}) ≅ H^{n - p}(K^{p, •})`. -/
lemma columnShortComplex_δ (p q n : ℤ) (hn : p + q = n) :
    (singleColumnTotalHomologyIso (K.X p) p q n hn).inv ≫
      (K.columnShortComplex_shortExact p).δ n (n + 1) rfl ≫
        HomologicalComplex.homologyMap (K.columnShortComplex (p + 1)).g (n + 1) ≫
          (singleColumnTotalHomologyIso (K.X (p + 1)) (p + 1) q (n + 1) (by omega)).hom =
      HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
  rw [← cancel_epi ((K.X p).homologyπ q)]
  have hπ : (K.X p).homologyπ q = (K.X p).liftCycles ((K.X p).iCycles q) (q + 1) (by simp)
      (by simp) ≫ (K.X p).homologyπ q := by
    have hl : (K.X p).liftCycles ((K.X p).iCycles q) (q + 1) (by simp) (by simp) = 𝟙 _ := by
      rw [← cancel_mono ((K.X p).iCycles q)]
      simp
    rw [hl, Category.id_comp]
  have := K.isIso_ιColumnsGE_f_f p p q le_rfl
  have := K.isIso_ιColumnsGE_f_f (p + 1) (p + 1) q le_rfl
  let x := (K.X p).iCycles q
  let x₃ := x ≫ (singleColumnObjTotalXIso (K.X p) p q n hn).inv
  let x₂ := x ≫ inv (((K.ιColumnsGE p).f p).f q) ≫ (K.columnsGE p).ιTotal (up ℤ) p q n hn
  let x₁ := x ≫ (K.d p (p + 1)).f q ≫ inv (((K.ιColumnsGE (p + 1)).f (p + 1)).f q) ≫
    (K.columnsGE (p + 1)).ιTotal (up ℤ) (p + 1) q (n + 1) (show p + 1 + q = n + 1 by omega)
  have hx₂ : x₂ ≫ (K.columnShortComplex p).g.f n = x₃ := by
    simp [x₂, x₃, ιTotal_columnShortComplex_g, singleColumnObjTotalXIso_inv]
  have hx₁ : x₁ ≫ (K.columnShortComplex p).f.f (n + 1) =
      x₂ ≫ (K.columnShortComplex p).X₂.d n (n + 1) := by
    have e₁ : x₁ ≫ (K.columnShortComplex p).f.f (n + 1) ≫ (K.totalιColumnsGE p).f (n + 1) =
        x ≫ (K.d p (p + 1)).f q ≫ K.ιTotal (up ℤ) (p + 1) q (n + 1)
          (show p + 1 + q = n + 1 by omega) := by
      rw [← HomologicalComplex.comp_f, columnShortComplex_f_comp]
      simp [x₁]
    have e₂ : x₂ ≫ (K.columnShortComplex p).X₂.d n (n + 1) ≫ (K.totalιColumnsGE p).f (n + 1) =
        x ≫ (K.d p (p + 1)).f q ≫ K.ιTotal (up ℤ) (p + 1) q (n + 1)
          (show p + 1 + q = n + 1 by omega) := by
      erw [← (K.totalιColumnsGE p).comm n (n + 1)]
      simp only [x₂, Category.assoc, ιTotal_totalιColumnsGE_assoc, IsIso.inv_hom_id_assoc,
        total_d, Preadditive.comp_add, ι_D₁, ι_D₂]
      rw [d₁_eq _ _ (by simp) _ _ (show p + 1 + q = n + 1 by omega),
        d₂_eq _ _ _ (by simp) _ (show p + (q + 1) = n + 1 by omega)]
      simp [x]
    rw [← cancel_mono ((K.totalιColumnsGE p).f (n + 1))]
    exact (Category.assoc _ _ _).trans ((e₁.trans e₂.symm).trans (Category.assoc _ _ _).symm)
  have hδ := (K.columnShortComplex_shortExact p).δ_eq n (n + 1) rfl x₃ (by
      simp only [x₃, Category.assoc]
      erw [singleColumnObjTotalXIso_inv_d (K.X p) p q (q + 1) n (n + 1) rfl hn (by omega)]
      simp [x]) x₂ hx₂ x₁ hx₁ (n + 2) (by
        simp
        omega)
  have hx₁' : x₁ ≫ (K.columnShortComplex (p + 1)).g.f (n + 1) =
      (x ≫ (K.d p (p + 1)).f q) ≫ (singleColumnObjTotalXIso (K.X (p + 1)) (p + 1) q (n + 1)
        (by omega)).inv := by
    simp [x₁, ιTotal_columnShortComplex_g, singleColumnObjTotalXIso_inv]
  have hΘ : (K.X p).homologyπ q ≫ (singleColumnTotalHomologyIso (K.X p) p q n hn).inv =
      (K.columnShortComplex p).X₃.liftCycles x₃ (n + 1) (by simp) (by
        simp only [x₃, Category.assoc]
        erw [singleColumnObjTotalXIso_inv_d (K.X p) p q (q + 1) n (n + 1) rfl hn (by omega)]
        simp [x]) ≫ (K.columnShortComplex p).X₃.homologyπ n := by
    rw [Iso.comp_inv_eq, Category.assoc]
    exact hπ.trans (liftCycles_singleColumnTotalHomologyIso_hom (K.X p) p q n hn x
      (by simp [x])).symm
  rw [reassoc_of% hΘ, reassoc_of% hδ, HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  rw [hπ, Category.assoc ((K.X p).liftCycles ((K.X p).iCycles q) (q + 1) (by simp) (by simp)),
    HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc,
    ← liftCycles_singleColumnTotalHomologyIso_hom (K.X (p + 1)) (p + 1) q (n + 1) (by omega)
      ((K.X p).iCycles q ≫ (K.d p (p + 1)).f q) (by simp)]
  congr 1
  rw [← cancel_mono (HomologicalComplex.iCycles _ _), HomologicalComplex.liftCycles_i]
  erw [HomologicalComplex.liftCycles_i]
  simpa using hx₁'

/-- The identification `E₁^{p, n} = Hⁿ(grᵖ Tot K) ≅ H^q(K^{p, •})` for `p + q = n` of the
`E₁`-terms of the spectral sequence of the column filtration with the vertical cohomology of
`K`. -/
noncomputable def columnFiltrationE₁Iso (p q n : ℤ) (hn : p + q = n) :
    K.columnFiltration.exactCouple.E (p, n) ≅ (K.X p).homology q :=
  K.columnFiltrationGrHomologyIso p n ≪≫ singleColumnTotalHomologyIso (K.X p) p q n hn

/-- **The differential `d₁` of the first spectral sequence of a double complex.** Under the
identifications `E₁^{p, p + q} ≅ H^q(K^{p, •})`, the differential
`d₁ : E₁^{p, p + q} ⟶ E₁^{p + 1, p + q + 1}` of the spectral sequence of the column filtration
is the morphism `H^q(K^{p, •}) ⟶ H^q(K^{p + 1, •})` induced by the horizontal differential `d_I`.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem columnFiltrationE₁Iso_d (p q n n' : ℤ) (hn : p + q = n) (hn' : p + 1 + q = n') :
    (K.columnFiltrationE₁Iso p q n hn).inv ≫ K.columnFiltration.exactCouple.d (p, n) (p + 1, n') ≫
      (K.columnFiltrationE₁Iso (p + 1) q n' hn').hom =
      HomologicalComplex.homologyMap (K.d p (p + 1)) q := by
  obtain rfl : n' = n + 1 := by omega
  have := K.isIso_columnFiltrationSesHom_τ₃ p
  have h₁ := HomologicalComplex.HomologySequence.δ_naturality (K.columnFiltrationSesHom p)
    (K.columnFiltration.ses_shortExact p) (K.columnShortComplex_shortExact p) n (n + 1) rfl
  have h₂ : HomologicalComplex.homologyMap (cokernel.π _) (n + 1) ≫
      HomologicalComplex.homologyMap (K.columnFiltrationSesHom (p + 1)).τ₃ (n + 1) =
      HomologicalComplex.homologyMap (K.columnFiltrationSesHom p).τ₁ (n + 1) ≫
        HomologicalComplex.homologyMap (K.columnShortComplex (p + 1)).g (n + 1) := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact (K.columnFiltrationSesHom (p + 1)).comm₂₃.symm
  rw [DecreasingFiltration.exactCouple_d]
  simp only [columnFiltrationE₁Iso, columnFiltrationGrHomologyIso, Iso.trans_inv, Iso.trans_hom,
    asIso_inv, asIso_hom, Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% h₁, IsIso.inv_hom_id_assoc]
  exact K.columnShortComplex_δ p q n hn

/-- A variant of `HomologicalComplex₂.columnFiltrationE₁Iso_d` with arbitrary indices. -/
lemma columnFiltrationE₁Iso_d' (p p' q n n' : ℤ) (hp : p + 1 = p') (hn : p + q = n)
    (hn' : p' + q = n') :
    (K.columnFiltrationE₁Iso p q n hn).inv ≫ K.columnFiltration.exactCouple.d (p, n) (p', n') ≫
      (K.columnFiltrationE₁Iso p' q n' hn').hom =
      HomologicalComplex.homologyMap (K.d p p') q := by
  subst hp
  exact K.columnFiltrationE₁Iso_d p q n n' hn hn'

/-! ### Convergence for first quadrant double complexes -/

section

variable {ι₁ ι₂ ι : Type*} [DecidableEq ι] {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}
  {c : ComplexShape ι} [TotalComplexShape c₁ c₂ c]

/-- A morphism of double complexes induces an isomorphism in degree `n` of the total complexes
if its components in total degree `n` are isomorphisms. -/
lemma isIso_total_map_f {L M : HomologicalComplex₂ C c₁ c₂} [L.HasTotal c] [M.HasTotal c]
    (φ : L ⟶ M) (n : ι) (h : ∀ x y, ComplexShape.π c₁ c₂ c (x, y) = n → IsIso ((φ.f x).f y)) :
    IsIso ((total.map φ c).f n) := by
  refine ⟨M.totalDesc (fun x y hxy ↦ (have := h x y hxy; inv ((φ.f x).f y)) ≫
    L.ιTotal c x y n hxy), ?_, ?_⟩
  · ext x y hxy
    have := h x y hxy
    simp
  · ext x y hxy
    have := h x y hxy
    simp

/-- The object of degree `n` of a total complex vanishes if all the objects of total degree `n`
of the double complex vanish. -/
lemma isZero_total_X (L : HomologicalComplex₂ C c₁ c₂) [L.HasTotal c] (n : ι)
    (h : ∀ x y, ComplexShape.π c₁ c₂ c (x, y) = n → IsZero ((L.X x).X y)) :
    IsZero ((L.total c).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext x y hxy
  exact (h x y hxy).eq_of_src _ _

end

variable {K} (hK : ∀ x y : ℤ, x < 0 ∨ y < 0 → IsZero ((K.X x).X y))
include hK

/-- For a first quadrant double complex, `Tot K^{≥ p, •} ⟶ Tot K` is an isomorphism if
`p ≤ 0`. -/
lemma isIso_totalιColumnsGE_f (p n : ℤ) (hp : p ≤ 0) : IsIso ((K.totalιColumnsGE p).f n) := by
  refine isIso_total_map_f _ n (fun x y _ ↦ ?_)
  by_cases hx : p ≤ x
  · exact K.isIso_ιColumnsGE_f_f p x y hx
  · exact ⟨0, (K.isZero_columnsGE_X_X p x y (by omega)).eq_of_src _ _,
      (hK x y (by omega)).eq_of_src _ _⟩

/-- For a first quadrant double complex, `Fᵖ Tot K = Tot K` if `p ≤ 0`. -/
lemma isIso_columnFiltration_arrow_f (p n : ℤ) (hp : p ≤ 0) :
    IsIso ((K.columnFiltration.F p).arrow.f n) := by
  have := K.isIso_totalιColumnsGE_f hK p n hp
  rw [← K.columnFiltrationPieceIso_hom_comp, HomologicalComplex.comp_f]
  infer_instance

/-- For a first quadrant double complex, `Fᵖ (Tot K)ⁿ = 0` if `p > n`. -/
lemma isZero_columnFiltration_piece_X (p n : ℤ) (hp : n < p) :
    IsZero ((K.columnFiltration.piece p).X n) := by
  refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ n).mapIso (K.columnFiltrationPieceIso p))
  refine isZero_total_X _ n (fun x y hxy ↦ ?_)
  replace hxy : x + y = n := hxy
  by_cases hx : p ≤ x
  · have := K.isIso_ιColumnsGE_f_f p x y hx
    exact (hK x y (by omega)).of_iso (asIso (((K.ιColumnsGE p).f x).f y))
  · exact K.isZero_columnsGE_X_X p x y (by omega)

/-- **Convergence of the first spectral sequence of a first quadrant double complex.** The
spectral sequence of the column filtration of the total complex of a double complex `K`
concentrated in the first quadrant converges to the cohomology of `Tot K`, with the filtration
`Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K) ⟶ Hⁿ(Tot K))`.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem columnFiltration_convergesTo :
    K.columnFiltration.exactCouple.ConvergesTo K.columnFiltration.toHomology
      K.columnFiltration.homologyFiltration :=
  K.columnFiltration.convergesTo_exactCouple
    (fun n ↦ ⟨0, fun p hp ↦ K.isIso_columnFiltration_arrow_f hK p n hp⟩)
    (fun n ↦ ⟨n + 1, fun p hp ↦ K.isZero_columnFiltration_piece_X hK p n (by omega)⟩)

/-- For a first quadrant double complex, `F⁰ Hⁿ(Tot K) = Hⁿ(Tot K)`. -/
lemma columnFiltration_homologyFiltration_F_zero (n : ℤ) :
    (K.columnFiltration.homologyFiltration n).F 0 = ⊤ := by
  have : IsIso (K.columnFiltration.toHomology 0 n) :=
    DecreasingFiltration.isIso_homologyMap_of_isIso_f _ n
      (K.isIso_columnFiltration_arrow_f hK 0 _ le_rfl)
      (K.isIso_columnFiltration_arrow_f hK 0 _ le_rfl)
      (K.isIso_columnFiltration_arrow_f hK 0 _ le_rfl)
  dsimp only [DecreasingFiltration.homologyFiltration, ExactCouple.abutmentFiltration]
  rw [imageSubobject_mono]
  exact Subobject.mk_eq_top_of_isIso _

/-- For a first quadrant double complex, `Fⁿ⁺¹ Hⁿ(Tot K) = 0`. -/
lemma columnFiltration_homologyFiltration_F_succ (n : ℤ) :
    (K.columnFiltration.homologyFiltration n).F (n + 1) = ⊥ := by
  have : K.columnFiltration.toHomology (n + 1) n = 0 :=
    (ShortComplex.isZero_homology_of_isZero_X₂ _
      (K.isZero_columnFiltration_piece_X hK (n + 1) n (by omega))).eq_of_src _ _
  dsimp only [DecreasingFiltration.homologyFiltration, ExactCouple.abutmentFiltration]
  simp only [this, imageSubobject_zero]

/-- For a first quadrant double complex, the `E₁`-terms `E₁^{p, n}` of the column filtration
vanish unless `0 ≤ p ≤ n`. -/
lemma isZero_columnFiltration_exactCouple_E (i : ℤ × ℤ) (hi : i.1 < 0 ∨ i.2 < i.1) :
    IsZero (K.columnFiltration.exactCouple.E i) :=
  (ShortComplex.isZero_homology_of_isZero_X₂ _ (hK i.1 (i.2 - i.1) (by omega))).of_iso
    (K.columnFiltrationE₁Iso i.1 (i.2 - i.1) i.2 (by omega))

end HomologicalComplex₂
