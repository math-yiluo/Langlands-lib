/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import WeilConjectures.Algebra.Homology.ExactCouple.FirstQuadrant
public import WeilConjectures.Algebra.Homology.ExactCouple.TotalComplexFiltration
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Ring.NegOnePow

/-!
# The spectral sequences of a first quadrant double complex

Let `K` be a first quadrant double complex in an abelian category, that is a
`HomologicalComplex₂ C (up ℕ) (up ℕ)`. Extending `K` by zero to a double complex indexed by
`ℤ × ℤ` (`HomologicalComplex₂.extendNat`), the column filtration of its total complex
(`HomologicalComplex₂.columnFiltration`) gives an exact couple whose spectral sequence, from the
`E₂`-page on, is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ H^p_I H^q_{II}(K)`, abutting to the cohomology of the total complex of `K`
(`HomologicalComplex₂.exists_spectralSequence`). Applying this to the transposed double complex
gives the second spectral sequence, with `E₂^{q, p} ≅ H^q_{II} H^p_I(K)`
(`HomologicalComplex₂.exists_spectralSequence_flip`).

## Main definitions

- `HomologicalComplex₂.extendNat`: the extension by zero of a first quadrant double complex.
- `HomologicalComplex₂.firstSpectralSequence`: the first spectral sequence of a first quadrant
  double complex.

## Main statements

- `HomologicalComplex₂.exists_spectralSequence`: the first spectral sequence.
- `HomologicalComplex₂.exists_spectralSequence_flip`: the second spectral sequence.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type*} [Category C] [Abelian C]
  (K : HomologicalComplex₂ C (up ℕ) (up ℕ))

/-- The extension by zero of a double complex indexed by `ℕ × ℕ` to a double complex indexed
by `ℤ × ℤ`. -/
noncomputable def extendNat : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K).extend embeddingUpNat

/-- The columns of `K.extendNat` are the extensions of the columns of `K`. -/
noncomputable def extendNatXIso (i : ℕ) :
    K.extendNat.X i ≅ (K.X i).extend embeddingUpNat :=
  (((embeddingUpNat.extendFunctor C).mapHomologicalComplex (up ℕ)).obj K).extendXIso
    embeddingUpNat rfl

/-- The objects of `K.extendNat` in the first quadrant are those of `K`. -/
noncomputable def extendNatXXIso (i j : ℕ) : (K.extendNat.X i).X j ≅ (K.X i).X j :=
  (HomologicalComplex.eval _ _ (j : ℤ)).mapIso (K.extendNatXIso i) ≪≫
    (K.X i).extendXIso embeddingUpNat rfl

/-- The columns of negative index of `K.extendNat` vanish. -/
lemma isZero_extendNat_X (x : ℤ) (hx : x < 0) : IsZero (K.extendNat.X x) :=
  HomologicalComplex.isZero_extend_X _ _ _ (fun i hi ↦ by
    simp at hi
    omega)

/-- `K.extendNat` is concentrated in the first quadrant. -/
lemma isZero_extendNat_X_X (x y : ℤ) (h : x < 0 ∨ y < 0) : IsZero ((K.extendNat.X x).X y) := by
  obtain hx | hy := h
  · exact (HomologicalComplex.eval _ _ y).map_isZero (K.isZero_extendNat_X x hx)
  · by_cases hx : x < 0
    · exact (HomologicalComplex.eval _ _ y).map_isZero (K.isZero_extendNat_X x hx)
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hx)
      exact ((HomologicalComplex.isZero_extend_X _ _ _ (fun j hj ↦ by
        simp at hj
        omega)).of_iso
        ((HomologicalComplex.eval _ _ y).mapIso (K.extendNatXIso i)))

/-- The horizontal differentials of `K.extendNat` are the extensions of those of `K`. -/
lemma extendNat_d (i i' : ℕ) :
    K.extendNat.d i i' = (K.extendNatXIso i).hom ≫
      HomologicalComplex.extendMap (K.d i i') embeddingUpNat ≫ (K.extendNatXIso i').inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

/-- The identifications `(K.extendNat)^{i, j} ≅ K^{i, j}` are compatible with the horizontal
differentials. -/
@[reassoc]
lemma extendNatXXIso_inv_d_f (i i' j : ℕ) :
    (K.extendNatXXIso i j).inv ≫ (K.extendNat.d i i').f j =
      (K.d i i').f j ≫ (K.extendNatXXIso i' j).inv := by
  have : (K.extendNatXIso i).inv.f j ≫ (K.extendNatXIso i).hom.f j = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]
  simp [reassoc_of% this, extendNatXXIso, extendNat_d, HomologicalComplex.extendMap_f _ _ (show
    embeddingUpNat.f j = (j : ℤ) from rfl)]

/-- The identifications `(K.extendNat)^{i, j} ≅ K^{i, j}` are compatible with the vertical
differentials. -/
@[reassoc]
lemma extendNatXXIso_inv_X_d (i j j' : ℕ) :
    (K.extendNatXXIso i j).inv ≫ (K.extendNat.X i).d j j' =
      (K.X i).d j j' ≫ (K.extendNatXXIso i j').inv := by
  simp [extendNatXXIso, HomologicalComplex.extend_d_eq _ _ (show
    embeddingUpNat.f j = (j : ℤ) from rfl) (show embeddingUpNat.f j' = (j' : ℤ) from rfl)]

/-- `K.extendNat` has a total complex: in each total degree only finitely many of its objects are
nonzero. -/
instance : K.extendNat.HasTotal (up ℤ) := fun n ↦
  hasCoproduct_of_isZero (J := Fin (n.toNat + 1))
    (ι := fun k ↦ ⟨⟨k, n - k⟩, by simp⟩) _ (fun k k' h ↦ by
      ext
      simpa using congrArg (fun x ↦ x.1.1) h) (by
      rintro ⟨⟨x, y⟩, hxy : x + y = n⟩ h
      by_cases hx : 0 ≤ x
      · by_cases hy : 0 ≤ y
        · exact (h ⟨⟨x.toNat, by omega⟩, by ext <;> simp <;> omega⟩).elim
        · exact K.isZero_extendNat_X_X x y (by omega)
      · exact K.isZero_extendNat_X_X x y (by omega))

/-! ### The total complex of `K.extendNat` -/

/-- The components of the inverse of `HomologicalComplex₂.totalExtendNatXIso`. -/
noncomputable def totalExtendNatXInv (m : ℕ) :
    (x y : ℤ) → x + y = m → ((K.extendNat.X x).X y ⟶ (K.total (up ℕ)).X m)
  | .ofNat i, .ofNat j, h => (K.extendNatXXIso i j).hom ≫ K.ιTotal (up ℕ) i j m (by
      simp only [Int.ofNat_eq_natCast] at h
      exact (by omega : i + j = m))
  | _, _, _ => 0

/-- The components of the inverse of `HomologicalComplex₂.totalExtendNatXIso` in the first
quadrant. -/
lemma totalExtendNatXInv_natCast (m i j : ℕ) (h : (i : ℤ) + j = m) :
    K.totalExtendNatXInv m i j h = (K.extendNatXXIso i j).hom ≫ K.ιTotal (up ℕ) i j m (by
      exact (by omega : i + j = m)) :=
  rfl

/-- The objects of the total complex of `K.extendNat` in nonnegative degrees are those of the
total complex of `K`. -/
noncomputable def totalExtendNatXIso (m : ℕ) :
    (K.total (up ℕ)).X m ≅ (K.extendNat.total (up ℤ)).X m where
  hom := K.totalDesc (fun i j h ↦ (K.extendNatXXIso i j).inv ≫
    K.extendNat.ιTotal (up ℤ) i j m (by
      replace h : i + j = m := h
      exact (by omega : (i : ℤ) + j = m)))
  inv := K.extendNat.totalDesc (fun x y h ↦ K.totalExtendNatXInv m x y h)
  hom_inv_id := by
    ext i j h
    simp [totalExtendNatXInv_natCast]
  inv_hom_id := by
    ext x y h
    replace h : x + y = m := h
    by_cases hxy : 0 ≤ x ∧ 0 ≤ y
    · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le hxy.1
      obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hxy.2
      simp [totalExtendNatXInv_natCast]
    · exact (K.isZero_extendNat_X_X x y (by omega)).eq_of_src _ _

/-- `HomologicalComplex₂.totalExtendNatXIso` on the summands. -/
@[reassoc (attr := simp)]
lemma ιTotal_totalExtendNatXIso_hom (i j m : ℕ) (h : i + j = m) :
    K.ιTotal (up ℕ) i j m h ≫ (K.totalExtendNatXIso m).hom =
      (K.extendNatXXIso i j).inv ≫ K.extendNat.ιTotal (up ℤ) i j m (by
        exact (by omega : (i : ℤ) + j = m)) := by
  simp [totalExtendNatXIso]

/-- The cohomology of the total complex of `K.extendNat` in degree `n ≥ 0` is the cohomology of
the total complex of `K`. -/
noncomputable def totalExtendNatHomologyIso (n : ℕ) :
    (K.extendNat.total (up ℤ)).homology n ≅ (K.total (up ℕ)).homology n :=
  (HomologicalComplex.homologyIsoOfComponents (K.extendNat.total (up ℤ)) (K.total (up ℕ))
    (fun m : ℕ ↦ (m : ℤ)) K.totalExtendNatXIso (by
      rintro k _ rfl
      ext i j h
      replace h : i + j = k := h
      simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
        ιTotal_totalExtendNatXIso_hom_assoc, ι_D₁, ι_D₂]
      rw [d₁_eq _ _ (show (up ℕ).Rel i (i + 1) from rfl) _ _ (show i + 1 + j = k + 1 by omega),
        d₂_eq _ _ _ (show (up ℕ).Rel j (j + 1) from rfl) _ (show i + (j + 1) = k + 1 by omega),
        d₁_eq _ _ (show (up ℤ).Rel (i : ℤ) ((i + 1 : ℕ) : ℤ) by simp) _ _
          (show ((i + 1 : ℕ) : ℤ) + j = (k + 1 : ℕ) by omega),
        d₂_eq _ _ _ (show (up ℤ).Rel (j : ℤ) ((j + 1 : ℕ) : ℤ) by simp) _
          (show (i : ℤ) + ((j + 1 : ℕ) : ℤ) = (k + 1 : ℕ) by omega)]
      simp only [Linear.comp_units_smul, Linear.units_smul_comp,
        extendNatXXIso_inv_d_f_assoc, extendNatXXIso_inv_X_d_assoc]
      simp [Int.negOnePow_natCast_eq_pow])
    (by
      rintro k _ rfl
      simp) n
    (fun h ↦ by
      cases n with
      | zero =>
        refine isZero_total_X _ _ (fun x y hxy ↦ K.isZero_extendNat_X_X x y ?_)
        replace hxy : x + y = (up ℤ).prev ((0 : ℕ) : ℤ) := hxy
        simp at hxy
        omega
      | succ k => exact (h (by simp)).elim)
    (fun h ↦ (h (by simp)).elim)).symm

/-! ### The `E₂`-page -/

/-- The vertical cohomology of the columns of `K.extendNat` is that of `K`. -/
noncomputable def extendNatXHomologyIso (p q : ℕ) :
    (K.extendNat.X p).homology q ≅ (K.X p).homology q :=
  HomologicalComplex.homologyMapIso (K.extendNatXIso p) q ≪≫
    (K.X p).extendHomologyIso embeddingUpNat (rfl : embeddingUpNat.f q = (q : ℤ))

/-- The identifications `H^q((K.extendNat)^{p, •}) ≅ H^q(K^{p, •})` are compatible with the
horizontal differentials. -/
@[reassoc]
lemma extendNatXHomologyIso_inv_naturality (p p' q : ℕ) :
    (K.extendNatXHomologyIso p q).inv ≫ HomologicalComplex.homologyMap (K.extendNat.d p p') q =
      HomologicalComplex.homologyMap (K.d p p') q ≫ (K.extendNatXHomologyIso p' q).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  simp only [extendNatXHomologyIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
    extendNat_d, HomologicalComplex.homologyMap_comp, Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp_assoc (K.extendNatXIso p').inv, Iso.inv_hom_id,
    HomologicalComplex.homologyMap_id, Category.id_comp]
  exact congrArg (HomologicalComplex.homologyMap (K.extendNatXIso p).hom q ≫ ·)
    (HomologicalComplex.extendHomologyIso_hom_naturality (K.d p p') embeddingUpNat
      (rfl : embeddingUpNat.f q = (q : ℤ)))

/-- The `E₁`-terms of the column filtration of `K.extendNat` vanish outside the first
quadrant. -/
lemma isZero_extendNat_columnFiltration_E (i : ℤ × ℤ) (hi : i.1 < 0 ∨ i.2 < i.1) :
    IsZero (K.extendNat.columnFiltration.exactCouple.E i) :=
  isZero_columnFiltration_exactCouple_E K.isZero_extendNat_X_X i hi

/-- The exact couple of the column filtration of `K.extendNat` is first quadrant. -/
lemma extendNat_columnFiltration_isFirstQuadrant :
    K.extendNat.columnFiltration.exactCouple.IsFirstQuadrant :=
  K.isZero_extendNat_columnFiltration_E

/-- The differentials `d₁` of the first spectral sequence, under the identifications
`E₁^{k, k + q} ≅ H^q(K^{k, •})`, are induced by the horizontal differentials of `K`. -/
lemma homologyMap_d_comp_E₁Iso_inv (k q : ℕ) :
    HomologicalComplex.homologyMap (K.d k (k + 1)) q ≫
      (K.extendNat.columnFiltrationE₁Iso ((k + 1 : ℕ) : ℤ) q _ rfl ≪≫
        K.extendNatXHomologyIso (k + 1) q).inv =
    (K.extendNat.columnFiltrationE₁Iso (k : ℤ) q _ rfl ≪≫ K.extendNatXHomologyIso k q).inv ≫
      K.extendNat.columnFiltration.exactCouple.d ((k : ℤ), (k : ℤ) + q)
        (((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ) + q) := by
  rw [Iso.trans_inv, Iso.trans_inv, ← K.extendNatXHomologyIso_inv_naturality_assoc,
    ← K.extendNat.columnFiltrationE₁Iso_d' (k : ℤ) ((k + 1 : ℕ) : ℤ) q _ _ (by omega) rfl rfl,
    Category.assoc, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **The first spectral sequence of a first quadrant double complex** `K`: the spectral
sequence, from the `E₂`-page on, of the filtration by the columns of the total complex of `K`
(extended by zero to `ℤ × ℤ`).

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
noncomputable def firstSpectralSequence : E₂CohomologicalSpectralSequenceNat C :=
  K.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequence
    K.extendNat_columnFiltration_isFirstQuadrant

/-- The `E₂`-term of the first spectral sequence of a first quadrant double complex:
`E₂^{p, q} ≅ H^p_I H^q_{II}(K)`, the `p`-th cohomology of the complex `p ↦ H^q(K^{p, •})` whose
differential is induced by the horizontal differential of `K`.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
noncomputable def firstSpectralSequencePageTwoIso (p q : ℕ) :
    (K.firstSpectralSequence.page 2).X (p, q) ≅
      (((HomologicalComplex.homologyFunctor C (up ℕ) q).mapHomologicalComplex
        (up ℕ)).obj K).homology p :=
  (HomologicalComplex.homologyIsoOfComponents K.extendNat.columnFiltration.exactCouple.dComplex
    (((HomologicalComplex.homologyFunctor C (up ℕ) q).mapHomologicalComplex (up ℕ)).obj K)
    (fun p : ℕ ↦ ((p : ℤ), (p : ℤ) + q))
    (fun p ↦ (K.extendNat.columnFiltrationE₁Iso p q _ rfl ≪≫ K.extendNatXHomologyIso p q).symm)
    (by
      rintro k _ rfl
      exact K.homologyMap_d_comp_E₁Iso_inv k q)
    (by
      rintro k _ rfl
      refine Prod.ext ?_ ?_
      · simp
      · simp
        omega) p
    (fun h ↦ by
      rw [ExactCouple.dComplex_prev]
      apply K.isZero_extendNat_columnFiltration_E
      cases p with
      | zero => simp
      | succ k => exact (h (by simp)).elim)
    (fun h ↦ (h (by simp)).elim)).symm

/-- The first spectral sequence of a first quadrant double complex `K` abuts to the cohomology
of the total complex of `K`, with the filtration induced by the column filtration.

(blueprint: `thm-sp-double-complex-spectral-sequences`, `det-def-groth-ss`) -/
lemma firstSpectralSequence_abutsTo :
    K.firstSpectralSequence.AbutsTo fun n ↦ (K.total (up ℕ)).homology n :=
  (K.extendNat.columnFiltration.exactCouple.firstQuadrantSpectralSequence_abutsTo
    K.extendNat_columnFiltration_isFirstQuadrant
    (columnFiltration_convergesTo K.isZero_extendNat_X_X)
    (fun n ↦ columnFiltration_homologyFiltration_F_zero K.isZero_extendNat_X_X n)
    (fun n ↦ columnFiltration_homologyFiltration_F_succ K.isZero_extendNat_X_X n)).of_iso
    K.totalExtendNatHomologyIso

/-- If `e : Y ≅ Z`, the image of the subobject `im f ⊆ Y` under `e` is `im (f ≫ e)`. -/
lemma _root_.CategoryTheory.Limits.mk_imageSubobject_arrow_comp_iso {X Y Z : C}
    (f : X ⟶ Y) (e : Y ≅ Z) :
    Subobject.mk ((imageSubobject f).arrow ≫ e.hom) = imageSubobject (f ≫ e.hom) := by
  have h := imageSubobject_comp_eq_of_epi (factorThruImageSubobject f)
    ((imageSubobject f).arrow ≫ e.hom)
  rw [imageSubobject_mono ((imageSubobject f).arrow ≫ e.hom)] at h
  rw [← h]
  congr 1
  simp


/-- **The abutment of the first spectral sequence** of a first quadrant double complex `K`: the
filtration of `Hⁿ(Tot K)` induced by the column filtration of the total complex, whose graded
pieces are the `E∞`-terms. Its filtration is described by
`firstSpectralSequenceAbutment_filtration`.

(blueprint: `det-def-groth-ss`, `thm-sp-double-complex-spectral-sequences`) -/
noncomputable def firstSpectralSequenceAbutment :
    K.firstSpectralSequence.Abutment fun n ↦ (K.total (up ℕ)).homology n :=
  (K.extendNat.columnFiltration.exactCouple.firstQuadrantAbutment
    K.extendNat_columnFiltration_isFirstQuadrant
    (columnFiltration_convergesTo K.isZero_extendNat_X_X)
    (fun n ↦ columnFiltration_homologyFiltration_F_zero K.isZero_extendNat_X_X n)
    (fun n ↦ columnFiltration_homologyFiltration_F_succ K.isZero_extendNat_X_X n)).ofIso
    K.totalExtendNatHomologyIso

/-- The filtration of the abutment of the first spectral sequence is the image filtration
`Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K) ⟶ Hⁿ(Tot K))` of the column filtration `Fᵖ Tot K` (computed
on the extension by zero `K.extendNat`, whose total cohomology in degree `n ≥ 0` is identified
with that of `K` by `totalExtendNatHomologyIso`).

(blueprint: `det-def-groth-ss`) -/
lemma firstSpectralSequenceAbutment_filtration (n p : ℕ) :
    K.firstSpectralSequenceAbutment.filtration n p =
      imageSubobject (HomologicalComplex.homologyMap
        (K.extendNat.columnFiltration.F p).arrow n ≫ (K.totalExtendNatHomologyIso n).hom) :=
  mk_imageSubobject_arrow_comp_iso _ _


/-- **The abutment of the second spectral sequence** of a first quadrant double complex `K`
(the first spectral sequence of `K.flip`): the filtration of `Hⁿ(Tot K)` induced by the row
filtration, transported along `Tot K.flip ≅ Tot K`. Its filtration is described by
`flipFirstSpectralSequenceAbutment_filtration`.

(blueprint: `det-def-groth-ss`, `thm-sp-double-complex-spectral-sequences`) -/
noncomputable def flipFirstSpectralSequenceAbutment :
    K.flip.firstSpectralSequence.Abutment fun n ↦ (K.total (up ℕ)).homology n :=
  K.flip.firstSpectralSequenceAbutment.ofIso fun n ↦
    HomologicalComplex.homologyMapIso (K.totalFlipIso (up ℕ)) n

/-- The filtration of the abutment of the second spectral sequence is the image filtration
`Fᵖ Hⁿ(Tot K) = im (Hⁿ(Fᵖ Tot K.flip) ⟶ Hⁿ(Tot K.flip) ≅ Hⁿ(Tot K))` of the row filtration.

(blueprint: `det-def-groth-ss`) -/
lemma flipFirstSpectralSequenceAbutment_filtration (n p : ℕ) :
    K.flipFirstSpectralSequenceAbutment.filtration n p =
      imageSubobject (HomologicalComplex.homologyMap
        (K.flip.extendNat.columnFiltration.F p).arrow n ≫
          (K.flip.totalExtendNatHomologyIso n).hom ≫
            HomologicalComplex.homologyMap (K.totalFlipIso (up ℕ)).hom n) := by
  change Subobject.mk (_ ≫ (HomologicalComplex.homologyMapIso (K.totalFlipIso (up ℕ)) n).hom) = _
  have key : ∀ (S : Subobject ((K.flip.total (up ℕ)).homology n)) {Y : C}
      (g : Y ⟶ (K.flip.total (up ℕ)).homology n), S = imageSubobject g →
      Subobject.mk (S.arrow ≫ (HomologicalComplex.homologyMapIso (K.totalFlipIso (up ℕ)) n).hom)
        = imageSubobject
          (g ≫ (HomologicalComplex.homologyMapIso (K.totalFlipIso (up ℕ)) n).hom) := by
    rintro S Y g rfl
    exact mk_imageSubobject_arrow_comp_iso _ _
  rw [key _ _ (K.flip.firstSpectralSequenceAbutment_filtration n p)]
  simp only [Category.assoc, HomologicalComplex.homologyMapIso_hom]


/-- **The first spectral sequence of a first quadrant double complex.** For a first quadrant
double complex `K` in an abelian category, the filtration of the total complex by the columns
gives a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ H^p_I H^q_{II}(K)` — the `p`-th cohomology of the complex
`p ↦ H^q(K^{p, •})` whose differential is induced by the horizontal differential of `K` —
abutting to the cohomology `H^{p + q}(Tot K)` of the total complex.

This is the first of the two spectral sequences of a double complex.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem exists_spectralSequence {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ, Nonempty ((E.page 2).X (p, q) ≅
        (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K).homology p)) ∧
      E.AbutsTo fun n ↦ (K.total (ComplexShape.up ℕ)).homology n :=
  ⟨K.firstSpectralSequence, fun p q ↦ ⟨K.firstSpectralSequencePageTwoIso p q⟩,
    K.firstSpectralSequence_abutsTo⟩

/-- **The second spectral sequence of a first quadrant double complex.** For a first quadrant
double complex `K` in an abelian category, the filtration of the total complex by the rows
gives a first quadrant cohomological spectral sequence with
`E₂^{q, p} ≅ H^q_{II} H^p_I(K)` — the `q`-th cohomology of the complex
`q ↦ H^p(K^{•, q})` whose differential is induced by the vertical differential of `K` —
abutting to the cohomology `H^{p + q}(Tot K)` of the total complex. It is the first spectral
sequence of the transposed double complex `K.flip`, whose total complex is isomorphic to that
of `K`.

(blueprint: `thm-sp-double-complex-spectral-sequences`) -/
theorem exists_spectralSequence_flip {C : Type*} [Category* C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ q p : ℕ, Nonempty ((E.page 2).X (q, p) ≅
        (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) p).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K.flip).homology q)) ∧
      E.AbutsTo fun n ↦ (K.total (ComplexShape.up ℕ)).homology n := by
  obtain ⟨E, hE₂, hE⟩ := K.flip.exists_spectralSequence
  exact ⟨E, hE₂, hE.of_iso fun n ↦
    HomologicalComplex.homologyMapIso (K.totalFlipIso (ComplexShape.up ℕ)) n⟩


end HomologicalComplex₂
