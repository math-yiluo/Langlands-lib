/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.Algebra.Homology.DerivedCategory.ProjectiveHom
public import WeilConjectures.Algebra.Homology.MinimalComplex
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Complexes of finite free modules given by matrices

Let `S` be a commutative ring and `r : ℤ → ℕ`. A *matrix complex* of ranks `r` over `S`
(`MatrixComplex r S`) is a family of matrices `d i` of size `r (i + 1) × r i` with
`d (i + 1) * d i = 0`. It defines a cochain complex `M.complex` of `S`-modules with terms
`Sʳ⁽ⁱ⁾` (`MatrixComplex.complex`).

Matrix complexes are convenient for base change and limits: the base change along a ring
morphism `φ : S →+* S'` is given by the reduced matrices (`MatrixComplex.map`), and the
reduction `Sʳ⁽ⁱ⁾ ⟶ S'ʳ⁽ⁱ⁾` is a chain map (`MatrixComplex.reduction`). When `φ` is surjective
with principal kernel and the ranks are bounded, this reduction exhibits the reduced complex as
the derived base change (`MatrixComplex.isDerivedBaseChange_reduction`).

## Main definitions

- `MatrixComplex`: matrix complexes.
- `MatrixComplex.complex`: the associated cochain complex.
- `MatrixComplex.homMk`: chain maps given by matrices.
- `MatrixComplex.map`: base change of matrix complexes.
- `MatrixComplex.reduction`: the reduction chain map.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- A *matrix complex* of ranks `r : ℤ → ℕ` over a commutative ring `S`: matrices `d i` of
size `r (i + 1) × r i` with `d (i + 1) * d i = 0`. -/
structure MatrixComplex (r : ℤ → ℕ) (S : Type u) [CommRing S] where
  /-- The differential `Sʳ⁽ⁱ⁾ ⟶ Sʳ⁽ⁱ⁺¹⁾`. -/
  d (i : ℤ) : Matrix (Fin (r (i + 1))) (Fin (r i)) S
  d_mul_d (i : ℤ) : d (i + 1) * d i = 0

namespace MatrixComplex

variable {r r' r'' : ℤ → ℕ} {S : Type u} [CommRing S] (M : MatrixComplex r S)

/-- The cochain complex of `S`-modules with terms `Sʳ⁽ⁱ⁾` defined by a matrix complex. -/
noncomputable def complex : CochainComplex (ModuleCat.{u} S) ℤ :=
  CochainComplex.of (fun i ↦ ModuleCat.of S (Fin (r i) → S))
    (fun i ↦ ModuleCat.ofHom (Matrix.toLin' (M.d i))) fun i ↦ by
      ext v
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ← Matrix.toLin'_mul, M.d_mul_d,
        map_zero, ModuleCat.hom_zero]

/-- The terms of the complex of a matrix complex. -/
lemma complex_X (i : ℤ) : M.complex.X i = ModuleCat.of S (Fin (r i) → S) := rfl

/-- The differentials of the complex of a matrix complex. -/
lemma complex_d (i : ℤ) :
    M.complex.d i (i + 1) = ModuleCat.ofHom (Matrix.toLin' (M.d i)) :=
  by simp [complex]

/-- The differentials of the complex of a matrix complex, elementwise. -/
lemma complex_d_apply (i : ℤ) (v : Fin (r i) → S) :
    (M.complex.d i (i + 1)).hom v = (M.d i).mulVec v := by
  rw [complex_d]
  rfl

/-- The terms of the complex of a matrix complex are free. -/
instance (i : ℤ) : Module.Free S (M.complex.X i) :=
  inferInstanceAs (Module.Free S (Fin (r i) → S))

/-- The terms of the complex of a matrix complex are finite. -/
instance (i : ℤ) : Module.Finite S (M.complex.X i) :=
  inferInstanceAs (Module.Finite S (Fin (r i) → S))

/-- The terms of the complex of a matrix complex are projective modules. -/
instance (i : ℤ) : Module.Projective S (M.complex.X i) :=
  inferInstanceAs (Module.Projective S (Fin (r i) → S))

/-- The terms of the complex of a matrix complex are projective objects. -/
instance (i : ℤ) : Projective (M.complex.X i) :=
  ModuleCat.projective_of_free (Pi.basisFun S (Fin (r i)))

/-- The terms of a matrix complex vanish in degrees of rank zero. -/
lemma isZero_complex_X {i : ℤ} (hi : r i = 0) : IsZero (M.complex.X i) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have : IsEmpty (Fin (r i)) := by
    rw [hi]
    infer_instance
  exact inferInstanceAs (Subsingleton (Fin (r i) → S))

/-- A matrix complex whose ranks vanish below `a` is strictly `≥ a`. -/
lemma isStrictlyGE_complex (a : ℤ) (h : ∀ i, i < a → r i = 0) : M.complex.IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  exact fun i hi ↦ M.isZero_complex_X (h i hi)

/-- A matrix complex whose ranks vanish above `b` is strictly `≤ b`. -/
lemma isStrictlyLE_complex (b : ℤ) (h : ∀ i, b < i → r i = 0) : M.complex.IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  exact fun i hi ↦ M.isZero_complex_X (h i hi)

/-! ### Chain maps given by matrices -/

variable {M} {N : MatrixComplex r' S} {P : MatrixComplex r'' S}

/-- The chain map between matrix complexes given by matrices `f i` commuting with the
differentials. -/
noncomputable def homMk (f : ∀ i, Matrix (Fin (r' i)) (Fin (r i)) S)
    (hf : ∀ i, N.d i * f i = f (i + 1) * M.d i) : M.complex ⟶ N.complex where
  f i := ModuleCat.ofHom (Matrix.toLin' (f i))
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [complex_d, complex_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hf]

/-- The components of `MatrixComplex.homMk`. -/
lemma homMk_f (f : ∀ i, Matrix (Fin (r' i)) (Fin (r i)) S)
    (hf : ∀ i, N.d i * f i = f (i + 1) * M.d i) (i : ℤ) :
    (homMk f hf).f i = ModuleCat.ofHom (Matrix.toLin' (f i)) :=
  rfl

/-- The matrices of the components of a chain map between matrix complexes. -/
noncomputable def toMatrix (g : M.complex ⟶ N.complex) (i : ℤ) :
    Matrix (Fin (r' i)) (Fin (r i)) S :=
  LinearMap.toMatrix' (g.f i).hom

/-- The components of a chain map are given by its matrices. -/
lemma toLin'_toMatrix (g : M.complex ⟶ N.complex) (i : ℤ) :
    Matrix.toLin' (toMatrix g i) = (g.f i).hom :=
  Matrix.toLin'_toMatrix' _

/-- The matrices of a chain map commute with the differentials. -/
lemma toMatrix_comm (g : M.complex ⟶ N.complex) (i : ℤ) :
    N.d i * toMatrix g i = toMatrix g (i + 1) * M.d i := by
  apply Matrix.toLin'.injective
  have := congrArg ModuleCat.Hom.hom (g.comm i (i + 1))
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, complex_d, complex_d, ModuleCat.hom_ofHom,
    ModuleCat.hom_ofHom] at this
  simp only [Matrix.toLin'_mul, toLin'_toMatrix]
  exact this

/-- A chain map between matrix complexes is given by its matrices. -/
lemma homMk_toMatrix (g : M.complex ⟶ N.complex) : homMk (toMatrix g) (toMatrix_comm g) = g := by
  ext i : 2
  rw [homMk_f, toLin'_toMatrix]
  rfl

/-- The matrices of `MatrixComplex.homMk`. -/
lemma toMatrix_homMk (f : ∀ i, Matrix (Fin (r' i)) (Fin (r i)) S)
    (hf : ∀ i, N.d i * f i = f (i + 1) * M.d i) (i : ℤ) : toMatrix (homMk f hf) i = f i := by
  rw [toMatrix, homMk_f, ModuleCat.hom_ofHom, LinearMap.toMatrix'_toLin']

/-- The matrices of a composition are the products of the matrices. -/
lemma toMatrix_comp (g : M.complex ⟶ N.complex) (g' : N.complex ⟶ P.complex) (i : ℤ) :
    toMatrix (g ≫ g') i = toMatrix g' i * toMatrix g i := by
  rw [toMatrix, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.toMatrix'_comp]
  rfl

/-- The matrices of the identity are identity matrices. -/
lemma toMatrix_id (i : ℤ) : toMatrix (𝟙 M.complex) i = 1 := by
  rw [toMatrix, HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.toMatrix'_id]

/-- The matrices of a sum are the sums of the matrices. -/
lemma toMatrix_add (g g' : M.complex ⟶ N.complex) (i : ℤ) :
    toMatrix (g + g') i = toMatrix g i + toMatrix g' i := by
  rw [toMatrix, HomologicalComplex.add_f_apply, ModuleCat.hom_add, map_add]
  rfl

/-- Chain maps between matrix complexes are determined by their matrices. -/
lemma toMatrix_injective {g g' : M.complex ⟶ N.complex} (h : ∀ i, toMatrix g i = toMatrix g' i) :
    g = g' := by
  rw [← homMk_toMatrix g, ← homMk_toMatrix g']
  ext i : 2
  rw [homMk_f, homMk_f, h]

/-! ### Base change -/

variable {S' : Type u} [CommRing S'] (φ : S →+* S')

variable (M) in
/-- The base change of a matrix complex along a ring morphism: the reduced matrices. -/
def map : MatrixComplex r S' where
  d i := (M.d i).map φ
  d_mul_d i := by rw [← Matrix.map_mul, M.d_mul_d, Matrix.map_zero _ (map_zero φ)]

/-- The reduction `Sᵏ ⟶ S'ᵏ` along `φ`, as an `S`-linear map to the restriction of scalars. -/
noncomputable def reductionHom (k : ℕ) :
    ModuleCat.of S (Fin k → S) ⟶
      (ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of S' (Fin k → S')) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars.{u} φ).obj (ModuleCat.of S' (Fin k → S')))
    { toFun v := fun j ↦ φ (v j)
      map_add' v w := by
        funext j
        exact map_add φ _ _
      map_smul' c v := by
        funext j
        exact map_mul φ _ _ }

/-- The reduction `Sᵏ ⟶ S'ᵏ` is the reduction of the coordinates. -/
lemma reductionHom_apply (k : ℕ) (v : Fin k → S) (j : Fin k) :
    (reductionHom φ k).hom v j = φ (v j) :=
  rfl

variable (M) in
/-- The reduction chain map `M ⟶ Res N` along `φ : S →+* S'`, for a matrix complex `N` over
`S'` whose matrices are the reductions of those of `M`. -/
noncomputable def reduction (N : MatrixComplex r S') (h : ∀ i, (M.d i).map φ = N.d i) :
    M.complex ⟶ ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj N.complex where
  f i := reductionHom φ (r i)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    ext v
    funext k
    refine (congrFun (N.complex_d_apply i (fun j ↦ φ (v j))) k).trans ?_
    rw [← h]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, complex_d_apply]
    exact (RingHom.map_mulVec φ (M.d i) v k).symm

/-- The components of `MatrixComplex.reduction`. -/
lemma reduction_f (N : MatrixComplex r S') (h : ∀ i, (M.d i).map φ = N.d i) (i : ℤ) :
    (M.reduction φ N h).f i = reductionHom φ (r i) :=
  rfl

/-- The components of a chain map between matrix complexes are given by their matrices. -/
lemma hom_f_apply (g : M.complex ⟶ N.complex) (i : ℤ) (v : Fin (r i) → S) :
    (g.f i).hom v = (toMatrix g i).mulVec v := by
  rw [← Matrix.toLin'_apply, toLin'_toMatrix]
  rfl

/-- The reduction chain maps commute with chain maps whose matrices are related by
reduction. -/
lemma reduction_naturality {M' : MatrixComplex r S'} {N' : MatrixComplex r' S'}
    (hM : ∀ i, (M.d i).map φ = M'.d i) (hN : ∀ i, (N.d i).map φ = N'.d i)
    (g : M.complex ⟶ N.complex) (g' : M'.complex ⟶ N'.complex)
    (hg : ∀ i, (toMatrix g i).map φ = toMatrix g' i) :
    g ≫ N.reduction φ N' hN =
      M.reduction φ M' hM ≫ ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).map g' := by
  ext i v
  funext k
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    reduction_f, hom_f_apply]
  refine (RingHom.map_mulVec φ _ v k).trans ?_
  rw [hg]
  exact (congrFun (hom_f_apply g' i (fun j ↦ φ (v j))) k).symm

/-- The reduction of a basis vector is a basis vector. -/
lemma reductionHom_single {k : ℕ} (l : Fin k) :
    (reductionHom φ k).hom (Pi.single l 1) = Pi.single l 1 := by
  funext j
  rw [reductionHom_apply, Pi.single_apply, Pi.single_apply]
  split_ifs <;> simp

/-- Conversely to `MatrixComplex.reduction_naturality`, chain maps compatible with the
reductions have matrices related by reduction. -/
lemma map_toMatrix_of_comp_reduction {M' : MatrixComplex r S'} {N' : MatrixComplex r' S'}
    (hM : ∀ i, (M.d i).map φ = M'.d i) (hN : ∀ i, (N.d i).map φ = N'.d i)
    (g : M.complex ⟶ N.complex) (g' : M'.complex ⟶ N'.complex)
    (h : g ≫ N.reduction φ N' hN =
      M.reduction φ M' hM ≫ ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).map g')
    (i : ℤ) : (toMatrix g i).map φ = toMatrix g' i := by
  ext j k
  have h' := congrFun (ConcreteCategory.congr_hom (HomologicalComplex.congr_hom h i)
    (Pi.single k 1)) j
  rw [Matrix.map_apply, toMatrix, toMatrix, LinearMap.toMatrix'_apply,
    LinearMap.toMatrix'_apply, ← reductionHom_apply, ← reductionHom_single φ k]
  exact h'

/-- The reduction `Sᵏ ⟶ S'ᵏ` along a surjective ring morphism is surjective. -/
lemma reductionHom_surjective (hφ : Function.Surjective φ) (k : ℕ) :
    Function.Surjective (reductionHom φ k).hom := fun y ↦
  ⟨fun j ↦ (hφ (y j)).choose, funext fun j ↦ (hφ (y j)).choose_spec⟩

/-- The kernel of the reduction `Sᵏ ⟶ S'ᵏ` along a ring morphism with kernel `(a)` consists of
the multiples of `a`. -/
lemma exists_eq_smul_of_reductionHom_eq_zero {a : S} (ha : RingHom.ker φ = Ideal.span {a})
    {k : ℕ} (v : Fin k → S) (hv : (reductionHom φ k).hom v = 0) : ∃ w : Fin k → S, v = a • w := by
  have hmem (j : Fin k) : v j ∈ Ideal.span {a} := by
    rw [← ha, RingHom.mem_ker]
    exact congrFun hv j
  choose c hc using fun j ↦ Ideal.mem_span_singleton'.1 (hmem j)
  exact ⟨c, funext fun j ↦ by simp [← hc j, mul_comm]⟩

/-- For a surjective ring morphism `φ` with kernel `(a)`, the descent along the extension of
scalars of a surjective map `X ⟶ Res Y` whose kernel consists of multiples of `a` is an
isomorphism. -/
lemma isIso_reductionDatum_desc (hφ : Function.Surjective φ) {a : S}
    (ha : RingHom.ker φ = Ideal.span {a}) [(ModuleCat.restrictScalars.{u} φ).Full]
    {X : ModuleCat.{u} S} {Y : ModuleCat.{u} S'}
    (g : X ⟶ (ModuleCat.restrictScalars.{u} φ).obj Y) (hg : Function.Surjective g.hom)
    (hker : ∀ x, g.hom x = 0 → ∃ y, x = a • y) :
    IsIso ((ModuleCat.reductionDatum φ hφ a ha).desc g) := by
  let D := ModuleCat.reductionDatum φ hφ a ha
  have hr (x : X) : (D.desc g).hom ((D.r.app X).hom x) = g.hom x :=
    ConcreteCategory.congr_hom (D.r_app_comp_map_desc g) x
  have hrs : Function.Surjective (D.r.app X).hom :=
    (ModuleCat.epi_iff_surjective _).1 (D.epi_r X)
  have hfa : φ a = 0 := by
    rw [← RingHom.mem_ker, ha]
    exact Ideal.mem_span_singleton_self a
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero (D.desc g).hom).2 fun z hz ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hrs z
    obtain ⟨y, rfl⟩ := hker x ((hr x).symm.trans hz)
    refine ((D.r.app X).hom.map_smul a y).trans ?_
    rw [ModuleCat.restrictScalars.smul_def, hfa, zero_smul]
  · obtain ⟨x, rfl⟩ := hg y
    exact ⟨_, hr x⟩

/-- **Homotopies lift along reductions.** If `a, b : M ⟶ Res N'` are homotopic chain maps to the
restriction of the reduction `N'` of a matrix complex `N` along a surjective ring morphism, then
`a - b` is the reduction of a null-homotopic chain map `M ⟶ N`. -/
lemma exists_comp_reduction_eq_sub (hφ : Function.Surjective φ) {N : MatrixComplex r' S}
    {N' : MatrixComplex r' S'} (hN : ∀ i, (N.d i).map φ = N'.d i)
    {a b : M.complex ⟶ ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).obj N'.complex}
    (H : Homotopy a b) :
    ∃ P : M.complex ⟶ N.complex, Nonempty (Homotopy P 0) ∧ P ≫ N.reduction φ N' hN = a - b := by
  choose h hh using fun i j (_ : (ComplexShape.up ℤ).Rel j i) ↦
    Module.projective_lifting_property ((N.reduction φ N' hN).f j).hom (H.hom i j).hom
      (reductionHom_surjective φ hφ _)
  refine ⟨Homotopy.nullHomotopicMap' fun i j hij ↦ ModuleCat.ofHom (h i j hij),
    ⟨Homotopy.nullHomotopy' _⟩, ?_⟩
  have hh' (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel j i) :
      ModuleCat.ofHom (h i j hij) ≫ (N.reduction φ N' hN).f j = H.hom i j :=
    ModuleCat.hom_ext (hh i j hij)
  rw [Homotopy.nullHomotopicMap'_comp]
  ext1 i
  rw [Homotopy.nullHomotopicMap'_f (k₂ := i - 1) (k₀ := i + 1) (by simp) rfl, hh', hh',
    HomologicalComplex.sub_f_apply, H.comm i, dNext_eq _ (i' := i + 1) rfl,
    prevD_eq _ (j' := i - 1) (by simp)]
  abel

/-- The base change of a chain map between matrix complexes: the reduced matrices. -/
noncomputable def mapHom {M' : MatrixComplex r S'} {N' : MatrixComplex r' S'}
    (hM : ∀ i, (M.d i).map φ = M'.d i) (hN : ∀ i, (N.d i).map φ = N'.d i)
    (g : M.complex ⟶ N.complex) : M'.complex ⟶ N'.complex :=
  homMk (fun i ↦ (toMatrix g i).map φ) fun i ↦ by
    rw [← hM, ← hN, ← Matrix.map_mul, ← Matrix.map_mul, toMatrix_comm]

/-- The matrices of `MatrixComplex.mapHom` are the reduced matrices. -/
lemma toMatrix_mapHom {M' : MatrixComplex r S'} {N' : MatrixComplex r' S'}
    (hM : ∀ i, (M.d i).map φ = M'.d i) (hN : ∀ i, (N.d i).map φ = N'.d i)
    (g : M.complex ⟶ N.complex) (i : ℤ) : toMatrix (mapHom φ hM hN g) i = (toMatrix g i).map φ :=
  toMatrix_homMk _ _ i

/-- The reductions of a chain map and of its base change are compatible. -/
lemma comp_reduction_mapHom {M' : MatrixComplex r S'} {N' : MatrixComplex r' S'}
    (hM : ∀ i, (M.d i).map φ = M'.d i) (hN : ∀ i, (N.d i).map φ = N'.d i)
    (g : M.complex ⟶ N.complex) :
    g ≫ N.reduction φ N' hN = M.reduction φ M' hM ≫
      ((ModuleCat.restrictScalars.{u} φ).mapHomologicalComplex _).map (mapHom φ hM hN g) :=
  reduction_naturality φ hM hN g _ fun i ↦ (toMatrix_mapHom φ hM hN g i).symm

/-- The trace of a component of a chain endomorphism of a matrix complex is the trace of its
matrix. -/
lemma trace_hom_f (g : M.complex ⟶ M.complex) (i : ℤ) :
    LinearMap.trace S (M.complex.X i) (g.f i).hom = (toMatrix g i).trace := by
  rw [← toLin'_toMatrix g i]
  exact Matrix.trace_toLin'_eq _

/-- The alternating sum of the traces of a chain endomorphism of a matrix complex reduces to
that of its base change. -/
lemma map_sum_negOnePow_trace {M' : MatrixComplex r S'} (hM : ∀ i, (M.d i).map φ = M'.d i)
    (g : M.complex ⟶ M.complex) (s : Finset ℤ) :
    φ (∑ i ∈ s, (i.negOnePow : ℤ) • LinearMap.trace S (M.complex.X i) (g.f i).hom) =
      ∑ i ∈ s, (i.negOnePow : ℤ) •
        LinearMap.trace S' (M'.complex.X i) ((mapHom φ hM hM g).f i).hom := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, trace_hom_f, trace_hom_f, toMatrix_mapHom, AddMonoidHom.map_trace]

variable [HasDerivedCategory.{u} (ModuleCat.{u} S)] [HasDerivedCategory.{u} (ModuleCat.{u} S')]

/-- **The reduction of a bounded matrix complex is its derived base change.** For a surjective
ring morphism `φ : S →+* S'` with principal kernel, the reduction `M ⟶ Res N` of a matrix
complex with bounded ranks exhibits `N` as the derived base change of `M`. -/
theorem isDerivedBaseChange_reduction (hφ : Function.Surjective φ) {a : S}
    (ha : RingHom.ker φ = Ideal.span {a}) (lo hi : ℤ) (hlo : ∀ i, i < lo → r i = 0)
    (hhi : ∀ i, hi < i → r i = 0) (N : MatrixComplex r S') (h : ∀ i, (M.d i).map φ = N.d i) :
    ModuleCat.IsDerivedBaseChange (f := φ)
      (DerivedCategory.Q.map (M.reduction φ N h) ≫
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategoryFactors.inv.app N.complex) := by
  have := ModuleCat.restrictScalars_full_of_surjective.{u} φ hφ
  have := M.isStrictlyGE_complex lo hlo
  have := M.isStrictlyLE_complex hi hhi
  let D := ModuleCat.reductionDatum φ hφ a ha
  have h₀ := ModuleCat.isDerivedBaseChange_Q_map_complexMap hφ ha M.complex
    (CochainComplex.kFlat_of_bounded_of_flat M.complex lo hi fun n ↦
      (ModuleCat.flat_iff_flat _).2 (inferInstanceAs (Module.Flat S (Fin (r n) → S))))
  let δ := D.descComplex (M.reduction φ N h)
  have : IsIso δ := by
    have (i : ℤ) : IsIso (δ.f i) := isIso_reductionDatum_desc φ hφ ha _
      (reductionHom_surjective φ hφ (r i))
      (exists_eq_smul_of_reductionHom_eq_zero φ ha)
    exact HomologicalComplex.Hom.isIso_of_components _
  convert h₀.comp_map_iso (asIso (DerivedCategory.Q.map δ)) using 1
  rw [← D.complexMap_comp_descComplex (M.reduction φ N h), Functor.map_comp, Category.assoc,
    Functor.mapDerivedCategoryFactors_inv_naturality, asIso_hom, Category.assoc]

end MatrixComplex

/-! ### Alternating sums of traces -/

/-- A telescoping identity for alternating sums over an interval of integers. -/
lemma Int.sum_Icc_negOnePow_smul_add {G : Type*} [AddCommGroup G] (u : ℤ → G) (a b : ℤ)
    (hab : a - 1 ≤ b) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • (u i + u (i + 1)) =
      (a.negOnePow : ℤ) • u a + (b.negOnePow : ℤ) • u (b + 1) := by
  induction b, hab using Int.leInduction with
  | base =>
    have h := Int.negOnePow_succ (a - 1)
    rw [sub_add_cancel] at h
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, sub_add_cancel, h, Units.val_neg,
      neg_smul, neg_add_cancel]
  | succ b hb ih =>
    have hI : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
      ext
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp), ih, Int.negOnePow_succ, Units.val_neg]
    simp only [neg_smul, smul_add]
    abel

/-- **The alternating sum of the traces is invariant under homotopy.** For homotopic chain
endomorphisms `f` and `g` of a complex of finite free modules which vanishes in degrees `a - 1`
and `b + 1`, the alternating sums over `[a, b]` of the traces of their components agree. -/
lemma CochainComplex.sum_negOnePow_trace_eq_of_homotopy {S : Type u} [CommRing S]
    {K : CochainComplex (ModuleCat.{u} S) ℤ} [∀ i, Module.Free S (K.X i)]
    [∀ i, Module.Finite S (K.X i)] {f g : K ⟶ K} (H : Homotopy f g) (a b : ℤ) (hab : a - 1 ≤ b)
    (ha : IsZero (K.X (a - 1))) (hb : IsZero (K.X (b + 1))) :
    ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • LinearMap.trace S (K.X i) (f.f i).hom =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) • LinearMap.trace S (K.X i) (g.f i).hom := by
  let u (i : ℤ) : S := LinearMap.trace S (K.X i) (prevD i H.hom).hom
  have hf (i : ℤ) : LinearMap.trace S (K.X i) (f.f i).hom =
      (u i + u (i + 1)) + LinearMap.trace S (K.X i) (g.f i).hom := by
    have hd : LinearMap.trace S (K.X i) (dNext i H.hom).hom = u (i + 1) := by
      simp only [u]
      rw [dNext_eq _ (i' := i + 1) rfl, prevD_eq _ (j' := i) rfl, ModuleCat.hom_comp,
        ModuleCat.hom_comp, LinearMap.trace_comp_comm']
    rw [H.comm i, ModuleCat.hom_add, ModuleCat.hom_add, map_add, map_add, hd, add_comm (u i)]
  have hua : u a = 0 := by
    simp only [u]
    rw [prevD_eq _ (j' := a - 1) (by simp), ha.eq_of_tgt (H.hom a _) 0,
      zero_comp, ModuleCat.hom_zero, map_zero]
  have hub : u (b + 1) = 0 := by
    simp only [u]
    rw [hb.eq_of_src (prevD (b + 1) H.hom) 0, ModuleCat.hom_zero, map_zero]
  rw [Finset.sum_congr rfl fun i _ ↦ by rw [hf, smul_add], Finset.sum_add_distrib,
    Int.sum_Icc_negOnePow_smul_add u a b hab, hua, hub, smul_zero, smul_zero, add_zero, zero_add]
