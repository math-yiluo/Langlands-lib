/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TensorBicomplex


public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.TensorBicomplexExtension
import WeilConjectures.Algebra.Homology.DoubleComplexCokernelHomologyIso
import WeilConjectures.Algebra.Category.ModuleCat.TorSymmetry
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Computing Tor from a flat resolution

Source: Stacks Project, Algebra, Section Tag 00LY, especially Lemmas 00M1 and 00M3.
(blueprint: lem-pc-flat-resolution-tor-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace HomologicalComplex₂

private lemma augmentation_zero {R : Type u} [CommRing R]
    {M : ModuleCat.{u} R} {P : ChainComplex (ModuleCat.{u} R) ℕ}
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M) :
    P.d 1 0 ≫ ε.f 0 = 0 := by
  rw [← ε.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]

private def columnAugmentation {R : Type u} [CommRing R]
    {N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ) (Q : ProjectiveResolution N) :
    (tensorBicomplex P Q.complex).flip.X 0 ⟶
      ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P where
  f p := 𝟙 (P.X p) ⊗ₘ Q.π.f 0
  comm' p p' h := by
    simp only [tensorBicomplex, flip_X_d, Functor.mapBifunctorHomologicalComplex_obj_obj_d_f,
    curriedTensor_map_app, ← tensorHom_id,
      Functor.mapHomologicalComplex_obj_d, Functor.flip_obj_map, curriedTensor_map_app,
      ← tensorHom_id,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

private theorem columnAugmentation_zero {R : Type u} [CommRing R]
    {N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ) (Q : ProjectiveResolution N) :
    (tensorBicomplex P Q.complex).flip.d 1 0 ≫ columnAugmentation P Q = 0 := by
  ext p
  simp only [HomologicalComplex.comp_f, columnAugmentation, flip_d_f,
    tensorBicomplex, Functor.mapBifunctorHomologicalComplex_obj_obj_X_d, curriedTensor_obj_map,
    ← id_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, ProjectiveResolution.complex_d_comp_π_f_zero,
    HomologicalComplex.zero_f]
  simp

private noncomputable def columnDesc {R : Type u} [CommRing R]
    {N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ) (Q : ProjectiveResolution N) :=
  (tensorBicomplex P Q.complex).flip.descOpcycles
    (columnAugmentation P Q) 1 (by simp) (columnAugmentation_zero P Q)

set_option backward.isDefEq.respectTransparency false in
private theorem columnDesc_isIso {R : Type u} [CommRing R]
    {N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ) (Q : ProjectiveResolution N) :
    IsIso (columnDesc P Q) := by
  rw [columnDesc, ChainComplex.isIso_descOpcycles_iff]
  constructor
  · apply HomologicalComplex.exact_of_degreewise_exact
    intro p
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    have h := lTensor_exact (P.X p)
      (LinearMap.exact_iff.mpr
        ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp Q.exact₀).symm)
      ((ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (Q.π.f 0)))
    intro x hx
    exact (h x).mp hx
  · apply HomologicalComplex.epi_of_epi_f
    intro p
    apply (ModuleCat.epi_iff_surjective _).mpr
    change Function.Surjective ((Q.π.f 0).hom.lTensor (P.X p))
    exact LinearMap.lTensor_surjective _ ((ModuleCat.epi_iff_surjective _).mp
      (inferInstance : Epi (Q.π.f 0)))


private noncomputable def rowAugmentation {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
    (Q : ProjectiveResolution N) :
    (tensorBicomplex P Q.complex).X 0 ⟶
      ((tensorRight M).mapHomologicalComplex (.down ℕ)).obj Q.complex where
  f q := (ε.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom
  comm' q q' h := by
    simp only [tensorBicomplex, Functor.mapBifunctorHomologicalComplex_obj_obj_X_d,
    curriedTensor_obj_map, ← id_tensorHom,
      Functor.mapHomologicalComplex_obj_d, Functor.flip_obj_map, curriedTensor_map_app,
      ← tensorHom_id]
    rw [Category.assoc, ← BraidedCategory.braiding_naturality]
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id]
    erw [Category.comp_id]

private theorem rowAugmentation_zero {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
    (Q : ProjectiveResolution N) :
    (tensorBicomplex P Q.complex).d 1 0 ≫ rowAugmentation P ε Q = 0 := by
  ext q
  simp only [HomologicalComplex.comp_f, rowAugmentation, tensorBicomplex,
    Functor.mapBifunctorHomologicalComplex_obj_obj_d_f, curriedTensor_map_app, ← tensorHom_id,
    ← Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id, augmentation_zero ε,
    HomologicalComplex.zero_f]
  simp

private noncomputable def rowDesc {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
    (Q : ProjectiveResolution N) :=
  (tensorBicomplex P Q.complex).descOpcycles
    (rowAugmentation P ε Q) 1 (by simp) (rowAugmentation_zero P ε Q)

private theorem rowDesc_isIso {R : Type u} [CommRing R]
    {M N : ModuleCat.{u} R} (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : P ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
    (Q : ProjectiveResolution N)
    [Epi (ε.f 0)]
    (hex : (ShortComplex.mk (P.d 1 0) (ε.f 0) (augmentation_zero ε)).Exact) :
    IsIso (rowDesc P ε Q) := by
  rw [rowDesc, ChainComplex.isIso_descOpcycles_iff]
  constructor
  · apply HomologicalComplex.exact_of_degreewise_exact
    intro q
    let S := (ShortComplex.mk _ _ (augmentation_zero ε)).map
      (tensorRight (Q.complex.X q))
    have hs : S.Exact := hex.map_of_epi_of_preservesCokernel
      (tensorRight (Q.complex.X q)) (inferInstance) (inferInstance)
    apply ShortComplex.exact_of_iso _ hs
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
      (β_ M (Q.complex.X q)) ?_ ?_
    · simp [S, ShortComplex.map, tensorBicomplex]
    · simp [S, ShortComplex.map, rowAugmentation]
  · apply HomologicalComplex.epi_of_epi_f
    intro q
    change Epi ((ε.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) ≫ (β_ M (Q.complex.X q)).hom)
    have : Epi (ε.f 0 ⊗ₘ 𝟙 (Q.complex.X q)) := by
      change Epi ((tensorRight (Q.complex.X q)).map (ε.f 0))
      infer_instance
    infer_instance


end HomologicalComplex₂

namespace ModuleCat

open HomologicalComplex₂

/-- An augmented nonnegative chain complex of flat modules computes first-variable Tor.
Source: Stacks Project, Algebra, Section 10.75 (Tag 00LY), the double-complex argument
of Lemma 10.75.3 (Tag 00M1) and symmetry in Lemma 10.75.5 (Tag 00M3).

Proof: choose a projective resolution Q of N and form the first-quadrant tensor
bicomplex F tensor Q. Each column is exact in positive degrees since F_p is flat.
Each row is exact in positive degrees since Q_q is projective, hence flat, and the
augmentation of F is a quasi-isomorphism to M[0]. The column cokernel complex is
F tensor N; the row cokernel complex is M tensor Q. Tag 00M1 identifies their
homology. Computing Tor from Q and using Tag 00M3 identifies the latter homology
with Tor'_j(M,N). All these are isomorphisms of R-modules. Degree zero is included:
right exactness identifies both augmentations with the ordinary tensor product.
The zero complex and zero modules satisfy the same argument.
(blueprint: lem-pc-flat-resolution-tor-comparison). -/
theorem flatResolution_torComparison
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (F : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : F ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M)
    [QuasiIso ε] (hflat : ∀ i : ℕ, Module.Flat R (F.X i))
    (N : ModuleCat.{u} R) (j : ℕ) :
    Nonempty ((((Tor' (ModuleCat.{u} R) j).obj M).obj N) ≅
      (((tensorRight N).mapHomologicalComplex (.down ℕ)).obj F).homology j) := by
  classical
  have hq := (ChainComplex.quasiIsoAt₀_iff ε).mp (inferInstance : QuasiIsoAt ε 0)
  have h₀ : (ShortComplex.mk (F.d 1 0) (ε.f 0) (augmentation_zero ε)).Exact ∧
      Epi (ε.f 0) := by
    simpa [HomologicalComplex.shortComplexFunctor', HomologicalComplex.sc',
      ShortComplex.mk] using
      (ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp) (by simp)).mp hq
  have : Epi (ε.f 0) := h₀.2
  let Q := projectiveResolution N
  have : IsIso (columnDesc F Q) := columnDesc_isIso F Q
  have : IsIso (rowDesc F ε Q) := rowDesc_isIso F ε Q h₀.1
  have hex (i : ℕ) : (ShortComplex.mk (F.d (i + 2) (i + 1))
      (F.d (i + 1) i) (F.d_comp_d _ _ _)).Exact := by
    have hF : F.ExactAt (i + 1) := by
      rw [← quasiIsoAt_iff_exactAt' ε (i + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      infer_instance
    exact (HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i
      (by simp) (by simp)).mp hF
  obtain ⟨θ, _⟩ := doubleComplexCokernelHomologyIso R
  have hE :
      (∀ (p q : ℕ), 0 < p →
        (ShortComplex.mk ((tensorBicomplex F Q.complex).d (p + 1) p |>.f q)
          ((tensorBicomplex F Q.complex).d p (p - 1) |>.f q)
          (by rw [← HomologicalComplex.comp_f, HomologicalComplex.d_comp_d,
            HomologicalComplex.zero_f])).Exact) ∧
      (∀ (p q : ℕ), 0 < q →
        (ShortComplex.mk (((tensorBicomplex F Q.complex).X p).d (q + 1) q)
          (((tensorBicomplex F Q.complex).X p).d q (q - 1))
          (by exact ((tensorBicomplex F Q.complex).X p).d_comp_d _ _ _)).Exact) := by
    constructor
    · intro p q hp
      cases p with
      | zero => simp at hp
      | succ p =>
        have : Module.Flat R (Q.complex.X q) := Module.Flat.of_projective
        simpa [tensorBicomplex, ShortComplex.map] using
          Module.Flat.rTensor_shortComplex_exact (Q.complex.X q) _ (hex p)
    · intro p q hq
      cases q with
      | zero => simp at hq
      | succ q =>
        have : Module.Flat R (F.X p) := hflat p
        simpa [tensorBicomplex, ShortComplex.map] using
          Module.Flat.lTensor_shortComplex_exact (F.X p) _ (Q.exact_succ q)
  obtain ⟨symmetry⟩ := CategoryTheory.nonempty_tor'_flip_iso R j
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℕ) j
  refine ⟨((symmetry.app M).app N) ≪≫ Q.isoLeftDerivedObj (tensorRight M) j ≪≫
    (H.mapIso (asIso (rowDesc F ε Q))).symm ≪≫
    (θ (tensorBicomplex F Q.complex) hE j).symm ≪≫
    H.mapIso (asIso (columnDesc F Q))⟩

end ModuleCat
