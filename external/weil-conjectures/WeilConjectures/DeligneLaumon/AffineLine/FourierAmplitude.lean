/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion
public import WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform
public import WeilConjectures.DeligneLaumon.AffineLine.Punctual

/-!
# The ordinary amplitude of the Fourier–Deligne transform on the line

This file collects the statements about the ordinary cohomology sheaves of the Fourier–Deligne
transform `FT_ψ` of the affine line which enter the perverse t-exactness of `FT_ψ`
(blueprint `proposition-fourier-transform-perverse-heart--1`):

- `FT_ψ` lowers the lower bound of the cohomological amplitude by at most one, since `Rpr₂!` is
  left t-exact and `pr₁^*` and the tensor product with the lisse kernel are exact
  (`AlgebraicGeometry.isGE_fourierTransform_obj`);
- by Fourier inversion, `FT_ψ` raises the upper bound by at most one
  (`AlgebraicGeometry.isLE_fourierTransform_obj`);
- a sheaf of finite support transforms into a complex concentrated in degree `-1`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil complex is `≤ n` exactly when its cohomology sheaves vanish in degrees `> n`. -/
lemma isLE_iff_isZero_homologySheaf (K : WeilComplex k₀ l X) (n : ℤ) :
    K.obj.IsLE n ↔ ∀ a : ℤ, n < a → IsZero ((homologySheaf a).obj K) := by
  rw [_root_.DerivedCategory.isLE_iff]
  exact forall₂_congr fun a _ ↦ (isZero_homologySheaf_obj_iff a K).symm

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil complex is `≥ n` exactly when its cohomology sheaves vanish in degrees `< n`. -/
lemma isGE_iff_isZero_homologySheaf (K : WeilComplex k₀ l X) (n : ℤ) :
    K.obj.IsGE n ↔ ∀ a : ℤ, a < n → IsZero ((homologySheaf a).obj K) := by
  rw [_root_.DerivedCategory.isGE_iff]
  exact forall₂_congr fun a _ ↦ (isZero_homologySheaf_obj_iff a K).symm

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The shift `K[a]` of a Weil complex `K ≥ n` is `≥ n - a`. -/
lemma isGE_shift_obj (K : WeilComplex k₀ l X) (n a n' : ℤ) (h : a + n' = n)
    (hK : K.obj.IsGE n) : (K⟦a⟧).obj.IsGE n' := by
  have := _root_.DerivedCategory.TStructure.t.isGE_shift K.obj n a n' h
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso (X := K.obj⟦a⟧)
    (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso a).app K).symm n'

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The shift `K[a]` of a Weil complex `K ≤ n` is `≤ n - a`. -/
lemma isLE_shift_obj (K : WeilComplex k₀ l X) (n a n' : ℤ) (h : a + n' = n)
    (hK : K.obj.IsLE n) : (K⟦a⟧).obj.IsLE n' := by
  have := _root_.DerivedCategory.TStructure.t.isLE_shift K.obj n a n' h
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso (X := K.obj⟦a⟧)
    (((WeilComplex.objectProperty k₀ l X).ι.commShiftIso a).app K).symm n'

/-- The cohomology sheaves of a Tate twist are the constant twists of the cohomology sheaves:
`𝓗ᵃ(K(m)) ≅ 𝓗ᵃ(K) ⊗ 𝓑_{χ_ℓ(σ)^m}`, the Tate twist being the derived functor of the exact
constant twist (`ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso`). -/
noncomputable def homologySheafTateTwistIso (m a : ℤ) (K : WeilComplex k₀ l X) :
    (homologySheaf a).obj ((tateTwist k₀ l X m).obj K) ≅
      ((homologySheaf a).obj K).constantTwist (WeilSheaf.cyclotomicUnit k₀ l ^ m) :=
  ObjectProperty.isoMk _
    ((_root_.DerivedCategory.homologyFunctor _ a).mapIso
        ((ProEtaleWeilSheaf.rightDerivedFunctorIhomFunctorTateTwistIso m).app K.obj) ≪≫
      ((ProEtaleWeilSheaf.constantTwist k₀ l X
        (WeilSheaf.cyclotomicUnit k₀ l ^ m)).mapDerivedCategoryHomologyFunctorIso a).symm.app
          K.obj ≪≫
      (ProEtaleWeilSheaf.mkConstantTwistIso k₀ l X _ _).symm)

/-- The Tate twist does not change the vanishing of a cohomology sheaf. -/
lemma isZero_homologySheaf_tateTwist_iff (m a : ℤ) (K : WeilComplex k₀ l X) :
    IsZero ((homologySheaf a).obj ((tateTwist k₀ l X m).obj K)) ↔
      IsZero ((homologySheaf a).obj K) := by
  rw [(homologySheafTateTwistIso m a K).isZero_iff, WeilSheaf.isZero_iff_isZero_carrier,
    WeilSheaf.isZero_iff_isZero_carrier]
  rfl

/-- The Tate twist does not change the support of a cohomology sheaf. -/
lemma support_homologySheaf_tateTwist (m a : ℤ) (K : WeilComplex k₀ l X) :
    ((homologySheaf a).obj ((tateTwist k₀ l X m).obj K)).support =
      ((homologySheaf a).obj K).support := by
  rw [WeilSheaf.support_congr (homologySheafTateTwistIso m a K)]
  rfl


/-- The truncation triangle `τ_{<n} K ⟶ K ⟶ τ_{≥n} K ⟶` of a Weil complex `K ≤ n`, whose third
term is concentrated in degree `n`, with the same `𝓗ⁿ` as `K`. -/
lemma exists_distTriang_of_isLE (K : WeilComplex k₀ l X) (n : ℤ) (hK : K.obj.IsLE n) :
    ∃ (K₁ K₃ : WeilComplex k₀ l X) (f : K₁ ⟶ K) (g : K ⟶ K₃) (h : K₃ ⟶ K₁⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang _ ∧ K₁.obj.IsLE (n - 1) ∧ K₃.obj.IsLE n ∧
        K₃.obj.IsGE n ∧ Nonempty ((homologySheaf n).obj K₃ ≅ (homologySheaf n).obj K) := by
  obtain ⟨A, Z, f, g, h, hT, hA, hZ, -, hZ'⟩ := exists_distTriang_truncLT K n
  refine ⟨A, Z, f, g, h, hT, hA, hZ' n hK, hZ, ⟨?_⟩⟩
  have : IsIso ((_root_.DerivedCategory.homologyFunctor _ n).map g.hom) :=
    @_root_.DerivedCategory.isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE _ _ _ _
      ((WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj (Triangle.mk f g h)) hT n n le_rfl
      hA hZ
  exact (ObjectProperty.isoMk _ (asIso ((_root_.DerivedCategory.homologyFunctor _ n).map
    g.hom))).symm


section Devissage

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (Φ : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y) [Φ.CommShift ℤ]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- A functor between Weil complexes commuting with shifts which carries Weil sheaves, placed in
degree zero, to complexes `≥ d` carries a Weil sheaf placed in degree `b` to a complex
`≥ b + d`. -/
theorem isGE_map_singleComplex_of_isGE (d : ℤ)
    (hΦ : ∀ G : WeilSheaf k₀ l X, (Φ.obj (WeilSheaf.toComplex.obj G)).obj.IsGE d)
    (b : ℤ) (G : WeilSheaf k₀ l X) : (Φ.obj (singleComplex b G)).obj.IsGE (b + d) := by
  let L := Φ.obj (WeilSheaf.toComplex.obj G)
  have := hΦ G
  let e : (Φ.obj (singleComplex b G)).obj ≅ L.obj⟦-b⟧ :=
    (WeilComplex.objectProperty k₀ l Y).ι.mapIso
      (Φ.mapIso (singleComplexIsoShift b G) ≪≫ (Φ.commShiftIso (-b)).app _) ≪≫
      ((WeilComplex.objectProperty k₀ l Y).ι.commShiftIso (-b)).app L
  have := _root_.DerivedCategory.TStructure.t.isGE_shift L.obj d (-b) (b + d)
  exact _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm (b + d)

variable [Φ.IsTriangulated]

/-- A triangulated functor between Weil complexes which carries Weil sheaves, placed in degree
zero, to complexes `≥ d` carries complexes concentrated in `[a, a + n - 1]` to complexes
`≥ a + d`, by dévissage along the truncation triangles. -/
theorem isGE_map_of_isGE_of_length (d : ℤ)
    (hΦ : ∀ G : WeilSheaf k₀ l X, (Φ.obj (WeilSheaf.toComplex.obj G)).obj.IsGE d) (n : ℕ) :
    ∀ (a : ℤ) (K : WeilComplex k₀ l X), K.obj.IsGE a → K.obj.IsLE (a + n - 1) →
      (Φ.obj K).obj.IsGE (a + d) := by
  induction n with
  | zero =>
    intro a K _ _
    have : K.obj.IsLE (a - 1) := by simpa using ‹K.obj.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK0 : IsZero K := IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (_root_.DerivedCategory.TStructure.t.isZero K.obj (a - 1) a (by lia))
    exact _root_.DerivedCategory.TStructure.t.isGE_of_isZero
      ((ObjectProperty.ι _).map_isZero (Φ.map_isZero hK0)) _
  | succ n ih =>
    intro a K _ hK
    obtain ⟨A, Z, f, g, h, hT, hA, hZ, hA', hZ'⟩ := exists_distTriang_truncLT K (a + n)
    have : A.obj.IsGE a := hA' a ‹_›
    have : Z.obj.IsLE (a + n) := by
      have := hZ' _ hK
      exact _root_.DerivedCategory.TStructure.t.isLE_of_le _ (a + ↑(n + 1) - 1) _
        (by push_cast; lia)
    obtain ⟨G, ⟨eZ⟩, -⟩ := exists_iso_singleComplex Z (a + n)
    have h₁ := ih a A ‹_› (by simpa using hA)
    have h₃ := isGE_map_singleComplex_of_isGE Φ d hΦ (a + n) G
    let e : (Φ.obj Z).obj ≅ (Φ.obj (singleComplex (a + n) G)).obj :=
      (ObjectProperty.ι _).mapIso (Φ.mapIso eZ)
    have hT' := Φ.map_distinguished _ hT
    refine _root_.DerivedCategory.TStructure.t.isGE₂
      ((WeilComplex.objectProperty k₀ l Y).ι.mapTriangle.obj (Φ.mapTriangle.obj
        (Triangle.mk f g h))) hT' (a + d) h₁ ?_
    have := _root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm (a + n + d)
    exact _root_.DerivedCategory.TStructure.t.isGE_of_ge (Φ.obj Z).obj (a + d) (a + n + d)
      (by lia)

/-- A triangulated functor between Weil complexes which carries Weil sheaves, placed in degree
zero, to complexes `≥ d` carries complexes `≥ a` to complexes `≥ a + d`. -/
theorem isGE_map_of_isGE (d : ℤ)
    (hΦ : ∀ G : WeilSheaf k₀ l X, (Φ.obj (WeilSheaf.toComplex.obj G)).obj.IsGE d)
    {K : WeilComplex k₀ l X} {a : ℤ} (hK : K.obj.IsGE a) : (Φ.obj K).obj.IsGE (a + d) := by
  obtain ⟨-, ⟨c, hc⟩⟩ := K.property.1
  have : K.obj.IsLE c := hc
  have : K.obj.IsLE (a + ((c - a + 1).toNat : ℕ) - 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_le _ c _ (by lia)
  exact isGE_map_of_isGE_of_length Φ d hΦ _ a K hK this

end Devissage

section LeftTExact

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

/-- The pullback of Weil complexes, induced by an exact functor, preserves complexes `≥ a`. -/
theorem isGE_upperStar_obj (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    {K : WeilComplex k₀ l Y} {a : ℤ} (hK : K.obj.IsGE a) :
    ((upperStar φ).obj K).obj.IsGE a :=
  (ProEtaleWeilSheaf.upperStar k₀ l φ).isGE_mapDerivedCategory_obj K.obj a

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product with a lisse Weil sheaf preserves complexes `≥ a`: it carries a Weil
sheaf placed in degree zero to a complex `≥ 0`, being a right derived functor. -/
theorem isGE_tensorLisse_obj (F : WeilSheaf k₀ l X) (hF : F.IsLisse)
    {K : WeilComplex k₀ l X} {a : ℤ} (hK : K.obj.IsGE a) :
    ((tensorLisse F hF).obj K).obj.IsGE a := by
  simpa using isGE_map_of_isGE (tensorLisse F hF) 0 (fun G ↦
    (ProEtaleWeilSheaf.ihomFunctor k₀ l X
      (F.dual hF).obj).isGE_rightDerivedFunctor_obj_singleFunctor G.obj) hK

variable [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- The direct image with compact support preserves complexes `≥ a`: it carries a Weil sheaf
placed in degree zero to a complex `≥ 0`. -/
theorem isGE_derivedLowerShriek_obj (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {K : WeilComplex k₀ l X} {a : ℤ} (hK : K.obj.IsGE a) :
    ((derivedLowerShriek k₀ l f).obj K).obj.IsGE a := by
  simpa using isGE_map_of_isGE (derivedLowerShriek k₀ l f) 0 (fun G ↦
    (isGE_iff_isZero_homologySheaf _ 0).2 fun _ hn ↦
      WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G hn) hK

end LeftTExact

end WeilComplex

/-- **Fourier inversion** on the line: `FT_{ψ⁻¹} ∘ FT_ψ ≅ (-)(-1)`, the shifts
`[-2][1][1]` of `nonempty_iso_fourierTransform_comp_inv` cancelled.
(blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_fourierTransform_comp_fourierTransform_inv_iso
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) :
    Nonempty (fourierTransform ψ ⋙ fourierTransform ψ⁻¹ ≅
      WeilComplex.tateTwist k₀ l (affineLine k₀) (-1)) :=
  ⟨(nonempty_iso_fourierTransform_comp_inv ψ hψ).some ≪≫
    Functor.isoWhiskerLeft (WeilComplex.tateTwist k₀ l (affineLine k₀) (-1))
      (Functor.isoWhiskerLeft (shiftFunctor _ (-2 : ℤ))
        (shiftFunctorAdd' (WeilComplex k₀ l (affineLine k₀)) (1 : ℤ) 1 2 (by norm_num)).symm ≪≫
        shiftFunctorCompIsoId _ (-2 : ℤ) 2 (by norm_num)) ≪≫
    Functor.rightUnitor _⟩

/-- `FT_ψ` lowers the lower bound of the amplitude by at most one: `pr₁^*` and the tensor
product with the lisse kernel are exact, `Rpr₂!` is left t-exact, and the shift `[1]` lowers
the bound by one. -/
theorem isGE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) {a : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsGE a) :
    ((fourierTransform ψ).obj K).obj.IsGE (a - 1) :=
  WeilComplex.isGE_shift_obj _ a 1 (a - 1) (by lia) (WeilComplex.isGE_derivedLowerShriek_obj _
    (WeilComplex.isGE_tensorLisse_obj _ _ (WeilComplex.isGE_upperStar_obj _ hK)))

/-- The inverse of `FT_ψ` lowers the lower bound of the amplitude by at most one: by Fourier
inversion, its Tate twist `(-1)` is `FT_{ψ⁻¹}`. -/
theorem isGE_fourierTransform_inv_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {a : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsGE a) :
    haveI := isEquivalence_fourierTransform (l := l) ψ hψ
    ((fourierTransform ψ).inv.obj K).obj.IsGE (a - 1) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  obtain ⟨e⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ hψ
  have h := isGE_fourierTransform_obj ψ⁻¹ hK
  rw [WeilComplex.isGE_iff_isZero_homologySheaf] at h ⊢
  intro b hb
  rw [← WeilComplex.isZero_homologySheaf_tateTwist_iff (-1)]
  exact (h b hb).of_iso ((WeilComplex.homologySheaf b).mapIso ((e.app _).symm ≪≫
    (fourierTransform ψ⁻¹).mapIso ((fourierTransform ψ).asEquivalence.counitIso.app K)))

/-- `FT_ψ` raises the upper bound of the amplitude by at most one: the truncation
`τ_{≥ m + 2} FT_ψ(K)` is right orthogonal to `FT_ψ(K)`, since by adjunction
`Hom(FT_ψ K, Z) = Hom(K, FT_ψ⁻¹ Z)` and `FT_ψ⁻¹ Z ≥ m + 1`. -/
theorem isLE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {m : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.obj.IsLE m) :
    ((fourierTransform ψ).obj K).obj.IsLE (m + 1) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  obtain ⟨A, Z, f, g, h, hT, hA, hZ, -, -⟩ :=
    WeilComplex.exists_distTriang_truncLT ((fourierTransform ψ).obj K) (m + 2)
  let adj := (fourierTransform ψ).asEquivalence.toAdjunction
  have hg : g = 0 := by
    have : ((fourierTransform ψ).inv.obj Z).obj.IsGE (m + 1) := by
      convert isGE_fourierTransform_inv_obj ψ hψ hZ using 2
      lia
    have h0 : adj.homEquiv K Z g = 0 := (ObjectProperty.ι _).map_injective (by
      rw [Functor.map_zero]
      exact _root_.DerivedCategory.TStructure.t.zero (X := K.obj)
        (Y := ((fourierTransform ψ).inv.obj Z).obj) _ m (m + 1))
    have := (adj.homEquiv K Z).symm_apply_apply g
    rw [h0, Adjunction.homEquiv_counit] at this
    simpa using this.symm
  -- `g = 0` makes `Z` a direct summand of `A[1] ≤ m`, while `Z ≥ m + 2`
  have hZ0 : IsZero Z := by
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₃ _ hT (𝟙 Z) (by simp [hg])
    have := WeilComplex.isLE_shift_obj A (m + 2 - 1) 1 m (by lia) hA
    have hr0 : r = 0 := (ObjectProperty.ι _).map_injective (by
      rw [Functor.map_zero]
      exact _root_.DerivedCategory.TStructure.t.zero (X := (A⟦(1 : ℤ)⟧).obj) (Y := Z.obj) _ m
        (m + 2))
    rw [IsZero.iff_id_eq_zero, hr, hr0, Limits.comp_zero]
  have : A.obj.IsLE (m + 1) := by
    convert hA using 2
    lia
  have : Z.obj.IsLE (m + 1) := _root_.DerivedCategory.TStructure.t.isLE_of_isZero
    ((ObjectProperty.ι _).map_isZero hZ0) _
  exact _root_.DerivedCategory.TStructure.t.isLE₂
    ((WeilComplex.objectProperty k₀ l _).ι.mapTriangle.obj (Triangle.mk f g h)) hT (m + 1)
    ‹_› ‹_›

omit [Finite k₀] in
/-- The complement of a finite set of closed points of the affine line is a dense open: it
contains the image of the generic point of the irreducible geometric line, which is not a
closed point since the affine line is not a single point. -/
theorem affineLine.exists_opens_dense_compl_finite (S : Set (affineLine k₀).finitePoints)
    (hS : S.Finite) :
    ∃ V : (affineLine k₀).Opens, Dense (V : Set (affineLine k₀)) ∧
      ∀ x ∈ S, x.1 ∉ (V : Set (affineLine k₀)) := by
  set T : Set (affineLine k₀) := ⋃ x ∈ S, {x.1} with hT
  have hTc : IsClosed T :=
    hS.isClosed_biUnion fun x _ ↦ (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
  refine ⟨⟨Tᶜ, hTc.isOpen_compl⟩, ?_, fun x hx hxV ↦ hxV (Set.mem_biUnion hx rfl)⟩
  set prA := (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj
  have : IrreducibleSpace (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
    Scheme.Hom.irreducibleSpace_geometricFiber _
  have hsp (z : affineLine k₀) : prA.base (genericPoint _) ⤳ z := by
    obtain ⟨z', hz'⟩ :=
      Scheme.Hom.geometricFiberProj_surjective (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) z
    have h1 := ((genericPoint_spec _).specializes (Set.mem_univ z')).map prA.continuous
    rwa [hz'] at h1
  have hξ : prA.base (genericPoint _) ∈ Tᶜ := by
    intro hS'
    obtain ⟨x, -, hxe⟩ := Set.mem_iUnion₂.1 hS'
    have hcl := (affineLine k₀).isClosed_singleton_of_mem_finitePoints x.2
    rw [Set.mem_singleton_iff] at hxe
    obtain ⟨a, b, hab⟩ := affineLine.nontrivial k₀
    have key (z : affineLine k₀) : z = x.1 := by
      have h1 := hsp z
      rw [hxe] at h1
      exact h1.mem_closed hcl rfl
    exact hab ((key a).trans (key b).symm)
  intro z
  exact closure_mono (Set.singleton_subset_iff.2 hξ) (specializes_iff_mem_closure.1 (hsp z))

/-- A sheaf of finite support transforms into a complex `≤ -1`: it vanishes on the dense
complement of its support, so its transform is a lisse sheaf placed in degree `-1`
(`AlgebraicGeometry.WeilSheaf.exists_isLisse_iso_fourierTransform_of_isZero_upperStar`). -/
theorem isLE_fourierTransform_toComplex_of_support_finite (ψ : AddChar k₀ (PadicAlgCl l))
    (P : WeilSheaf k₀ l (affineLine k₀)) (hP : P.support.Finite) :
    ((fourierTransform ψ).obj (WeilSheaf.toComplex.obj P)).obj.IsLE (-1) := by
  obtain ⟨V, hV, hVS⟩ := affineLine.exists_opens_dense_compl_finite _ hP
  have hz : IsZero ((WeilSheaf.upperStar V.ι).obj P) := by
    refine WeilSheaf.isZero_upperStar_of_forall_notMem_support V.ι P fun y hy ↦ ?_
    refine hVS _ hy ?_
    change V.ι.base y.1 ∈ (V : Set (affineLine k₀))
    rw [Scheme.Opens.ι_apply]
    exact y.1.2
  have : IsDominant V.ι := ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩
  have : TopologicalSpace.NoetherianSpace (affineLine k₀) := by
    have := LocallyOfFiniteType.isLocallyNoetherian (affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    have : IsNoetherian (affineLine k₀) := {}
    infer_instance
  have : TopologicalSpace.NoetherianSpace V :=
    V.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : QuasiCompact V.ι := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  obtain ⟨B', -, ⟨e⟩⟩ :=
    WeilSheaf.exists_isLisse_iso_fourierTransform_of_isZero_upperStar ψ V.ι P hz
  rw [WeilComplex.isLE_iff_isZero_homologySheaf]
  intro a ha
  exact (WeilSheaf.isZero_homologySheaf_toShiftedComplex (by lia) B').of_iso
    ((WeilComplex.homologySheaf a).mapIso e)

/-- A complex concentrated in degree `n` whose `𝓗ⁿ` has finite support transforms into a
complex `≤ n - 1`: it is a sheaf of finite support placed in degree `n`. -/
theorem isLE_fourierTransform_of_isGE_of_isLE (ψ : AddChar k₀ (PadicAlgCl l)) {n : ℤ}
    {K : WeilComplex k₀ l (affineLine k₀)} (hge : K.obj.IsGE n) (hle : K.obj.IsLE n)
    (hK : ((WeilComplex.homologySheaf n).obj K).support.Finite) :
    ((fourierTransform ψ).obj K).obj.IsLE (n - 1) := by
  obtain ⟨G, ⟨e⟩, ⟨eG⟩⟩ := WeilComplex.exists_iso_singleComplex K n
  have h := WeilComplex.isLE_shift_obj _ (-1) (-n) (n - 1) (by lia)
    (isLE_fourierTransform_toComplex_of_support_finite ψ G
      ((WeilSheaf.support_congr (ObjectProperty.isoMk (X := (WeilComplex.homologySheaf n).obj K)
        (Y := G) _ eG)) ▸ hK))
  exact _root_.DerivedCategory.TStructure.t.isLE_of_iso
    (X := (((fourierTransform ψ).obj (WeilSheaf.toComplex.obj G))⟦-n⟧).obj)
    ((WeilComplex.objectProperty k₀ l _).ι.mapIso
      ((fourierTransform ψ).mapIso (e ≪≫ WeilComplex.singleComplexIsoShift n G) ≪≫
        ((fourierTransform ψ).commShiftIso (-n)).app _)).symm (n - 1)

end AlgebraicGeometry
