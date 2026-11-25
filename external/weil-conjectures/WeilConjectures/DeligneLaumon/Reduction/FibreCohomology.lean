/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk
public import WeilConjectures.DeligneLaumon.Reduction.Weights

/-!
# Higher direct images over a base quasi-finite over `k₀`

Let `f : X ⟶ Y` be a separated morphism of finite type of `k₀`-schemes and let `t : T ⟶ Y` be a
morphism from a `k₀`-scheme quasi-finite over `k₀` (for instance the spectrum of the residue
field at a closed point of `Y`), with fibre product `X_T = X ×_Y T`. Then

`H_c^0(T, t^* Rⁱf₀!F) ≅ H_c^i(X_T, F|_{X_T})`

as Frobenius modules: compact support base change identifies `t^* Rf₀!F` with `Rf_T₀!(F|_{X_T})`,
composition identifies `R(X_T ⟶ Spec k₀)₀!` with `R(T ⟶ Spec k₀)₀! ∘ Rf_T₀!`, and the direct image
with compact support along the quasi-finite `T ⟶ Spec k₀` is exact, so it commutes with the
cohomology sheaves.

The last step, and the commutation of `t^*` with the cohomology sheaves, are instances of a
general statement: a triangulated functor `Φ` between Weil complexes which carries Weil sheaves,
placed in degree zero, to complexes concentrated in degree zero is t-exact, by dévissage along
the truncation triangles, hence `𝓗ⁱ(Φ K) ≅ 𝓗⁰(Φ 𝓗ⁱ(K))`.

## Main statements

- `AlgebraicGeometry.WeilComplex.isGE_map`, `AlgebraicGeometry.WeilComplex.isLE_map` and
  `AlgebraicGeometry.WeilComplex.nonempty_homologySheaf_map_iso`: t-exactness of functors carrying
  sheaves to sheaves, and their commutation with the cohomology sheaves.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber`
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

open _root_.DerivedCategory

/-- The truncation `τ_{<b}K` of a Weil complex is a Weil complex (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`, auxiliary). -/
theorem objectProperty_truncLT (K : WeilComplex k₀ l X) (b : ℤ) :
    WeilComplex.objectProperty k₀ l X ((TStructure.t.truncLT b).obj K.obj) := by
  obtain ⟨⟨a, ha⟩, -⟩ := K.property.1
  have : TStructure.t.IsGE K.obj a := ha
  refine ⟨⟨⟨a, inferInstance⟩, ⟨b - 1, TStructure.t.isLE_truncLT_obj _ _ _ (by lia)⟩⟩,
    fun m ↦ ?_⟩
  by_cases hm : m < b
  · have := isIso_homologyFunctor_map_truncLTι_app K.obj b m hm
    exact (WeilSheaf.objectProperty k₀ l X).prop_of_iso
      (asIso ((homologyFunctor _ m).map ((TStructure.t.truncLTι b).app K.obj))).symm (K.2.2 m)
  · have : ((TStructure.t.truncLT b).obj K.obj).IsLE (b - 1) :=
      TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
    exact (WeilSheaf.objectProperty k₀ l X).prop_of_isZero (isZero_of_isLE _ (b - 1) _ (by lia))

/-- A Weil complex concentrated in degree `b` is a Weil sheaf placed in degree `b`, namely its
`b`-th cohomology sheaf (blueprint: `theorem-pure-lisse-sheaves-over-relative--1`, auxiliary). -/
theorem exists_iso_singleComplex (Z : WeilComplex k₀ l X) (b : ℤ) [Z.obj.IsGE b]
    [Z.obj.IsLE b] : ∃ G : WeilSheaf k₀ l X, Nonempty (Z ≅ singleComplex b G) ∧
      Nonempty ((homologyFunctor _ b).obj Z.obj ≅ G.obj) := by
  obtain ⟨G, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE Z.obj b
  let eG : (homologyFunctor _ b).obj Z.obj ≅ G :=
    (homologyFunctor _ b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app G
  exact ⟨⟨G, (WeilSheaf.objectProperty k₀ l X).prop_of_iso eG (Z.2.2 b)⟩,
    ⟨ObjectProperty.isoMk _ e⟩, ⟨eG⟩⟩

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The truncation triangle `τ_{<b}K ⟶ K ⟶ Z ⟶` of a Weil complex, as a distinguished
triangle of Weil complexes (blueprint: `theorem-pure-lisse-sheaves-over-relative--1`, auxiliary). -/
theorem exists_distTriang_truncLT (K : WeilComplex k₀ l X) (b : ℤ) :
    ∃ (A Z : WeilComplex k₀ l X) (f : A ⟶ K) (g : K ⟶ Z) (h : Z ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang (WeilComplex k₀ l X) ∧ A.obj.IsLE (b - 1) ∧
        Z.obj.IsGE b ∧ (∀ a, K.obj.IsGE a → A.obj.IsGE a) ∧
        (∀ c, K.obj.IsLE c → Z.obj.IsLE c) := by
  let A : WeilComplex k₀ l X := ⟨_, objectProperty_truncLT K b⟩
  let f : A ⟶ K := ObjectProperty.homMk ((TStructure.t.truncLTι b).app K.obj)
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let e := isoTriangleOfIso₁₂
    ((WeilComplex.objectProperty k₀ l X).ι.mapTriangle.obj (Triangle.mk f g h)) _ hT
    (TStructure.t.triangleLTGE_distinguished b K.obj) (Iso.refl _) (Iso.refl _) (by
      simp
      rfl)
  have eZ : Z.obj ≅ (TStructure.t.truncGE b).obj K.obj := Triangle.π₃.mapIso e
  refine ⟨A, Z, f, g, h, hT, TStructure.t.isLE_truncLT_obj _ _ _ (by lia),
    TStructure.t.isGE_of_iso eZ.symm b, fun a ha ↦ ?_, fun c hc ↦ ?_⟩
  · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj K.obj) a)
  · exact TStructure.t.isLE_of_iso eZ.symm c

variable [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (Φ : WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y) [Φ.CommShift ℤ]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] in
/-- A functor between Weil complexes commuting with shifts which carries Weil sheaves, placed in
degree zero, to complexes concentrated in degree zero carries a Weil sheaf placed in degree `b`
to a complex concentrated in degree `b` (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem isGE_and_isLE_map_singleComplex
    (hΦ : ∀ (G : WeilSheaf k₀ l X) (n : ℤ), n ≠ 0 →
      IsZero ((homologySheaf n).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (b : ℤ) (G : WeilSheaf k₀ l X) :
    (Φ.obj (singleComplex b G)).obj.IsGE b ∧ (Φ.obj (singleComplex b G)).obj.IsLE b := by
  let L := Φ.obj (WeilSheaf.toComplex.obj G)
  have : L.obj.IsGE 0 := (isGE_iff _ 0).2 fun n hn ↦
    (isZero_homologySheaf_obj_iff n L).1 (hΦ G n hn.ne)
  have : L.obj.IsLE 0 := (isLE_iff _ 0).2 fun n hn ↦
    (isZero_homologySheaf_obj_iff n L).1 (hΦ G n hn.ne')
  let e : (Φ.obj (singleComplex b G)).obj ≅ L.obj⟦-b⟧ :=
    (WeilComplex.objectProperty k₀ l Y).ι.mapIso
      (Φ.mapIso (singleComplexIsoShift b G) ≪≫ (Φ.commShiftIso (-b)).app _) ≪≫
      ((WeilComplex.objectProperty k₀ l Y).ι.commShiftIso (-b)).app L
  have := TStructure.t.isGE_shift L.obj 0 (-b) b
  have := TStructure.t.isLE_shift L.obj 0 (-b) b
  exact ⟨TStructure.t.isGE_of_iso e.symm b, TStructure.t.isLE_of_iso e.symm b⟩

variable [Φ.IsTriangulated]

/-- A triangulated functor between Weil complexes which carries Weil sheaves, placed in degree
zero, to complexes concentrated in degree zero carries complexes concentrated in `[a, a + n - 1]`
to complexes concentrated in `[a, a + n - 1]` (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem isGE_and_isLE_map_of_length
    (hΦ : ∀ (G : WeilSheaf k₀ l X) (n : ℤ), n ≠ 0 →
      IsZero ((homologySheaf n).obj (Φ.obj (WeilSheaf.toComplex.obj G)))) (n : ℕ) :
    ∀ (a : ℤ) (K : WeilComplex k₀ l X), K.obj.IsGE a → K.obj.IsLE (a + n - 1) →
      (Φ.obj K).obj.IsGE a ∧ (Φ.obj K).obj.IsLE (a + n - 1) := by
  induction n with
  | zero =>
    intro a K _ _
    have : K.obj.IsLE (a - 1) := by simpa using ‹K.obj.IsLE (a + ↑(0 : ℕ) - 1)›
    have hK0 : IsZero K := IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
      (TStructure.t.isZero K.obj (a - 1) a (by lia))
    have h := (ObjectProperty.ι _).map_isZero (Φ.map_isZero hK0)
    exact ⟨TStructure.t.isGE_of_isZero h _, TStructure.t.isLE_of_isZero h _⟩
  | succ n ih =>
    intro a K _ hK
    obtain ⟨A, Z, f, g, h, hT, hA, hZ, hA', hZ'⟩ := exists_distTriang_truncLT K (a + n)
    have : A.obj.IsGE a := hA' a ‹_›
    have : Z.obj.IsLE (a + n) := by
      have := hZ' _ hK
      exact TStructure.t.isLE_of_le _ (a + ↑(n + 1) - 1) _ (by push_cast; lia)
    obtain ⟨G, ⟨eZ⟩, -⟩ := exists_iso_singleComplex Z (a + n)
    obtain ⟨h₁, h₂⟩ := ih a A ‹_› (by simpa using hA)
    obtain ⟨h₃, h₄⟩ := isGE_and_isLE_map_singleComplex Φ hΦ (a + n) G
    let e : (Φ.obj Z).obj ≅ (Φ.obj (singleComplex (a + n) G)).obj :=
      (ObjectProperty.ι _).mapIso (Φ.mapIso eZ)
    have hT' := Φ.map_distinguished _ hT
    refine ⟨TStructure.t.isGE₂
      ((WeilComplex.objectProperty k₀ l Y).ι.mapTriangle.obj (Φ.mapTriangle.obj
        (Triangle.mk f g h))) hT' a h₁ ?_, TStructure.t.isLE₂
      ((WeilComplex.objectProperty k₀ l Y).ι.mapTriangle.obj (Φ.mapTriangle.obj
        (Triangle.mk f g h))) hT' _ ?_ ?_⟩
    · have := TStructure.t.isGE_of_iso e.symm (a + n)
      exact TStructure.t.isGE_of_ge (Φ.obj Z).obj a (a + n) (by lia)
    · exact TStructure.t.isLE_of_le (Φ.obj A).obj (a + n - 1) _ (by push_cast; lia)
    · have := TStructure.t.isLE_of_iso e.symm (a + n)
      exact TStructure.t.isLE_of_le (Φ.obj Z).obj (a + n) _ (by push_cast; lia)

/-- A triangulated functor between Weil complexes which carries Weil sheaves, placed in degree
zero, to complexes concentrated in degree zero preserves complexes concentrated in degrees
`≥ a` (blueprint: `theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem isGE_map
    (hΦ : ∀ (G : WeilSheaf k₀ l X) (n : ℤ), n ≠ 0 →
      IsZero ((homologySheaf n).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (K : WeilComplex k₀ l X) (a : ℤ) [K.obj.IsGE a] : (Φ.obj K).obj.IsGE a := by
  obtain ⟨-, ⟨c, hc⟩⟩ := K.property.1
  have : K.obj.IsLE c := hc
  have : K.obj.IsLE (a + ((c - a + 1).toNat : ℕ) - 1) := TStructure.t.isLE_of_le _ c _ (by lia)
  exact (isGE_and_isLE_map_of_length Φ hΦ _ a K ‹_› this).1

/-- A triangulated functor between Weil complexes which carries Weil sheaves, placed in degree
zero, to complexes concentrated in degree zero preserves complexes concentrated in degrees
`≤ c` (blueprint: `theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem isLE_map
    (hΦ : ∀ (G : WeilSheaf k₀ l X) (n : ℤ), n ≠ 0 →
      IsZero ((homologySheaf n).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (K : WeilComplex k₀ l X) (c : ℤ) [K.obj.IsLE c] : (Φ.obj K).obj.IsLE c := by
  obtain ⟨⟨a, ha⟩, -⟩ := K.property.1
  obtain ⟨a', h₁, h₂⟩ : ∃ a', a' ≤ a ∧ a' ≤ c + 1 :=
    ⟨min a (c + 1), min_le_left _ _, min_le_right _ _⟩
  have : K.obj.IsGE a := ha
  have : K.obj.IsGE a' := TStructure.t.isGE_of_ge _ a' a h₁
  have : K.obj.IsLE (a' + ((c + 1 - a').toNat : ℕ) - 1) :=
    TStructure.t.isLE_of_le _ c _ (by lia)
  have := (isGE_and_isLE_map_of_length Φ hΦ _ _ K ‹_› this).2
  exact TStructure.t.isLE_of_le _ (a' + ((c + 1 - a').toNat : ℕ) - 1) c (by lia)

/-- **A t-exact functor commutes with the cohomology sheaves.** A triangulated functor `Φ`
between Weil complexes which carries Weil sheaves, placed in degree zero, to complexes
concentrated in degree zero satisfies `𝓗ⁱ(Φ K) ≅ 𝓗⁰(Φ 𝓗ⁱ(K))` (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`). -/
theorem nonempty_homologySheaf_map_iso
    (hΦ : ∀ (G : WeilSheaf k₀ l X) (n : ℤ), n ≠ 0 →
      IsZero ((homologySheaf n).obj (Φ.obj (WeilSheaf.toComplex.obj G))))
    (K : WeilComplex k₀ l X) (i : ℤ) :
    Nonempty ((homologySheaf i).obj (Φ.obj K) ≅
      (homologySheaf 0).obj (Φ.obj (WeilSheaf.toComplex.obj ((homologySheaf i).obj K)))) := by
  obtain ⟨A, Z, f, g, h, hT, hA, hZ, -, -⟩ := exists_distTriang_truncLT K i
  obtain ⟨A', Z', f', g', h', hT', hA'', hZ'', hA''', -⟩ := exists_distTriang_truncLT Z (i + 1)
  have : A'.obj.IsGE i := hA''' i hZ
  have : A'.obj.IsLE i := by simpa using hA''
  obtain ⟨G, ⟨eA'⟩, ⟨eG⟩⟩ := exists_iso_singleComplex A' i
  let P := WeilComplex.objectProperty k₀ l X
  let Q := WeilComplex.objectProperty k₀ l Y
  -- `𝓗ⁱK ≅ 𝓗ⁱZ ≅ 𝓗ⁱA'`
  have : IsIso ((homologyFunctor _ i).map g.hom) :=
    @isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE _ _ _ _
      (P.ι.mapTriangle.obj (Triangle.mk f g h)) hT i i le_rfl hA hZ
  have : IsIso ((homologyFunctor _ i).map f'.hom) :=
    @isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE _ _ _ _
      (P.ι.mapTriangle.obj (Triangle.mk f' g' h')) hT' (i + 1) i (by lia) hA'' hZ''
  let eK : G ≅ (homologySheaf i).obj K := ObjectProperty.isoMk _ (eG.symm ≪≫
    asIso ((homologyFunctor _ i).map f'.hom) ≪≫ (asIso ((homologyFunctor _ i).map g.hom)).symm)
  -- `𝓗ⁱ(Φ K) ≅ 𝓗ⁱ(Φ Z) ≅ 𝓗ⁱ(Φ A')`
  have : IsIso ((homologyFunctor _ i).map (Φ.map g).hom) :=
    @isIso_homologyFunctor_map_mor₂_of_isLE_of_isGE _ _ _ _
      (Q.ι.mapTriangle.obj (Φ.mapTriangle.obj (Triangle.mk f g h))) (Φ.map_distinguished _ hT)
      i i le_rfl (isLE_map Φ hΦ A (i - 1)) (isGE_map Φ hΦ Z i)
  have : IsIso ((homologyFunctor _ i).map (Φ.map f').hom) :=
    @isIso_homologyFunctor_map_mor₁_of_isLE_of_isGE _ _ _ _
      (Q.ι.mapTriangle.obj (Φ.mapTriangle.obj (Triangle.mk f' g' h')))
      (Φ.map_distinguished _ hT') (i + 1) i (by lia) (isLE_map Φ hΦ A' (i + 1 - 1))
      (isGE_map Φ hΦ Z' (i + 1))
  -- `Φ A' ≅ (Φ G)[-i]`
  let L := Φ.obj (WeilSheaf.toComplex.obj G)
  let e : (Φ.obj A').obj ≅ L.obj⟦-i⟧ :=
    Q.ι.mapIso (Φ.mapIso (eA' ≪≫ singleComplexIsoShift i G) ≪≫ (Φ.commShiftIso (-i)).app _) ≪≫
      (Q.ι.commShiftIso (-i)).app L
  let E : (homologyFunctor _ i).obj (Φ.obj K).obj ≅ (homologyFunctor _ 0).obj L.obj :=
    asIso ((homologyFunctor _ i).map (Φ.map g).hom) ≪≫
      (asIso ((homologyFunctor _ i).map (Φ.map f').hom)).symm ≪≫
      (homologyFunctor _ i).mapIso e ≪≫ ((homologyFunctor _ 0).shiftIso (-i) i 0 (by lia)).app _
  let E' : (homologySheaf i).obj (Φ.obj K) ≅ (homologySheaf 0).obj L := ObjectProperty.isoMk _ E
  exact ⟨E' ≪≫
    (homologySheaf 0).mapIso (Φ.mapIso (WeilSheaf.toComplex.mapIso eK))⟩

end WeilComplex

variable {X Y X' T : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [X'.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
  {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  {f' : X' ⟶ T} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f'] [LocallyOfFiniteType f']
  [QuasiCompact f'] [IsSeparated (T ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))] [LocallyQuasiFinite (T ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X' ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))]
  {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {t : T ⟶ Y}
  [t.IsOver (Spec (CommRingCat.of k₀))]

/-- **Compactly supported cohomology of a fibre over a quasi-finite base.** For a cartesian square
`X' = X ×_Y T` of `k₀`-schemes with `f : X ⟶ Y` separated of finite type and `T` quasi-finite over
`k₀`, `H_c^0(T, t^* Rⁱf₀!F) ≅ H_c^i(X', g^*F)` as Frobenius modules (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`, the identification of the stalks of `Rⁱh₀!F` with the
compactly supported cohomology of the fibres by compact support base change). -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber
    (hH : IsPullback g f' f t) (F : WeilSheaf k₀ l X) (i : ℕ) :
    Nonempty ((((WeilSheaf.upperStar t).obj ((WeilSheaf.higherLowerShriek k₀ l f i).obj
      F)).compactlySupportedCohomology 0).Equiv
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology i)) := by
  -- `t^*` and `R(T ⟶ Spec k₀)₀!` carry sheaves to sheaves
  have ht (G : WeilSheaf k₀ l Y) (n : ℤ) (hn : n ≠ 0) : IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.upperStar t).obj (WeilSheaf.toComplex.obj G))) :=
    (WeilComplex.isZero_homologySheaf_singleComplex hn _).of_iso
      ((WeilComplex.homologySheaf n).mapIso (WeilComplex.upperStarToComplexIso t G))
  have ha (G : WeilSheaf k₀ l T) (n : ℤ) (hn : n ≠ 0) : IsZero ((WeilComplex.homologySheaf n).obj
      ((WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj G))) := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
      exact isZero_higherLowerShriek_of_quasiFinite (T ↘ Spec (CommRingCat.of k₀)) m
        (by exact_mod_cast hn) G
  let L := (WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)
  -- `t^* 𝓗ⁱ(Rf₀!F) ≅ 𝓗ⁱ(t^* Rf₀!F)`
  obtain ⟨e₁⟩ := WeilComplex.nonempty_homologySheaf_map_iso (WeilComplex.upperStar t) ht L i
  let e₁' : (WeilSheaf.upperStar t).obj ((WeilComplex.homologySheaf i).obj L) ≅
      (WeilComplex.homologySheaf i).obj ((WeilComplex.upperStar t).obj L) :=
    (WeilSheaf.toComplexCompHomologySheafIso.app _).symm ≪≫
      (WeilComplex.homologySheaf 0).mapIso (WeilComplex.upperStarToComplexIso t _).symm ≪≫ e₁.symm
  -- `𝓗ⁱ(Ra₀! K) ≅ 𝓗⁰(Ra₀! 𝓗ⁱ(K))` for `K = t^* Rf₀!F`
  obtain ⟨e₂⟩ := WeilComplex.nonempty_homologySheaf_map_iso
    (WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))) ha
    ((WeilComplex.upperStar t).obj L) i
  -- base change and composition
  obtain ⟨e₃⟩ := WeilComplex.nonempty_upperStar_derivedLowerShriek_iso (k₀ := k₀) (l := l) hH
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f'
    (T ↘ Spec (CommRingCat.of k₀))
  let E : (WeilComplex.upperStar t).obj L ≅ (WeilComplex.derivedLowerShriek k₀ l f').obj
      (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar g).obj F)) :=
    e₃.app _ ≪≫
      (WeilComplex.derivedLowerShriek k₀ l f').mapIso (WeilComplex.upperStarToComplexIso g F)
  let E' := (WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))).mapIso E ≪≫
    (e₅.app _).symm ≪≫ (WeilComplex.derivedLowerShriekCongr (comp_over f' _)).app _
  let e₀ : (WeilSheaf.higherLowerShriek k₀ l f i).obj F ≅ (WeilComplex.homologySheaf i).obj L :=
    Iso.refl _
  let Ψ : (WeilComplex.homologySheaf 0).obj
      ((WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))).obj
        (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar t).obj
          ((WeilSheaf.higherLowerShriek k₀ l f i).obj F)))) ≅
      (WeilComplex.homologySheaf i).obj
        ((WeilComplex.derivedLowerShriek k₀ l (X' ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj ((WeilSheaf.upperStar g).obj F))) :=
    (WeilComplex.homologySheaf 0).mapIso
      ((WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))).mapIso
        (WeilSheaf.toComplex.mapIso ((WeilSheaf.upperStar t).mapIso e₀ ≪≫ e₁'))) ≪≫
      e₂.symm ≪≫ (WeilComplex.homologySheaf i).mapIso E'
  have h₁ (G : WeilSheaf k₀ l T) : G.compactlySupportedCohomology 0 =
      ((WeilComplex.homologySheaf 0).obj
        ((WeilComplex.derivedLowerShriek k₀ l (T ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj G))).globalSections := rfl
  have h₂ (G : WeilSheaf k₀ l X') : G.compactlySupportedCohomology i =
      ((WeilComplex.homologySheaf i).obj
        ((WeilComplex.derivedLowerShriek k₀ l (X' ↘ Spec (CommRingCat.of k₀))).obj
          (WeilSheaf.toComplex.obj G))).globalSections := rfl
  rw [h₁, h₂]
  exact ⟨WeilSheaf.globalSectionsEquivOfIso Ψ⟩

/-- **The fibre over a closed point.** Let `f : X ⟶ Y` be a separated morphism of finite type of
`k₀`-schemes and `y` a closed point of `Y` of degree `d = [κ(y) : k₀]`. The fibre
`X' = X ×_Y Spec κ(y)`, with its map `g : X' ⟶ X`, is a separated `k₀`-scheme of finite type,
and compact support base change identifies the stalks of the `Rⁱf₀!F` at `y` with the compactly
supported cohomology of the fibre: `H_c^i(X' ⊗ k̄, g^*F)` vanishes if `Rⁱf₀!F` does, and

`det (1 - T^d F_y ∣ (Rⁱf₀!F)_ȳ) = det (1 - T F ∣ H_c^i(X' ⊗ k̄, g^*F))`

(proper base change at the spectrum of a residue field). -/
theorem WeilSheaf.exists_fiber_expand_charpolyRev_stalk_higherLowerShriek (y : Y.finitePoints) :
    ∃ (X' : Scheme.{u}) (_ : X'.Over (Spec (CommRingCat.of k₀))) (g : X' ⟶ X)
      (_ : g.IsOver (Spec (CommRingCat.of k₀)))
      (_ : IsSeparated (X' ↘ Spec (CommRingCat.of k₀)))
      (_ : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)))
      (_ : QuasiCompact (X' ↘ Spec (CommRingCat.of k₀))), ∀ (F : WeilSheaf k₀ l X) (i : ℕ),
        (IsZero ((WeilSheaf.higherLowerShriek k₀ l f i).obj F) →
          Subsingleton (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology i).carrier) ∧
        Polynomial.expand _ ((Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1)
          (((WeilSheaf.higherLowerShriek k₀ l f i).obj F).stalk y).frobeniusEnd.charpolyRev =
        (((WeilSheaf.upperStar g).obj F).compactlySupportedCohomology
          i).frobeniusEnd.charpolyRev := by
  -- the closed point `y`, as the spectrum of its residue field, a finite extension of `k₀`
  let Z : Scheme.{u} := Spec (Y.residueField y.1)
  let t : Z ⟶ Y := Y.fromSpecResidueField y.1
  let : Z.Over (Spec (CommRingCat.of k₀)) := ⟨t ≫ Y ↘ Spec (CommRingCat.of k₀)⟩
  have : t.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have : Finite (Y.residueField y.1) := y.2
  have hfin : IsFinite (t ≫ Y ↘ Spec (CommRingCat.of k₀)) := by
    rw [← Scheme.Hom.specMap_residueFieldAlgebraMap, IsFinite.SpecMap_iff]
    let := ((Y ↘ Spec (CommRingCat.of k₀)).residueFieldAlgebraMap y.1).toAlgebra
    exact Module.Finite.of_finite
  have : IsFinite (Z ↘ Spec (CommRingCat.of k₀)) := hfin
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀)) := by
    rw [← comp_over f (Spec (CommRingCat.of k₀))]
    infer_instance
  -- the fibre `X' = X ×_Y Spec κ(y)`
  obtain ⟨X', g, f', hH⟩ : ∃ (X' : Scheme.{u}) (g : X' ⟶ X) (f' : X' ⟶ Z),
      IsPullback g f' f t :=
    ⟨_, _, _, IsPullback.of_hasPullback f t⟩
  let instX : X'.Over (Spec (CommRingCat.of k₀)) := ⟨g ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : g.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hf' : f' ≫ t ≫ Y ↘ Spec (CommRingCat.of k₀) = g ≫ X ↘ Spec (CommRingCat.of k₀) := by
    rw [← Category.assoc, ← hH.w, Category.assoc, comp_over]
  have : f'.IsOver (Spec (CommRingCat.of k₀)) := ⟨hf'⟩
  have : IsSeparated f' := MorphismProperty.of_isPullback hH ‹_›
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback hH inferInstance
  have : QuasiCompact f' := MorphismProperty.of_isPullback hH ‹_›
  have hX : X' ↘ Spec (CommRingCat.of k₀) = f' ≫ Z ↘ Spec (CommRingCat.of k₀) :=
    (comp_over f' _).symm
  have : IsSeparated (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  have : LocallyOfFiniteType (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  have : QuasiCompact (X' ↘ Spec (CommRingCat.of k₀)) := by
    rw [hX]
    infer_instance
  refine ⟨X', instX, g, ‹_›, ‹_›, ‹_›, ‹_›, fun F i ↦ ?_⟩
  -- compact support base change
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_fiber hH F i
  refine ⟨fun h ↦ ?_, ?_⟩
  · have : Subsingleton (((WeilSheaf.upperStar t).obj ((WeilSheaf.higherLowerShriek k₀ l f
        i).obj F)).compactlySupportedCohomology 0).carrier :=
      WeilSheaf.subsingleton_globalSections_of_isZero <| (WeilComplex.homologySheaf 0).map_isZero <|
        (WeilComplex.derivedLowerShriek k₀ l (Z ↘ Spec (CommRingCat.of k₀))).map_isZero <|
          WeilSheaf.toComplex.map_isZero <| (WeilSheaf.upperStar t).map_isZero h
    exact E.toLinearEquiv.symm.injective.subsingleton
  -- the degree `d` of `y` and the unique point `z₀` of `Z`
  set d := (Y ↘ Spec (CommRingCat.of k₀)).degreeOver y.1 with hd_def
  have hd : d ≠ 0 := Scheme.Hom.degreeOver_ne_zero _ y.2
  let z₀ : Z := IsLocalRing.closedPoint (Y.residueField y.1)
  have hiz (z : Z) : t.base z = y.1 := Scheme.fromSpecResidueField_apply _ _
  have (z : Z) : IsIso (t.residueFieldMap z) := Scheme.Hom.isIso_residueFieldMap t z
  have hz₀ : z₀ ∈ Z.finitePoints :=
    (Scheme.Hom.mem_finitePoints_iff_of_isIso t z₀).1 ((hiz z₀).symm ▸ y.2)
  have hdegZ (z : Z) : (Z ↘ Spec (CommRingCat.of k₀)).degreeOver z = d :=
    (Scheme.Hom.degreeOver_comp_of_isIso t (Y ↘ Spec (CommRingCat.of k₀)) z).trans
      (congrArg _ (hiz z))
  have hy : (⟨t.base z₀, Scheme.Hom.map_mem_finitePoints t hz₀⟩ : Y.finitePoints) = y :=
    Subtype.ext (hiz z₀)
  -- `H_c^0` of the point `Spec κ(y)`
  have hZ : (((WeilSheaf.upperStar t).obj ((WeilSheaf.higherLowerShriek k₀ l f i).obj
      F)).compactlySupportedCohomology 0).frobeniusEnd.charpolyRev = Polynomial.expand _ d
        (((WeilSheaf.higherLowerShriek k₀ l f i).obj F).stalk y).frobeniusEnd.charpolyRev := by
    rw [WeilSheaf.charpolyRev_compactlySupportedCohomology_zero_of_subsingleton _ ⟨z₀, hz₀⟩,
      hdegZ, LinearMap.charpolyRev_def, LinearMap.charpolyRev_def,
      WeilSheaf.charpoly_frobeniusEnd_stalk_upperStar, hy, hdegZ, hiz, ← hd_def,
      Nat.div_self (Nat.pos_of_ne_zero hd), pow_one]
  have hE := E.localPolynomial_eq
  rw [FrobeniusModule.localPolynomial, FrobeniusModule.localPolynomial] at hE
  exact hZ.symm.trans hE

end AlgebraicGeometry
