import Langlands.Cohomology.HyperextAbutmentFiltration
import Langlands.Cohomology.HyperextSecondPage

/-!
# Surjectivity of the hyperext edge map

Let `C` be an abelian category, `K` an object of its derived category and `W` an object of `C`,
placed in degree `0` as `W₀`. The edge map `HyperextDegeneration.edgeMap K W n` of
`Langlands.Cohomology.HyperextDegeneration.Statement` sends `f : K ⟶ W₀⟦n⟧` to the morphism
`H^{-n} K ⟶ W` it induces on cohomology. This module proves that the edge map is surjective under
the hypotheses of `HyperextDegenerationStatement`: the cohomology of `K` vanishes above some `b`,
and `Ext^i(H^k K, W)` vanishes for every `k` and every `i > 0` (`edgeMap_surjective_of_ext`).

The proof uses three general facts about the canonical t-structure on the derived category.

* The truncation maps `τ_{< k} X ⟶ X` and `X ⟶ τ_{≥ k} X` induce isomorphisms on `H^j` for
  `j < k` and for `j ≥ k` respectively (`isIso_homologyMap_truncLTι`,
  `isIso_homologyMap_truncGEπ`).
* On objects concentrated in a single degree `m`, the functor `H^m` is full
  (`homologyFunctor_map_surjective_of_isGE_of_isLE`). Since the edge map is `H^{-n}` followed by
  the isomorphism `edgeTargetIso W n : H^{-n}(W₀⟦n⟧) ≅ W` (`edgeMap_eq_comp`), the edge map is
  surjective on such objects for `m = -n` (`edgeMap_surjective_of_isGE_of_isLE`).
* Dévissage: if `X` lies in degrees `≥ a` and `≤ a + k`, and every morphism from
  `H^j(X)` placed in degree `j` to `Y` vanishes for `a ≤ j ≤ a + k`, then every morphism
  `X ⟶ Y` vanishes (`eq_zero_of_isGE_of_isLE`).

For the main result, write `K₁ = τ_{≥ -n} K`. A morphism `H^{-n} K ⟶ W` gives a morphism
`h₀ : τ_{< 1 - n} K₁ ⟶ W₀⟦n⟧` by the second fact, since `τ_{< 1 - n} K₁` is concentrated in
degree `-n`. The obstruction to extending `h₀` to `K₁` is a morphism from `τ_{≥ 1 - n} K₁`, which
lies in degrees `[1 - n, b]`, to `W₀⟦n⟧⟦1⟧ ≅ W₀⟦n + 1⟧`. By dévissage it vanishes: for
`1 - n ≤ j`, the cohomology `H^j` of `τ_{≥ 1 - n} K₁` is `H^j K`, and morphisms from `H^j K`
placed in degree `j` to `W₀⟦n + 1⟧` form `Ext^{j + n + 1}(H^j K, W)` with `j + n + 1 ≥ 2`
(`singleFunctor_hom_eq_zero_of_ext`, through `HyperextSpectralSequence.secondPageExtAddEquiv`).
Precomposing the extension with `K ⟶ K₁` gives the required preimage.

Together with `edgeMap_injective_of_ext` of `Langlands.Cohomology.HyperextGradedVanishing`, this
gives the bijectivity asserted by `HyperextDegenerationStatement`. This module does not import
that module and does not state the combination.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Langlands.Cohomology

namespace HyperextAbutment

open HyperextSpectralSequence

universe w' w v u

section Generic

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D]

/-- If every morphism `A' ⟶ Y` is zero and `A ≅ A'`, then every morphism `A ⟶ Y` is zero. -/
lemma eq_zero_of_iso_of_forall_eq_zero {A A' Y : D} (e : A ≅ A')
    (h : ∀ g : A' ⟶ Y, g = 0) (g : A ⟶ Y) : g = 0 := by
  rw [← e.hom_inv_id_assoc g, h (e.inv ≫ g), comp_zero]

end Generic

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- The truncation map `τ_{< k} X ⟶ X` induces an isomorphism on `H^j` for `j < k`. -/
lemma isIso_homologyMap_truncLTι (X : DerivedCategory C) {k j : ℤ} (hj : j < k) :
    IsIso ((homologyFunctor C j).map ((TStructure.t.truncLTι k).app X)) := by
  have hT := TStructure.t.triangleLTGE_distinguished k X
  have hZ : IsZero ((homologyFunctor C j).obj ((TStructure.t.triangleLTGE k).obj X).obj₃) :=
    isZero_of_isGE _ k j hj
  have hZ' : IsZero
      ((homologyFunctor C (j - 1)).obj ((TStructure.t.triangleLTGE k).obj X).obj₃) :=
    isZero_of_isGE _ k (j - 1) (by lia)
  have hm : Mono ((homologyFunctor C j).map ((TStructure.t.triangleLTGE k).obj X).mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT (j - 1) j
      (by lia)).2 (hZ'.eq_of_src _ _)
  have he : Epi ((homologyFunctor C j).map ((TStructure.t.triangleLTGE k).obj X).mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT j).2
      (hZ.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- The truncation map `X ⟶ τ_{≥ k} X` induces an isomorphism on `H^j` for `k ≤ j`. -/
lemma isIso_homologyMap_truncGEπ (X : DerivedCategory C) {k j : ℤ} (hj : k ≤ j) :
    IsIso ((homologyFunctor C j).map ((TStructure.t.truncGEπ k).app X)) := by
  have hT := TStructure.t.triangleLTGE_distinguished k X
  have hZ : IsZero ((homologyFunctor C j).obj ((TStructure.t.triangleLTGE k).obj X).obj₁) :=
    isZero_of_isLE _ (k - 1) j (by lia)
  have hZ' : IsZero
      ((homologyFunctor C (j + 1)).obj ((TStructure.t.triangleLTGE k).obj X).obj₁) :=
    isZero_of_isLE _ (k - 1) (j + 1) (by lia)
  have hm : Mono ((homologyFunctor C j).map ((TStructure.t.triangleLTGE k).obj X).mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT j).2
      (hZ.eq_of_src _ _)
  have he : Epi ((homologyFunctor C j).map ((TStructure.t.triangleLTGE k).obj X).mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT j (j + 1) rfl).2
      (hZ'.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- On objects concentrated in degree `m`, the cohomology functor `H^m` is full. -/
lemma homologyFunctor_map_surjective_of_isGE_of_isLE {X Y : DerivedCategory C} (m : ℤ)
    [X.IsGE m] [X.IsLE m] [Y.IsGE m] [Y.IsLE m]
    (u : (homologyFunctor C m).obj X ⟶ (homologyFunctor C m).obj Y) :
    ∃ g : X ⟶ Y, (homologyFunctor C m).map g = u := by
  obtain ⟨A, ⟨e₁⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  obtain ⟨B, ⟨e₂⟩⟩ := Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  have : (singleFunctor C m ⋙ homologyFunctor C m).Full :=
    Functor.Full.of_iso (singleFunctorCompHomologyFunctorIso C m).symm
  obtain ⟨a, ha⟩ := (singleFunctor C m ⋙ homologyFunctor C m).map_surjective
    ((homologyFunctor C m).map e₁.inv ≫ u ≫ (homologyFunctor C m).map e₂.hom)
  refine ⟨e₁.hom ≫ (singleFunctor C m).map a ≫ e₂.inv, ?_⟩
  have ha' : (homologyFunctor C m).map ((singleFunctor C m).map a) =
      (homologyFunctor C m).map e₁.inv ≫ u ≫ (homologyFunctor C m).map e₂.hom := ha
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ha']
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The isomorphism `H^{-n}(W₀⟦n⟧) ≅ W` used by the edge map: the shift isomorphism of the
cohomology functors followed by the identification `H^0(W₀) ≅ W`. -/
def edgeTargetIso (W : C) (n : ℤ) :
    (homologyFunctor C (-n)).obj (((singleFunctor C 0).obj W)⟦n⟧) ≅ W :=
  ((homologyFunctor C 0).shiftIso n (-n) 0 (by lia)).app ((singleFunctor C 0).obj W) ≪≫
    (singleFunctorCompHomologyFunctorIso C 0).app W

/-- The edge map is `H^{-n}` followed by `edgeTargetIso W n`. -/
lemma edgeMap_eq_comp (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap K W n f =
      (homologyFunctor C (-n)).map f ≫ (edgeTargetIso W n).hom :=
  Category.assoc _ _ _

/-- The edge map is surjective on objects concentrated in degree `-n`. -/
lemma edgeMap_surjective_of_isGE_of_isLE (X : DerivedCategory C) (W : C) (n : ℤ)
    [X.IsGE (-n)] [X.IsLE (-n)] : Function.Surjective (HyperextDegeneration.edgeMap X W n) := by
  have : (((singleFunctor C 0).obj W)⟦n⟧).IsGE (-n) :=
    TStructure.t.isGE_shift ((singleFunctor C 0).obj W) 0 n (-n)
  have : (((singleFunctor C 0).obj W)⟦n⟧).IsLE (-n) :=
    TStructure.t.isLE_shift ((singleFunctor C 0).obj W) 0 n (-n)
  intro g
  obtain ⟨h, hh⟩ := homologyFunctor_map_surjective_of_isGE_of_isLE (-n)
    (g ≫ (edgeTargetIso W n).inv)
  exact ⟨h, by rw [edgeMap_eq_comp, hh, Category.assoc, Iso.inv_hom_id, Category.comp_id]⟩

/-- A morphism out of an object `X` concentrated in degree `m` vanishes when every morphism from
`H^m(X)` placed in degree `m` vanishes. -/
lemma eq_zero_of_isGE_of_isLE_self {X Y : DerivedCategory C} (m : ℤ) [X.IsGE m] [X.IsLE m]
    (hY : ∀ g : (singleFunctor C m).obj ((homologyFunctor C m).obj X) ⟶ Y, g = 0)
    (f : X ⟶ Y) : f = 0 :=
  eq_zero_of_iso_of_forall_eq_zero (isoSingleHomology X m) hY f

/-- Dévissage: if `X` lies in degrees `≥ a` and `≤ a + k`, and every morphism from `H^j(X)`
placed in degree `j` to `Y` vanishes for `a ≤ j ≤ a + k`, then every morphism `X ⟶ Y` vanishes.
The proof is by induction on `k`, with the truncation triangle at `a + k + 1`. -/
lemma eq_zero_of_isGE_of_isLE (Y : DerivedCategory C) (a : ℤ) (k : ℕ) :
    ∀ (X : DerivedCategory C) [X.IsGE a] [X.IsLE (a + k)],
      (∀ j : ℤ, a ≤ j → j ≤ a + k →
        ∀ g : (singleFunctor C j).obj ((homologyFunctor C j).obj X) ⟶ Y, g = 0) →
      ∀ f : X ⟶ Y, f = 0 := by
  induction k with
  | zero =>
    intro X _ _ hY f
    have : X.IsLE a := TStructure.t.isLE_of_le X (a + ((0 : ℕ) : ℤ)) a (by simp)
    exact eq_zero_of_isGE_of_isLE_self a (hY a le_rfl (by simp)) f
  | succ k ih =>
    intro X _ _ hY f
    have hX : X.IsLE (a + k + 1) :=
      TStructure.t.isLE_of_le X (a + ((k + 1 : ℕ) : ℤ)) (a + k + 1) (by push_cast; lia)
    have h₁ : (TStructure.t.truncLTι (a + k + 1)).app X ≫ f = 0 := by
      have : ((TStructure.t.truncLT (a + k + 1)).obj X).IsLE (a + k) :=
        TStructure.t.isLE_of_le _ (a + k + 1 - 1) (a + k) (by lia)
      refine ih _ (fun j hj hj' g => ?_) _
      have := isIso_homologyMap_truncLTι X (k := a + k + 1) (j := j) (by lia)
      exact eq_zero_of_iso_of_forall_eq_zero ((singleFunctor C j).mapIso
        (asIso ((homologyFunctor C j).map ((TStructure.t.truncLTι (a + k + 1)).app X))))
        (hY j hj (by push_cast; lia)) g
    obtain ⟨f', hf'⟩ :=
      Triangle.yoneda_exact₂ _ (TStructure.t.triangleLTGE_distinguished (a + k + 1) X) f h₁
    have := isIso_homologyMap_truncGEπ X (k := a + k + 1) (j := a + k + 1) le_rfl
    have hf'0 : f' = 0 :=
      eq_zero_of_isGE_of_isLE_self (X := (TStructure.t.truncGE (a + k + 1)).obj X) (a + k + 1)
        (eq_zero_of_iso_of_forall_eq_zero ((singleFunctor C (a + k + 1)).mapIso
          (asIso ((homologyFunctor C (a + k + 1)).map
            ((TStructure.t.truncGEπ (a + k + 1)).app X)))).symm
          (hY _ (by lia) (by push_cast; lia))) f'
    rw [hf', hf'0]
    exact comp_zero

/-- For `p : ℕ` with `p = j + d`, every morphism from `H^j(K)` placed in degree `j` to `W₀⟦d⟧`
vanishes when `Ext^p(H^j K, W)` is zero. This uses `heartPieceIso K (-j)` and
`secondPageExtAddEquiv K W p (-j)`. -/
lemma singleFunctor_hom_eq_zero_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (W : C)
    (j d : ℤ) (p : ℕ) (hp : (p : ℤ) = j + d)
    (h : Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C j).obj K) W p))
    (g : (singleFunctor C j).obj ((homologyFunctor C j).obj K) ⟶
      ((singleFunctor C 0).obj W)⟦d⟧) : g = 0 := by
  have h₁ : Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C (-(-j))).obj K) W p) := by
    rw [neg_neg]
    exact h
  have h₂ := (secondPageExtAddEquiv.{w'} K W p (-j)).injective.subsingleton
  have h₃ : ∀ g : (singleFunctor C (-(-j))).obj ((homologyFunctor C (-(-j))).obj K) ⟶
      ((singleFunctor C 0).obj W)⟦(p : ℤ) + -j⟧, g = 0 :=
    eq_zero_of_iso_of_forall_eq_zero (heartPieceIso K (-j)).symm
      (fun _ => Subsingleton.elim _ _)
  rw [neg_neg, show (p : ℤ) + -j = d by lia] at h₃
  exact h₃ g

/-- Under the hypotheses of `HyperextDegenerationStatement`, the edge map
`Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` is surjective. -/
lemma edgeMap_surjective_of_ext [HasExt.{w'} C] (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ) :
    Function.Surjective (HyperextDegeneration.edgeMap K W n) := by
  have : K.IsLE b := (K.isLE_iff b).2 hK
  intro g
  have hT := TStructure.t.triangleLTGE_distinguished (1 - n) ((TStructure.t.truncGE (-n)).obj K)
  have : ((TStructure.t.truncLT (1 - n)).obj ((TStructure.t.truncGE (-n)).obj K)).IsLE (-n) :=
    TStructure.t.isLE_of_le _ (1 - n - 1) (-n) (by lia)
  have : ((TStructure.t.truncGE (1 - n)).obj ((TStructure.t.truncGE (-n)).obj K)).IsLE
      (1 - n + ((b - (1 - n)).toNat : ℕ)) :=
    TStructure.t.isLE_of_le _ b _ (by lia)
  have hι := isIso_homologyMap_truncLTι ((TStructure.t.truncGE (-n)).obj K)
    (k := 1 - n) (j := -n) (by lia)
  have hπ := isIso_homologyMap_truncGEπ K (k := -n) (j := -n) le_rfl
  obtain ⟨h₀, hh₀⟩ := edgeMap_surjective_of_isGE_of_isLE
    ((TStructure.t.truncLT (1 - n)).obj ((TStructure.t.truncGE (-n)).obj K)) W n
    ((homologyFunctor C (-n)).map
        ((TStructure.t.truncLTι (1 - n)).app ((TStructure.t.truncGE (-n)).obj K)) ≫
      inv ((homologyFunctor C (-n)).map ((TStructure.t.truncGEπ (-n)).app K)) ≫ g)
  have hδ : ((TStructure.t.triangleLTGE (1 - n)).obj
      ((TStructure.t.truncGE (-n)).obj K)).mor₃ ≫ h₀⟦(1 : ℤ)⟧' = 0 := by
    let e := (shiftFunctorAdd' (DerivedCategory C) n 1 (n + 1) rfl).app
      ((singleFunctor C 0).obj W)
    refine (cancel_mono e.inv).1 ?_
    rw [zero_comp]
    refine eq_zero_of_isGE_of_isLE _ (1 - n) (b - (1 - n)).toNat
      ((TStructure.t.truncGE (1 - n)).obj ((TStructure.t.truncGE (-n)).obj K))
      (fun j hj _ g' => ?_) _
    have := isIso_homologyMap_truncGEπ ((TStructure.t.truncGE (-n)).obj K) (k := 1 - n) (j := j) hj
    have := isIso_homologyMap_truncGEπ K (k := -n) (j := j) (by lia)
    refine eq_zero_of_iso_of_forall_eq_zero ((singleFunctor C j).mapIso
      ((asIso ((homologyFunctor C j).map
        ((TStructure.t.truncGEπ (1 - n)).app ((TStructure.t.truncGE (-n)).obj K)))).symm ≪≫
        (asIso ((homologyFunctor C j).map ((TStructure.t.truncGEπ (-n)).app K))).symm))
      (singleFunctor_hom_eq_zero_of_ext K W j (n + 1) (j + (n + 1)).toNat (by lia)
        (hW j _ (by lia))) g'
  obtain ⟨g', hg'⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) (h₀⟦(1 : ℤ)⟧') hδ
  obtain ⟨f₁, rfl⟩ : ∃ f₁ : (TStructure.t.truncGE (-n)).obj K ⟶ ((singleFunctor C 0).obj W)⟦n⟧,
      f₁⟦(1 : ℤ)⟧' = g' := (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_surjective g'
  have hext : h₀ = (TStructure.t.truncLTι (1 - n)).app ((TStructure.t.truncGE (-n)).obj K) ≫
      (-f₁) := by
    apply (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_injective
    refine hg'.trans ?_
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_neg, Preadditive.comp_neg]
    exact Preadditive.neg_comp _ _
  refine ⟨(TStructure.t.truncGEπ (-n)).app K ≫ (-f₁), ?_⟩
  have h₁ : HyperextDegeneration.edgeMap ((TStructure.t.truncGE (-n)).obj K) W n (-f₁) =
      inv ((homologyFunctor C (-n)).map ((TStructure.t.truncGEπ (-n)).app K)) ≫ g := by
    rw [← cancel_epi ((homologyFunctor C (-n)).map
      ((TStructure.t.truncLTι (1 - n)).app ((TStructure.t.truncGE (-n)).obj K)))]
    exact (edgeMap_comp ((TStructure.t.truncLTι (1 - n)).app ((TStructure.t.truncGE (-n)).obj K))
      W n (-f₁)).symm.trans
        ((congrArg (HyperextDegeneration.edgeMap _ W n) hext.symm).trans hh₀)
  rw [edgeMap_comp, h₁, IsIso.hom_inv_id_assoc]

end Derived

end HyperextAbutment

end Langlands.Cohomology
