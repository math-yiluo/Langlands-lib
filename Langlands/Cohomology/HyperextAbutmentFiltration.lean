import Langlands.Cohomology.HyperextDegeneration.Statement
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The abutment filtration of the hyperext spectral sequence

Let `t` be a t-structure on a pretriangulated category `C` and let `K` and `B` be objects of `C`.
The hyperext spectral sequence of `Langlands.Cohomology.HyperextSpectralSequence` is built by
applying `Hom(-, B)` to the truncations of `K`; its intended abutment in total degree `n` is
`Hom(K, B⟦n⟧)`. This module defines the corresponding filtration of the abutment: `F^p` is the
subgroup of morphisms `K ⟶ B⟦n⟧` that factor through `K ⟶ τ_{≥ p - n} K`, equivalently that
vanish on `τ_{< p - n} K` (`filtration`, `mem_filtration_iff_truncLTι_comp_eq_zero`). With this
indexing the graded piece `gr^p = F^p / F^{p+1}` (`graded`) corresponds to the term
`E_∞^{p, n - p}` of the spectral sequence, which involves the cohomology object `H^{p - n} K`.

The filtration is decreasing (`antitone_filtration`). It is the whole group for `p ≤ 0` when `B`
lies in degrees `≥ 0` (`filtration_eq_top`), and it is zero once `p - n` exceeds an upper bound for
`K` (`filtration_eq_bot`). The module does not compare `graded` with the pages of the spectral
sequence, and it does not prove convergence.

For the canonical t-structure on the derived category of an abelian category and `B = W₀` the
object `W` placed in degree `0` (`derivedFiltration`), the first step `F^1` is the kernel of the
edge map `HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` of
`Langlands.Cohomology.HyperextDegeneration.Statement` (`derivedFiltration_one_eq_ker`), and
`gr^0` is identified with the image of the edge map (`gradedZeroAddEquivRange`). The edge map is
injective when `K` lies in degrees `≤ -n` (`edgeMap_injective_of_isLE`), a consequence of the
faithfulness lemma `eq_zero_of_homologyFunctor_map_eq_zero`.

This module does not prove `HyperextDegenerationStatement`: it assumes nothing about `Ext` groups,
and it shows neither that the higher graded pieces vanish nor that the edge map is surjective.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w v u

section TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] (t : TStructure C)

/-- The step `F^p` of the abutment filtration on `Hom(K, B⟦n⟧)`: the morphisms that factor
through the truncation `K ⟶ τ_{≥ p - n} K`. -/
def filtration (K B : C) (n p : ℤ) : AddSubgroup (ShiftedHom K B n) :=
  (Preadditive.leftComp (B⟦n⟧) ((t.truncGEπ (p - n)).app K)).range

variable {t}

lemma mem_filtration_iff {K B : C} {n p : ℤ} (f : ShiftedHom K B n) :
    f ∈ filtration t K B n p ↔
      ∃ g : (t.truncGE (p - n)).obj K ⟶ B⟦n⟧, (t.truncGEπ (p - n)).app K ≫ g = f :=
  Iff.rfl

/-- A morphism `K ⟶ B⟦n⟧` lies in `F^p` exactly when it vanishes on `τ_{< p - n} K`. -/
lemma mem_filtration_iff_truncLTι_comp_eq_zero {K B : C} {n p : ℤ} (f : ShiftedHom K B n) :
    f ∈ filtration t K B n p ↔ (t.truncLTι (p - n)).app K ≫ f = 0 := by
  rw [mem_filtration_iff]
  constructor
  · rintro ⟨g, rfl⟩
    rw [← Category.assoc, t.truncLTι_comp_truncGEπ_app, zero_comp]
  · intro hf
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (t.triangleLTGE_distinguished (p - n) K) f hf
    exact ⟨g, hg.symm⟩

lemma filtration_le_of_le {K B : C} {n p q : ℤ} (hpq : p ≤ q) :
    filtration t K B n q ≤ filtration t K B n p := by
  intro f hf
  rw [mem_filtration_iff_truncLTι_comp_eq_zero] at hf ⊢
  rw [← t.natTransTruncLTOfLE_ι_app (p - n) (q - n) (by lia) K, Category.assoc, hf, comp_zero]

/-- The abutment filtration is decreasing. -/
lemma antitone_filtration (K B : C) (n : ℤ) : Antitone (filtration t K B n) :=
  fun _ _ h => filtration_le_of_le h

/-- If `B` lies in degrees `≥ 0`, then `F^p` is the whole group for `p ≤ 0`. -/
lemma filtration_eq_top {K B : C} [t.IsGE B 0] {n p : ℤ} (hp : p ≤ 0) :
    filtration t K B n p = ⊤ := by
  refine eq_top_iff.2 fun f _ => (mem_filtration_iff_truncLTι_comp_eq_zero f).2 ?_
  have : t.IsGE (B⟦n⟧) (-n) := t.isGE_shift B 0 n (-n)
  exact t.zero _ (p - n - 1) (-n) (by lia)

/-- If `K` lies in degrees `≤ b`, then `F^p` is zero as soon as `b < p - n`. -/
lemma filtration_eq_bot {K B : C} {n p : ℤ} (b : ℤ) [t.IsLE K b] (hp : b < p - n) :
    filtration t K B n p = ⊥ := by
  refine eq_bot_iff.2 fun f hf => ?_
  obtain ⟨g, rfl⟩ := (mem_filtration_iff f).1 hf
  have : t.IsLE K (p - n - 1) := t.isLE_of_le K b (p - n - 1) (by lia)
  have hz : IsZero ((t.truncGE (p - n)).obj K) :=
    t.isZero_truncGE_obj_of_isLE (p - n - 1) (p - n) (by lia) K
  rw [hz.eq_of_src g 0, comp_zero]
  exact (AddSubgroup.mem_bot).2 rfl

variable (t) in
/-- The graded piece `gr^p = F^p / F^{p+1}` of the abutment filtration on `Hom(K, B⟦n⟧)`. -/
abbrev graded (K B : C) (n p : ℤ) : Type v :=
  filtration t K B n p ⧸ (filtration t K B n (p + 1)).addSubgroupOf (filtration t K B n p)

/-- The graded piece `gr^p` is trivial when `F^p ≤ F^{p+1}`. -/
lemma subsingleton_graded_of_le {K B : C} {n p : ℤ}
    (h : filtration t K B n p ≤ filtration t K B n (p + 1)) : Subsingleton (graded t K B n p) := by
  unfold graded
  rw [(AddSubgroup.addSubgroupOf_eq_top).2 h]
  exact QuotientAddGroup.subsingleton_quotient_top

lemma subsingleton_graded_of_lt_zero {K B : C} [t.IsGE B 0] {n p : ℤ} (hp : p < 0) :
    Subsingleton (graded t K B n p) :=
  subsingleton_graded_of_le (by rw [filtration_eq_top (by lia), filtration_eq_top (by lia)])

lemma subsingleton_graded_of_isLE {K B : C} {n p : ℤ} (b : ℤ) [t.IsLE K b] (hp : b < p - n) :
    Subsingleton (graded t K B n p) :=
  subsingleton_graded_of_le (by rw [filtration_eq_bot b hp]; exact bot_le)

end TStructure

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- The abutment filtration on `Hom(K, W₀⟦n⟧)` for the canonical t-structure on the derived
category, where `W₀` is `W` placed in degree `0`. -/
abbrev derivedFiltration (K : DerivedCategory C) (W : C) (n p : ℤ) :
    AddSubgroup (ShiftedHom K ((singleFunctor C 0).obj W) n) :=
  filtration TStructure.t K ((singleFunctor C 0).obj W) n p

/-- `F^p` is the whole group for `p ≤ 0`. -/
lemma derivedFiltration_eq_top (K : DerivedCategory C) (W : C) {n p : ℤ} (hp : p ≤ 0) :
    derivedFiltration K W n p = ⊤ :=
  filtration_eq_top hp

/-- If the cohomology of `K` vanishes in degrees `> b`, then `F^p` is zero as soon as
`b < p - n`. -/
lemma derivedFiltration_eq_bot (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K)) (W : C) {n p : ℤ}
    (hp : b < p - n) : derivedFiltration K W n p = ⊥ := by
  have : K.IsLE b := (K.isLE_iff b).2 hK
  exact filtration_eq_bot b hp

/-- The edge map is natural in the source. -/
lemma edgeMap_comp {X K : DerivedCategory C} (φ : X ⟶ K) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap X W n (φ ≫ f) =
      (homologyFunctor C (-n)).map φ ≫ HyperextDegeneration.edgeMap K W n f := by
  simp only [HyperextDegeneration.edgeMap, Functor.shiftMap_comp']
  exact Category.assoc _ _ _

/-- The edge map vanishes exactly when the induced morphism on cohomology in degree `-n`
vanishes. -/
lemma edgeMap_eq_zero_iff (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap K W n f = 0 ↔ (homologyFunctor C (-n)).map f = 0 := by
  have : IsIso (X := ((homologyFunctor C 0).shift (0 : ℤ)).obj ((singleFunctor C 0).obj W)) (Y := W)
      ((singleFunctorCompHomologyFunctorIso C 0).hom.app W) :=
    Iso.isIso_hom ((singleFunctorCompHomologyFunctorIso C 0).app W)
  exact (Preadditive.IsIso.comp_right_eq_zero
      (((homologyFunctor C 0).shift (-n)).map f ≫
        ((homologyFunctor C 0).shiftIso n (-n) 0 (by lia)).hom.app ((singleFunctor C 0).obj W))
      ((singleFunctorCompHomologyFunctorIso C 0).hom.app W)).trans
    (Preadditive.IsIso.comp_right_eq_zero (((homologyFunctor C 0).shift (-n)).map f)
      (((homologyFunctor C 0).shiftIso n (-n) 0 (by lia)).hom.app ((singleFunctor C 0).obj W)))

/-- The edge map as a morphism of abelian groups. -/
def edgeMapAddMonoidHom (K : DerivedCategory C) (W : C) (n : ℤ) :
    ShiftedHom K ((singleFunctor C 0).obj W) n →+ ((homologyFunctor C (-n)).obj K ⟶ W) where
  toFun := HyperextDegeneration.edgeMap K W n
  map_zero' := by
    simp only [HyperextDegeneration.edgeMap, Functor.shiftMap_zero]
    exact zero_comp
  map_add' f g := by
    simp only [HyperextDegeneration.edgeMap, Functor.shiftMap, Functor.map_add,
      Preadditive.add_comp]
    exact Preadditive.add_comp _ _ _ _ _ _

@[simp]
lemma edgeMapAddMonoidHom_apply (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    edgeMapAddMonoidHom K W n f = HyperextDegeneration.edgeMap K W n f := rfl

/-- On objects whose cohomology is concentrated in degree `m`, the cohomology functor in
degree `m` is faithful. -/
lemma eq_zero_of_homologyFunctor_map_eq_zero_of_isGE_of_isLE {X Y : DerivedCategory C} (m : ℤ)
    [X.IsGE m] [X.IsLE m] [Y.IsGE m] [Y.IsLE m] (g : X ⟶ Y)
    (hg : (homologyFunctor C m).map g = 0) : g = 0 := by
  obtain ⟨A, ⟨e₁⟩⟩ := X.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  obtain ⟨B, ⟨e₂⟩⟩ := Y.exists_iso_singleFunctor_obj_of_isGE_of_isLE m
  obtain ⟨u, hu⟩ := (singleFunctor C m).map_surjective (e₁.inv ≫ g ≫ e₂.hom)
  have : (singleFunctor C m ⋙ homologyFunctor C m).Faithful :=
    Functor.Faithful.of_iso (singleFunctorCompHomologyFunctorIso C m).symm
  have hu₀ : u = 0 := (singleFunctor C m ⋙ homologyFunctor C m).map_injective (by
    rw [Functor.map_zero, Functor.comp_map, hu, Functor.map_comp, Functor.map_comp, hg,
      zero_comp, comp_zero])
  have h₀ : e₁.inv ≫ g ≫ e₂.hom = 0 := by rw [← hu, hu₀, Functor.map_zero]
  calc g = e₁.hom ≫ (e₁.inv ≫ g ≫ e₂.hom) ≫ e₂.inv := by simp
    _ = 0 := by rw [h₀, zero_comp, comp_zero]

/-- A morphism from an object with cohomology in degrees `≤ m` to an object with cohomology in
degrees `≥ m` vanishes as soon as the morphism it induces on cohomology in degree `m`
vanishes. -/
lemma eq_zero_of_homologyFunctor_map_eq_zero {X Y : DerivedCategory C} (m : ℤ)
    [X.IsLE m] [Y.IsGE m] (g : X ⟶ Y) (hg : (homologyFunctor C m).map g = 0) : g = 0 := by
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : (TStructure.t.truncGE m).obj X ⟶ (TStructure.t.truncLT (m + 1)).obj Y,
      (TStructure.t.truncGEπ m).app X ≫ g₂ ≫ (TStructure.t.truncLTι (m + 1)).app Y = g :=
    ⟨TStructure.t.liftTruncLT (TStructure.t.descTruncGE g m) m (m + 1) rfl, by simp⟩
  have hπ : Epi ((homologyFunctor C m).map ((TStructure.t.truncGEπ m).app X)) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _
      (TStructure.t.triangleLTGE_distinguished m X) m (m + 1)).2
      (IsZero.eq_of_tgt (isZero_of_isLE ((TStructure.t.triangleLTGE m).obj X).obj₁ (m - 1)
        (m + 1) (by lia)) _ _)
  have hι : Mono ((homologyFunctor C m).map ((TStructure.t.truncLTι (m + 1)).app Y)) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _
      (TStructure.t.triangleLTGE_distinguished (m + 1) Y) (m - 1) m).2
      (IsZero.eq_of_src (isZero_of_isGE ((TStructure.t.triangleLTGE (m + 1)).obj Y).obj₃ (m + 1)
        (m - 1) (by lia)) _ _)
  have h₀ : (homologyFunctor C m).map g₂ = 0 := by
    rw [← cancel_epi ((homologyFunctor C m).map ((TStructure.t.truncGEπ m).app X)),
      ← cancel_mono ((homologyFunctor C m).map ((TStructure.t.truncLTι (m + 1)).app Y))]
    simp only [comp_zero, zero_comp, Category.assoc, ← Functor.map_comp, hg₂, hg]
  rw [← hg₂, eq_zero_of_homologyFunctor_map_eq_zero_of_isGE_of_isLE m g₂ h₀, zero_comp,
    comp_zero]

/-- The edge map is injective when the cohomology of `K` vanishes in degrees above `-n`. -/
lemma edgeMap_injective_of_isLE (K : DerivedCategory C) (W : C) (n : ℤ) [K.IsLE (-n)] :
    Function.Injective (HyperextDegeneration.edgeMap K W n) := by
  have : (((singleFunctor C 0).obj W)⟦n⟧).IsGE (-n) :=
    TStructure.t.isGE_shift ((singleFunctor C 0).obj W) 0 n (-n)
  refine (injective_iff_map_eq_zero (edgeMapAddMonoidHom K W n)).2 fun f hf => ?_
  exact eq_zero_of_homologyFunctor_map_eq_zero (-n) f ((edgeMap_eq_zero_iff K W n f).1 hf)

/-- The first step of the abutment filtration is the kernel of the edge map. -/
lemma mem_derivedFiltration_one_iff (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    f ∈ derivedFiltration K W n 1 ↔ HyperextDegeneration.edgeMap K W n f = 0 := by
  constructor
  · rintro ⟨g, rfl⟩
    have hz : IsZero ((homologyFunctor C (-n)).obj ((TStructure.t.truncGE (1 - n)).obj K)) :=
      isZero_of_isGE _ (1 - n) (-n) (by lia)
    change HyperextDegeneration.edgeMap K W n ((TStructure.t.truncGEπ (1 - n)).app K ≫ g) = 0
    rw [edgeMap_comp, hz.eq_of_tgt ((homologyFunctor C (-n)).map _) 0, zero_comp]
  · intro hf
    refine (mem_filtration_iff_truncLTι_comp_eq_zero f).2 ?_
    have : ((TStructure.t.truncLT (1 - n)).obj K).IsLE (-n) :=
      TStructure.t.isLE_of_le _ (1 - n - 1) (-n) (by lia)
    refine edgeMap_injective_of_isLE ((TStructure.t.truncLT (1 - n)).obj K) W n ?_
    have h := edgeMap_comp (K := K) ((TStructure.t.truncLTι (1 - n)).app K) W n f
    rw [hf, comp_zero] at h
    exact h.trans ((edgeMapAddMonoidHom _ W n).map_zero).symm

/-- The first step of the abutment filtration as the kernel of the edge map. -/
lemma derivedFiltration_one_eq_ker (K : DerivedCategory C) (W : C) (n : ℤ) :
    derivedFiltration K W n 1 = (edgeMapAddMonoidHom K W n).ker := by
  ext f
  exact (mem_derivedFiltration_one_iff K W n f).trans (AddMonoidHom.mem_ker (f := edgeMapAddMonoidHom K W n) (x := f)).symm

/-- The edge map restricted to the step `F^0` of the abutment filtration, with values in its
image. -/
def edgeMapRangeRestrict (K : DerivedCategory C) (W : C) (n : ℤ) :
    derivedFiltration K W n 0 →+ (edgeMapAddMonoidHom K W n).range :=
  (edgeMapAddMonoidHom K W n).rangeRestrict.comp (derivedFiltration K W n 0).subtype

/-- `edgeMapRangeRestrict` is surjective, because `F^0` is the whole group. -/
lemma edgeMapRangeRestrict_surjective (K : DerivedCategory C) (W : C) (n : ℤ) :
    Function.Surjective (edgeMapRangeRestrict K W n) := by
  rintro ⟨y, f, rfl⟩
  refine ⟨⟨f, ?_⟩, rfl⟩
  rw [derivedFiltration_eq_top K W le_rfl]
  exact AddSubgroup.mem_top f

/-- Inside `F^0`, the step `F^1` is the kernel of `edgeMapRangeRestrict`. -/
lemma addSubgroupOf_derivedFiltration_one_eq_ker (K : DerivedCategory C) (W : C) (n : ℤ) :
    (derivedFiltration K W n 1).addSubgroupOf (derivedFiltration K W n 0) =
      (edgeMapRangeRestrict K W n).ker := by
  ext f
  rw [AddSubgroup.mem_addSubgroupOf, mem_derivedFiltration_one_iff, AddMonoidHom.mem_ker]
  constructor
  · intro hf
    exact Subtype.ext hf
  · intro hf
    exact congrArg Subtype.val hf

/-- The graded piece `gr^0 = F^0 / F^1` of the abutment filtration is identified, through the
edge map, with the image of the edge map in `Hom(H^{-n} K, W)`. -/
def gradedZeroAddEquivRange (K : DerivedCategory C) (W : C) (n : ℤ) :
    graded TStructure.t K ((singleFunctor C 0).obj W) n 0 ≃+
      (edgeMapAddMonoidHom K W n).range :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (addSubgroupOf_derivedFiltration_one_eq_ker K W n)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (edgeMapRangeRestrict_surjective K W n))

end Derived

end HyperextAbutment

end Langlands.Cohomology
