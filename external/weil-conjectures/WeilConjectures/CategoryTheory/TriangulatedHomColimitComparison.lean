/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.CategoryTheory.Limits.Types.ColimitTypeFiltered
import Mathlib.Algebra.FiveLemma

/-! # Third Hom comparison for a cofiltered diagram of distinguished triangles

Source: Stacks Project, Derived Categories, Lemma 05SC, five-term Hom diagram, dualized.
(blueprint: lem-pur-triangulated-hom-colimit-comparison).
-/

@[expose] public section

universe uJ vJ uD vD

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Functor

namespace CategoryTheory

variable {J : Type uJ} {D : Type uD} [Category.{vJ} J] [Category.{vD} D]
  [Preadditive D]
/-- Lift the Hom groups so both index universes fit in the colimit universe. -/
private abbrev homDiagram (K : J ⥤ D) (W : D) :=
  K.op ⋙ preadditiveYoneda.obj W ⋙ AddCommGrpCat.uliftFunctor.{max uJ vJ, vD}
/-- The actual abelian-group colimit of the lifted Hom diagram. -/
private noncomputable def homColim (K : J ⥤ D) (W : D) := colimit (homDiagram K W)
/-- Precomposition at the specified stage, followed by the colimit inclusion. -/
private noncomputable def homComparison (K : J ⥤ D) (W A : D) (j : J) (m : K.obj j ⟶ A) :
    (A ⟶ W) →+ homColim K W :=
  ((colimit.ι (homDiagram K W) (Opposite.op j)).hom).comp
    { toFun := fun f ↦ ULift.up (m ≫ f)
      map_zero' := by apply ULift.ext; simp
      map_add' := by
        intro x y
        change ULift.up (m ≫ (x + y)) = ULift.up (m ≫ x + m ≫ y)
        rw [Preadditive.comp_add] }
/-- A natural transformation acts contravariantly on the Hom colimits. -/
private noncomputable def homColimMap {K L : J ⥤ D} (a : K ⟶ L) (W : D) :
    homColim L W →+ homColim K W :=
  (colim.map (whiskerRight (whiskerRight (NatTrans.op a) (preadditiveYoneda.obj W))
    AddCommGrpCat.uliftFunctor.{max uJ vJ, vD})).hom
@[simp] private lemma homComparison_apply (K : J ⥤ D) (W A : D) (j : J)
    (m : K.obj j ⟶ A) (f : A ⟶ W) :
    homComparison K W A j m f =
      (colimit.ι (homDiagram K W) (Opposite.op j)).hom (ULift.up (m ≫ f)) := rfl
private lemma homColimMap_ι {K L : J ⥤ D} (a : K ⟶ L) (W : D) (j : J) (f : L.obj j ⟶ W) :
    homColimMap a W ((colimit.ι (homDiagram L W) (Opposite.op j)).hom (ULift.up f)) =
      (colimit.ι (homDiagram K W) (Opposite.op j)).hom (ULift.up (a.app j ≫ f)) := by
  have h := ConcreteCategory.congr_hom
    (colimit.ι_map (whiskerRight (whiskerRight (NatTrans.op a) (preadditiveYoneda.obj W))
      AddCommGrpCat.uliftFunctor.{max uJ vJ, vD}) (Opposite.op j)) (ULift.up f)
  exact h
private lemma homComparison_comm {K L : J ⥤ D} (a : K ⟶ L) (W A B : D) (j : J)
    (mA : K.obj j ⟶ A) (mB : L.obj j ⟶ B) (b : A ⟶ B)
    (h : a.app j ≫ mB = mA ≫ b) :
    (homColimMap a W).comp (homComparison L W B j mB) =
      (homComparison K W A j mA).comp (Preadditive.leftComp W b) := by
  ext f
  simp only [AddMonoidHom.comp_apply, homComparison_apply, homColimMap_ι]
  change _ = (colimit.ι (homDiagram K W) (Opposite.op j)).hom
    (ULift.up (mA ≫ b ≫ f))
  rw [← Category.assoc, h, Category.assoc]
variable [IsCofiltered J]
private theorem homDiagram_preserves (K : J ⥤ D) (W : D) :
    PreservesColimit (homDiagram K W) (forget AddCommGrpCat) := by
  let : PreservesFilteredColimitsOfSize.{vJ, uJ}
      (forget AddCommGrpCat.{max uJ vJ vD}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max uJ vJ vD, max uJ vJ vD, vJ, uJ} _
  infer_instance
attribute [local instance] homDiagram_preserves
/-- Both colimits identify representatives precisely when they agree at a common stage. -/
private lemma homColim_rep_eq_iff (K : J ⥤ D) (W : D) (i j : J)
    (x : K.obj i ⟶ W) (y : K.obj j ⟶ W) :
    (colimit.ι (homDiagram K W) (Opposite.op i)).hom (ULift.up x) =
        (colimit.ι (homDiagram K W) (Opposite.op j)).hom (ULift.up y) ↔
      (K.op ⋙ yoneda.obj W).ιColimitType (Opposite.op i) x =
        (K.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) y := by
  rw [Functor.ιColimitType_eq_iff_of_isFiltered]
  have h := Concrete.colimit_rep_eq_iff_exists (homDiagram K W) (ULift.up x) (ULift.up y)
  change _ ↔ _ at h
  rw [h]
  constructor
  · rintro ⟨k, f, g, h⟩
    exact ⟨k, f, g, congrArg ULift.down h⟩
  · rintro ⟨k, f, g, h⟩
    exact ⟨k, f, g, congrArg ULift.up h⟩
/-- Transfer bijectivity between the group colimit and the original quotient of types. -/
private lemma homComparison_bijective_iff (K : J ⥤ D) (W A : D) (j : J)
    (m : K.obj j ⟶ A) :
    Function.Bijective (homComparison K W A j m) ↔
      Function.Bijective (fun f : A ⟶ W =>
        (K.op ⋙ yoneda.obj W).ιColimitType (Opposite.op j) (m ≫ f)) := by
  constructor
  · rintro ⟨hi, hs⟩
    refine ⟨fun x y h ↦ hi ((homColim_rep_eq_iff K W j j _ _).mpr h), ?_⟩
    intro z
    obtain ⟨k, x, rfl⟩ := (K.op ⋙ yoneda.obj W).ιColimitType_jointly_surjective z
    obtain ⟨f, hf⟩ := hs ((colimit.ι (homDiagram K W) k).hom (ULift.up x))
    exact ⟨f, (homColim_rep_eq_iff K W j k.unop _ _).mp hf⟩
  · rintro ⟨hi, hs⟩
    refine ⟨fun x y h ↦ hi ((homColim_rep_eq_iff K W j j _ _).mp h), ?_⟩
    intro z
    obtain ⟨k, x, rfl⟩ := Concrete.colimit_exists_rep (homDiagram K W) z
    obtain ⟨f, hf⟩ := hs ((K.op ⋙ yoneda.obj W).ιColimitType k x.down)
    exact ⟨f, (homColim_rep_eq_iff K W j k.unop _ _).mpr hf⟩
/-- Exactness passes to the colimit: represent a kernel element and refine until it
is zero, then lift at that stage. This is the element argument of Stacks Tag 00DB. -/
private lemma homColimMap_exact {K L M : J ⥤ D} (a : K ⟶ L) (b : L ⟶ M) (W : D)
    (h : ∀ j, Function.Exact (Preadditive.leftComp W (b.app j))
      (Preadditive.leftComp W (a.app j))) :
    Function.Exact (homColimMap b W) (homColimMap a W) := by
  intro z
  constructor
  · intro hz
    obtain ⟨j, x, rfl⟩ := Concrete.colimit_exists_rep (homDiagram L W) z
    change homColimMap a W
      ((colimit.ι (homDiagram L W) j).hom (ULift.up x.down)) = 0 at hz
    rw [homColimMap_ι] at hz
    have hz' : (colimit.ι (homDiagram K W) j).hom
        (ULift.up (a.app j.unop ≫ x.down)) =
      (colimit.ι (homDiagram K W) j).hom (ULift.up 0) := by
      change _ = 0 at hz
      rw [show (ULift.up (0 : K.obj j.unop ⟶ W)) =
        (0 : (homDiagram K W).obj j) from rfl, map_zero]
      exact hz
    obtain ⟨k, f, g, hk⟩ := Concrete.colimit_exists_of_rep_eq
      (homDiagram K W) _ _ hz'
    have hk' : a.app k.unop ≫ L.map f.unop ≫ x.down = 0 := by
      have hh := congrArg ULift.down hk
      change K.map f.unop ≫ (a.app j.unop ≫ x.down) = K.map g.unop ≫ 0 at hh
      rw [← Category.assoc, a.naturality, Category.assoc, Limits.comp_zero] at hh
      exact hh
    obtain ⟨y, hy⟩ := (h k.unop _).mp hk'
    refine ⟨(colimit.ι (homDiagram M W) k).hom (ULift.up y), ?_⟩
    rw [homColimMap_ι]
    change b.app k.unop ≫ y = L.map f.unop ≫ x.down at hy
    rw [hy]
    exact ConcreteCategory.congr_hom (colimit.w (homDiagram L W) f) x
  · rintro ⟨x, rfl⟩
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep (homDiagram M W) x
    change homColimMap a W (homColimMap b W
      ((colimit.ι (homDiagram M W) j).hom (ULift.up y.down))) = 0
    rw [homColimMap_ι, homColimMap_ι]
    have hh := (h j.unop).apply_apply_eq_zero y.down
    change a.app j.unop ≫ b.app j.unop ≫ y.down = 0 at hh
    rw [hh]
    change (colimit.ι (homDiagram K W) j).hom 0 = 0
    exact map_zero _
/-- Transport the comparisons along an equivalence using its natural adjunction
Hom bijections and the common-stage equality criterion. -/
private lemma homComparison_equivalence (K : J ⥤ D) (A : D) (j : J) (m : K.obj j ⟶ A)
    (E : D ≌ D) (h : ∀ W, Function.Bijective (homComparison K W A j m)) (W : D) :
    Function.Bijective (homComparison (K ⋙ E.functor) W (E.functor.obj A) j
      (E.functor.map m)) := by
  rw [homComparison_bijective_iff]
  have h' := (homComparison_bijective_iff K (E.inverse.obj W) A j m).mp
    (h (E.inverse.obj W))
  let adj := E.toAdjunction
  constructor
  · intro x y hxy
    apply (adj.homEquiv A W).injective
    apply h'.1
    rw [Functor.ιColimitType_eq_iff_of_isFiltered] at hxy ⊢
    obtain ⟨k, f, g, hfg⟩ := hxy
    refine ⟨k, f, g, ?_⟩
    change E.functor.map (K.map f.unop) ≫ E.functor.map m ≫ x =
      E.functor.map (K.map g.unop) ≫ E.functor.map m ≫ y at hfg
    have hh := congrArg (adj.homEquiv (K.obj k.unop) W) hfg
    change K.map f.unop ≫ m ≫ adj.homEquiv A W x =
      K.map g.unop ≫ m ≫ adj.homEquiv A W y
    simpa only [adj.homEquiv_naturality_left] using hh
  · intro z
    obtain ⟨k, x, rfl⟩ := ((K ⋙ E.functor).op ⋙ yoneda.obj W).ιColimitType_jointly_surjective z
    obtain ⟨y, hy⟩ := h'.2 ((K.op ⋙ yoneda.obj (E.inverse.obj W)).ιColimitType k
      (adj.homEquiv (K.obj k.unop) W x))
    refine ⟨(adj.homEquiv A W).symm y, ?_⟩
    rw [Functor.ιColimitType_eq_iff_of_isFiltered] at hy ⊢
    obtain ⟨l, f, g, hfg⟩ := hy
    refine ⟨l, f, g, ?_⟩
    apply (adj.homEquiv (K.obj l.unop) W).injective
    change K.map f.unop ≫ m ≫ y = K.map g.unop ≫
      adj.homEquiv (K.obj k.unop) W x at hfg
    change adj.homEquiv (K.obj l.unop) W
        (E.functor.map (K.map f.unop) ≫ E.functor.map m ≫
          (adj.homEquiv A W).symm y) =
      adj.homEquiv (K.obj l.unop) W (E.functor.map (K.map g.unop) ≫ x)
    simpa only [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] using hfg


/-- The five-term contravariant Hom sequence, including the sign from the second rotation. -/
private lemma triangle_hom_exact
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (T : Triangle D) (hT : T ∈ distTriang D) (W : D) :
    Function.Exact (Preadditive.leftComp W (T.mor₁⟦(1 : ℤ)⟧'))
      (Preadditive.leftComp W T.mor₃) ∧
    Function.Exact (Preadditive.leftComp W T.mor₃) (Preadditive.leftComp W T.mor₂) ∧
    Function.Exact (Preadditive.leftComp W T.mor₂) (Preadditive.leftComp W T.mor₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := T.rotate.rotate.yoneda_exact₂
        (rot_of_distTriang _ (rot_of_distTriang _ hT)) x hx
      refine ⟨-y, ?_⟩
      change T.mor₁⟦(1 : ℤ)⟧' ≫ (-y) = x
      simpa using hy.symm
    · rintro ⟨y, rfl⟩
      change T.mor₃ ≫ T.mor₁⟦(1 : ℤ)⟧' ≫ y = 0
      rw [← Category.assoc, comp_distTriang_mor_zero₃₁ T hT, zero_comp]
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := T.yoneda_exact₃ hT x hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      change T.mor₂ ≫ T.mor₃ ≫ y = 0
      rw [← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := T.yoneda_exact₂ hT x hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      change T.mor₁ ≫ T.mor₂ ≫ y = 0
      rw [← Category.assoc, comp_distTriang_mor_zero₁₂ T hT, zero_comp]

/-- A triangle morphism at one stage induces bijective third Hom comparisons if it
induces bijective first and second Hom comparisons for every test object.

Source: Stacks Project, Derived Categories, Lemma 05SC, displayed five-term Hom diagram,
with contravariant Hom and cofiltered indexing.
(blueprint: lem-pur-triangulated-hom-colimit-comparison).

Proof: For a test object W apply Hom(-,W) to the distinguished triangles H(j) and U.
The five terms are Hom(second[1],W), Hom(first[1],W), Hom(third,W), Hom(second,W),
and Hom(first,W). Triangle morphisms give a diagram of exact sequences over J opposite.
Its filtered colimit is exact (filtered colimits of abelian groups preserve exactness).
Precomposition with m gives a map from the exact sequence of U to this colimit sequence;
the triangle-morphism equations ensure all four squares commute. The last two vertical
maps are bijective by h₂ and h₁. The first two are bijective by the same hypotheses with
W shifted by -1, using the shift equivalence and its natural Hom bijections. The five
lemma makes the middle vertical map bijective. Forgetting the abelian group structures
identifies the filtered colimit with ColimitType, and its middle vertical map sends phi
to the class of m.hom₃ followed by phi at j₀, exactly the map below. -/
theorem triangulated_hom_colimit_comparison
    {J : Type uJ} {D : Type uD} [Category.{vJ} J] [Category.{vD} D]
    [IsCofiltered J] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (H : J ⥤ Triangle D) (hH : ∀ j, H.obj j ∈ distTriang D)
    (U : Triangle D) (hU : U ∈ distTriang D) (j₀ : J) (m : H.obj j₀ ⟶ U)
    (h₁ : ∀ W : D, Function.Bijective (fun φ : U.obj₁ ⟶ W ↦
      (((H ⋙ Triangle.π₁).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₁ ≫ φ))))
    (h₂ : ∀ W : D, Function.Bijective (fun φ : U.obj₂ ⟶ W ↦
      (((H ⋙ Triangle.π₂).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₂ ≫ φ)))) :
    ∀ W : D, Function.Bijective (fun φ : U.obj₃ ⟶ W ↦
      (((H ⋙ Triangle.π₃).op ⋙ yoneda.obj W).ιColimitType
        (Opposite.op j₀) (m.hom₃ ≫ φ))) := by
  intro W
  let K₁ := H ⋙ Triangle.π₂ ⋙ shiftFunctor D (1 : ℤ)
  let K₂ := H ⋙ Triangle.π₁ ⋙ shiftFunctor D (1 : ℤ)
  let K₃ := H ⋙ Triangle.π₃
  let K₄ := H ⋙ Triangle.π₂
  let K₅ := H ⋙ Triangle.π₁
  let a₁ : K₂ ⟶ K₁ := Functor.whiskerRight
    (Functor.whiskerLeft H Triangle.π₁Toπ₂) (shiftFunctor D (1 : ℤ))
  let a₂ : K₃ ⟶ K₂ := Functor.whiskerLeft H Triangle.π₃Toπ₁
  let a₃ : K₄ ⟶ K₃ := Functor.whiskerLeft H Triangle.π₂Toπ₃
  let a₄ : K₅ ⟶ K₄ := Functor.whiskerLeft H Triangle.π₁Toπ₂
  have ht := triangle_hom_exact U hU W
  have hb := fun j ↦ triangle_hom_exact (H.obj j) (hH j) W
  have hi₄ := (homComparison_bijective_iff K₄ W U.obj₂ j₀ m.hom₂).mpr (h₂ W)
  have hi₅ := (homComparison_bijective_iff K₅ W U.obj₁ j₀ m.hom₁).mpr (h₁ W)
  have hi₁ := homComparison_equivalence (H ⋙ Triangle.π₂) U.obj₂ j₀ m.hom₂
    (shiftEquiv D (1 : ℤ))
    (fun V ↦ (homComparison_bijective_iff _ _ _ _ _).mpr (h₂ V)) W
  have hi₂ := homComparison_equivalence (H ⋙ Triangle.π₁) U.obj₁ j₀ m.hom₁
    (shiftEquiv D (1 : ℤ))
    (fun V ↦ (homComparison_bijective_iff _ _ _ _ _).mpr (h₁ V)) W
  apply (homComparison_bijective_iff K₃ W U.obj₃ j₀ m.hom₃).mp
  apply AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (Preadditive.leftComp W (U.mor₁⟦(1 : ℤ)⟧'))
    (Preadditive.leftComp W U.mor₃) (Preadditive.leftComp W U.mor₂)
    (Preadditive.leftComp W U.mor₁)
    (homColimMap a₁ W) (homColimMap a₂ W) (homColimMap a₃ W) (homColimMap a₄ W)
    (homComparison K₁ W _ j₀ (m.hom₂⟦(1 : ℤ)⟧'))
    (homComparison K₂ W _ j₀ (m.hom₁⟦(1 : ℤ)⟧'))
    (homComparison K₃ W _ j₀ m.hom₃)
    (homComparison K₄ W _ j₀ m.hom₂) (homComparison K₅ W _ j₀ m.hom₁)
  · apply homComparison_comm
    change (H.obj j₀).mor₁⟦(1 : ℤ)⟧' ≫ m.hom₂⟦(1 : ℤ)⟧' =
      m.hom₁⟦(1 : ℤ)⟧' ≫ U.mor₁⟦(1 : ℤ)⟧'
    have hh := congrArg ((shiftFunctor D (1 : ℤ)).map) m.comm₁
    simpa only [Functor.map_comp] using hh
  · exact homComparison_comm a₂ W _ _ j₀ _ _ U.mor₃ m.comm₃
  · exact homComparison_comm a₃ W _ _ j₀ _ _ U.mor₂ m.comm₂
  · exact homComparison_comm a₄ W _ _ j₀ _ _ U.mor₁ m.comm₁
  · exact ht.1
  · exact ht.2.1
  · exact ht.2.2
  · exact homColimMap_exact a₂ a₁ W (fun j ↦ (hb j).1)
  · exact homColimMap_exact a₃ a₂ W (fun j ↦ (hb j).2.1)
  · exact homColimMap_exact a₄ a₃ W (fun j ↦ (hb j).2.2)
  · exact hi₁.2
  · exact hi₂
  · exact hi₄
  · exact hi₅.1

end CategoryTheory
