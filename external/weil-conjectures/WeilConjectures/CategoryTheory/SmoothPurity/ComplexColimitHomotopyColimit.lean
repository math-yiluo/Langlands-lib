/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SmoothPurity.TruncationsAndHomotopyColimits
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.CategoryTheory.SequentialTelescopeMono
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedCountableSumsExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Sequential colimits of complexes represent homotopy colimits

Source: blueprint chap-Smooth-purity, proposition-ordinary-external-kunneth--1, order 1719;
Stacks Project, Derived Categories, Tags 093W, 0949, 0A5L and 090Z
(blueprint: proposition-open-direct-image-preserves-finite).

The two statements cover abelian sheaves and sheaves of modules over a commutative
ring sheaf. Arbitrary coproduct and colimit cocones are used, so the statements apply
to the degreewise chosen colimits as well. The equations for `u` and `q` specify
exactly the canonical telescope and colimit maps. The cone comparison is specified
by both its summand restrictions, without choosing a triangulated cone.
-/

@[expose] public section

universe w u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory

private theorem derived_coproduct
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    {I : Type} [Countable I] (K : I → CochainComplex A ℤ)
    (B : Cofan K) (hB : IsColimit B) :
    Nonempty (IsColimit (DerivedCategory.Q.mapCocone B)) := by
  obtain ⟨hc⟩ := DerivedCategory.isColimit_mapCocone_countableSum A I K
  have : PreservesColimit (Discrete.functor K) (DerivedCategory.Q (C := A)) :=
    preservesColimit_of_preserves_colimit_cocone
      (HomologicalComplex.isColimitCoconeOfHasColimitEval _) hc
  exact ⟨isColimitOfPreserves _ hB⟩

private theorem derived_countableCoproducts
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [CountableAB4 A] :
    HasCountableCoproducts (DerivedCategory A) := by
  classical
  constructor
  intro I _
  constructor
  intro F
  let K : I → CochainComplex A ℤ := fun i ↦ DerivedCategory.Q.objPreimage (F.obj ⟨i⟩)
  have h := derived_coproduct K _
    (HomologicalComplex.isColimitCoconeOfHasColimitEval (Discrete.functor K))
  have : HasColimit (Discrete.functor K ⋙ DerivedCategory.Q) := ⟨⟨_, h.some⟩⟩
  exact hasColimit_of_iso (show F ≅ Discrete.functor K ⋙ DerivedCategory.Q from
    Discrete.natIso (fun i ↦ (DerivedCategory.Q.objObjPreimageIso (F.obj i)).symm))

private theorem hocolim_of_cofan
    {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D] [HasCountableCoproducts D]
    (E : ℕ → D) (f : ∀ n : ℕ, E n ⟶ E (n + 1))
    (B : Cofan E) (hB : IsColimit B) (t : B.pt ⟶ B.pt)
    (ht : ∀ n, B.inj n ≫ t = B.inj n - f n ≫ B.inj (n + 1))
    {H : D} (g : B.pt ⟶ H) (h : H ⟶ B.pt⟦(1 : ℤ)⟧)
    (hT : Triangle.mk t g h ∈ distTriang D) :
    IsSequentialHomotopyColimit E f H := by
  let e : (∐ E) ≅ B.pt := (colimit.isColimit _).coconePointUniqueUpToIso hB
  have he (n : ℕ) : Sigma.ι E n ≫ e.hom = B.inj n := by
    exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _) hB
      (Discrete.mk n)
  let s : (∐ E) ⟶ (∐ E) :=
    𝟙 _ - Sigma.desc (fun n : ℕ ↦ f n ≫ Sigma.ι E (n + 1))
  have hs : s ≫ e.hom = e.hom ≫ t := by
    apply Sigma.hom_ext
    intro n
    simp only [s, Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub,
      ← Category.assoc, Sigma.ι_comp_desc]
    simp only [Category.assoc, he]
    rw [← ht]
  refine ⟨e.hom ≫ g, h ≫ (shiftFunctor D (1 : ℤ)).map e.inv, ?_⟩
  apply isomorphic_distinguished _ hT _
  refine Triangle.isoMk _ _ e e (Iso.refl H) hs ?_ ?_
  · change (e.hom ≫ g) ≫ 𝟙 H = e.hom ≫ g
    exact Category.comp_id _
  · change (h ≫ (shiftFunctor D (1 : ℤ)).map e.inv) ≫
        (shiftFunctor D (1 : ℤ)).map e.hom = 𝟙 H ≫ h
    rw [Category.assoc, ← Functor.map_comp, e.inv_hom_id, Functor.map_id,
      Category.comp_id, Category.id_comp]

private theorem telescope_zero
    {A : Type u} [Category.{v} A] [Abelian A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n))
    (hB : IsColimit B) (L : Cocone E)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n) :
    u ≫ q = 0 := by
  apply hB.hom_ext
  rintro ⟨n⟩
  change B.inj n ≫ (u ≫ q) = B.inj n ≫ 0
  rw [← Category.assoc, hu, Preadditive.sub_comp, Category.assoc, hq, hq]
  simp only [Cocone.w, sub_self, comp_zero]

private noncomputable def telescope_cokernel
    {A : Type u} [Category.{v} A] [Abelian A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L) (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n)
    (hz : u ≫ q = 0) : IsColimit (CokernelCofork.ofπ q hz) := by
  let c (s : CokernelCofork u) : Cocone E :=
    { pt := s.pt
      ι := NatTrans.ofSequence (fun n ↦ B.inj n ≫ s.π) (by
        intro n
        have hn := congrArg (fun f ↦ B.inj n ≫ f) s.condition
        rw [← Category.assoc, hu, Preadditive.sub_comp, Category.assoc, comp_zero] at hn
        change _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact (sub_eq_zero.mp hn).symm) }
  refine CokernelCofork.IsColimit.ofπ q hz (fun s hs ↦ hL.desc (c (CokernelCofork.ofπ s hs))) ?_ ?_
  · intro Z s hs
    apply hB.hom_ext
    rintro ⟨n⟩
    change B.inj n ≫ (q ≫ _) = B.inj n ≫ s
    rw [← Category.assoc, hq]
    exact hL.fac (c (CokernelCofork.ofπ s hs)) n
  · intro Z s hs m hm
    apply hL.hom_ext
    intro n
    change L.ι.app n ≫ m = L.ι.app n ≫ hL.desc (c (CokernelCofork.ofπ s hs))
    rw [hL.fac]
    change L.ι.app n ≫ m = B.inj n ≫ s
    rw [← hq, Category.assoc, hm]

private theorem telescope_shortExact
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasFilteredColimitsOfSize.{0, 0} A] [AB5OfSize.{0, 0} A]
    (E : ℕ ⥤ A) (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L) (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n)
    (hz : u ≫ q = 0) : (ShortComplex.mk u q hz).ShortExact := by
  let S := ShortComplex.mk u q hz
  have hc := telescope_cokernel E B hB L hL u hu q hq hz
  exact { exact := S.exact_of_g_is_cokernel hc
          mono_f := sequentialTelescope_mono E B hB u hu
          epi_g := epi_of_isColimit_cofork hc }

/-- The canonical cone and localized telescope triangle of a short exact sequence.
The specified coprojections are used in both homotopy-colimit assertions.
Source: Stacks Project, Derived Categories, Tags 0949 and 0A5L
(blueprint: proposition-open-direct-image-preserves-finite). -/
private theorem complex_colimit_homotopyColimit_of_shortExact
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A] [CountableAB4 A]
    (E : ℕ ⥤ CochainComplex A ℤ)
    (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (_hL : IsColimit L)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hz : u ≫ q = 0)
    (hS : (ShortComplex.mk u q hz).ShortExact) :
    ∃ p : mappingCone u ⟶ L.pt,
      mappingCone.inr u ≫ p = q ∧
      (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 ∧
      QuasiIso p ∧
      Nonempty (IsColimit
        (Cofan.mk (DerivedCategory.Q.obj B.pt)
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n)))) ∧
      ∃ e : DerivedCategory.Q.obj (mappingCone u) ≅ DerivedCategory.Q.obj L.pt,
        e.hom = DerivedCategory.Q.map p ∧
        DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈
          distTriang (DerivedCategory A) ∧
        Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
          (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
          distTriang (DerivedCategory A) ∧
        ∃ h : HasCountableCoproducts (DerivedCategory A),
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj (mappingCone u)) ∧
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj L.pt) := by
  classical
  let S := ShortComplex.mk u q hz
  let p := mappingCone.descShortComplex S
  have hp : mappingCone.inr u ≫ p = q := mappingCone.inr_descShortComplex S
  have hp' : (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 :=
    mappingCone.inl_desc _ _ _ _
  have hqi : QuasiIso p := mappingCone.quasiIso_descShortComplex hS
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A p).2 hqi
  let e := asIso (DerivedCategory.Q.map p)
  obtain ⟨hQB⟩ := derived_coproduct (fun n : ℕ ↦ E.obj n) B hB
  have hQB' : IsColimit (Cofan.mk (DerivedCategory.Q.obj B.pt)
      (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n))) :=
    Cofan.isColimitMapCoconeEquiv DerivedCategory.Q _ B hQB
  have hT := DerivedCategory.mappingCone_triangle_distinguished u
  have hT' : Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
      (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
      distTriang (DerivedCategory A) := by
    apply isomorphic_distinguished _ hT _
    refine (Triangle.isoMk
      (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u))
      (Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
        (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃))
      (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_).symm
    · change DerivedCategory.Q.map u ≫ 𝟙 _ = 𝟙 _ ≫ DerivedCategory.Q.map u
      rw [Category.comp_id, Category.id_comp]
    · change DerivedCategory.Q.map (mappingCone.inr u) ≫ DerivedCategory.Q.map p =
        𝟙 _ ≫ DerivedCategory.Q.map q
      rw [Category.id_comp, ← Functor.map_comp, hp]
    · change _ ≫ (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (𝟙 _) =
        e.hom ≫ e.inv ≫ _
      rw [Functor.map_id, Category.comp_id, e.hom_inv_id_assoc]
  have hcop : HasCountableCoproducts (DerivedCategory A) := derived_countableCoproducts
  have huQ (n : ℕ) : DerivedCategory.Q.map (B.inj n) ≫ DerivedCategory.Q.map u =
      DerivedCategory.Q.map (B.inj n) -
        DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))) ≫
          DerivedCategory.Q.map (B.inj (n + 1)) := by
    rw [← Functor.map_comp, hu, Functor.map_sub, Functor.map_comp]
  refine ⟨p, hp, hp', hqi, ⟨hQB'⟩, e, rfl, hT, hT', hcop, ?_, ?_⟩
  · exact hocolim_of_cofan _ _ _ hQB' _ huQ _ _ hT
  · exact hocolim_of_cofan _ _ _ hQB' _ huQ _ _ hT'

/-- The telescope comparison in any abelian category with exact sequential colimits.
This is the site-independent form of the two preceding specializations.
Source: Stacks Project, Derived Categories, Tags 093W, 0949 and 0A5L
(blueprint: proposition-open-direct-image-preserves-finite).
Proof: the cocone is the cokernel of the injective telescope map, giving a short
exact sequence; apply the cone comparison and preservation of countable sums. -/
theorem complex_colimit_homotopyColimit
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableCoproducts A]
    [HasFilteredColimitsOfSize.{0, 0} A] [AB5OfSize.{0, 0} A]
    (E : ℕ ⥤ CochainComplex A ℤ)
    (B : Cofan (fun n : ℕ ↦ E.obj n)) (hB : IsColimit B)
    (L : Cocone E) (hL : IsColimit L)
    (u : B.pt ⟶ B.pt)
    (hu : ∀ n : ℕ, B.inj n ≫ u =
      B.inj n - E.map (homOfLE (Nat.le_succ n)) ≫ B.inj (n + 1))
    (q : B.pt ⟶ L.pt) (hq : ∀ n : ℕ, B.inj n ≫ q = L.ι.app n) :
    ∃ p : mappingCone u ⟶ L.pt,
      mappingCone.inr u ≫ p = q ∧
      (mappingCone.inl u).comp (Cochain.ofHom p) (add_zero _) = 0 ∧
      QuasiIso p ∧
      Nonempty (IsColimit
        (Cofan.mk (DerivedCategory.Q.obj B.pt)
          (fun n : ℕ ↦ DerivedCategory.Q.map (B.inj n)))) ∧
      ∃ e : DerivedCategory.Q.obj (mappingCone u) ≅ DerivedCategory.Q.obj L.pt,
        e.hom = DerivedCategory.Q.map p ∧
        DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u) ∈
          distTriang (DerivedCategory A) ∧
        Triangle.mk (DerivedCategory.Q.map u) (DerivedCategory.Q.map q)
          (e.inv ≫ (DerivedCategory.Q.mapTriangle.obj (mappingCone.triangle u)).mor₃) ∈
          distTriang (DerivedCategory A) ∧
        ∃ h : HasCountableCoproducts (DerivedCategory A),
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj (mappingCone u)) ∧
          @IsSequentialHomotopyColimit
            (DerivedCategory A) _ _ _ _ _ _ _ h
            (fun n : ℕ ↦ DerivedCategory.Q.obj (E.obj n))
            (fun n : ℕ ↦ DerivedCategory.Q.map (E.map (homOfLE (Nat.le_succ n))))
            (DerivedCategory.Q.obj L.pt) := by
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : CountableAB4 A := CountableAB4.of_countableAB5 A
  have hz := telescope_zero E B hB L u hu q hq
  exact complex_colimit_homotopyColimit_of_shortExact E B hB L hL u hu q hz
    (telescope_shortExact E B hB L hL u hu q hq hz)

end CategoryTheory
