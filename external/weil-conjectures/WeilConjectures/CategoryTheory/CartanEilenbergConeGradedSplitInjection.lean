/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # A normalized split injection from the retained column cone

Source: Stacks Project, Homology, Tags 012X and 0133; retained-column construction
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection).
-/

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false in
/-- The retained column cone lifts to the filtration step, with ambient normalization.
Source: Stacks Project, Tags 012X and 0133, retained-column filtration calculation.

Proof: each retained resolution term maps into the image supremum defining step p:
when p >= b and r+p=m it is the s=p term of the finite interval; when p<b it
is zero by the assumed vanishing of I.X p. Factor its inclusion through the
step's degreewise monomorphism using the image-subobject universal property.
In degree m=p-1 the extended resolution term is zero. The extended single
term is zero unless m+1=p; in that case the K inclusion belongs to the first
summand of the supremum, and factors through the step. Transport these
factorizations by extendXIso, and use the mapping-cone degreewise biproduct
to combine them into w. Cancellation of the step monomorphism identifies
all the transported lifts with w on their respective cone coprojections.
This asserts no retraction and involves no quotient.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection). -/
private theorem cartanEilenberg_cone_retained_lift
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (_hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) (hm : p - 1 ≤ m) :
    ∃ w : (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p) ⟶
        (F.step p : CochainComplex A ℤ).X m,
      (∀ (r : ℕ) (h : (r : ℤ) + p = m),
        ((HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).f (m - p)) ≫
          w ≫ (F.step p).arrow.f m =
          (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m) ∧
      (∀ h : m + 1 = p,
        ((HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).v
          (m - p + 1) (m - p) (by omega)) ≫
          w ≫ (F.step p).arrow.f m =
          (K.XIsoOfEq h.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega)) := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  let c := HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat
  let e₀ := (ComplexShape.embeddingUpNat.extendFunctor A).mapIso
    ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℕ)).app (I.X p))
  let jR : ((I.X p).extend ComplexShape.embeddingUpNat).X (m - p) ⟶
      (CochainComplex.mappingCone aug).X m :=
    e₀.inv.f (m - p) ≫ J.ιTotal (ComplexShape.up ℤ) (m - p) p m
      (by change (m - p) + p = m; omega) ≫ (CochainComplex.mappingCone.inr aug).f m
  have hjR : imageSubobject jR ≤ F.complexStep p m := by
    by_cases hbp : b ≤ p
    · by_cases hpm : p ≤ m
      · rw [hF]
        apply le_trans (imageSubobject_comp_le (e₀.inv.f (m - p)) _)
        apply le_trans _ le_sup_right
        convert Finset.le_sup (f := fun s ↦ imageSubobject
          (J.ιTotalOrZero (ComplexShape.up ℤ) (m - s) s m ≫
            (CochainComplex.mappingCone.inr aug).f m))
          (Finset.mem_Icc.mpr (show max b p ≤ p ∧ p ≤ m from ⟨max_le hbp le_rfl, hpm⟩))
          using 1
        rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
          change (m - p) + p = m; omega)]
      · have hz : IsZero (((I.X p).extend ComplexShape.embeddingUpNat).X (m - p)) :=
          HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat _ (by
            intro n; change (n : ℤ) ≠ m - p; omega)
        simpa only [hz.eq_zero_of_src jR, imageSubobject_zero] using
          (bot_le : (⊥ : Subobject _) ≤ F.complexStep p m)
    · have hz : IsZero (((I.X p).extend ComplexShape.embeddingUpNat).X (m - p)) :=
        (HomologicalComplex.eval A (ComplexShape.up ℤ) (m - p)).map_isZero
          ((ComplexShape.embeddingUpNat.extendFunctor A).map_isZero (hIbelow p (by omega)))
      simpa only [hz.eq_zero_of_src jR, imageSubobject_zero] using
        (bot_le : (⊥ : Subobject _) ≤ F.complexStep p m)
  have hjR' : imageSubobject jR ≤ Subobject.mk ((F.step p).arrow.f m) := by
    have h : imageSubobject jR ≤ imageSubobject ((F.step p).arrow.f m) := hjR
    simpa only [imageSubobject_mono] using h
  let lR := factorThruImageSubobject jR ≫
    Subobject.ofLE _ _ hjR' ≫ (Subobject.underlyingIso ((F.step p).arrow.f m)).hom
  have hlR : lR ≫ (F.step p).arrow.f m = jR := by
    simp [lR]
  let jL : ((((CochainComplex.single₀ A).obj (K.X p)).extend
      ComplexShape.embeddingUpNat).X (m - p + 1)) ⟶
      (CochainComplex.mappingCone aug).X m :=
    if h : m + 1 = p then
      (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
        ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
        (by change (0 : ℤ) = m - p + 1; omega)).hom ≫
      (K.XIsoOfEq h.symm).hom ≫
      (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega)
    else 0
  have hjL : imageSubobject jL ≤ F.complexStep p m := by
    by_cases hmp : m + 1 = p
    · simp only [jL, dite_eq_left hmp]
      rw [hF, ite_eq_left (by omega : p ≤ m + 1)]
      apply le_trans _ le_sup_left
      simpa only [← Category.assoc] using imageSubobject_comp_le
        ((HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).hom ≫ (K.XIsoOfEq hmp.symm).hom)
        ((CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega))
    · simp only [jL, dite_eq_right hmp, imageSubobject_zero]
      exact bot_le
  have hjL' : imageSubobject jL ≤ Subobject.mk ((F.step p).arrow.f m) := by
    have h : imageSubobject jL ≤ imageSubobject ((F.step p).arrow.f m) := hjL
    simpa only [imageSubobject_mono] using h
  let lL := factorThruImageSubobject jL ≫
    Subobject.ofLE _ _ hjL' ≫ (Subobject.underlyingIso ((F.step p).arrow.f m)).hom
  have hlL : lL ≫ (F.step p).arrow.f m = jL := by
    simp [lL]
  let w := (CochainComplex.mappingCone.fst c).1.v (m - p) (m - p + 1) (by omega) ≫ lL +
    (CochainComplex.mappingCone.snd c).v (m - p) (m - p) (by omega) ≫ lR
  have hwL : (CochainComplex.mappingCone.inl c).v (m - p + 1) (m - p) (by omega) ≫
      w = lL := by simp [w]
  have hwR : (CochainComplex.mappingCone.inr c).f (m - p) ≫ w = lR := by simp [w]
  refine ⟨w, ?_, ?_⟩
  · intro n hn
    simp only [c] at hwR
    simp only [Category.assoc, reassoc_of% hwR, hlR]
    dsimp [jR]
    change _ ≫ (HomologicalComplex.extendMap
      ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℕ)).app (I.X p)).inv
      ComplexShape.embeddingUpNat).f (m - p) ≫ _ = _
    rw [HomologicalComplex.extendMap_f _ _ (by change (n : ℤ) = m - p; omega)]
    simp only [id_obj, Iso.app_inv, mapHomologicalComplexIdIso_inv_app_f,
      Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc, J]
  · intro hmp
    simp only [c] at hwL
    simp only [Category.assoc, reassoc_of% hwL, hlL]
    simp [jL, hmp]

/-- An ambient projection selects the retained column and kills the next filtration step.
Source: Stacks Project, Tags 012X and 0133, retained-column filtration calculation.

Proof: on the total-complex coproduct select the complex-index-p component,
using zero on every other component, and undo the identity-functor extension
identification. Compose with the target-side inclusion into the column cone.
On the source cone summand use zero unless m+1=p; in that case identify K
indices, extend the degree-zero single term, and include it into the column
cone. Combine these maps by the ambient cone biproduct. Its composites with
the retained inclusions are the displayed canonical column-cone inclusions.
Every term of the finite supremum defining step p+1 has column index at
least p+1 and is killed by the selected projection. The source summand of
that step occurs only when p+1 <= m+1, so m+1 differs from p and is killed
too. Hence the map annihilates the degreewise step inclusion, by the
universal property of the supremum of image subobjects. Empty intervals
and p<b need no exceptional choices. No lift, quotient or splitting is
asserted here.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection). -/
private theorem cartanEilenberg_cone_retained_projection
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (_hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (_hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) (_hm : p - 1 ≤ m) :
    ∃ t : (CochainComplex.mappingCone aug).X m ⟶ (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p),
      (F.step (p + 1)).arrow.f m ≫ t = 0 ∧
      (∀ (r : ℕ) (h : (r : ℤ) + p = m),
        ((HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m
            (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m) ≫
          t = (HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).f (m - p)) ∧
      (∀ h : m + 1 = p,
        ((K.XIsoOfEq h.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega)) ≫ t =
          (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).v
          (m - p + 1) (m - p) (by omega)) := by
  classical
  let J := ((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip
  let c := HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat
  let e₀ := (ComplexShape.embeddingUpNat.extendFunctor A).mapIso
    ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℕ)).app (I.X p))
  let s : K.X (m + 1) ⟶ (CochainComplex.mappingCone c).X (m - p) :=
    if h : m + 1 = p then
      (K.XIsoOfEq h).hom ≫
        (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl c).v (m - p + 1) (m - p) (by omega)
    else 0
  let r : (J.total (ComplexShape.up ℤ)).X m ⟶
      (CochainComplex.mappingCone c).X (m - p) :=
    J.totalDesc (fun i j h ↦ if hj : j = p then
      (J.XXIsoOfEq A (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (by change i + j = m at h; omega) hj).hom ≫ e₀.hom.f (m - p) ≫
          (CochainComplex.mappingCone.inr c).f (m - p)
      else 0)
  let t := (CochainComplex.mappingCone.fst aug).1.v m (m + 1) (by omega) ≫ s +
    (CochainComplex.mappingCone.snd aug).v m m (by omega) ≫ r
  have hs : (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) ≫ t = s := by
    simp [t]
  have hr : (CochainComplex.mappingCone.inr aug).f m ≫ t = r := by
    simp [t]
  refine ⟨t, ?_, ?_, ?_⟩
  · let Q := Subobject.mk (kernel.ι t)
    have kill {X : A} (f : X ⟶ (CochainComplex.mappingCone aug).X m)
        (hf : f ≫ t = 0) : imageSubobject f ≤ Q := by
      exact imageSubobject_le_mk (kernel.ι t) f (kernel.lift t f hf) (by simp)
    have hQ : F.complexStep (p + 1) m ≤ Q := by
      rw [hF]
      apply sup_le
      · split_ifs with h
        · apply kill
          rw [hs]
          dsimp [s]
          rw [dite_eq_right (by omega)]
        · exact bot_le
      · apply Finset.sup_le
        intro j hj
        apply kill
        rw [Category.assoc, hr]
        change J.ιTotalOrZero (ComplexShape.up ℤ) (m - j) j m ≫ r = 0
        rw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by
          change (m - j) + j = m; omega)]
        dsimp [r]
        rw [HomologicalComplex₂.ι_totalDesc, dite_eq_right (by
          have := (Finset.mem_Icc.mp hj).1
          omega)]
    have hqarrow : Q.arrow ≫ t = 0 := by
      dsimp [Q]
      rw [← Subobject.underlyingIso_hom_comp_eq_mk]
      simp
    have hstep : (F.complexStep (p + 1) m).arrow ≫ t = 0 := by
      rw [← Subobject.ofLE_arrow hQ, Category.assoc, hqarrow, comp_zero]
    rw [← imageSubobject_arrow_comp ((F.step (p + 1)).arrow.f m), Category.assoc]
    change factorThruImageSubobject _ ≫ ((F.complexStep (p + 1) m).arrow ≫ t) = 0
    rw [hstep, comp_zero]
  · intro n hn
    rw [Category.assoc, Category.assoc, hr]
    dsimp [r]
    rw [HomologicalComplex₂.ι_totalDesc]
    simp only [HomologicalComplex₂.XXIsoOfEq_rfl, Iso.refl_hom,
      Category.id_comp]
    change _ ≫ (HomologicalComplex.extendMap
      ((Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℕ)).app (I.X p)).hom
      ComplexShape.embeddingUpNat).f (m - p) ≫ _ = _
    rw [HomologicalComplex.extendMap_f _ _ (by change (n : ℤ) = m - p; omega)]
    simp [Functor.mapHomologicalComplexIdIso, c]
  · intro hmp
    rw [Category.assoc, hs]
    dsimp [s]
    rw [dite_eq_left hmp]
    simp [c]

/-- The retained cone summands give a normalized map into the quotient with a left inverse.
Source: Stacks Project, Tags 012X and 0133; retained-column quotient construction.
(blueprint: lem-sp-cartan-eilenberg-cone-graded-split-injection).

Proof: in degree m, project the ambient cone onto the complex-index-p summands.
The cone K summand is retained only when m+1=p; otherwise the corresponding
extended-single source in the column cone is zero. On the total summand use
its coproduct universal property to project onto index p, and identify this
summand with the extended resolution term. The projection kills every
column of index greater than p and the K summand present in step p+1.
It therefore descends from step p through the evaluated cokernel to a map u.
For each retained term, its ambient inclusion factors through step p since
its image is one of the summands in the stipulated supremum. Below b that
term is zero, so use its unique zero map. The two resulting lifts, with
extension identifications, define v by the degreewise cone biproduct.
Their quotient composites are the displayed normalization equations.
The ambient projection after each inclusion is identity. Thus v followed
by u is identity, checked on the two cone coprojections. When m=p-1 the
resolution term is zero; when m>=p the extended-single term is zero. These
cases also cover p<b, when both retained terms vanish. No identity for u
followed by v is asserted here: surjectivity is a separate generating-family
argument. -/
theorem cartanEilenberg_cone_graded_split_injection
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (F : DecreasingFiltration (CochainComplex.mappingCone aug))
    (hF : ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)))
    (p m : ℤ) (hm : p - 1 ≤ m) :
    ∃ v : (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).X (m - p) ⟶
        (F.gradedPiece p).X m,
      (∃ u, v ≫ u = 𝟙 _) ∧
  (∀ (r : ℕ) (h : (r : ℤ) + p = m),
    ∃ l : (I.X p).X r ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (HomologicalComplex.extendXIso
          (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X p))
          ComplexShape.embeddingUpNat (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
          (ComplexShape.up ℤ) (m - p) p m (by change (m - p) + p = m; omega) ≫
        (CochainComplex.mappingCone.inr aug).f m ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p)
          (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).f (m - p) ≫
        v) ∧
  (∀ h : m + 1 = p,
    ∃ l : K.X p ⟶ (F.step p : CochainComplex A ℤ).X m,
      l ≫ (F.step p).arrow.f m =
        (K.XIsoOfEq h.symm).hom ≫
        (CochainComplex.mappingCone.inl aug).v (m + 1) m (by omega) ∧
      l ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m =
        (HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl
          (HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat)).v
          (m - p + 1) (m - p) (by omega) ≫ v) := by
  obtain ⟨w, hwI, hwK⟩ := cartanEilenberg_cone_retained_lift
    K I a b hIbelow hKbelow aug F hF p m hm
  obtain ⟨t, htzero, htI, htK⟩ := cartanEilenberg_cone_retained_projection
    K I a b hIbelow hKbelow aug F hF p m hm
  let c := HomologicalComplex.extendMap (a.f p) ComplexShape.embeddingUpNat
  have hwt : w ≫ (F.step p).arrow.f m ≫ t = 𝟙 _ := by
    apply CochainComplex.mappingCone.ext_from c (m - p + 1) (m - p) (by omega)
    · by_cases hmp : m + 1 = p
      · let e := HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
          ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
          (by change (0 : ℤ) = m - p + 1; omega)
        apply (cancel_epi e.inv).1
        simpa only [e, c, Category.assoc, Category.comp_id] using
          (congrArg (fun f ↦ f ≫ t) (hwK hmp)).trans (htK hmp)
      · have hz : IsZero
            ((((CochainComplex.single₀ A).obj (K.X p)).extend
              ComplexShape.embeddingUpNat).X (m - p + 1)) := by
          let e := HomologicalComplex.extendSingleIso (C := A)
            (X := K.X p) ComplexShape.embeddingUpNat 0 (0 : ℤ) rfl
          exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ)
            0 (K.X p) (m - p + 1) (by omega)).of_iso
              ((HomologicalComplex.eval A (ComplexShape.up ℤ) (m - p + 1)).mapIso e)
        exact hz.eq_of_src _ _
    · by_cases hpm : p ≤ m
      · let r := (m - p).toNat
        have hr : (r : ℤ) + p = m := by
          dsimp [r]
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        let e := HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
          (i := r) (i' := m - p) (by change (r : ℤ) = m - p; omega)
        apply (cancel_epi e.inv).1
        simpa only [e, c, Category.assoc, Category.comp_id] using
          (congrArg (fun f ↦ f ≫ t) (hwI r hr)).trans (htI r hr)
      · have hz : IsZero (((I.X p).extend ComplexShape.embeddingUpNat).X (m - p)) :=
          HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat _ (by
            intro r
            change (r : ℤ) ≠ m - p
            omega)
        exact hz.eq_of_src _ _
  let inc := Subobject.ofLE (F.step (p + 1)) (F.step p) (F.antitone_step (by omega))
  have hinc : inc.f m ≫ (F.step p).arrow.f m = (F.step (p + 1)).arrow.f m :=
    congrArg (fun f ↦ f.f m) (Subobject.ofLE_arrow (F.antitone_step (by omega : p ≤ p + 1)))
  have hz : inc.f m ≫ ((F.step p).arrow.f m ≫ t) = 0 := by
    rw [← Category.assoc, hinc, htzero]
  let e := PreservesCokernel.iso (HomologicalComplex.eval A (ComplexShape.up ℤ) m) inc
  let u := e.hom ≫ cokernel.desc (inc.f m) ((F.step p).arrow.f m ≫ t) hz
  have hu : (F.complexQuotientπ p (p + 1) (by omega)).f m ≫ u =
      (F.step p).arrow.f m ≫ t := by
    change ((HomologicalComplex.eval A (ComplexShape.up ℤ) m).map (cokernel.π inc)) ≫
      e.hom ≫ cokernel.desc (inc.f m) ((F.step p).arrow.f m ≫ t) hz = _
    rw [← Category.assoc, PreservesCokernel.π_iso_hom]
    exact cokernel.π_desc (inc.f m) _ hz
  refine ⟨w ≫ (F.complexQuotientπ p (p + 1) (by omega)).f m, ?_, ?_, ?_⟩
  · exact ⟨u, by rw [Category.assoc, hu, hwt]⟩
  · intro r hr
    refine ⟨(HomologicalComplex.extendXIso (I.X p) ComplexShape.embeddingUpNat
      (i := r) (i' := m - p) (by change (r : ℤ) = m - p; omega)).inv ≫
        (CochainComplex.mappingCone.inr c).f (m - p) ≫ w, ?_, ?_⟩
    · simpa only [Category.assoc] using hwI r hr
    · simp only [c, Category.assoc]
  · intro hmp
    refine ⟨(HomologicalComplex.extendXIso ((CochainComplex.single₀ A).obj (K.X p))
      ComplexShape.embeddingUpNat (i := 0) (i' := m - p + 1)
      (by change (0 : ℤ) = m - p + 1; omega)).inv ≫
        (CochainComplex.mappingCone.inl c).v (m - p + 1) (m - p) (by omega) ≫ w,
      ?_, ?_⟩
    · simpa only [Category.assoc] using hwK hmp
    · simp only [c, Category.assoc]

end CategoryTheory.Functor
