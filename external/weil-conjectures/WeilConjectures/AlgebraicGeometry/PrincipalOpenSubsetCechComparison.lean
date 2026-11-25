/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Reindexing ordered Čech cochains by subsets

Source: Stacks Project, Cohomology, Tags 01FJ, 01FK and 01FM.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private def tupleSubsetEquiv (r p : ℕ) :
    {t : Fin (p + 1) → Fin r // StrictMono t} ≃
      {T : Finset (Fin r) // T.card = p + 1} where
  toFun t := ⟨Finset.univ.image t.val, by
    rw [Finset.card_image_of_injective _ t.property.injective]
    simp⟩
  invFun T := ⟨T.val.orderEmbOfFin T.property,
    (T.val.orderEmbOfFin T.property).strictMono⟩
  left_inv t := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique _
      (fun i ↦ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) t.property).symm
  right_inv T := by
    apply Subtype.ext
    exact Finset.image_orderEmbOfFin_univ T.val T.property

private theorem basicOpen_product (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A) (T : Finset (Fin r)) :
    PrimeSpectrum.basicOpen (∏ j ∈ T, f j) = ⨅ j ∈ T, PrimeSpectrum.basicOpen (f j) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert j T hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.basicOpen_mul, ih]
    simpa only [Finset.mem_insert, Set.mem_insert_iff, Finset.mem_coe] using
      (iInf_insert (s := (T : Set (Fin r))) (b := j)
        (f := fun i ↦ PrimeSpectrum.basicOpen (f i))).symm

private theorem tupleOpen (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤)))
    (p : ℕ) (t : Fin (p + 1) → Fin r) :
    S.W p t = PrimeSpectrum.basicOpen (∏ j ∈ Finset.univ.image t, f j) := by
  classical
  rw [basicOpen_product]
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact leOfHom (S.pr p t i)
  · let V : (Spec (.of A)).Opens :=
      ⨅ j ∈ Finset.univ.image t, PrimeSpectrum.basicOpen (f j)
    have hV (i : Fin (p + 1)) : V ≤ PrimeSpectrum.basicOpen (f (t i)) :=
      iInf_le_of_le (t i) (iInf_le _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    obtain ⟨b, _, _⟩ := S.universal p t V (fun i ↦ homOfLE (hV i))
      (fun _ ↦ Subsingleton.elim _ _)
    exact leOfHom b

private noncomputable def sectionCast (A : Type u) [CommRing A]
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    {U V : (Spec (.of A)).Opens} (h : U = V) : F.obj (op U) ≃+ F.obj (op V) :=
  (F.mapIso (eqToIso h.symm).op).toLinearEquiv.toAddEquiv

private theorem sectionCast_refl (A : Type u) [CommRing A]
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (U : (Spec (.of A)).Opens) (x : F.obj (op U)) :
    sectionCast A F rfl x = x := by
  simp [sectionCast]

private noncomputable def subsetIso (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :
    AddCommGrpCat.of (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t},
      F.obj (op (S.W p t.val))) ≅
      AddCommGrpCat.of (∀ T : {T : Finset (Fin r) // T.card = p + 1},
        F.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ T.val, f j)))) := by
  classical
  let E := tupleSubsetEquiv r p
  let H (t : {t : Fin (p + 1) → Fin r // StrictMono t}) :=
    sectionCast A F (tupleOpen A r f S p t.val)
  let K := Equiv.piCongr
    (Z := fun T : {T : Finset (Fin r) // T.card = p + 1} ↦
      F.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ T.val, f j)))) E
    (fun t ↦ (H t).toEquiv)
  let e : (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t},
      F.obj (op (S.W p t.val))) ≃+
      (∀ T : {T : Finset (Fin r) // T.card = p + 1},
        F.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ T.val, f j)))) :=
    { toEquiv := K
      map_add' := by
        intro x y
        funext T
        obtain ⟨t, rfl⟩ := E.surjective T
        change K (x + y) (E t) = K x (E t) + K y (E t)
        dsimp only [K]
        rw [Equiv.piCongr_apply_apply, Equiv.piCongr_apply_apply,
          Equiv.piCongr_apply_apply]
        exact (H t).map_add (x t) (y t) }
  exact e.toAddCommGrpIso

private theorem subsetIso_apply (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ)
    (c : ∀ t : {t : Fin (p + 1) → Fin r // StrictMono t}, F.obj (op (S.W p t.val)))
    (t : {t : Fin (p + 1) → Fin r // StrictMono t}) :
    (subsetIso A r f F S p).hom c (tupleSubsetEquiv r p t) =
      sectionCast A F (tupleOpen A r f S p t.val) (c t) := by
  exact Equiv.piCongr_apply_apply (Z := fun T : {T : Finset (Fin r) // T.card = p + 1} ↦
      F.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ T.val, f j))))
    (tupleSubsetEquiv r p)
    (fun t ↦ (sectionCast A F (tupleOpen A r f S p t.val)).toEquiv) c t

private theorem subsetIso_apply_of_eq (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ)
    (c : ∀ t : {t : Fin (p + 1) → Fin r // StrictMono t}, F.obj (op (S.W p t.val)))
    (t : {t : Fin (p + 1) → Fin r // StrictMono t})
    (T : {T : Finset (Fin r) // T.card = p + 1}) (ht : tupleSubsetEquiv r p t = T) :
    (subsetIso A r f F S p).hom c T =
      sectionCast A F ((tupleOpen A r f S p t.val).trans
        (congrArg (fun R ↦ PrimeSpectrum.basicOpen (∏ j ∈ R, f j))
          (congrArg Subtype.val ht))) (c t) := by
  cases ht
  exact subsetIso_apply A r f F S p c t

private theorem eraseEnumeration (r p : ℕ)
    (T : {T : Finset (Fin r) // T.card = (p + 1) + 1}) (j : Fin (p + 2)) :
    (T.val.orderEmbOfFin T.property) ∘ j.succAbove =
      (T.val.erase (T.val.orderEmbOfFin T.property j)).orderEmbOfFin (by
        rw [Finset.card_erase_of_mem (T.val.orderEmbOfFin_mem T.property j), T.property]
        omega) := by
  apply Finset.orderEmbOfFin_unique
  · intro i
    apply Finset.mem_erase.mpr
    constructor
    · intro h
      exact Fin.succAbove_ne j i ((T.val.orderEmbOfFin T.property).injective h)
    · exact T.val.orderEmbOfFin_mem T.property (j.succAbove i)
  · exact (T.val.orderEmbOfFin T.property).strictMono.comp (Fin.strictMono_succAbove j)

private theorem countBefore (r p : ℕ)
    (T : {T : Finset (Fin r) // T.card = p + 1}) (j : Fin (p + 1)) :
    (T.val.filter (fun i ↦ i < T.val.orderEmbOfFin T.property j)).card = j.val := by
  classical
  let t := T.val.orderEmbOfFin T.property
  change (T.val.filter (fun i ↦ i < t j)).card = j.val
  conv_lhs => arg 1; arg 2; rw [← Finset.image_orderEmbOfFin_univ T.val T.property]
  rw [Finset.filter_image]
  have hfilter : (Finset.univ.filter (fun i ↦
      T.val.orderEmbOfFin T.property i < T.val.orderEmbOfFin T.property j)) =
      Finset.Iio j := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact (T.val.orderEmbOfFin T.property).lt_iff_lt
  rw [hfilter, Finset.card_image_of_injective _ (T.val.orderEmbOfFin T.property).injective,
    Fin.card_Iio]

private theorem sectionCast_natural (A : Type u) [CommRing A]
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    {U V U' V' : (Spec (.of A)).Opens} (hU : U = U') (hV : V = V')
    (i : U ⟶ V) (i' : U' ⟶ V') (x : F.obj (op V)) :
    sectionCast A F hU (F.map i.op x) = F.map i'.op (sectionCast A F hV x) := by
  subst U'
  subst V'
  have : i = i' := Subsingleton.elim _ _
  subst i'
  simp only [sectionCast_refl]

private def orderedTerms (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :=
  AddCommGrpCat.of (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t},
    F.obj (op (S.W p t.val)))

private def orderedRestriction (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :
    S.cochains (F ⋙ forget₂ _ AddCommGrpCat) p ⟶ orderedTerms A r f F S p :=
  AddCommGrpCat.ofHom
    { toFun := fun c t ↦ c t.val
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

private noncomputable def orderedD (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :
    orderedTerms A r f F S p ⟶ orderedTerms A r f F S (p + 1) :=
  AddCommGrpCat.ofHom
    { toFun := fun c t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        F.map (S.indexMap t.val j.succAbove).op
          (c ⟨t.val ∘ j.succAbove, t.property.comp (Fin.strictMono_succAbove j)⟩)
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp [map_add, smul_add, Finset.sum_add_distrib] }

private theorem ordered_comm (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :
    orderedRestriction A r f F S p ≫ orderedD A r f F S p =
      S.differential (F ⋙ forget₂ _ AddCommGrpCat) p ≫
        orderedRestriction A r f F S (p + 1) := by
  rfl

private theorem ordered_squared (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) (p : ℕ) :
    orderedD A r f F S p ≫ orderedD A r f F S (p + 1) = 0 := by
  classical
  have : Epi (orderedRestriction A r f F S p) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (by
      intro c
      refine ⟨fun t ↦ if h : StrictMono t then c ⟨t, h⟩ else 0, ?_⟩
      funext t
      change (if h : StrictMono t.val then c ⟨t.val, h⟩ else 0) = c t
      simp [t.property])
  apply (cancel_epi (orderedRestriction A r f F S p)).mp
  rw [← Category.assoc, ordered_comm, Category.assoc, ordered_comm,
    ← Category.assoc, S.differential_squared]
  simp

private theorem orderedD_subset_formula (A : Type u) [CommRing A]
    (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤)))
    (hle : ∀ (T : Finset (Fin r)) (j : Fin r),
      PrimeSpectrum.basicOpen (∏ i ∈ T, f i) ≤
        PrimeSpectrum.basicOpen (∏ i ∈ T.erase j, f i))
    (p : ℕ) (c : orderedTerms A r f F S p)
    (T : {T : Finset (Fin r) // T.card = (p + 1) + 1}) :
    (subsetIso A r f F S (p + 1)).hom (orderedD A r f F S p c) T =
      ∑ j : T.val, (-1 : A) ^ ((T.val.filter (fun i ↦ i < j.val)).card) •
        F.map (homOfLE (hle T.val j.val)).op
          ((subsetIso A r f F S p).hom c ⟨T.val.erase j.val, by
            rw [Finset.card_erase_of_mem j.property, T.property]
            omega⟩) := by
  classical
  let t : {t : Fin ((p + 1) + 1) → Fin r // StrictMono t} :=
    (tupleSubsetEquiv r (p + 1)).symm T
  have ht : tupleSubsetEquiv r (p + 1) t = T :=
    (tupleSubsetEquiv r (p + 1)).apply_symm_apply T
  have hsource : S.W (p + 1) t.val =
      PrimeSpectrum.basicOpen (∏ i ∈ T.val, f i) :=
    (tupleOpen A r f S (p + 1) t.val).trans
      (congrArg (fun R ↦ PrimeSpectrum.basicOpen (∏ i ∈ R, f i))
        (congrArg Subtype.val ht))
  rw [subsetIso_apply_of_eq A r f F S (p + 1) (orderedD A r f F S p c) t T ht]
  change sectionCast A F hsource
    (∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
      F.map (S.indexMap t.val j.succAbove).op
        (c ⟨t.val ∘ j.succAbove, t.property.comp (Fin.strictMono_succAbove j)⟩)) = _
  rw [map_sum]
  apply Fintype.sum_equiv (T.val.orderIsoOfFin T.property)
  intro j
  rw [map_zsmul]
  have hs : (T.val.filter (fun i ↦ i < (T.val.orderIsoOfFin T.property j).val)).card =
      j.val := countBefore r (p + 1) T j
  erw [hs]
  have he : (tupleSubsetEquiv r p)
      ⟨t.val ∘ j.succAbove, t.property.comp (Fin.strictMono_succAbove j)⟩ =
      ⟨T.val.erase (T.val.orderIsoOfFin T.property j).val, by
        rw [Finset.card_erase_of_mem (T.val.orderIsoOfFin T.property j).property,
          T.property]
        omega⟩ := by
    apply Subtype.ext
    change Finset.univ.image (T.val.orderEmbOfFin T.property ∘ j.succAbove) = _
    rw [eraseEnumeration]
    exact Finset.image_orderEmbOfFin_univ _ _
  erw [subsetIso_apply_of_eq A r f F S p c
    ⟨t.val ∘ j.succAbove, t.property.comp (Fin.strictMono_succAbove j)⟩ _ he]
  have htarget : S.W p (t.val ∘ j.succAbove) =
      PrimeSpectrum.basicOpen
        (∏ i ∈ T.val.erase (T.val.orderIsoOfFin T.property j).val, f i) := by
    have h := tupleOpen A r f S p (t.val ∘ j.succAbove)
    have hset := congrArg Subtype.val he
    change Finset.univ.image (t.val ∘ j.succAbove) =
      T.val.erase (T.val.orderIsoOfFin T.property j).val at hset
    rw [hset] at h
    exact h
  have hnat := sectionCast_natural A F hsource htarget
    (S.indexMap t.val j.succAbove)
    (homOfLE (hle T.val (T.val.orderIsoOfFin T.property j).val))
    (c ⟨t.val ∘ j.succAbove, t.property.comp (Fin.strictMono_succAbove j)⟩)
  erw [show (-1 : A) ^ j.val = (((-1 : ℤ) ^ j.val : ℤ) : A) by simp,
    Int.cast_smul_eq_zsmul A]
  exact congrArg (fun x ↦ (-1 : ℤ) ^ j.val • x) hnat

/-- Subset-coordinate comparison for any module presheaf, without acyclicity assumptions.

Source: Stacks Project, Cohomology, Tags 01FJ, 01FK and 01FM.
(blueprint: lem-sc-principal-open-subset-cech-comparison).

Proof: Construct the ordered complex for the family D(f_i), with cochains the
products over strictly increasing tuples and the usual signed deletion maps.
Restrict full cochains to increasing tuples. This is surjective in each degree
by extension by zero, commutes with the differential by its formula, and hence
the ordered differential squares to zero. The existing restriction homotopy
lemma applies to this concrete complex for any family of opens: it has no cover
hypothesis. Its induced homology maps are isomorphisms.
Reindex each increasing tuple by its range; conversely enumerate a subset of
size p+1 using its order embedding from Fin (p+1). These operations are inverse
because an increasing enumeration of a finite linear order is unique. The
universal properties of the chosen intersections identify the tuple's open
with the intersection over its range, hence with D of the finite product.
Transport sections along this equality. Omitting position j erases the element
in that position, and exactly j entries are smaller. Thus reindexing carries
the tuple differential to the displayed subset formula. Use these additive group
isomorphisms as subset coordinates on the ordered complex. Integer signs agree
with scalar signs in A. The restriction map induces isomorphisms on homology.
Degrees above r-1 are empty products, so the construction includes
the empty index set, repeated or empty opens, and vanishing high degrees. -/
theorem principalOpen_subset_cech_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : (Spec (.of A)).Opensᵒᵖ ⥤ ModuleCat.{u} A)
    (S : SiteCechComplex (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (fun i ↦ homOfLE (le_top : PrimeSpectrum.basicOpen (f i) ≤ ⊤))) :
    let D : Finset (Fin r) → (Spec (.of A)).Opens :=
      fun T ↦ PrimeSpectrum.basicOpen (∏ j ∈ T, f j)
    ∀ (hle : ∀ (T : Finset (Fin r)) (j : Fin r), D T ≤ D (T.erase j)),
    ∃ C : CochainComplex AddCommGrpCat.{u} ℕ,
      ∃ e : ∀ p : ℕ, C.X p ≅ AddCommGrpCat.of
        (∀ T : {T : Finset (Fin r) // T.card = p + 1}, F.obj (op (D T.val))),
        ∃ z : S.complex (F ⋙ forget₂ (ModuleCat A) AddCommGrpCat) ⟶ C,
          (∀ (p : ℕ) (c : C.X p)
            (T : {T : Finset (Fin r) // T.card = (p + 1) + 1}),
            (e (p + 1)).hom (C.d p (p + 1) c) T =
              ∑ j : T.val, (-1 : A) ^ ((T.val.filter (fun i ↦ i < j.val)).card) •
                F.map (homOfLE (hle T.val j.val)).op
                  ((e p).hom c ⟨T.val.erase j.val, by
                    rw [Finset.card_erase_of_mem j.property, T.property]
                    omega⟩)) ∧
          ∀ p : ℕ, IsIso (HomologicalComplex.homologyMap z p) := by
  classical
  dsimp only
  intro hle
  let C := CochainComplex.of (orderedTerms A r f F S)
    (orderedD A r f F S) (ordered_squared A r f F S)
  let e : ∀ p : ℕ, C.X p ≅ AddCommGrpCat.of
      (∀ T : {T : Finset (Fin r) // T.card = p + 1},
        F.obj (op (PrimeSpectrum.basicOpen (∏ j ∈ T.val, f j)))) :=
    subsetIso A r f F S
  let z : S.complex (F ⋙ forget₂ _ AddCommGrpCat) ⟶ C :=
    CochainComplex.ofHom (orderedRestriction A r f F S) (by
      intro p
      simpa only [C, SiteCechComplex.complex, CochainComplex.of_d] using
        ordered_comm A r f F S p)
  refine ⟨C, e, z, ?_, ?_⟩
  · intro p c T
    simp only [C, e, CochainComplex.of_d]
    exact orderedD_subset_formula A r f F S hle p c T
  · let et : ∀ p : ℕ, C.X p ≅ AddCommGrpCat.of
        (∀ t : {t : Fin (p + 1) → Fin r // StrictMono t},
          (F ⋙ forget₂ _ AddCommGrpCat).obj (op (S.W p t.val))) := fun p ↦ Iso.refl _
    have hr : ∀ (p : ℕ) (c : S.cochains (F ⋙ forget₂ _ AddCommGrpCat) p)
        (t : {t : Fin (p + 1) → Fin r // StrictMono t}),
        (et p).hom (z.f p c) t = c t.val := by intros; rfl
    obtain ⟨i, hzi, hiz⟩ := Scheme.alternatingCechRestrictionHomotopy
      (Spec (.of A)) (fun i ↦ PrimeSpectrum.basicOpen (f i))
      (F ⋙ forget₂ _ AddCommGrpCat) S C et z hr
    let E : HomotopyEquiv (S.complex (F ⋙ forget₂ _ AddCommGrpCat)) C :=
      ⟨z, i, hzi.some, hiz.some⟩
    intro p
    exact (E.toHomologyIso p).isIso_hom

end AlgebraicGeometry
