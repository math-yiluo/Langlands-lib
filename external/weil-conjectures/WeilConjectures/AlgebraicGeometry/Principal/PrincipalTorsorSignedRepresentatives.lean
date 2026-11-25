/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Principal.PrincipalTorsorConeCoordinates
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.DivisorTorsorBoundarySigns
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Signed representatives of relative cohomology classes

This file develops the calculus of the predicate `TorsorSignedRepresents` in every degree:
uniqueness and additivity of represented classes, existence of a class for every signed
cocycle, the representatives of boundaries, and the behaviour under maps of relative
complexes.

## References

* Stacks Project, Tag 03AJ, relative refinement
* Tag 0G71
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

namespace AlgebraicGeometry.Etale

private local instance identityForget :
    HasForget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1} where
  forget₂ := 𝟭 _
  forget_comp := rfl

private local instance identityForgetAdditive :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).Additive :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).Additive

private local instance identityForgetHomology :
    (forget₂ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).PreservesHomology :=
  inferInstanceAs (𝟭 AddCommGrpCat.{u + 1}).PreservesHomology

/-- In a complex of abelian groups, a cycle whose homology class vanishes is a boundary. -/
lemma exists_d_eq_iCycles_of_homologyπ_eq_zero (C : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (i j : ℤ) (hij : i + 1 = j) (z : C.cycles j) (hz : C.homologyπ j z = 0) :
    ∃ y : C.X i, C.d i j y = C.iCycles j z := by
  let S := C.sc' i j (j + 1)
  have hi : (ComplexShape.up ℤ).prev j = i := by simp [← hij]
  have hk : (ComplexShape.up ℤ).next j = j + 1 := by simp
  let w := (C.cyclesIsoSc' i j (j + 1) hi hk).hom z
  have hw : S.homologyπ w = 0 := by
    have h := ConcreteCategory.congr_hom (C.π_homologyIsoSc'_hom i j (j + 1) hi hk) z
    simp only [ConcreteCategory.comp_apply, hz, map_zero] at h
    exact h.symm
  let K := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
  have hK : K.Exact := ShortComplex.exact_of_g_is_cokernel _ S.homologyIsCokernel
  obtain ⟨y, hy⟩ := K.ab_exact_iff.mp hK w hw
  refine ⟨y, ?_⟩
  have h := congrArg S.iCycles hy
  rw [← ConcreteCategory.comp_apply, S.toCycles_i, ← ConcreteCategory.comp_apply,
    cyclesIsoSc'_hom_iCycles] at h
  exact h

lemma embeddingUpNat_f_succ (q : ℕ) : ComplexShape.embeddingUpNat.f (q + 1) = (q : ℤ) + 1 := by
  simp

lemma embeddingUpNat_f_succ_succ (q : ℕ) :
    ComplexShape.embeddingUpNat.f (q + 1 + 1) = (q : ℤ) + 1 + 1 := by
  simp

/-- In a complex of abelian groups, an element with zero differential is a cycle. -/
lemma exists_iCycles_eq_of_d_eq_zero (C : CochainComplex AddCommGrpCat.{u + 1} ℤ)
    (i j : ℤ) (hij : i + 1 = j) (v : C.X i) (hv : C.d i j v = 0) :
    ∃ z : C.cycles i, C.iCycles i z = v :=
  ⟨C.cyclesMk v j (by simp [← hij]) hv, C.i_cyclesMk v j (by simp [← hij]) hv⟩

variable (T : Scheme.{u}) (U : T.Etale)
  (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ)

/-- The extension-by-zero identification of global sections in degree `q`. -/
abbrev globalXIso {i' : ℤ} (i : ℕ) (hi : ComplexShape.embeddingUpNat.f i = i') :=
  (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj
    I).extendXIso ComplexShape.embeddingUpNat hi

/-- The extension-by-zero identification of sections over `U` in degree `q`. -/
abbrev openXIso {i' : ℤ} (i : ℕ) (hi : ComplexShape.embeddingUpNat.f i = i') :=
  (((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
    ComplexShape.embeddingUpNat hi

lemma torsorSignedA_apply (q : ℕ) (x : (relativeSectionComplex T U I).X ((q : ℤ) + 1)) :
    torsorSignedA T U I q x = (globalXIso T I (q + 1) (embeddingUpNat_f_succ q)).hom
      (ShiftedCone.fst (relativeSectionRestriction T U I) ((q : ℤ) + 1) q rfl x) :=
  rfl

lemma torsorSignedB_apply (q : ℕ) (x : (relativeSectionComplex T U I).X ((q : ℤ) + 1)) :
    torsorSignedB T U I q x = -(openXIso T U I q (ComplexShape.embeddingUpNat_f q)).hom
      (ShiftedCone.snd (relativeSectionRestriction T U I) ((q : ℤ) + 1) q rfl x) :=
  rfl

lemma relativeSectionComplex_d_fst (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n')
    (x : (relativeSectionComplex T U I).X n) :
    ShiftedCone.fst (relativeSectionRestriction T U I) n' n h'
        ((relativeSectionComplex T U I).d n n' x) =
      (relativeSections (Scheme.Etale.mk (𝟙 T)) I).d n n'
        (ShiftedCone.fst (relativeSectionRestriction T U I) n m h x) :=
  ShiftedCone.d_fst_apply _ n n' m h h' x

lemma relativeSectionComplex_d_snd (n n' m : ℤ) (h : m + 1 = n) (h' : n + 1 = n')
    (x : (relativeSectionComplex T U I).X n) :
    ShiftedCone.snd (relativeSectionRestriction T U I) n' n h'
        ((relativeSectionComplex T U I).d n n' x) =
      -((relativeSectionRestriction T U I).f n
          (ShiftedCone.fst (relativeSectionRestriction T U I) n m h x) +
        (relativeSections U I).d m n
          (ShiftedCone.snd (relativeSectionRestriction T U I) n m h x)) :=
  ShiftedCone.d_snd_apply _ n n' m h h' x

/-- The differential of an extended section complex in nonnegative degrees. -/
lemma relativeSections_d_apply (V : T.Etale) {i j : ℕ} {i' j' : ℤ}
    (hi : ComplexShape.embeddingUpNat.f i = i') (hj : ComplexShape.embeddingUpNat.f j = j')
    (x : (relativeSections V I).X i') :
    (relativeSections V I).d i' j' x =
      ((((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
        ComplexShape.embeddingUpNat hj).inv ((I.d i j).hom.app (op V)
          (((((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
            ComplexShape.embeddingUpNat hi).hom x)) := by
  exact ConcreteCategory.congr_hom (extend_d_eq _ _ hi hj) x

/-- The restriction map of extended section complexes in nonnegative degrees. -/
lemma relativeSectionRestriction_f_apply {i : ℕ} {i' : ℤ}
    (hi : ComplexShape.embeddingUpNat.f i = i')
    (x : (relativeSections (Scheme.Etale.mk (𝟙 T)) I).X i') :
    (relativeSectionRestriction T U I).f i' x = (openXIso T U I i hi).inv
      ((I.X i).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op
        ((globalXIso T I i hi).hom x)) := by
  exact ConcreteCategory.congr_hom (extendMap_f _ _ hi) x

variable {T U I}

/-- A class is determined by any of its signed representatives. -/
theorem TorsorSignedRepresents.unique {q : ℕ}
    {a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))} {b : (I.X q).obj.obj (op U)}
    {x y : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)}
    (hx : TorsorSignedRepresents T U I q a b x) (hy : TorsorSignedRepresents T U I q a b y) :
    x = y := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  obtain ⟨z', ha', hb', rfl⟩ := hy
  congr 1
  apply (AddCommGrpCat.mono_iff_injective
    ((relativeSectionComplex T U I).iCycles ((q : ℤ) + 1))).1 inferInstance
  apply ShiftedCone.ext (relativeSectionRestriction T U I) (rfl : (q : ℤ) + 1 = (q : ℤ) + 1)
  · apply (ConcreteCategory.bijective_of_isIso
      (globalXIso T I (q + 1) (embeddingUpNat_f_succ q)).hom).1
    rw [torsorSignedA_apply] at ha ha'
    exact ha.trans ha'.symm
  · apply (ConcreteCategory.bijective_of_isIso
      (openXIso T U I q (ComplexShape.embeddingUpNat_f q)).hom).1
    rw [torsorSignedB_apply] at hb hb'
    exact neg_injective (hb.trans hb'.symm)

/-- Signed representatives add. -/
theorem TorsorSignedRepresents.add {q : ℕ}
    {a a' : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))} {b b' : (I.X q).obj.obj (op U)}
    {x y : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)}
    (hx : TorsorSignedRepresents T U I q a b x) (hy : TorsorSignedRepresents T U I q a' b' y) :
    TorsorSignedRepresents T U I q (a + a') (b + b') (x + y) := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  obtain ⟨z', ha', hb', rfl⟩ := hy
  exact ⟨z + z', by simp only [map_add, ha, ha'], by simp only [map_add, hb, hb'],
    by simp only [map_add]⟩

/-- Signed representatives negate. -/
theorem TorsorSignedRepresents.neg {q : ℕ}
    {a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))} {b : (I.X q).obj.obj (op U)}
    {x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)}
    (hx : TorsorSignedRepresents T U I q a b x) :
    TorsorSignedRepresents T U I q (-a) (-b) (-x) := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  exact ⟨-z, by simp only [map_neg, ha], by simp only [map_neg, hb], by simp only [map_neg]⟩

variable (T U I) in
/-- Every class has a signed representative. -/
theorem exists_torsorSignedRepresents_of_class (q : ℕ)
    (x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)) :
    ∃ (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
      (b : (I.X q).obj.obj (op U)), TorsorSignedRepresents T U I q a b x := by
  obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    ((relativeSectionComplex T U I).homologyπ ((q : ℤ) + 1))).1 inferInstance x
  exact ⟨_, _, z, rfl, rfl, rfl⟩

variable (T U I) in
/-- A signed cocycle represents a class: the cocycle conditions are `d a = 0` and
`res a = d b`. -/
theorem exists_torsorSignedRepresents (q : ℕ)
    (a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) (b : (I.X q).obj.obj (op U))
    (ha : (I.d (q + 1) (q + 1 + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) a = 0)
    (hb : (I.X (q + 1)).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op a =
      (I.d q (q + 1)).hom.app (op U) b) :
    ∃ x, TorsorSignedRepresents T U I q a b x := by
  let r := relativeSectionRestriction T U I
  let v : (relativeSectionComplex T U I).X ((q : ℤ) + 1) := ShiftedCone.mk r ((q : ℤ) + 1) q rfl
    ((globalXIso T I (q + 1) (embeddingUpNat_f_succ q)).inv a)
    (-(openXIso T U I q (ComplexShape.embeddingUpNat_f q)).inv b)
  have hd : (relativeSectionComplex T U I).d ((q : ℤ) + 1) ((q : ℤ) + 1 + 1) v = 0 := by
    apply ShiftedCone.ext r (rfl : (q : ℤ) + 1 + 1 = (q : ℤ) + 1 + 1)
    · rw [relativeSectionComplex_d_fst T U I _ _ q rfl rfl, ShiftedCone.fst_mk,
        relativeSections_d_apply T I _ (i := q + 1) (j := q + 1 + 1) (embeddingUpNat_f_succ q)
          (embeddingUpNat_f_succ_succ q), Iso.inv_hom_id_apply, ha]
      simp
    · rw [relativeSectionComplex_d_snd T U I _ _ q rfl rfl, ShiftedCone.fst_mk,
        ShiftedCone.snd_mk, relativeSectionRestriction_f_apply T U I (embeddingUpNat_f_succ q),
        relativeSections_d_apply T I U (i := q) (j := q + 1) (ComplexShape.embeddingUpNat_f q)
          (embeddingUpNat_f_succ q),
        Iso.inv_hom_id_apply, map_neg, Iso.inv_hom_id_apply, hb, map_neg, map_neg]
      simp
  obtain ⟨z, hz⟩ := exists_iCycles_eq_of_d_eq_zero (relativeSectionComplex T U I) _ _ rfl v hd
  refine ⟨_, z, ?_, ?_, rfl⟩
  · rw [torsorSignedA_apply, hz, ShiftedCone.fst_mk, Iso.inv_hom_id_apply]
  · rw [torsorSignedB_apply, hz, ShiftedCone.snd_mk, map_neg, Iso.inv_hom_id_apply,
      neg_neg]


variable (T I) in
lemma relativeSections_d_hom_apply (V : T.Etale) {i j : ℕ} {i' j' : ℤ}
    (hi : ComplexShape.embeddingUpNat.f i = i') (hj : ComplexShape.embeddingUpNat.f j = j')
    (x : (relativeSections V I).X i') :
    ((((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
        ComplexShape.embeddingUpNat hj).hom ((relativeSections V I).d i' j' x) =
      (I.d i j).hom.app (op V)
        (((((etaleSectionFunctor V).mapHomologicalComplex (.up ℕ)).obj I).extendXIso
          ComplexShape.embeddingUpNat hi).hom x) := by
  rw [relativeSections_d_apply T I V hi hj, Iso.inv_hom_id_apply]

variable (T U I) in
lemma relativeSectionRestriction_f_hom_apply {i : ℕ} {i' : ℤ}
    (hi : ComplexShape.embeddingUpNat.f i = i')
    (x : (relativeSections (Scheme.Etale.mk (𝟙 T)) I).X i') :
    (openXIso T U I i hi).hom ((relativeSectionRestriction T U I).f i' x) =
      (I.X i).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op
        ((globalXIso T I i hi).hom x) := by
  rw [relativeSectionRestriction_f_apply T U I hi, Iso.inv_hom_id_apply]

variable (T U I) in
/-- The boundary of a global cochain `c` has signed coordinates `(d c, res c)`. -/
theorem torsorSignedRepresents_boundary (q : ℕ)
    (c : (I.X q).obj.obj (op (Scheme.Etale.mk (𝟙 T)))) :
    TorsorSignedRepresents T U I q ((I.d q (q + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) c)
      ((I.X q).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op c) 0 := by
  let r := relativeSectionRestriction T U I
  let K := relativeSectionComplex T U I
  let y : K.X (q : ℤ) := ShiftedCone.mk r (q : ℤ) ((q : ℤ) - 1) (by omega)
    ((globalXIso T I q (ComplexShape.embeddingUpNat_f q)).inv c) 0
  have hi : K.iCycles ((q : ℤ) + 1) (K.toCycles (q : ℤ) ((q : ℤ) + 1) y) =
      K.d (q : ℤ) ((q : ℤ) + 1) y :=
    ConcreteCategory.congr_hom (K.toCycles_i _ _) y
  refine ⟨K.toCycles (q : ℤ) ((q : ℤ) + 1) y, ?_, ?_, ?_⟩
  · rw [torsorSignedA_apply, hi, relativeSectionComplex_d_fst T U I _ _ ((q : ℤ) - 1) (by omega)
      rfl, ShiftedCone.fst_mk, relativeSections_d_hom_apply T I _ (ComplexShape.embeddingUpNat_f q)
      (embeddingUpNat_f_succ q), Iso.inv_hom_id_apply]
  · rw [torsorSignedB_apply, hi, relativeSectionComplex_d_snd T U I _ _ ((q : ℤ) - 1)
      (by omega) rfl, ShiftedCone.fst_mk, ShiftedCone.snd_mk, map_zero, add_zero, map_neg,
      neg_neg, relativeSectionRestriction_f_hom_apply T U I (ComplexShape.embeddingUpNat_f q),
      Iso.inv_hom_id_apply]
  · exact ConcreteCategory.congr_hom (K.toCycles_comp_homologyπ _ _) y

variable (T U I) in
/-- Restriction of extended section complexes is degreewise surjective as soon as the
restriction of each term is. -/
lemma relativeSectionRestriction_f_surjective
    (hsurj : ∀ p : ℕ, Function.Surjective
      ((I.X p).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op))
    (n : ℤ) : Function.Surjective ((relativeSectionRestriction T U I).f n) := by
  intro e
  cases n with
  | ofNat p =>
    have hp : ComplexShape.embeddingUpNat.f p = Int.ofNat p := rfl
    obtain ⟨c, hc⟩ := hsurj p ((openXIso T U I p hp).hom e)
    refine ⟨(globalXIso T I p hp).inv c, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (openXIso T U I p hp).hom).1
    rw [relativeSectionRestriction_f_hom_apply T U I hp, Iso.inv_hom_id_apply, hc]
  | negSucc p =>
    refine ⟨0, ?_⟩
    have hz : IsZero ((relativeSections U I).X (Int.negSucc p)) :=
      isZero_extend_X _ _ _ (fun m hm ↦ by simp at hm)
    exact (AddCommGrpCat.isZero_iff_subsingleton.1 hz).elim _ _

/-- A signed pair represents zero precisely when it is the boundary of a global cochain;
this direction needs surjective restriction maps, as for injective resolutions. -/
theorem TorsorSignedRepresents.exists_of_zero {q : ℕ}
    {a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))} {b : (I.X q).obj.obj (op U)}
    (hsurj : ∀ p : ℕ, Function.Surjective
      ((I.X p).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op))
    (h : TorsorSignedRepresents T U I q a b 0) :
    ∃ c : (I.X q).obj.obj (op (Scheme.Etale.mk (𝟙 T))),
      (I.d q (q + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) c = a ∧
      (I.X q).obj.map ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op c = b := by
  obtain ⟨z, ha, hb, hz⟩ := h
  let r := relativeSectionRestriction T U I
  let K := relativeSectionComplex T U I
  obtain ⟨y, hy⟩ := exists_d_eq_iCycles_of_homologyπ_eq_zero K (q : ℤ) ((q : ℤ) + 1) rfl z hz
  obtain ⟨e, he⟩ := relativeSectionRestriction_f_surjective T U I hsurj ((q : ℤ) - 1)
    (ShiftedCone.snd r (q : ℤ) ((q : ℤ) - 1) (by omega) y)
  let c' := ShiftedCone.fst r (q : ℤ) ((q : ℤ) - 1) (by omega) y +
    (relativeSections (Scheme.Etale.mk (𝟙 T)) I).d ((q : ℤ) - 1) q e
  refine ⟨(globalXIso T I q (ComplexShape.embeddingUpNat_f q)).hom c', ?_, ?_⟩
  · rw [← relativeSections_d_hom_apply T I _ (ComplexShape.embeddingUpNat_f q)
      (embeddingUpNat_f_succ q),
      ← ha, torsorSignedA_apply, ← hy, relativeSectionComplex_d_fst T U I _ _ ((q : ℤ) - 1)
      (by omega) rfl]
    have hdd : (relativeSections (Scheme.Etale.mk (𝟙 T)) I).d q ((q : ℤ) + 1)
        ((relativeSections (Scheme.Etale.mk (𝟙 T)) I).d ((q : ℤ) - 1) q e) = 0 := by
      rw [← ConcreteCategory.comp_apply, d_comp_d]
      rfl
    simp only [c', map_add, hdd, add_zero]
    rfl
  · rw [← relativeSectionRestriction_f_hom_apply T U I (ComplexShape.embeddingUpNat_f q), ← hb,
      torsorSignedB_apply, ← hy, relativeSectionComplex_d_snd T U I _ _ ((q : ℤ) - 1)
      (by omega) rfl, map_neg, neg_neg]
    congr 1
    simp only [c', map_add]
    congr 1
    rw [← he]
    exact (ConcreteCategory.congr_hom (r.comm ((q : ℤ) - 1) q) e).symm


/-- The extension by zero of a morphism of nonnegative complexes, elementwise. -/
lemma extendMap_apply {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ} (φ : K ⟶ L) {i : ℕ}
    {i' : ℤ} (hi : ComplexShape.embeddingUpNat.f i = i')
    (x : (K.extend ComplexShape.embeddingUpNat).X i') :
    (extendMap φ ComplexShape.embeddingUpNat).f i' x =
      (L.extendXIso ComplexShape.embeddingUpNat hi).inv
        (φ.f i ((K.extendXIso ComplexShape.embeddingUpNat hi).hom x)) :=
  ConcreteCategory.congr_hom (extendMap_f _ _ hi) x

section RepresentativeMaps

variable {T' : Scheme.{u}} {U' : T'.Etale}
  {J : CochainComplex (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
  (α : ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex (.up ℕ)).obj I ⟶
    ((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T'))).mapHomologicalComplex (.up ℕ)).obj J)
  (β : ((etaleSectionFunctor U).mapHomologicalComplex (.up ℕ)).obj I ⟶
    ((etaleSectionFunctor U').mapHomologicalComplex (.up ℕ)).obj J)
  (h : extendMap α ComplexShape.embeddingUpNat ≫ relativeSectionRestriction T' U' J =
    relativeSectionRestriction T U I ≫ extendMap β ComplexShape.embeddingUpNat)

/-- Maps of relative complexes induced by maps of section complexes act on signed
representatives coordinatewise. -/
theorem TorsorSignedRepresents.map {q : ℕ}
    {a : (I.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))} {b : (I.X q).obj.obj (op U)}
    {x : (relativeSectionComplex T U I).homology ((q : ℤ) + 1)}
    (hx : TorsorSignedRepresents T U I q a b x) :
    TorsorSignedRepresents T' U' J q (α.f (q + 1) a) (β.f q b)
      (homologyMap (relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
        (extendMap β ComplexShape.embeddingUpNat) h) ((q : ℤ) + 1) x) := by
  obtain ⟨z, ha, hb, rfl⟩ := hx
  let f := relativeFiberMap _ _ (extendMap α ComplexShape.embeddingUpNat)
    (extendMap β ComplexShape.embeddingUpNat) h
  have hi : (relativeSectionComplex T' U' J).iCycles _ (cyclesMap f _ z) =
      f.f _ ((relativeSectionComplex T U I).iCycles _ z) :=
    ConcreteCategory.congr_hom (cyclesMap_i f _) z
  refine ⟨cyclesMap f _ z, ?_, ?_, (ConcreteCategory.congr_hom (homologyπ_naturality f _) z).symm⟩
  · rw [hi, torsorSignedA_apply, ← ha, torsorSignedA_apply, ShiftedCone.fiberMap_fst_apply]
    erw [extendMap_apply α (embeddingUpNat_f_succ q), Iso.inv_hom_id_apply]
    rfl
  · rw [hi, torsorSignedB_apply, ← hb, torsorSignedB_apply, ShiftedCone.fiberMap_snd_apply]
    erw [extendMap_apply β (ComplexShape.embeddingUpNat_f q), Iso.inv_hom_id_apply, map_neg]
    rfl

end RepresentativeMaps

/-- The connecting map of a short exact sequence of complexes of abelian groups on cycles:
if `v₂` lifts the cycle `z` and `v₁` maps to the differential of `v₂`, then `v₁` is a cycle
whose class is the image of the class of `z`. -/
lemma exists_cycle_connecting (R : ShortComplex (CochainComplex AddCommGrpCat.{u + 1} ℤ))
    (hR : R.ShortExact) (q : ℤ) (z : R.X₃.cycles q) (v₂ : R.X₂.X q)
    (hv₂ : R.g.f q v₂ = R.X₃.iCycles q z) (v₁ : R.X₁.X (q + 1))
    (hv₁ : R.f.f (q + 1) v₁ = R.X₂.d q (q + 1) v₂) :
    ∃ w : R.X₁.cycles (q + 1), R.X₁.iCycles (q + 1) w = v₁ ∧
      R.X₁.homologyπ (q + 1) w = hR.δ q (q + 1) rfl (R.X₃.homologyπ q z) := by
  let v₃ := R.X₃.iCycles q z
  have hv₃ : R.X₃.d q (q + 1) v₃ = 0 :=
    ConcreteCategory.congr_hom (R.X₃.iCycles_d q (q + 1)) z
  have hd := hR.δ_apply q (q + 1) rfl v₃ hv₃ v₂ hv₂ v₁ hv₁ (q + 2) (by simp [add_assoc])
  have heq : R.X₃.cyclesMk (i := q) v₃ (q + 1) (by simp) hv₃ = z := by
    apply (AddCommGrpCat.mono_iff_injective (R.X₃.iCycles q)).1 inferInstance
    exact HomologicalComplex.i_cyclesMk R.X₃ (i := q) v₃ (q + 1) (by simp) hv₃
  rw [heq] at hd
  refine ⟨_, ?_, hd.symm⟩
  exact HomologicalComplex.i_cyclesMk R.X₁ (i := q + 1) v₁ (q + 2)
    (by simp [add_assoc]) (hR.d_eq_zero_of_f_eq_d_apply q (q + 1) v₂ v₁ hv₁ (q + 2))

section SectionMap

variable {J : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ}
  (f : I ⟶ J)

lemma relativeSectionMap_fst_apply {n m : ℤ} (h : m + 1 = n) {i : ℕ}
    (hi : ComplexShape.embeddingUpNat.f i = n) (x : (relativeSectionComplex T U I).X n) :
    (globalXIso T J i hi).hom (ShiftedCone.fst (relativeSectionRestriction T U J) n m h
      ((relativeSectionMap T U f).f n x)) =
      (f.f i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
        ((globalXIso T I i hi).hom
          (ShiftedCone.fst (relativeSectionRestriction T U I) n m h x)) := by
  rw [relativeSectionMap]
  erw [ShiftedCone.fiberMap_fst_apply, extendMap_apply _ hi, Iso.inv_hom_id_apply]
  rfl

lemma relativeSectionMap_snd_apply {n m : ℤ} (h : m + 1 = n) {i : ℕ}
    (hi : ComplexShape.embeddingUpNat.f i = m) (x : (relativeSectionComplex T U I).X n) :
    (openXIso T U J i hi).hom (ShiftedCone.snd (relativeSectionRestriction T U J) n m h
      ((relativeSectionMap T U f).f n x)) =
      (f.f i).hom.app (op U)
        ((openXIso T U I i hi).hom
          (ShiftedCone.snd (relativeSectionRestriction T U I) n m h x)) := by
  rw [relativeSectionMap]
  erw [ShiftedCone.fiberMap_snd_apply, extendMap_apply _ hi, Iso.inv_hom_id_apply]
  rfl

end SectionMap

/-- The relative connecting map on signed representatives with vanishing open coordinate:
lift the global coordinate, take its differential and pull it back. -/
theorem TorsorSignedRepresents.connecting
    (S : ShortComplex (CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ))
    (hs : ∀ n : ℕ, Nonempty ((S.map (HomologicalComplex.eval _ (.up ℕ) n)).Splitting))
    {q : ℕ} {a : (S.X₃.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T)))}
    {x : (relativeSectionComplex T U S.X₃).homology ((q : ℤ) + 1)}
    (hx : TorsorSignedRepresents T U S.X₃ q a 0 x)
    (b : (S.X₂.X (q + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (hb : (S.g.f (q + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) b = a)
    (hres : (S.X₂.X (q + 1)).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from U).op b = 0)
    (c : (S.X₁.X (q + 1 + 1)).obj.obj (op (Scheme.Etale.mk (𝟙 T))))
    (hc : (S.f.f (q + 1 + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) c =
      (S.X₂.d (q + 1) (q + 1 + 1)).hom.app (op (Scheme.Etale.mk (𝟙 T))) b) :
    TorsorSignedRepresents T U S.X₁ (q + 1) c 0
      (relativeConnecting T U S hs ((q : ℤ) + 1) x) := by
  obtain ⟨z, ha, hb0, rfl⟩ := hx
  let r₁ := relativeSectionRestriction T U S.X₁
  let r₂ := relativeSectionRestriction T U S.X₂
  let r₃ := relativeSectionRestriction T U S.X₃
  let v₂ : (relativeSectionComplex T U S.X₂).X ((q : ℤ) + 1) := ShiftedCone.mk r₂ ((q : ℤ) + 1)
    q rfl ((globalXIso T S.X₂ (q + 1) (embeddingUpNat_f_succ q)).inv b) 0
  let v₁ : (relativeSectionComplex T U S.X₁).X ((q : ℤ) + 1 + 1) := ShiftedCone.mk r₁
    ((q : ℤ) + 1 + 1) ((q : ℤ) + 1) rfl
    ((globalXIso T S.X₁ (q + 1 + 1) (embeddingUpNat_f_succ_succ q)).inv c) 0
  have hv₂ : (relativeSectionMap T U S.g).f ((q : ℤ) + 1) v₂ =
      (relativeSectionComplex T U S.X₃).iCycles ((q : ℤ) + 1) z := by
    apply ShiftedCone.ext r₃ (rfl : (q : ℤ) + 1 = _)
    · apply (ConcreteCategory.bijective_of_isIso
        (globalXIso T S.X₃ (q + 1) (embeddingUpNat_f_succ q)).hom).1
      rw [relativeSectionMap_fst_apply S.g rfl (embeddingUpNat_f_succ q), ShiftedCone.fst_mk,
        Iso.inv_hom_id_apply, hb, ← ha, torsorSignedA_apply]
    · apply (ConcreteCategory.bijective_of_isIso
        (openXIso T U S.X₃ q (ComplexShape.embeddingUpNat_f q)).hom).1
      rw [relativeSectionMap_snd_apply S.g rfl (ComplexShape.embeddingUpNat_f q),
        ShiftedCone.snd_mk, map_zero, map_zero]
      rw [torsorSignedB_apply, neg_eq_zero] at hb0
      exact hb0.symm
  have hv₁ : (relativeSectionMap T U S.f).f ((q : ℤ) + 1 + 1) v₁ =
      (relativeSectionComplex T U S.X₂).d ((q : ℤ) + 1) ((q : ℤ) + 1 + 1) v₂ := by
    apply ShiftedCone.ext r₂ (rfl : (q : ℤ) + 1 + 1 = _)
    · apply (ConcreteCategory.bijective_of_isIso
        (globalXIso T S.X₂ (q + 1 + 1) (embeddingUpNat_f_succ_succ q)).hom).1
      rw [relativeSectionMap_fst_apply S.f rfl (embeddingUpNat_f_succ_succ q),
        ShiftedCone.fst_mk, Iso.inv_hom_id_apply, hc,
        relativeSectionComplex_d_fst T U S.X₂ _ _ q rfl rfl, ShiftedCone.fst_mk,
        relativeSections_d_hom_apply T S.X₂ _ (embeddingUpNat_f_succ q)
          (embeddingUpNat_f_succ_succ q), Iso.inv_hom_id_apply]
    · apply (ConcreteCategory.bijective_of_isIso
        (openXIso T U S.X₂ (q + 1) (embeddingUpNat_f_succ q)).hom).1
      rw [relativeSectionMap_snd_apply S.f rfl (embeddingUpNat_f_succ q), ShiftedCone.snd_mk,
        map_zero, map_zero, relativeSectionComplex_d_snd T U S.X₂ _ _ q rfl rfl,
        ShiftedCone.fst_mk, ShiftedCone.snd_mk, map_zero, add_zero, map_neg,
        relativeSectionRestriction_f_hom_apply T U S.X₂ (embeddingUpNat_f_succ q),
        Iso.inv_hom_id_apply, hres, neg_zero]
  obtain ⟨w, hw, hwπ⟩ := exists_cycle_connecting (relativeShortComplex T U S)
    (relativeShortComplex_shortExact T U S hs) ((q : ℤ) + 1) z v₂ hv₂ v₁ hv₁
  refine ⟨w, ?_, ?_, hwπ⟩
  · rw [torsorSignedA_apply]
    erw [hw]
    exact (congrArg (globalXIso T S.X₁ (q + 1 + 1) (embeddingUpNat_f_succ_succ q)).hom
      (ShiftedCone.fst_mk r₁ _ _ rfl _ _)).trans (Iso.inv_hom_id_apply _ c)
  · rw [torsorSignedB_apply]
    erw [hw]
    exact (congrArg (fun t ↦ -(openXIso T U S.X₁ (q + 1) (embeddingUpNat_f_succ q)).hom t)
      (ShiftedCone.snd_mk r₁ _ _ rfl _ _)).trans (by simp only [map_zero, neg_zero])


end AlgebraicGeometry.Etale
