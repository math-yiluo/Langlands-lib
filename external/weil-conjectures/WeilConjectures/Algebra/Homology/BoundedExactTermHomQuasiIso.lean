/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.SingleDegreeExactTermHomQuasiIso
import WeilConjectures.Algebra.Homology.StupidTailHomShortExact
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Bounded Hom complexes with exact internal Hom in each source degree

Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation,
and Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-pc-bounded-exact-term-hom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homObjMap_zero_source
    {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A A' B B' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (g : B ⟶ B') :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

private lemma homObj_isZero_source
    {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (hA : IsZero A) (B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    IsZero (SheafOfModules.homObj (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id (R := R) (M := A) (N := B)]
  rw [hA.eq_of_src (𝟙 A) 0, homObjMap_zero_source]

private lemma exact_homObj_of_isZero
    {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (hA : IsZero A)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 A) S.g) hz).ShortExact := by
  have h₁ := homObj_isZero_source hA S.X₁
  have h₂ := homObj_isZero_source hA S.X₂
  have h₃ := homObj_isZero_source hA S.X₃
  refine ⟨h₁.eq_of_src _ _, ?_⟩
  exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
          mono_f := h₁.mono _
          epi_g := h₃.epi _ }

set_option backward.isDefEq.respectTransparency false in
private lemma exact_homObj_of_iso
    {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (e : A ≅ B)
    (S : ShortComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))
    (hB : ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 B) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 B) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 B) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 B) S.g) hz).ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap (R := R) (𝟙 A) S.g) hz).ShortExact := by
  obtain ⟨hz, hS⟩ := hB
  have hzA : SheafOfModules.homObjMap (R := R) (𝟙 A) S.f ≫
      SheafOfModules.homObjMap (R := R) (𝟙 A) S.g = 0 := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
    rw [S.zero]
    apply SheafOfModules.hom_ext
    ext X φ : 3
    change (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 A : A ⟶ A).val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
    ext W x
    rfl
  refine ⟨hzA, ShortComplex.shortExact_of_iso ?_ hS⟩
  let i (D : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
      SheafOfModules.homObj (R := R) B D ≅ SheafOfModules.homObj (R := R) A D :=
    ((SheafOfModules.homFunctor R).flip.obj D).mapIso e.op
  exact ShortComplex.isoMk (i S.X₁) (i S.X₂) (i S.X₃) (by
    dsimp [i, SheafOfModules.homFunctor]
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id, Category.id_comp])
    (by
      dsimp [i, SheafOfModules.homFunctor]
      simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.comp_id, Category.id_comp])

private lemma quasiIso_homComplex_map_of_stupid_tail
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N)
    (hsingle : QuasiIso (((homComplexFunctor (R := R)).obj
      (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj (P.X k)))).map f))
    (htail : QuasiIso (((homComplexFunctor (R := R)).obj
      (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by
  obtain ⟨S, T, φ, hS, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_homComplex_stupid_tail_shortExact J R P k hbelow f
  have h₁ : QuasiIso φ.τ₁ :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e₁).2 hsingle
  have h₃ : QuasiIso φ.τ₃ :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e₃).2 htail
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e₂).1
    (HomologicalComplex.HomologySequence.quasiIso_τ₂ φ hS hT h₁ h₃)

private lemma quasiIso_homComplex_map_of_interval
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (a : ℤ) (d : ℕ)
    (hbounded : ∀ n : ℤ, n < a ∨ a + (d : ℤ) < n → IsZero (P.X n))
    (hexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g) hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f)  := by
  induction d generalizing P a with
  | zero =>
    apply quasiIso_homComplex_map_of_single_degree_exact_term J R P a
    · intro n hn
      apply hbounded n
      simp only [Nat.cast_zero, add_zero]
      omega
    · exact hexact a
  | succ d ih =>
    let T := P.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))
    have hTbound : ∀ n : ℤ, n < a + 1 ∨ a + 1 + (d : ℤ) < n →
        IsZero (T.X n) := by
      intro n hn
      by_cases hlow : n < a + 1
      · exact P.isZero_stupidTrunc_X _ n
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff (a + 1) n).2 hlow)
      · obtain ⟨i, hi⟩ := Int.le.dest (show a + 1 ≤ n by omega)
        have heq : (ComplexShape.embeddingUpIntGE (a + 1)).f i = n := by
          simpa using hi
        exact (hbounded n (Or.inr (by omega))).of_iso
          (P.stupidTruncXIso _ heq)
    have hTexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
        S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (T.X n)) S.f ≫
            SheafOfModules.homObjMap (R := R) (𝟙 (T.X n)) S.g = 0,
          (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (T.X n)) S.f)
            (SheafOfModules.homObjMap (R := R) (𝟙 (T.X n)) S.g) hz).ShortExact := by
      intro n S hS
      by_cases hlow : n < a + 1
      · exact exact_homObj_of_isZero
          (P.isZero_stupidTrunc_X _ n
            ((ComplexShape.notMem_range_embeddingUpIntGE_iff (a + 1) n).2 hlow)) S
      · obtain ⟨i, hi⟩ := Int.le.dest (show a + 1 ≤ n by omega)
        have heq : (ComplexShape.embeddingUpIntGE (a + 1)).f i = n := by
          simpa using hi
        exact exact_homObj_of_iso (P.stupidTruncXIso _ heq) S (hexact n S hS)
    have htail : QuasiIso (((homComplexFunctor (R := R)).obj (op T)).map f) :=
      ih T (a + 1) hTbound hTexact
    have hsingle : QuasiIso (((homComplexFunctor (R := R)).obj
        (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj (P.X a)))).map f) := by
      apply quasiIso_homComplex_map_of_single_degree_exact_term J R _ a
      · intro n hn
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      · intro S hS
        exact exact_homObj_of_iso
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (P.X a)) S
          (hexact a S hS)
    exact quasiIso_homComplex_map_of_stupid_tail J R P a
      (fun n hn ↦ hbounded n (Or.inl hn)) f hsingle htail


/-- A bounded source complex whose termwise internal Hom preserves short exact sequences
sends every quasi-isomorphism in the second variable to a quasi-isomorphism. The second
variable is arbitrary, and no K-injective resolution or derived category occurs here.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation;
Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-pc-bounded-exact-term-hom-quasi-iso).

Proof:
1. Prove the assertion for a source supported in [a,a+d], by induction on the
   natural number d. For d=0 use the single-degree exact-term Hom calculation.
2. For a successor width, take the stupid tail starting at a+1. Its terms are
   either zero or isomorphic to the corresponding terms of P. Internal Hom from
   zero is zero; transport short exactness through the other term isomorphisms.
   The tail has width d, so the induction hypothesis applies. The single complex
   on P.X a is handled by the base calculation, transporting the exact-term
   hypothesis through its degree-a term isomorphism.
3. Extension by zero and restriction of the Hom product factors give a natural
   short exact sequence with singleton and tail as its outer terms. Apply the
   upstream long-exact-sequence lemma quasiIso_τ₂ to the outer quasi-isomorphisms
   and transport the middle quasi-isomorphism through its arrow isomorphism.
4. For the original bounds a,b choose d=(b-a).toNat, so b ≤ a+d even if b<a.
   Apply the interval induction. Both target complexes may be unbounded, and no
   exactness of an infinite product is needed. -/
theorem quasiIso_homComplex_map_of_bounded_exact_terms
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X n)) S.g) hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by
  obtain ⟨a, b, hb⟩ := hbounded
  apply quasiIso_homComplex_map_of_interval J R P a (b - a).toNat _ hexact f
  intro n hn
  apply hb n
  rcases hn with hn | hn
  · exact Or.inl hn
  · exact Or.inr (by omega)

end CategoryTheory
