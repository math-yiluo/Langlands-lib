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
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit

/-! # Hom from a complex concentrated in one degree

Source: Stacks Project, Tag 0A8X, Hom complexes; Tag 08DM, bounded Hom calculation;
Tag 010N, exact functors. The argument isolates step 1 of the bounded exact-term proof.
(blueprint: lem-pc-single-degree-exact-term-hom-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homFunctor_additive
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (A : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ((SheafOfModules.homFunctor R).obj (op A)).Additive := by
  constructor
  intro X Y f g
  apply SheafOfModules.hom_ext
  ext U φ : 3
  rfl

private lemma fan_projection_isIso {D : Type*} [Category* D] [HasZeroMorphisms D]
    {Q : ℤ → D} {s : Fan Q} (hs : IsLimit s) (k : ℤ)
    (hz : ∀ p, p ≠ k → IsZero (Q p)) : IsIso (s.proj k) := by
  classical
  let v : Q k ⟶ s.pt := Fan.IsLimit.lift hs
    (fun p ↦ if h : p = k then eqToHom (congrArg Q h.symm) else 0)
  have hv : v ≫ s.proj k = 𝟙 (Q k) := by
    rw [Fan.IsLimit.fac]
    simp
  have hp : s.proj k ≫ v = 𝟙 s.pt := by
    apply Fan.IsLimit.hom_ext hs
    intro p
    by_cases h : p = k
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz p h).eq_of_tgt _ _
  exact (Iso.mk (s.proj k) v hp hv).isIso_hom

set_option backward.isDefEq.respectTransparency true in
/-- Internal Hom from a complex concentrated in one degree preserves quasi-isomorphisms
if internal Hom from its sole possibly nonzero term preserves short exact sequences.

Source: Stacks Project, Tag 0A8X, Hom complexes; Tag 08DM, bounded Hom calculation;
Tag 010N, exact functors.
(blueprint: lem-pc-single-degree-exact-term-hom-quasi-iso).

Proof: all factors of the degree-n Hom product other than the factor at k are zero:
internal Hom from a zero object is zero. The product universal property identifies
that degree with internal Hom from P.X k to M.X (k+n). The source differential is zero,
so the Hom differential is just postcomposition with the target differential. These
identifications commute with postcomposition by f. Internal Hom from P.X k is additive,
as follows sectionwise from addition of localized linear maps. Its short-exact-sequence
preservation implies finite-limit and finite-colimit preservation by the exact-functor
criterion (Tag 010N). The natural homology comparison for an exact functor identifies
homology of its degreewise image with its image of homology. Thus the map at every
homology degree is an isomorphism since f is a quasi-isomorphism. Translating the
integer grading by k preserves this assertion; no bound on M or N is needed.
The argument includes the case P.X k is zero and then all Hom terms are zero. -/
theorem quasiIso_homComplex_map_of_single_degree_exact_term
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hsingle : ∀ n : ℤ, n ≠ k → IsZero (P.X n))
    (hexact : ∀ (S : ShortComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.f ≫
          SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.f)
          (SheafOfModules.homObjMap (R := R) (𝟙 (P.X k)) S.g) hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor (R := R)).obj (op P)).map f) := by
  let F := (SheafOfModules.homFunctor R).obj (op (P.X k))
  have : F.Additive := homFunctor_additive J R (P.X k)
  have hF : ∀ S : ShortComplex _, S.ShortExact → (S.map F).ShortExact := by
    intro S hS
    obtain ⟨hz, h⟩ := hexact S hS
    exact h
  have : F.PreservesHomology := ((Functor.exact_tfae F).out 1 3).mp hF
  classical
  let H := (homComplexFunctor (R := R)).obj (op P)
  obtain ⟨π, hπ⟩ :=
    homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  have hi (T : CochainComplex _ ℤ) (n : ℤ) :
      IsIso (π P T n k (k + n) rfl) := by
    let Q := fun p : ℤ ↦ SheafOfModules.homObj (R := R) (P.X p) (T.X (p + n))
    have hc : IsLimit (Fan.mk ((H.obj T).X n)
        (fun p : ℤ ↦ π P T n p (p + n) rfl)) := Classical.choice (hπ.1 P T n)
    have hz (p : ℤ) (h : p ≠ k) : IsZero (Q p) := by
      let G := (SheafOfModules.homFunctor R).flip.obj (T.X (p + n))
      have : G.Additive := by
        constructor
        intro X Y a b
        change SheafOfModules.homObjMap (a + b).unop (𝟙 _) = _
        rw [unop_add]
        exact SheafOfModules.hom_ext
          (PresheafOfModules.homObjMap_add_left a.unop.val b.unop.val (𝟙 _))
      exact G.map_isZero (hsingle p h).op
    exact fan_projection_isIso hc k hz
  have hd (T : CochainComplex _ ℤ) (n m : ℤ) (h : n + 1 = m) :
      (H.obj T).d n m ≫ π P T m k (k + m) rfl =
        π P T n k (k + n) rfl ≫ F.map (T.d (k + n) (k + m)) := by
    have hzero : P.d k (k + m - n) = 0 :=
      (hsingle (k + m - n) (by omega)).eq_of_tgt _ _
    have h := hπ.2.1 P T n m k (k + m) (k + n) (k + m - n) h rfl rfl (by omega)
    rw [hzero] at h
    have hz : SheafOfModules.homObjMap (R := R)
        (0 : P.X k ⟶ P.X (k + m - n)) (𝟙 (T.X (k + m))) = 0 :=
      SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left (𝟙 _))
    rw [hz, comp_zero, smul_zero, sub_zero] at h
    exact h
  have hm {T U : CochainComplex _ ℤ} (g : T ⟶ U) (n : ℤ) :
      (H.map g).f n ≫ π P U n k (k + n) rfl =
        π P T n k (k + n) rfl ≫ F.map (g.f (k + n)) := by
    have h := hπ.2.2 P P T U (𝟙 P) g n k (k + n) rfl
    simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at h
    exact h
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let A := H ⋙ HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℤ)
    (n - 1) n (n + 1)
  let B := HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℤ)
    (k + (n - 1)) (k + n) (k + (n + 1)) ⋙ F.mapShortComplex
  let e (T : CochainComplex _ ℤ) : A.obj T ≅ B.obj T := by
    exact ShortComplex.isoMk (@asIso _ _ _ _ (π P T (n - 1) k (k + (n - 1)) rfl) (hi T (n - 1)))
      (@asIso _ _ _ _ (π P T n k (k + n) rfl) (hi T n))
      (@asIso _ _ _ _ (π P T (n + 1) k (k + (n + 1)) rfl) (hi T (n + 1)))
      (hd T (n - 1) n (by omega)).symm (hd T n (n + 1) (by omega)).symm
  have he : A.map f ≫ (e N).hom = (e M).hom ≫ B.map f := by
    apply ShortComplex.hom_ext
    · exact hm f (n - 1)
    · exact hm f n
    · exact hm f (n + 1)
  have hf : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor' _ (ComplexShape.up ℤ)
        (k + (n - 1)) (k + n) (k + (n + 1))).map f) :=
    (quasiIsoAt_iff' f (k + (n - 1)) (k + n) (k + (n + 1))
      (by simp; omega) (by simp; omega)).mp inferInstance
  have : ShortComplex.QuasiIso (B.map f) := by
    change ShortComplex.QuasiIso (F.mapShortComplex.map _)
    exact ShortComplex.quasiIso_map_of_preservesLeftHomology F _
  exact (ShortComplex.quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e M) (e N) he.symm)).mpr this

end CategoryTheory
