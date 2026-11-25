/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus

import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution

/-!
# Functorial injective resolutions preserving every lower bound

Source: Stacks Project, Derived Categories, Tag 0141, assertion (1) and its construction
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject ComplexShape
open HomologicalComplex₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
private theorem projection_iso (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    [K.HasTotal (up ℤ)] (y x n : ℤ) (hn : n ≤ x + y)
    [∀ p, CochainComplex.IsStrictlyGE (K.X p) y] :
    IsIso ((total.map (HomologicalComplex.πStupidTrunc K (embeddingUpIntLE x))
      (up ℤ)).f n) := by
  apply GradedObject.isIso_mapMap_apply
  rintro ⟨p, q⟩ (hpq : p + q = n)
  by_cases hp : p ≤ x
  · obtain ⟨j, hj⟩ : ∃ j, (embeddingUpIntLE x).f j = p := by
      obtain ⟨k, hk⟩ := Int.le.dest hp
      exact ⟨k, by change x - (k : ℤ) = p; omega⟩
    have := HomologicalComplex.isIso_πStupidTrunc_f K (embeddingUpIntLE x) hj
    change IsIso ((HomologicalComplex.eval _ _ q).map _)
    infer_instance
  · have hz : IsZero ((K.X p).X q) :=
      CochainComplex.isZero_of_isStrictlyGE (K.X p) y q (by omega)
    have hz' : IsZero (((K.stupidTrunc (embeddingUpIntLE x)).X p).X q) :=
      (HomologicalComplex.eval _ _ q).map_isZero
        (HomologicalComplex.isZero_stupidTrunc_X K (embeddingUpIntLE x) p
          (by intro j hj; change x - (j : ℤ) = p at hj; omega))
    exact ⟨0, hz.eq_of_src _ _, hz'.eq_of_src _ _⟩

private theorem projection_quasiIsoAt (K : HomologicalComplex₂ C (up ℤ) (up ℤ))
    [K.HasTotal (up ℤ)] (y x n : ℤ) (hn : n < x + y)
    [∀ p, CochainComplex.IsStrictlyGE (K.X p) y] :
    QuasiIsoAt (total.map (HomologicalComplex.πStupidTrunc K (embeddingUpIntLE x))
      (up ℤ)) n := by
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' C (up ℤ)
      (n - 1) n (n + 1)).map
        (total.map (HomologicalComplex.πStupidTrunc K (embeddingUpIntLE x)) (up ℤ))) := by
    rw [ShortComplex.isIso_iff]
    exact ⟨projection_iso K y x _ (by omega), projection_iso K y x _ (by omega),
      projection_iso K y x _ (by omega)⟩
  exact ShortComplex.quasiIso_of_isIso _

/-- Bounded below bicomplex comparison, by finite column truncation.
Only the supplied totals are needed; the category need not have countable coproducts. -/
private theorem boundedBelowComparison {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)}
    (f : K ⟶ L) [K.HasTotal (up ℤ)] [L.HasTotal (up ℤ)] (a b : ℤ)
    [CochainComplex.IsStrictlyGE K a] [CochainComplex.IsStrictlyGE L a]
    [∀ p, CochainComplex.IsStrictlyGE (K.X p) b]
    [∀ p, CochainComplex.IsStrictlyGE (L.X p) b]
    (hf : ∀ p, QuasiIso (f.f p)) : QuasiIso (total.map f (up ℤ)) := by
  rw [quasiIso_iff]
  intro n
  -- Truncation at x leaves the three terms computing degree-n homology unchanged.
  let x := n - b + 1
  let e := embeddingUpIntLE x
  have hfin : QuasiIso (total.map (HomologicalComplex.stupidTruncMap f e) (up ℤ)) := by
    apply total.quasiIso_map_of_finitely_many_columns _ a x
    intro p hp hpx
    obtain ⟨j, hj⟩ : ∃ j, e.f j = p := by
      obtain ⟨k, hk⟩ := Int.le.dest hpx
      exact ⟨k, by change x - (k : ℤ) = p; omega⟩
    have hK := HomologicalComplex.isIso_πStupidTrunc_f K e hj
    have hL := HomologicalComplex.isIso_πStupidTrunc_f L e hj
    have hnat := HomologicalComplex.πStupidTrunc_f_naturality f e p
    rw [← quasiIso_iff_comp_left ((HomologicalComplex.πStupidTrunc K e).f p),
      hnat, quasiIso_iff_comp_right]
    exact hf p
  have hK := projection_quasiIsoAt K b x n (by dsimp [x]; omega)
  have hL := projection_quasiIsoAt L b x n (by dsimp [x]; omega)
  rw [← quasiIsoAt_iff_comp_right _
    (total.map (HomologicalComplex.πStupidTrunc L e) (up ℤ)),
    ← total.map_comp, ← HomologicalComplex.πStupidTrunc_naturality, total.map_comp,
    quasiIsoAt_iff_comp_left]
  infer_instance

end HomologicalComplex₂

namespace CochainComplex
namespace FunctorialInjectiveTotal

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (E : C ⥤ CochainComplex C ℕ)
variable (ε : single₀ C ⟶ E)
variable [E.PreservesZeroMorphisms]

private noncomputable abbrev extension : C ⥤ CochainComplex C ℤ :=
  E ⋙ embeddingUpNat.extendFunctor C

set_option backward.isDefEq.respectTransparency false in
private noncomputable def singleExtensionIso :
    single₀ C ⋙ embeddingUpNat.extendFunctor C ≅
      HomologicalComplex.single C (up ℤ) 0 :=
  NatIso.ofComponents (fun A ↦ HomologicalComplex.extendSingleIso embeddingUpNat A 0 0 rfl)
    (by
      intro A B f
      apply HomologicalComplex.Hom.ext
      funext n
      by_cases hn : n = 0
      · subst n
        dsimp only [Functor.comp_map, HomologicalComplex.comp_f]
        change (HomologicalComplex.extendMap ((single₀ C).map f) embeddingUpNat).f 0 ≫ _ = _
        rw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := (0 : ℤ)) rfl]
        simp [HomologicalComplex.extendSingleIso_hom_f,
          HomologicalComplex.single_map_f_self]
      · apply IsZero.eq_of_tgt
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

private noncomputable def extendedAugmentation :
    HomologicalComplex.single C (up ℤ) 0 ⟶ extension E :=
  (singleExtensionIso (C := C)).inv ≫ Functor.whiskerRight ε (embeddingUpNat.extendFunctor C)

-- Outer degree is the original complex degree; inner degree is resolution degree.
private noncomputable def bicomplexFunctor :
    CochainComplex C ℤ ⥤ HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (extension E).mapHomologicalComplex (up ℤ)

private noncomputable def bicomplexAugmentation :
    singleRow C (up ℤ) (up ℤ) 0 ⟶ bicomplexFunctor E :=
  NatTrans.mapHomologicalComplex (extendedAugmentation E ε) (up ℤ)

omit [E.PreservesZeroMorphisms] in
private theorem extension_neg (A : C) (q : ℤ) (hq : q < 0) :
    IsZero ((extension E).obj A |>.X q) := by
  change IsZero (((E.obj A).extend embeddingUpNat).X q)
  exact isZero_of_isStrictlyGE _ 0 q hq

private theorem bicomplex_below (K : CochainComplex C ℤ) (a : ℤ)
    [K.IsStrictlyGE a] (p q : ℤ) (hp : p < a) :
    IsZero (((bicomplexFunctor E).obj K).X p |>.X q) := by
  exact (HomologicalComplex.eval _ _ q).map_isZero
    ((extension E).map_isZero (isZero_of_isStrictlyGE K a p hp))

private instance hasTotal (K : Plus C) :
    ((bicomplexFunctor E).obj K.obj).HasTotal (up ℤ) := by
  obtain ⟨a, ha⟩ := K.property
  exact hasTotal_of_boundedBelow _ a (bicomplex_below E K.obj a)
    (fun p q hq ↦ extension_neg E (K.obj.X p) q hq)

private theorem total_below (K : Plus C) (a : ℤ) [K.obj.IsStrictlyGE a] :
    IsStrictlyGE (((bicomplexFunctor E).obj K.obj).total (up ℤ)) a := by
  rw [isStrictlyGE_iff]
  intro n hn
  rw [IsZero.iff_id_eq_zero]
  apply total.hom_ext
  intro p q hpq
  by_cases hq : q < 0
  · exact (extension_neg E (K.obj.X p) q hq).eq_of_src _ _
  · exact (bicomplex_below E K.obj a p q (by change p + q = n at hpq; omega)).eq_of_src _ _

private noncomputable def replacement : Plus C ⥤ Plus C where
  obj K := ⟨((bicomplexFunctor E).obj K.obj).total (up ℤ), by
    obtain ⟨a, ha⟩ := K.property
    exact ⟨a, total_below E K a⟩⟩
  map f := ObjectProperty.homMk (total.map ((bicomplexFunctor E).map f.hom) (up ℤ))
  map_id K := by
    ext : 1
    simp
  map_comp f g := by
    ext : 1
    simp

private noncomputable def augmentation : Plus.ι C ⟶ replacement E ⋙ Plus.ι C where
  app K := (singleRow₀ObjTotal K.obj).inv ≫
    total.map ((bicomplexAugmentation E ε).app K.obj) (up ℤ)
  naturality {K L} f := by
    have h := (bicomplexAugmentation E ε).naturality f.hom
    dsimp [replacement]
    have hi : f.hom ≫ (singleRow₀ObjTotal L.obj).inv =
        (singleRow₀ObjTotal K.obj).inv ≫ total.map
          ((singleRow C (up ℤ) (up ℤ) 0).map f.hom) (up ℤ) := by
      rw [← cancel_mono (singleRow₀ObjTotal L.obj).hom]
      simp [Category.assoc, singleRow₀ObjTotal_hom_naturality]
    change f.hom ≫ _ ≫ _ = (_ ≫ _) ≫ _
    rw [← Category.assoc, hi, Category.assoc, ← total.map_comp, h, total.map_comp]
    simp only [Category.assoc]

private theorem injective_total (K : Plus C)
    (hE : ∀ (A : C) (q : ℕ), Injective ((E.obj A).X q)) (n : ℤ) :
    Injective (((replacement E).obj K).obj.X n) := by
  classical
  obtain ⟨a, ha⟩ := K.property
  let B := (bicomplexFunctor E).obj K.obj
  let κ : B.CoreHasTotal (up ℤ) n :=
    { J := ↥(Finset.Icc a n)
      φ₁ := fun p ↦ p.val
      φ₂ := fun p ↦ n - p.val
      π_φ := fun p ↦ by change p.val + (n - p.val) = n; omega
      hφ := by intro p p' h; exact Subtype.ext (congrArg Prod.fst h)
      isZero := by
        intro p q hpq hz
        have hp : a ≤ p := by
          by_contra hp
          exact hz (bicomplex_below E K.obj a p q (by omega))
        have hq : 0 ≤ q := by
          by_contra hq
          exact hz (extension_neg E (K.obj.X p) q (by omega))
        change p + q = n at hpq
        exact ⟨⟨p, Finset.mem_Icc.mpr ⟨hp, by omega⟩⟩, rfl, by dsimp; omega⟩ }
  let Y := fun p : κ.J ↦ (B.X (κ.φ₁ p)).X (κ.φ₂ p)
  have hY : ∀ p, Injective (Y p) := by
    intro p
    have : ∀ q : ℕ, Injective ((E.obj (K.obj.X (κ.φ₁ p))).X q) :=
      hE (K.obj.X (κ.φ₁ p))
    exact inferInstanceAs (Injective
      (((E.obj (K.obj.X (κ.φ₁ p))).extend embeddingUpNat).X (κ.φ₂ p)))
  have : ∀ p, Injective (Y p) := hY
  have : Finite κ.J := by dsimp [κ]; infer_instance
  have : HasFiniteBiproducts C := Abelian.hasFiniteBiproducts
  have hi : Injective (∐ Y) := Injective.of_iso (biproduct.isoCoproduct Y) inferInstance
  let e := IsColimit.coconePointUniqueUpToIso κ.isColimit
    (coproductIsCoproduct (B.toGradedObject.mapObjFun (π (up ℤ) (up ℤ) (up ℤ)) n))
  exact Injective.of_iso e hi

private theorem augmentation_quasiIso (hε : ∀ A, QuasiIso (ε.app A)) (K : Plus C) :
    QuasiIso ((augmentation E ε).app K) := by
  have h := hε
  have hc (A : C) : QuasiIso ((extendedAugmentation E ε).app A) := by
    dsimp [extendedAugmentation]
    change QuasiIso (_ ≫ HomologicalComplex.extendMap (ε.app A) embeddingUpNat)
    infer_instance
  have hcol (p : ℤ) : QuasiIso (((bicomplexAugmentation E ε).app K.obj).f p) :=
    hc (K.obj.X p)
  have hq (p : ℤ) : IsStrictlyGE (((bicomplexFunctor E).obj K.obj).X p) 0 := by
    change IsStrictlyGE ((E.obj (K.obj.X p)).extend embeddingUpNat) 0
    infer_instance
  have hs (p : ℤ) : IsStrictlyGE
      (((singleRow C (up ℤ) (up ℤ) 0).obj K.obj).X p) 0 := by
    change IsStrictlyGE ((HomologicalComplex.single C (up ℤ) 0).obj (K.obj.X p)) 0
    infer_instance
  obtain ⟨a, ha⟩ := K.property
  have hB : IsStrictlyGE ((bicomplexFunctor E).obj K.obj) a := by
    change IsStrictlyGE (((extension E).mapHomologicalComplex (up ℤ)).obj K.obj) a
    infer_instance
  have hS : IsStrictlyGE ((singleRow C (up ℤ) (up ℤ) 0).obj K.obj) a := by
    change IsStrictlyGE (((HomologicalComplex.single C (up ℤ) 0).mapHomologicalComplex
      (up ℤ)).obj K.obj) a
    infer_instance
  have ht := boundedBelowComparison ((bicomplexAugmentation E ε).app K.obj) a 0 hcol
  dsimp [augmentation]
  infer_instance

end FunctorialInjectiveTotal

/-- Totalize a supplied functorial objectwise injective resolution.

Source: Stacks Project, Derived Categories, Tag 0141, assertion (1) and its construction.
(auxiliary; not a blueprint node).

Apply the supplied nonnegative augmented resolutions termwise to an integer-indexed
bounded-below complex, form the first-quadrant bicomplex, and take finite diagonal
biproducts with the signed total differential.  The first-quadrant column augmentation
criterion proves the augmentation is a quasi-isomorphism after choosing a lower bound only
for verification.  Finite biproducts of injectives give injective total terms, and the
vanishing of all columns below the chosen bound gives preservation of every lower bound.
-/
theorem exists_functorial_bounded_injective_resolution_of_object_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (E : C ⥤ CochainComplex C ℕ)
    (ε : (CochainComplex.single₀ C) ⟶ E)
    (hε : ∀ A : C, QuasiIso (ε.app A))
    (hEzero : ∀ (A B : C), E.map (0 : A ⟶ B) = 0)
    (hEobjzero : IsZero (E.obj (0 : C)))
    (hE : ∀ (A : C) (n : ℕ), Injective ((E.obj A).X n)) :
    ∃ (I : Plus C ⥤ Plus C) (α : Plus.ι C ⟶ I ⋙ Plus.ι C),
      (∀ K : Plus C, QuasiIso (α.app K)) ∧
      (∀ (K : Plus C) (n : ℤ), Injective (((I.obj K).obj).X n)) ∧
      (∀ (K : Plus C) (a : ℤ), K.obj.IsStrictlyGE a →
        (I.obj K).obj.IsStrictlyGE a) := by
  have _ := hEobjzero
  let : E.PreservesZeroMorphisms := ⟨hEzero⟩
  refine ⟨FunctorialInjectiveTotal.replacement E, FunctorialInjectiveTotal.augmentation E ε,
    FunctorialInjectiveTotal.augmentation_quasiIso E ε hε,
    (fun K ↦ FunctorialInjectiveTotal.injective_total E K hE), ?_⟩
  intro K a ha
  exact FunctorialInjectiveTotal.total_below E K a

/-- A functorial injective embedding gives one injective replacement functor on all
bounded-below complexes, preserving every termwise lower bound simultaneously.
Source: Stacks Project, `derived.tex`, Tag 0141, assertion (1) and its construction
(auxiliary; not a blueprint node).

Proof:
1. Normalize J by replacing J(A) with the kernel of J(A) → J(0). The maps induced by
   A → 0 → A split off J(0); the complementary projection retracts J(A) onto this
   kernel. Naturality factors the given monomorphism through that kernel. Kernel
   uniqueness defines the normalized functor and its natural monomorphic embedding.
2. A retract of an injective is injective: extend after inclusion into J(A), then
   project back. The normalized functor sends zero objects and zero morphisms to zero.
3. Fix kernels and cokernels. Starting with Q₀ = id, set E_q = J₀ Q_q and let Q_{q+1}
   be the cokernel of Q_q → E_q. Cokernel uniqueness defines maps functorially.
   Inductively these functors preserve zero objects and zero morphisms. The quotient
   followed by the next embedding gives natural differentials E_q → E_{q+1}.
4. Each augmented column 0 → A → E₀(A) → E₁(A) → ⋯ is exact: the embeddings are
   monic, the quotient maps epic, and their kernel-image identities give exactness.
   Every E_q(A) is injective (`def-sp-injective-resolutions`).
5. Form D_K^{q,p} = E_q(K.X p) for q ≥ 0, and zero for q < 0. Its differentials
   commute by naturality, square to zero, and give a bicomplex functorial in K.
   The column augmentations give a natural augmentation. Every lower bound a of K
   also bounds its p-index, because the E_q preserve zero objects.
6. Totalize with differential v + (-1)^q E_q(d_K), using
   `def-sp-double-complex-total`. Each diagonal has only finitely many nonzero terms
   for bounded-below K, so finite biproducts supply a coproduct of its entire diagonal.
   Choose these coproducts independently of any bound. Their universal properties
   define the maps on morphisms, respecting identities and composition. The mixed
   terms in the squared differential cancel. Naturality of v and functoriality of
   E_q prove the chain-map equation on each coprojection. The (0,n) inclusions after
   the embeddings give a chain map K → I(K), natural by the same equations.
7. For verification only, choose a bound a and reindex p = a+r. Apply
   `lem-sc-first-quadrant-column-augmentation` to the first-quadrant bicomplex:
   its augmented columns are resolutions by step 4. The diagonal bijection identifies
   its total with I(K) in degrees a+m, respecting signs and augmentation. This proves
   quasi-isomorphism above a; below a both complexes and their cohomology are zero.
8. Each total term is a finite biproduct of injectives, hence injective by extending
   each component along a monomorphism. The empty biproduct is zero and injective.
   No diagonal in degree n < a has q ≥ 0 and p ≥ a, so I(K) vanishes there.
   The construction preceded the choice of a and is natural for every chain map.
   Postcomposition therefore resolves any diagram, even without a common bound. -/
theorem exists_functorial_bounded_injective_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (J : C ⥤ C) (η : 𝟭 C ⟶ J)
    (hη : ∀ A : C, Mono (η.app A)) (hJ : ∀ A : C, Injective (J.obj A)) :
    ∃ (I : Plus C ⥤ Plus C) (α : Plus.ι C ⟶ I ⋙ Plus.ι C),
      (∀ K : Plus C, QuasiIso (α.app K)) ∧
      (∀ (K : Plus C) (n : ℤ), Injective (((I.obj K).obj).X n)) ∧
      (∀ (K : Plus C) (a : ℤ), K.obj.IsStrictlyGE a → (I.obj K).obj.IsStrictlyGE a) := by
  obtain ⟨E, ε, hε, hEzero, hEobjzero, hE⟩ :=
    exists_functorial_object_injective_resolution J η hη hJ
  exact exists_functorial_bounded_injective_resolution_of_object_resolution E ε hε hEzero
    hEobjzero hE

end CochainComplex
