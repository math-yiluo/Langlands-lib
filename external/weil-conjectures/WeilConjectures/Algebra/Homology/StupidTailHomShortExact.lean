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
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Short exact Hom sequences for a stupid source tail

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private lemma homMap_zero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A A' B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : A' ⟶ A) (𝟙 B) = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = 0
  ext W x
  change ((𝟙 B : B ⟶ B).val.app _).hom ((φ.app W).hom 0) = 0
  rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency true in
private lemma homComplex_preservesZero {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ((homComplexFunctor (R := R)).flip.obj M).PreservesZeroMorphisms := by
  classical
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  constructor
  intro L L'
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (Classical.choice (hlim L'.unop M n))
  intro p
  change (((homComplexFunctor (R := R)).map (0 : L ⟶ L')).app M).f n ≫
    π L'.unop M n p (p + n) rfl = _
  have hm := hmap L.unop L'.unop M M (0 : L'.unop ⟶ L.unop) (𝟙 M)
    n p (p + n) rfl
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.zero_f,
    HomologicalComplex.id_f, op_zero,
    homMap_zero, comp_zero, zero_comp] using hm

private lemma homMap_add {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    {A A' B : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f g : A' ⟶ A) :
    SheafOfModules.homObjMap (R := R) (f + g) (𝟙 B) =
      SheafOfModules.homObjMap (R := R) f (𝟙 B) + SheafOfModules.homObjMap (R := R) g (𝟙 B) := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (f.val + g.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = _
  ext W x
  change ((φ.app W).hom) (((f.val.app _).hom) x + ((g.val.app _).hom) x) =
    ((φ.app W).hom) ((f.val.app _).hom x) + ((φ.app W).hom) ((g.val.app _).hom x)
  exact map_add _ _ _

-- Construct the product splitting in an abstract category so that its identities do not
-- repeatedly elaborate the internal Hom objects and the chosen Hom-complex functor.
private noncomputable def stupidTailFanSplitting
    {D : Type*} [Category* D] [Preadditive D] {I : Type*}
    (S : ShortComplex D) (T : I → ShortComplex D)
    (p₁ : ∀ i, S.X₁ ⟶ (T i).X₁) (p₂ : ∀ i, S.X₂ ⟶ (T i).X₂)
    (p₃ : ∀ i, S.X₃ ⟶ (T i).X₃)
    (h₁ : IsLimit (Fan.mk _ p₁)) (h₂ : IsLimit (Fan.mk _ p₂))
    (h₃ : IsLimit (Fan.mk _ p₃)) (σ : ∀ i, (T i).Splitting)
    (hf : ∀ i, S.f ≫ p₂ i = p₁ i ≫ (T i).f)
    (hg : ∀ i, S.g ≫ p₃ i = p₂ i ≫ (T i).g) : S.Splitting := by
  let r : S.X₂ ⟶ S.X₁ := Fan.IsLimit.lift h₁ (fun i ↦ p₂ i ≫ (σ i).r)
  let s : S.X₃ ⟶ S.X₂ := Fan.IsLimit.lift h₂ (fun i ↦ p₃ i ≫ (σ i).s)
  have hr (i) : r ≫ p₁ i = p₂ i ≫ (σ i).r := Fan.IsLimit.fac _ _ _
  have hs (i) : s ≫ p₂ i = p₃ i ≫ (σ i).s := Fan.IsLimit.fac _ _ _
  refine { r := r, s := s, f_r := ?_, s_g := ?_, id := ?_ }
  · apply Fan.IsLimit.hom_ext h₁
    intro i
    change (S.f ≫ r) ≫ p₁ i = (𝟙 _) ≫ p₁ i
    rw [Category.assoc, hr, ← Category.assoc, hf, Category.assoc,
      (σ i).f_r, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext h₃
    intro i
    change (s ≫ S.g) ≫ p₃ i = (𝟙 _) ≫ p₃ i
    rw [Category.assoc, hg, ← Category.assoc, hs, Category.assoc,
      (σ i).s_g, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext h₂
    intro i
    change (r ≫ S.f + S.g ≫ s) ≫ p₂ i = (𝟙 _) ≫ p₂ i
    calc
      (r ≫ S.f + S.g ≫ s) ≫ p₂ i =
          (r ≫ p₁ i) ≫ (T i).f + (S.g ≫ p₃ i) ≫ (σ i).s := by
        simp only [Preadditive.add_comp, Category.assoc, hf, hs]
      _ = p₂ i ≫ ((σ i).r ≫ (T i).f + (T i).g ≫ (σ i).s) := by
        rw [hr, hg]
        simp only [Category.assoc, Preadditive.comp_add]
      _ = (𝟙 _) ≫ p₂ i := by rw [(σ i).id, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
private lemma homComplex_degreewise_split {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C} {R : Sheaf J CommRingCat.{u}}
    (S : ShortComplex (CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ))
    (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    (M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    [((homComplexFunctor (R := R)).flip.obj M).PreservesZeroMorphisms] :
    (S.op.map ((homComplexFunctor (R := R)).flip.obj M)).ShortExact := by
  classical
  let F := homComplexFunctor (R := R)
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R)
  have hm {L L' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
      (f : L' ⟶ L) (n p : ℤ) :
      ((F.map f.op).app M).f n ≫ π L' M n p (p + n) rfl =
        π L M n p (p + n) rfl ≫ SheafOfModules.homObjMap (R := R) (f.f p) (𝟙 _) := by
    simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
      hmap L L' M M f (𝟙 M) n p (p + n) rfl
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let G (p : ℤ) := (SheafOfModules.homFunctor R).flip.obj (M.X (p + n))
  have hG (p : ℤ) : (G p).Additive := by
    constructor
    intro X Y a b
    change SheafOfModules.homObjMap (R := R) (a + b).unop (𝟙 _) = _
    rw [unop_add]
    exact homMap_add a.unop b.unop
  let T (p : ℤ) := (S.map (HomologicalComplex.eval _ (.up ℤ) p)).op.map (G p)
  have hT (p : ℤ) : (T p).Splitting := (σ p).op.map (G p)
  exact (stupidTailFanSplitting _ T
    (fun p ↦ π S.X₃ M n p (p + n) rfl)
    (fun p ↦ π S.X₂ M n p (p + n) rfl)
    (fun p ↦ π S.X₁ M n p (p + n) rfl)
    (Classical.choice (hlim S.X₃ M n)) (Classical.choice (hlim S.X₂ M n))
    (Classical.choice (hlim S.X₁ M n)) hT
    (fun p ↦ hm S.g n p) (fun p ↦ hm S.f n p)).shortExact

/-- The Hom maps for the bottom source term, the entire source, and its next stupid
tail occur as the three components of a morphism of short exact sequences.
The arrow isomorphisms include the identifications of each Hom complex and its map,
so the statement supplies naturality in the second variable as well as exactness.

Source: Stacks Project, Tag 0A8X, product Hom differential;
Tag 0117, natural long exact cohomology sequence.
(blueprint: lem-pc-stupid-tail-hom-short-exact).

Proof: let T be the stupid tail of P in degrees at least k+1 and let G be P.X k
placed in degree k. Since P vanishes below k, inclusion of T and projection to G
give a degreewise split short exact sequence 0 to T to P to G to 0. Applying
internal Hom into M gives 0 to Hom(G,M) to Hom(P,M) to Hom(T,M) to 0.
Construct the maps by extending a family at k by zero and restricting a family
to degrees at least k+1. The formula d_M h - (-1)^n h d_P proves both are chain
maps: for the extension map, its source-composition term vanishes because the
only possible incoming source differential is from the zero term P.X (k-1);
restriction is compatible because the differential at a source degree p only
uses p and p+1. In each Hom degree, splitting the product index set into the
singleton k, the tail, and the zero terms below k makes this sequence split.
Use the same maps for N. Postcomposition by f commutes with extension and
restriction componentwise, giving a morphism of these short exact sequences.
Take S and T to be these two short exact Hom sequences and φ to have
these three postcomposition maps as its components. The product identifications
with the named Hom complexes give the required arrow isomorphisms.
The product splitting uses no exactness of an infinite product; it is a
splitting of an existing product into two factors, valid for unbounded P, M, N. -/
theorem exists_homComplex_stupid_tail_shortExact
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : M ⟶ N) : ∃ S T : ShortComplex (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ),
      ∃ φ : S ⟶ T, S.ShortExact ∧ T.ShortExact ∧
        Nonempty (Arrow.mk φ.τ₁ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
            (P.X k)))).map f)) ∧
        Nonempty (Arrow.mk φ.τ₂ ≅ Arrow.mk
          (((homComplexFunctor (R := R)).obj (op P)).map f)) ∧
        Nonempty (Arrow.mk φ.τ₃ ≅ Arrow.mk (((homComplexFunctor (R := R)).obj
          (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) := by
  classical
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
  let e := ComplexShape.embeddingUpIntGE (k + 1)
  let G := (HomologicalComplex.single A (ComplexShape.up ℤ) k).obj (P.X k)
  let i := P.ιStupidTrunc e
  have hd : ∀ n : ℤ, (ComplexShape.up ℤ).Rel n k → P.d n k ≫ 𝟙 (P.X k) = 0 := by
    intro n hn
    exact (hbelow n (by simp only [ComplexShape.up_Rel] at hn; omega)).eq_of_src _ _
  let q : P ⟶ G := HomologicalComplex.mkHomToSingle (𝟙 (P.X k)) hd
  have hiq : i ≫ q = 0 := by
    apply HomologicalComplex.to_single_hom_ext
    apply IsZero.eq_of_src
    apply P.isZero_stupidTrunc_X e
    intro n
    simp only [e, ComplexShape.embeddingUpIntGE_f]
    omega
  let S₀ := ShortComplex.mk i q hiq
  have σ : ∀ n : ℤ, (S₀.map (HomologicalComplex.eval A (ComplexShape.up ℤ) n)).Splitting := by
    intro n
    by_cases hn : n = k
    · subst n
      apply ShortComplex.Splitting.ofIsZeroOfIsIso
      · apply P.isZero_stupidTrunc_X e
        intro n
        simp only [e, ComplexShape.embeddingUpIntGE_f]
        omega
      · change IsIso (q.f k)
        dsimp [q]
        rw [HomologicalComplex.mkHomToSingle_f]
        simp only [Category.id_comp]
        infer_instance
    · apply ShortComplex.Splitting.ofIsIsoOfIsZero
      · change IsIso (i.f n)
        by_cases hkn : k + 1 ≤ n
        · obtain ⟨m, hm⟩ := Int.le.dest hkn
          exact P.isIso_ιStupidTrunc_f e (i := m) (by
            simp only [e, ComplexShape.embeddingUpIntGE_f]
            omega)
        · have hP := hbelow n (by omega)
          have hU : IsZero ((P.stupidTrunc e).X n) := by
            apply P.isZero_stupidTrunc_X e
            intro m
            simp only [e, ComplexShape.embeddingUpIntGE_f]
            omega
          exact ⟨⟨0, hU.eq_of_src _ _, hP.eq_of_src _ _⟩⟩
      · exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) k (P.X k) n hn
  let F := homComplexFunctor (R := R)
  let : (F.flip.obj M).PreservesZeroMorphisms := homComplex_preservesZero M
  let : (F.flip.obj N).PreservesZeroMorphisms := homComplex_preservesZero N
  let S := S₀.op.map (F.flip.obj M)
  let T := S₀.op.map (F.flip.obj N)
  let φ : S ⟶ T := S₀.op.mapNatTrans (F.flip.map f)
  refine ⟨S, T, φ, ?_, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  · exact homComplex_degreewise_split S₀ σ M
  · exact homComplex_degreewise_split S₀ σ N

end CategoryTheory
