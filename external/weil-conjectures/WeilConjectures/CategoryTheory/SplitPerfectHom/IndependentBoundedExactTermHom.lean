/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.Single
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Bounded exact-term Hom with independent site universes

Source: Stacks Project, Tags 08DM, 0A8X and 0117.
(blueprint: lem-sfb-independent-bounded-exact-term-hom).
This extends the existing bounded exact-term proof without equating the site,
coefficient and morphism universes. All auxiliary proofs are private.
-/

@[expose] public section

set_option autoImplicit false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SplitPerfectHom

private lemma single_homFunctor_additive
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (A : SheafOfModules.{max c v r} ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max
      c v r})).obj R)) :
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op A)).Additive := by
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
-- The dependent product projections need extra elaboration steps.
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
private theorem quasiIso_homComplex_map_of_single_degree_exact_term
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (k : ℤ) (hsingle : ∀ n : ℤ, n ≠ k → IsZero (P.X n))
    (hexact : ∀ (S : ShortComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
        k)) S.f ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X k)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
          k)) S.f)
          (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X k)) S.g)
            hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f) := by
  let F := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).obj (op (P.X k))
  have : F.Additive := single_homFunctor_additive.{c, v, r} J R (P.X k)
  have hF : ∀ S : ShortComplex _, S.ShortExact → (S.map F).ShortExact := by
    intro S hS
    obtain ⟨hz, h⟩ := hexact S hS
    exact h
  have : F.PreservesHomology := ((Functor.exact_tfae F).out 1 3).mp hF
  classical
  let H := (homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)
  let π := Classical.choose
    (homComplex_projections_exists.{c, v, max c v r, max c v r} (C := C) (J := J) (R := R))
  have hπ := Classical.choose_spec
    (homComplex_projections_exists.{c, v, max c v r, max c v r} (C := C) (J := J) (R := R))
  have hi (T : CochainComplex _ ℤ) (n : ℤ) :
      IsIso (π P T n k (k + n) rfl) := by
    let Q := fun p : ℤ ↦ SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) (P.X p) (T.X
      (p + n))
    have hc : IsLimit (Fan.mk ((H.obj T).X n)
        (fun p : ℤ ↦ π P T n p (p + n) rfl)) := Classical.choice (hπ.1 P T n)
    have hz (p : ℤ) (h : p ≠ k) : IsZero (Q p) := by
      let G := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj (T.X (p + n))
      have : G.Additive := by
        constructor
        intro X Y a b
        change SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (a + b).unop (𝟙 _) = _
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
    have hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
        (P.d k (k + m - n)) (𝟙 (T.X (k + m))) = 0 :=
      (congrArg (fun x ↦ SheafOfModules.homObjMap.{max c v r, v, c, max c v r}
        (R := R) x (𝟙 (T.X (k + m)))) hzero).trans
        (SheafOfModules.hom_ext (PresheafOfModules.homObjMap_zero_left (𝟙 _)))
    exact h.trans (by simp only [hz, comp_zero, smul_zero, sub_zero]; rfl)
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

private lemma tail_homMap_zero {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)} :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (0 : A' ⟶ A) (𝟙 B) = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 B : B ⟶ B).val = 0
  ext W x
  change ((𝟙 B : B ⟶ B).val.app _).hom ((φ.app W).hom 0) = 0
  rw [map_zero, map_zero]

set_option backward.isDefEq.respectTransparency true in
private lemma homComplex_preservesZero {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    (M : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ) :
    ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).flip.obj M).PreservesZeroMorphisms
      := by
  classical
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{c, v, max c v r, max c v r} (C := C) (J := J) (R := R)
  constructor
  intro L L'
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (Classical.choice (hlim L'.unop M n))
  intro p
  change (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).map (0 : L ⟶ L')).app M).f n ≫
    π L'.unop M n p (p + n) rfl = _
  have hm := hmap L.unop L'.unop M M (0 : L'.unop ⟶ L.unop) (𝟙 M)
    n p (p + n) rfl
  simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.zero_f,
    HomologicalComplex.id_f, op_zero,
    tail_homMap_zero.{c, v, r}, comp_zero, zero_comp] using hm

private noncomputable def fanSplitting
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
-- The product projections are elaborated through their recorded universal properties.
private lemma homComplex_degreewise_split {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    (S : ShortComplex (CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ))
    (σ : ∀ n : ℤ, (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    (M : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    [((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).flip.obj
      M).PreservesZeroMorphisms] :
    (S.op.map ((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).flip.obj M)).ShortExact
      := by
  classical
  let F := homComplexFunctor.{c, v, max c v r, max c v r} (R := R)
  obtain ⟨π, hlim, _, hmap⟩ :=
    homComplex_projections_exists.{c, v, max c v r, max c v r} (C := C) (J := J) (R := R)
  have hm {L L' : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
      (f : L' ⟶ L) (n p : ℤ) :
      ((F.map f.op).app M).f n ≫ π L' M n p (p + n) rfl =
        π L M n p (p + n) rfl ≫ SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R)
          (f.f p) (𝟙 _) := by
    simpa only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] using
      hmap L L' M M f (𝟙 M) n p (p + n) rfl
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let G (p : ℤ) := (SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj
    (M.X (p + n))
  have hG (p : ℤ) : (G p).Additive := by
    constructor
    intro X Y a b
    change SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (a + b).unop (𝟙 _) = _
    rw [unop_add]
    exact SheafOfModules.hom_ext
      (PresheafOfModules.homObjMap_add_left a.unop.val b.unop.val (𝟙 _))
  let T (p : ℤ) := (S.map (HomologicalComplex.eval _ (.up ℤ) p)).op.map (G p)
  have hT (p : ℤ) : (T p).Splitting := (σ p).op.map (G p)
  exact (fanSplitting _ T
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
private theorem exists_homComplex_stupid_tail_shortExact
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : M ⟶ N) : ∃ S T : ShortComplex (CochainComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ),
      ∃ φ : S ⟶ T, S.ShortExact ∧ T.ShortExact ∧
        Nonempty (Arrow.mk φ.τ₁ ≅ Arrow.mk (((homComplexFunctor.{c, v, max c v r, max c v r} (R :=
          R)).obj
          (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj
            (P.X k)))).map f)) ∧
        Nonempty (Arrow.mk φ.τ₂ ≅ Arrow.mk
          (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f)) ∧
        Nonempty (Arrow.mk φ.τ₃ ≅ Arrow.mk (((homComplexFunctor.{c, v, max c v r, max c v r} (R :=
          R)).obj
          (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) := by
  classical
  let A := SheafOfModules.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
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
  let F := homComplexFunctor.{c, v, max c v r, max c v r} (R := R)
  let : (F.flip.obj M).PreservesZeroMorphisms := homComplex_preservesZero.{c, v, r} M
  let : (F.flip.obj N).PreservesZeroMorphisms := homComplex_preservesZero.{c, v, r} N
  let S := S₀.op.map (F.flip.obj M)
  let T := S₀.op.map (F.flip.obj N)
  let φ : S ⟶ T := S₀.op.mapNatTrans (F.flip.map f)
  refine ⟨S, T, φ, ?_, ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  · exact homComplex_degreewise_split.{c, v, r} S₀ σ M
  · exact homComplex_degreewise_split.{c, v, r} S₀ σ N

private lemma homObjMap_zero_source
    {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    {A A' B B' : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)} (g : B ⟶ B') :
    SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (0 : A' ⟶ A) g = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map 0 ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map g.val = 0
  ext W x
  change ((g.val.app _).hom) ((φ.app W).hom (0)) = 0
  rw [map_zero, map_zero]

private lemma homObj_isZero_source
    {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    {A : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (hA : IsZero A) (B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    IsZero (SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) A B) := by
  rw [IsZero.iff_id_eq_zero, ← SheafOfModules.homObjMap_id (R := R) (M := A) (N := B)]
  rw [hA.eq_of_src (𝟙 A) 0, homObjMap_zero_source.{c, v, r}]

private lemma exact_homObj_of_isZero
    {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    {A : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (hA : IsZero A)
    (S : ShortComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) :
    ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.g) hz).ShortExact
          := by
  have h₁ := homObj_isZero_source.{c, v, r} hA S.X₁
  have h₂ := homObj_isZero_source.{c, v, r} hA S.X₂
  have h₃ := homObj_isZero_source.{c, v, r} hA S.X₃
  refine ⟨h₁.eq_of_src _ _, ?_⟩
  exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
          mono_f := h₁.mono _
          epi_g := h₃.epi _ }

set_option backward.isDefEq.respectTransparency false in
private lemma exact_homObj_of_iso
    {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}] {R : Sheaf J CommRingCat.{max c v r}}
    {A B : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)}
    (e : A ≅ B)
    (S : ShortComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)))
    (hB : ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 B) S.f ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 B) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 B) S.f)
        (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 B) S.g) hz).ShortExact) :
    ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.f ≫
        SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.g = 0,
      (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.f)
        (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.g) hz).ShortExact
          := by
  obtain ⟨hz, hS⟩ := hB
  have hzA : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.f ≫
      SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 A) S.g = 0 := by
    simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
    rw [S.zero]
    apply SheafOfModules.hom_ext
    ext X φ : 3
    change (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 A : A ⟶ A).val ≫ φ ≫
      (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
    ext W x
    rfl
  refine ⟨hzA, ShortComplex.shortExact_of_iso ?_ hS⟩
  let i (D : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
      SheafOfModules.homObj.{max c v r, v, c, max c v r} (R := R) B D ≅ SheafOfModules.homObj.{max
        c v r, v, c, max c v r} (R := R) A D :=
    ((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).flip.obj D).mapIso e.op
  exact ShortComplex.isoMk (i S.X₁) (i S.X₂) (i S.X₃)
    (((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).map e.op.hom).naturality
      S.f).symm
    (((SheafOfModules.homFunctor.{max c v r, v, c, max c v r} R).map e.op.hom).naturality
      S.g).symm

private lemma quasiIso_homComplex_map_of_stupid_tail
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (k : ℤ) (hbelow : ∀ n : ℤ, n < k → IsZero (P.X n))
    {M N : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : M ⟶ N)
    (hsingle : QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj
      (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj (P.X k)))).map f))
    (htail : QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj
      (op (P.stupidTrunc (ComplexShape.embeddingUpIntGE (k + 1))))).map f)) :
    QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f) := by
  obtain ⟨S, T, φ, hS, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_homComplex_stupid_tail_shortExact.{c, v, r} J R P k hbelow f
  have h₁ : QuasiIso φ.τ₁ :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e₁).2 hsingle
  have h₃ : QuasiIso φ.τ₃ :=
    (quasiIso_iff_of_arrow_mk_iso _ _ e₃).2 htail
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e₂).1
    (HomologicalComplex.HomologySequence.quasiIso_τ₂ φ hS hT h₁ h₃)

private lemma quasiIso_homComplex_map_of_interval
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (a : ℤ) (d : ℕ)
    (hbounded : ∀ n : ℤ, n < a ∨ a + (d : ℤ) < n → IsZero (P.X n))
    (hexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
        n)) S.f ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
          n)) S.f)
          (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X n)) S.g)
            hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f)  := by
  induction d generalizing P a with
  | zero =>
    apply quasiIso_homComplex_map_of_single_degree_exact_term.{c, v, r} J R P a
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
    have hTexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))),
        S.ShortExact → ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙
          (T.X n)) S.f ≫
            SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (T.X n)) S.g = 0,
          (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (T.X
            n)) S.f)
            (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (T.X n)) S.g)
              hz).ShortExact := by
      intro n S hS
      by_cases hlow : n < a + 1
      · exact exact_homObj_of_isZero.{c, v, r}
          (P.isZero_stupidTrunc_X _ n
            ((ComplexShape.notMem_range_embeddingUpIntGE_iff (a + 1) n).2 hlow)) S
      · obtain ⟨i, hi⟩ := Int.le.dest (show a + 1 ≤ n by omega)
        have heq : (ComplexShape.embeddingUpIntGE (a + 1)).f i = n := by
          simpa using hi
        exact exact_homObj_of_iso.{c, v, r} (P.stupidTruncXIso _ heq) S (hexact n S hS)
    have htail : QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op
      T)).map f) :=
      ih T (a + 1) hTbound hTexact
    have hsingle : QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj
        (op ((HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj (P.X a)))).map f) := by
      apply quasiIso_homComplex_map_of_single_degree_exact_term.{c, v, r} J R _ a
      · intro n hn
        exact HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
      · intro S hS
        exact exact_homObj_of_iso.{c, v, r}
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (P.X a)) S
          (hexact a S hS)
    exact quasiIso_homComplex_map_of_stupid_tail.{c, v, r} J R P a
      (fun n hn ↦ hbounded n (Or.inl hn)) f hsingle htail

/-- A bounded source complex whose termwise internal Hom preserves short exact sequences
sends every quasi-isomorphism in the second variable to a quasi-isomorphism. The second
variable is arbitrary, and no K-injective resolution or derived category occurs here.

The site object and morphism universes may differ from the coefficient universe.
Source: Stacks Project, Cohomology of Sheaves, Tag 08DM, bounded Hom calculation;
Homology, Tag 0117, long exact cohomology sequence.
(blueprint: lem-sfb-independent-bounded-exact-term-hom).

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
    {C : Type c} [Category.{v} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (P : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ)
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n))
    (hexact : ∀ (n : ℤ) (S : ShortComplex (SheafOfModules.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))),
      S.ShortExact → ∃ hz : SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
        n)) S.f ≫
          SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X n)) S.g = 0,
        (ShortComplex.mk (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X
          n)) S.f)
          (SheafOfModules.homObjMap.{max c v r, v, c, max c v r} (R := R) (𝟙 (P.X n)) S.g)
            hz).ShortExact)
    {M N : CochainComplex (SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ℤ}
    (f : M ⟶ N) [QuasiIso f] :
    QuasiIso (((homComplexFunctor.{c, v, max c v r, max c v r} (R := R)).obj (op P)).map f) := by
  obtain ⟨a, b, hb⟩ := hbounded
  apply quasiIso_homComplex_map_of_interval.{c, v, r} J R P a (b - a).toNat _ hexact f
  intro n hn
  apply hb n
  rcases hn with hn | hn
  · exact Or.inl hn
  · exact Or.inr (by omega)

end CategoryTheory.SplitPerfectHom
