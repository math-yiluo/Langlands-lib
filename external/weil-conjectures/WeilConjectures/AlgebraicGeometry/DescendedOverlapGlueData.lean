/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-!
# Descended overlap transitions before gluing

Source: Stacks Project, Descent, Tag 0AP4, construction of U_ij and transition maps.
(blueprint: lem-pd-descended-overlap-glue-data).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The fpqc sheaf condition for representables makes a covering singleton effective epi.
Source: Stacks Project, Descent, Tag 023Q; Mathlib's fpqc subcanonical instance.
(blueprint: lem-pd-descended-overlap-glue-data). -/
private theorem effectiveEpi_of_cover {A B : Scheme.{u}}
    (J : Precoverage Scheme) (hJ : J ≤ Scheme.fpqcPrecoverage)
    (q : A ⟶ B) (hq : Presieve.singleton q ∈ J B) : EffectiveEpi q := by
  rw [← Sieve.effectiveEpimorphic_singleton,
    Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck (hJ B hq))

/-- Pairwise cartesian lifts and the transition factorization imply the triple cocycle.

Source: Stacks Project, Descent, Tag 0AP4, omitted verification of the gluing identities.
(blueprint: lem-pd-descended-overlap-glue-data).

Pull back each double overlap along its map to W_i to obtain an fpqc effective epi c.
The cartesian lifts give maps a and b to the original pairwise intersections, with the
same U_i projection. Their other projections define d into U_k times_V U_l. The maps
e and e' express the two cyclic reorderings of these three points. Descend e along c:
its second projection factors through c, and that projection is monic, so effective-epi
compatibility holds. Each cyclic transition sends the corresponding reordered lift to
the next one. The third sends it back to c. Cancel c to prove the cyclic identity. -/
private theorem overlap_cocycle
    {V : Scheme.{u}} {I : Type u} (U : I → V.Opens)
    (W : I → Scheme.{u}) (q : ∀ i, (U i).toScheme ⟶ W i)
    (hq : ∀ i, Presieve.singleton (q i) ∈ Scheme.fpqcPrecoverage (W i))
    (Z : I × I → Scheme.{u}) (f : ∀ i k, Z (i, k) ⟶ W i)
    (hf : ∀ i k, IsOpenImmersion (f i k))
    (r : ∀ i k, Limits.pullback (U i).ι (U k).ι ⟶ Z (i, k))
    (hrcart : ∀ i k, IsPullback (r i k) (pullback.fst (U i).ι (U k).ι) (f i k) (q i))
    (t : ∀ i k, Z (i, k) ⟶ Z (k, i))
    (hrt : ∀ i k, r i k ≫ t i k =
      (pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i) :
    ∃ (t' : ∀ i k l, Limits.pullback (f i k) (f i l) ⟶
        Limits.pullback (f k l) (f k i)),
      (∀ i k l, t' i k l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i k) ∧
      (∀ i k l, t' i k l ≫ t' k l i ≫ t' l i k = 𝟙 _) := by
  classical
  have hrf (i k : I) : r i k ≫ f i k = pullback.fst (U i).ι (U k).ι ≫ q i :=
    (hrcart i k).w
  let P (i k l : I) := Limits.pullback (f i k) (f i l)
  let B (i k l : I) := Limits.pullback (pullback.fst (f i k) (f i l) ≫ f i k) (q i)
  let c (i k l : I) : B i k l ⟶ P i k l := pullback.fst _ _
  have hc (i k l : I) : EffectiveEpi (c i k l) := by
    apply effectiveEpi_of_cover Scheme.fpqcPrecoverage le_rfl
    have hqi := hq i
    rw [← Presieve.ofArrows_pUnit.{0}] at hqi ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ q i) hqi
      (pullback.fst (f i k) (f i l) ≫ f i k) (fun _ ↦ c i k l)
      (fun _ ↦ pullback.snd _ _) (fun _ ↦ IsPullback.of_hasPullback _ _)
  let a (i k l : I) : B i k l ⟶ Limits.pullback (U i).ι (U k).ι :=
    (hrcart i k).lift (c i k l ≫ pullback.fst _ _) (pullback.snd _ _) (by
      simpa only [c, Category.assoc] using
        (pullback.condition (f := pullback.fst (f i k) (f i l) ≫ f i k) (g := q i)))
  let b (i k l : I) : B i k l ⟶ Limits.pullback (U i).ι (U l).ι :=
    (hrcart i l).lift (c i k l ≫ pullback.snd _ _) (pullback.snd _ _) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc]
      simpa only [c, Category.assoc] using
        (pullback.condition (f := pullback.fst (f i k) (f i l) ≫ f i k) (g := q i)))
  have har (i k l : I) : a i k l ≫ r i k = c i k l ≫ pullback.fst _ _ := by
    simp [a]
  have haf (i k l : I) : a i k l ≫ pullback.fst (U i).ι (U k).ι =
      pullback.snd (pullback.fst (f i k) (f i l) ≫ f i k) (q i) := by simp [a]
  have hbr (i k l : I) : b i k l ≫ r i l = c i k l ≫ pullback.snd _ _ := by
    simp [b]
  have hbf (i k l : I) : b i k l ≫ pullback.fst (U i).ι (U l).ι =
      pullback.snd (pullback.fst (f i k) (f i l) ≫ f i k) (q i) := by simp [b]
  let d (i k l : I) : B i k l ⟶ Limits.pullback (U k).ι (U l).ι :=
    pullback.lift (a i k l ≫ pullback.snd _ _) (b i k l ≫ pullback.snd _ _) (by
      simp only [Category.assoc, ← pullback.condition]
      rw [← Category.assoc, haf, ← Category.assoc, hbf])
  let e (i k l : I) : B i k l ⟶ P k l i :=
    pullback.lift (d i k l ≫ r k l)
      (a i k l ≫ (pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i) (by
        simp only [Category.assoc, hrf, pullbackSymmetry_hom_comp_fst_assoc]
        simp [d])
  let e' (i k l : I) : B i k l ⟶ P l i k :=
    pullback.lift
      (b i k l ≫ (pullbackSymmetry (U i).ι (U l).ι).hom ≫ r l i)
      (d i k l ≫ (pullbackSymmetry (U k).ι (U l).ι).hom ≫ r l k) (by
        simp only [Category.assoc, hrf, pullbackSymmetry_hom_comp_fst_assoc]
        simp [d])
  have hes (i k l : I) : e i k l ≫ pullback.snd _ _ =
      c i k l ≫ pullback.fst _ _ ≫ t i k := by
    dsimp [e]
    simp only [pullback.lift_snd, ← hrt, ← Category.assoc, har]
  have ex (i k l : I) : ∃ m : P i k l ⟶ P k l i,
      m ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i k := by
    let m := EffectiveEpi.desc (c i k l) (e i k l) (by
      intro T g₁ g₂ hg
      apply (cancel_mono (pullback.snd (f k l) (f k i))).mp
      simp only [Category.assoc, hes]
      simpa only [← Category.assoc] using
        congrArg (fun z ↦ z ≫ pullback.fst (f i k) (f i l) ≫ t i k) hg)
    refine ⟨m, ?_⟩
    apply (cancel_epi (c i k l)).mp
    rw [← Category.assoc, EffectiveEpi.fac]
    exact hes i k l
  choose t' ht' using ex
  refine ⟨t', ht', ?_⟩
  intro i k l
  have hce : c i k l ≫ t' i k l = e i k l := by
    apply (cancel_mono (pullback.snd (f k l) (f k i))).mp
    rw [Category.assoc, ht', ← hes]
  have hee' : e i k l ≫ t' k l i = e' i k l := by
    apply (cancel_mono (pullback.snd (f l i) (f l k))).mp
    simp only [Category.assoc, ht']
    simp only [e, e', pullback.lift_fst_assoc, pullback.lift_snd, Category.assoc, hrt]
  have he'c : e' i k l ≫ t' l i k = c i k l := by
    apply (cancel_mono (pullback.snd (f i k) (f i l))).mp
    simp only [Category.assoc, ht']
    simp only [e', pullback.lift_fst_assoc, Category.assoc, hrt]
    have hs : (pullbackSymmetry (U i).ι (U l).ι).hom ≫
        (pullbackSymmetry (U l).ι (U i).ι).hom = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    calc
      _ = b i k l ≫ r i l := by
        rw [← Category.assoc (pullbackSymmetry (U i).ι (U l).ι).hom, hs]
        simp
      _ = _ := hbr i k l
  apply (cancel_epi (c i k l)).mp
  rw [← Category.assoc, ← Category.assoc, hce, hee', he'c, Category.comp_id]

/-- Compatibility with the ambient datum preserves factorization through another open.
Source: Stacks Project, Descent, Tag 0AP4, compatibility of the overlap with descent data.
(blueprint: lem-pd-descended-overlap-glue-data).
Lift the initial point through U_k, transport both lifts, and compare their inclusions
using hcompat. The transported point still factors through U_k. -/
private theorem transport_range_open
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) {I : Type u} (U : I → V.left.Opens)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (i k : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
    (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom))
    (ha : Set.range (a.left ≫ (U i).ι) ⊆ Set.range (U k).ι) :
    Set.range (((E i).transport f₁ f₂ h a).left ≫ (U i).ι) ⊆
      Set.range (U k).ι := by
  let b : T ⟶ (U k).toScheme := IsOpenImmersion.lift (U k).ι (a.left ≫ (U i).ι) ha
  have hb : b ≫ (U k).ι = a.left ≫ (U i).ι := IsOpenImmersion.lift_fac ..
  let b' : Over.mk f₁ ⟶ Over.mk ((U k).ι ≫ V.hom) := Over.homMk b (by
    simpa only [Over.mk_hom, ← Category.assoc, hb] using Over.w a)
  have hab : (Over.homMk (a.left ≫ (U i).ι) (by
      simpa only [Over.mk_hom, Category.assoc] using Over.w a) : Over.mk f₁ ⟶ V) =
      Over.homMk (b'.left ≫ (U k).ι) (by
        simpa only [Over.mk_hom, Category.assoc] using Over.w b') := by
    ext
    exact hb.symm
  have heq : ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
      ((E k).transport f₁ f₂ h b').left ≫ (U k).ι := by
    rw [hcompat, hcompat, hab]
  rw [heq]
  rintro x ⟨z, rfl⟩
  exact ⟨((E k).transport f₁ f₂ h b').left z, rfl⟩

/-- The intersection open satisfies the double-overlap equality required by open descent.
Source: Stacks Project, Descent, Tags 0AP4 and 03N0.
(blueprint: lem-pd-descended-overlap-glue-data).
For two maps a and b with the same q_i composite, restrict their test scheme to the
preimage of U_k under a. Cartesian uniqueness and hinv identify transport of a with b.
The preceding factorization lemma gives containment of the preimage under a in that
under b. Interchange a and b for the reverse containment. -/
private theorem intersections_invariant
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∀ i k, pullback.fst (q i) (q i) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ U k) =
      pullback.snd (q i) (q i) ⁻¹ᵁ ((U i).ι ⁻¹ᵁ U k) := by
  intro i k
  have sub {T : Scheme.{u}} (a b : T ⟶ (U i).toScheme)
      (hab : a ≫ q i = b ≫ q i) :
      (a ≫ (U i).ι) ⁻¹ᵁ U k ≤ (b ≫ (U i).ι) ⁻¹ᵁ U k := by
    let O := (a ≫ (U i).ι) ⁻¹ᵁ U k
    let a₀ := O.ι ≫ a
    let b₀ := O.ι ≫ b
    let f₁ := a₀ ≫ (U i).ι ≫ V.hom
    let f₂ := b₀ ≫ (U i).ι ≫ V.hom
    have hf : f₁ ≫ p = f₂ ≫ p := by
      dsimp [f₁, f₂, a₀, b₀]
      simp only [Category.assoc, ← (hcart i).w]
      simpa only [Category.assoc] using congrArg (fun m ↦ O.ι ≫ m ≫ (W i).hom) hab
    let a' : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom) := Over.homMk a₀ rfl
    have ht : ((E i).transport f₁ f₂ hf a').left = b₀ := by
      apply (hcart i).hom_ext
      · simpa only [Over.homMk_left, Category.assoc] using
          (hinv i f₁ f₂ hf a').trans (by
            dsimp [a', a₀, b₀]
            simpa only [Over.homMk_left, Category.assoc] using
              congrArg (fun m ↦ O.ι ≫ m) hab)
      · exact Over.w ((E i).transport f₁ f₂ hf a')
    have hr : Set.range (a'.left ≫ (U i).ι) ⊆ Set.range (U k).ι := by
      rw [Scheme.Opens.range_ι]
      rintro x ⟨z, rfl⟩
      exact z.property
    have hs := transport_range_open D U E hcompat i k f₁ f₂ hf a' hr
    rw [ht, Scheme.Opens.range_ι] at hs
    intro x hx
    exact hs ⟨(⟨x, hx⟩ : O), by simp [b₀]⟩
  apply le_antisymm
  · simpa only [Scheme.Hom.comp_preimage] using
      sub (pullback.fst (q i) (q i)) (pullback.snd (q i) (q i)) pullback.condition
  · simpa only [Scheme.Hom.comp_preimage] using
      sub (pullback.snd (q i) (q i)) (pullback.fst (q i) (q i)) pullback.condition.symm

/-- The effective local models have open overlap transitions and lifts of the intersections.

Source: Stacks Project, Descent, Tag 0AP4, proof through the construction of gluing data;
Tags 03N0 and 02W0 for descent of opens and morphisms, respectively.
(blueprint: lem-pd-descended-overlap-glue-data).

Proof:
1. Inside U_i, take the inverse image of U_k under its inclusion in V. Given two
   transports over the same map to Y, membership in this intersection is preserved:
   compatibility with D makes the two inclusions agree after transport, and inverse
   transport gives the reverse implication. The pullback square for q_i identifies
   U_i with W_i times_Y X. Transport invariance of q_i and the pullback universal
   property identify E_i with the canonical descent datum. Base change of the fpqc
   singleton p makes q_i an fpqc singleton. Tag 03N0 descends the invariant intersection
   to a unique open O_ik of W_i. Set Z(i,k) to its open subscheme and f i k to its
   inclusion. The diagonal intersection is all U_i, so uniqueness gives O_ii = W_i
   and f i i is an isomorphism.
2. The common intersection U_i times_V U_k identifies the pullbacks of Z(i,k) and
   Z(k,i) along p. Its identity commutes with the canonical descent data just identified.
   Tag 02W0 descends this identity to t i k over Y, and descends its inverse to t k i.
   Injectivity proves the inverse identities and t i i = identity. The restriction of
   q_i to the intersection factors through the descended open, giving r i k. The
   factorization equations are r i k followed by f i k = first projection followed by
   q_i, and r i k followed by t i k and f k i = second projection followed by q_k.
   Descent of the open identifies its pullback along q_i with this intersection,
   giving the asserted cartesian square for r i k.
3. On triple intersections, uniqueness in Tag 03N0 identifies the overlap domains.
   Restrict the transitions there and use the pullback universal property to obtain
   t' i k l. Its second projection is the first projection followed by t i k.
   After fpqc base change the three cyclic restrictions are identities on the same
   triple intersection; injectivity in Tag 02W0 gives the cyclic cocycle equation.
   The f i k are open immersions by construction. No covering assumption on U is used,
   and no ambient glued scheme or map from it to Y is asserted. Empty I gives empty
   families with all assertions vacuous; empty individual opens descend to empty opens.
-/
theorem exists_descended_overlap_glue_data
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type u} (U : I → V.left.Opens)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (W : I → Over Y) (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hinv : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ q i = a.left ≫ q i) :
    ∃ (Z : I × I → Scheme.{u}) (f : ∀ i k, Z (i, k) ⟶ (W i).left)
      (t : ∀ i k, Z (i, k) ⟶ Z (k, i)),
      (∀ i k, IsOpenImmersion (f i k)) ∧
      (∀ i, IsIso (f i i)) ∧
      (∀ i, t i i = 𝟙 _) ∧
      (∃ (t' : ∀ i k l, Limits.pullback (f i k) (f i l) ⟶ Limits.pullback (f k l) (f k i)),
        (∀ i k l, t' i k l ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i k) ∧
        (∀ i k l, t' i k l ≫ t' k l i ≫ t' l i k = 𝟙 _)) ∧
      (∀ i k, ∃ (r : Limits.pullback (U i).ι (U k).ι ⟶ Z (i, k)),
        IsPullback r (pullback.fst (U i).ι (U k).ι) (f i k) (q i) ∧
        r ≫ t i k ≫ f k i = pullback.snd (U i).ι (U k).ι ≫ q k) := by
  classical
  have hq (i : I) : Presieve.singleton (q i) ∈ Scheme.fpqcPrecoverage (W i).left := by
    rw [← Presieve.ofArrows_pUnit.{0}] at hp ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ p) hp
      (W i).hom (fun _ ↦ q i) (fun _ ↦ (U i).ι ≫ V.hom) (fun _ ↦ hcart i)
  have hO (i k : I) : ∃! O : (W i).left.Opens, q i ⁻¹ᵁ O = (U i).ι ⁻¹ᵁ U k := by
    have hqi := hq i
    rw [← Presieve.ofArrows_pUnit.{0}] at hqi
    simpa using openSubscheme_existsUnique_of_fpqc (fun _ : PUnit.{1} ↦ q i) hqi
      (fun _ ↦ (U i).ι ⁻¹ᵁ U k)
      (fun _ _ ↦ intersections_invariant D U E hcompat W q hcart hinv i k)
  let O : ∀ i k, (W i).left.Opens := fun i k ↦ (hO i k).choose
  have hpre (i k : I) : q i ⁻¹ᵁ O i k = (U i).ι ⁻¹ᵁ U k := (hO i k).choose_spec.1
  have hdiag (i : I) : O i i = ⊤ := by
    exact ((hO i i).choose_spec.2 ⊤ (by simp)).symm
  let Z : I × I → Scheme.{u} := fun ik ↦ (O ik.1 ik.2).toScheme
  let f : ∀ i k, Z (i, k) ⟶ (W i).left := fun i k ↦ (O i k).ι
  have hf (i k : I) : IsOpenImmersion (f i k) := by dsimp [f]; infer_instance
  have hfi (i : I) : IsIso (f i i) := by
    have hi (A : (W i).left.Opens) (hA : A = ⊤) : IsIso A.ι := by
      subst A
      exact (inferInstance : IsIso (W i).left.topIso.hom)
    exact hi (O i i) (hdiag i)
  have hrange (i k : I) :
      Set.range (pullback.fst (U i).ι (U k).ι ≫ q i) ⊆ Set.range (f i k) := by
    rw [show Set.range (f i k) = O i k from Scheme.Opens.range_ι _]
    rintro x ⟨z, rfl⟩
    change pullback.fst (U i).ι (U k).ι z ∈ q i ⁻¹ᵁ O i k
    rw [hpre]
    change (pullback.fst (U i).ι (U k).ι ≫ (U i).ι) z ∈ U k
    rw [pullback.condition]
    exact (pullback.snd (U i).ι (U k).ι z).property
  let r : ∀ i k, Limits.pullback (U i).ι (U k).ι ⟶ Z (i, k) := fun i k ↦
    IsOpenImmersion.lift (f i k) (pullback.fst (U i).ι (U k).ι ≫ q i) (hrange i k)
  have hrf (i k : I) : r i k ≫ f i k = pullback.fst (U i).ι (U k).ι ≫ q i :=
    IsOpenImmersion.lift_fac ..
  have hrcart (i k : I) :
      IsPullback (r i k) (pullback.fst (U i).ι (U k).ι) (f i k) (q i) := by
    apply IsOpenImmersion.isPullback
    · exact (hrf i k).symm
    · rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
      simpa only [Scheme.Opens.opensRange_ι] using hpre i k
  have hrcover (i k : I) : Presieve.singleton (r i k) ∈ Scheme.fpqcPrecoverage (Z (i, k)) := by
    have hqi := hq i
    rw [← Presieve.ofArrows_pUnit.{0}] at hqi ⊢
    exact Precoverage.mem_coverings_of_isPullback (fun _ : PUnit.{1} ↦ q i) hqi
      (f i k) (fun _ ↦ r i k) (fun _ ↦ pullback.fst (U i).ι (U k).ι)
      (fun _ ↦ hrcart i k)
  have hrepi (i k : I) : EffectiveEpi (r i k) :=
    effectiveEpi_of_cover Scheme.fpqcPrecoverage le_rfl _ (hrcover i k)
  have heq (i k : I) {T : Scheme.{u}}
      (g₁ g₂ : T ⟶ Limits.pullback (U i).ι (U k).ι)
      (hg : g₁ ≫ r i k = g₂ ≫ r i k) :
      g₁ ≫ (pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i =
        g₂ ≫ (pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i := by
    let a₁ := g₁ ≫ pullback.fst (U i).ι (U k).ι
    let a₂ := g₂ ≫ pullback.fst (U i).ι (U k).ι
    let b₁ := g₁ ≫ pullback.snd (U i).ι (U k).ι
    let b₂ := g₂ ≫ pullback.snd (U i).ι (U k).ι
    have hab₁ : a₁ ≫ (U i).ι = b₁ ≫ (U k).ι := by
      dsimp [a₁, b₁]; simp only [Category.assoc, pullback.condition]
    have hab₂ : a₂ ≫ (U i).ι = b₂ ≫ (U k).ι := by
      dsimp [a₂, b₂]; simp only [Category.assoc, pullback.condition]
    have haq : a₁ ≫ q i = a₂ ≫ q i := by
      dsimp [a₁, a₂]
      simpa only [Category.assoc, hrf] using congrArg (fun m ↦ m ≫ f i k) hg
    let f₁ := a₁ ≫ (U i).ι ≫ V.hom
    let f₂ := a₂ ≫ (U i).ι ≫ V.hom
    have hp₁₂ : f₁ ≫ p = f₂ ≫ p := by
      dsimp [f₁, f₂]
      simp only [Category.assoc, ← (hcart i).w]
      simpa only [Category.assoc] using congrArg (fun m ↦ m ≫ (W i).hom) haq
    let a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom) := Over.homMk a₁ rfl
    let b : Over.mk f₁ ⟶ Over.mk ((U k).ι ≫ V.hom) := Over.homMk b₁ (by
      dsimp [f₁]; rw [← Category.assoc, ← hab₁, Category.assoc])
    have ha₂ : ((E i).transport f₁ f₂ hp₁₂ a).left = a₂ := by
      apply (hcart i).hom_ext
      · exact (hinv i f₁ f₂ hp₁₂ a).trans haq
      · exact Over.w ((E i).transport f₁ f₂ hp₁₂ a)
    have hpoints : (Over.homMk (a.left ≫ (U i).ι) (by
        simpa only [Over.mk_hom, Category.assoc] using Over.w a) : Over.mk f₁ ⟶ V) =
        Over.homMk (b.left ≫ (U k).ι) (by
          simpa only [Over.mk_hom, Category.assoc] using Over.w b) := by
      ext; exact hab₁
    have hb₂ : ((E k).transport f₁ f₂ hp₁₂ b).left = b₂ := by
      apply (cancel_mono (U k).ι).mp
      rw [hcompat, ← hpoints, ← hcompat, ha₂, hab₂]
    have hbq : b₁ ≫ q k = b₂ ≫ q k := by
      simpa only [hb₂, b, Over.homMk_left] using (hinv k f₁ f₂ hp₁₂ b).symm
    apply (cancel_mono (f k i)).mp
    simpa only [b₁, b₂, Category.assoc, hrf, pullbackSymmetry_hom_comp_fst_assoc] using hbq
  let t : ∀ i k, Z (i, k) ⟶ Z (k, i) := fun i k ↦
    EffectiveEpi.desc (r i k) ((pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i)
      (heq i k)
  have hrt (i k : I) : r i k ≫ t i k =
      (pullbackSymmetry (U i).ι (U k).ι).hom ≫ r k i := EffectiveEpi.fac ..
  have htself (i : I) : t i i = 𝟙 _ := by
    apply (cancel_epi (r i i)).mp
    rw [hrt, pullbackSymmetry_hom_of_mono_eq]
    simp
  have hrtf (i k : I) : r i k ≫ t i k ≫ f k i =
      pullback.snd (U i).ι (U k).ι ≫ q k := by
    rw [← Category.assoc, hrt]
    simp only [Category.assoc, hrf, pullbackSymmetry_hom_comp_fst_assoc]
  obtain ⟨t', ht', hcoc⟩ := overlap_cocycle U (fun i ↦ (W i).left) q hq Z f hf r hrcart t hrt
  exact ⟨Z, f, t, hf, hfi, htself, ⟨t', ht', hcoc⟩, fun i k ↦ ⟨r i k, hrcart i k, hrtf i k⟩⟩

end CategoryTheory.Over.DescentDatum
