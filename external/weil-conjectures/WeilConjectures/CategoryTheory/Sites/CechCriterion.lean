/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Vanishing of sheaf cohomology from vanishing of Čech cohomology on a site

Let `(C, J)` be a site, `B` a class of objects of `C` containing a terminal object, such that
every covering sieve of a member `V` of `B` contains a finite covering family `U` whose Čech
nerve `U (y 0) ×_V ⋯ ×_V U (y k)` lies in `B`. If an abelian sheaf `F` has vanishing higher Čech
cohomology on all these families, then its higher cohomology vanishes.

This is [Stacks, Cohomology on Sites, Lemma 21.10.9] (tag `03F7`), and the site analogue of
`TopCat.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`. The proof is the usual dimension
shifting: embed `F` into an injective sheaf `I` with cokernel `Q`. The vanishing of the first
Čech cohomology of `F` shows that `I(V) → Q(V)` is surjective for every `V` in `B`, hence that
the Čech complexes of `F`, `I` and `Q` on the families form a short exact sequence. Since the
Čech complexes of `I` are exact in positive degrees
(`CategoryTheory.Presheaf.exactAt_cechComplex_of_injective`), `Q` again has vanishing higher
Čech cohomology, and `H^{q + 1}(F) ≅ H^q(Q)` for `q > 0` while `H^1(F)` is the cokernel of
`I(T) → Q(T)`.

## Main statements

- `CategoryTheory.Sheaf.surjective_app_of_exactAt_cechComplex_one`: if the first Čech cohomology
  of `F` vanishes on finite covering families refining every covering of `V`, then
  `I(V) → Q(V)` is surjective for every short exact sequence `0 → F → I → Q → 0`.
- `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`: the vanishing criterion.
-/

@[expose] public section

universe w' v w

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Presheaf

variable {C : Type w} [Category.{v} C] {V : C} [HasFiniteProducts (Over V)] {ι : Type*}
  (U : ι → Over V) (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v})

/-- The Čech differential of the restrictions of a single section vanishes. -/
lemma cechComplex_d_zero_restrict (s : P.obj (op V)) (c : ((cechComplex U).obj P).X 0)
    (hc : ∀ z, c z = P.map (cechNerveObj U z).hom.op s) : ((cechComplex U).obj P).d 0 1 c = 0 := by
  funext (y : Fin 2 → ι)
  rw [cechComplex_d_apply]
  simp only [hc]
  have key (x : Fin (0 + 2)) : P.map (cechNerveMap U y x.succAbove).left.op
      (P.map (cechNerveObj U (y ∘ x.succAbove)).hom.op s) = P.map (cechNerveObj U y).hom.op s := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
  simp only [key, ← Finset.sum_smul]
  simp [Fin.sum_univ_succ]

/-- Two components of a Čech cochain indexed by equal tuples agree, after transport of the
restriction along the equality. -/
lemma map_cechCochain_congr {k : ℕ} (c : ((cechComplex U).obj P).X k) {y y' : Fin (k + 1) → ι}
    (h : y = y') {Z : C} (G : Z ⟶ (cechNerveObj U y).left) (G' : Z ⟶ (cechNerveObj U y').left)
    (hG : G ≫ (eqToHom (congrArg (cechNerveObj U) h)).left = G') :
    P.map G.op (c y) = P.map G'.op (c y') := by
  subst h hG
  simp

/-- The restriction of a component of a Čech cochain along a face of the Čech nerve, followed by
a transport along an equality of tuples. -/
lemma map_cechCochain_face_eq {k : ℕ} (c : ((cechComplex U).obj P).X k) {Z : C}
    {f : Z ⟶ V} {m : ℕ} {y : Fin (m + 1) → ι} (G : Over.mk f ⟶ cechNerveObj U y)
    (θ : Fin (k + 1) → Fin (m + 1)) {y' : Fin (k + 1) → ι} (h : y ∘ θ = y')
    (G' : Over.mk f ⟶ cechNerveObj U y')
    (hG : ∀ l, G ≫ Pi.π _ (θ l) ≫ eqToHom (congrArg U (congrFun h l)) = G' ≫ Pi.π _ l) :
    P.map (G ≫ cechNerveMap U y θ).left.op (c (y ∘ θ)) = P.map G'.left.op (c y') := by
  refine map_cechCochain_congr U P c h _ _ ?_
  rw [← Over.comp_left]
  congr 1
  refine Pi.hom_ext _ _ fun l ↦ ?_
  rw [Category.assoc, Category.assoc, eqToHom_cechNerveObj_π U h, ← hG]
  erw [Pi.lift_comp_π_assoc]

/-- A Čech `0`-cocycle is compatible: its members agree on the overlaps. -/
lemma map_eq_of_cechComplex_d_zero (c : ((cechComplex U).obj P).X 0)
    (hc : ((cechComplex U).obj P).d 0 1 c = 0) (z z' : Fin 1 → ι) {Z : C}
    (g₁ : Z ⟶ (cechNerveObj U z).left) (g₂ : Z ⟶ (cechNerveObj U z').left)
    (hg : g₁ ≫ (cechNerveObj U z).hom = g₂ ≫ (cechNerveObj U z').hom) :
    P.map g₁.op (c z) = P.map g₂.op (c z') := by
  let G : Over.mk (g₁ ≫ (cechNerveObj U z).hom) ⟶
      cechNerveObj U (Fin.cons (z 0) z' : Fin 2 → ι) :=
    cechNerveCons U (Over.homMk g₁ ≫ Pi.π (fun l ↦ U (z l)) 0) (Over.homMk g₂ hg.symm)
  have h := congrArg (P.map G.left.op) (congrFun hc (Fin.cons (z 0) z'))
  rw [cechComplex_d_apply, cechComplex_zero_apply, map_zero, map_sum, Fin.sum_univ_two] at h
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one,
    neg_smul, map_neg] at h
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, ← Over.comp_left] at h
  rw [add_neg_eq_zero] at h
  have h₀ : (Fin.cons (z 0) z' : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = z' := by
    funext l
    fin_cases l
    rfl
  have h₁ : (Fin.cons (z 0) z' : Fin 2 → ι) ∘ (1 : Fin 2).succAbove = z := by
    funext l
    fin_cases l
    rfl
  refine ((map_cechCochain_face_eq U P c G _ h₁ (Over.homMk g₁) fun l ↦ ?_).symm.trans
    h.symm).trans (map_cechCochain_face_eq U P c G _ h₀ (Over.homMk g₂ hg.symm) fun l ↦ ?_)
  · fin_cases l
    exact cechNerveCons_π_of_eq_zero U _ _ _ (by decide) _
  · exact cechNerveCons_π_of_eq_succ U _ _ _ l (by simp) _

end Presheaf

namespace Sheaf

open Presheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}

section

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})}

/-- The composite of the two maps of a short complex of abelian sheaves vanishes on sections. -/
lemma app_g_app_f (W : Cᵒᵖ) (x : S.X₁.obj.obj W) : S.g.hom.app W (S.f.hom.app W x) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congr_arg (fun φ ↦ φ.hom) S.zero) W) x

/-- In a short exact sequence of abelian sheaves, the first map is injective on sections. -/
lemma injective_app_f (hS : S.ShortExact) (W : Cᵒᵖ) : Function.Injective (S.f.hom.app W) := by
  have := hS.mono_f
  exact (AddCommGrpCat.mono_iff_injective _).1
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W).map_mono S.f)

/-- A short exact sequence of abelian sheaves is left exact on sections. -/
lemma exists_app_f_eq [HasSheafify J AddCommGrpCat.{max w v}] (hS : S.ShortExact) (W : Cᵒᵖ)
    (x : S.X₂.obj.obj W) (hx : S.g.hom.app W x = 0) : ∃ y, S.f.hom.app W y = x := by
  have := hS.mono_f
  exact (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W) inferInstance inferInstance) x hx

end

/-- An abelian sheaf satisfies the sheaf condition for a family of morphisms generating a
covering sieve. -/
lemma isSheafFor_ofArrows (F : Sheaf J AddCommGrpCat.{max w v}) {V : C} {κ : Type*}
    {Y : κ → C} (π : ∀ a, Y a ⟶ V) (hπ : Sieve.ofArrows Y π ∈ J V) :
    Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows Y π) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ hπ

variable [HasSheafify J AddCommGrpCat.{max w v}]

/-- The Čech complexes of an injective abelian sheaf are exact in positive degrees. -/
lemma exactAt_cechComplex_of_injective (I : Sheaf J AddCommGrpCat.{max w v}) [Injective I]
    {V : C} [HasFiniteProducts (Over V)] {ι : Type*} (U : ι → Over V) (q : ℕ) :
    ((cechComplex U).obj I.obj).ExactAt (q + 1) :=
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  Presheaf.exactAt_cechComplex_of_injective U I.obj q

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves and `V` an object such
that every covering sieve of `V` contains a finite family `U` generating a covering sieve, on
which the first Čech cohomology of `F` vanishes. Then `I(V) → Q(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) {V : C}
    [HasFiniteProducts (Over V)] [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]
    (hV : ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V), (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V ∧
      ((cechComplex U).obj S.X₁.obj).ExactAt 1) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  have := hS.epi_g
  have : Presheaf.IsLocallySurjective J S.g.hom :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max w v} S.g).2 this
  obtain ⟨n, U, hR, hcov, hU⟩ := hV _ (Presheaf.imageSieve_mem J S.g.hom s)
  choose t ht using hR
  let a : ((cechComplex U).obj S.X₂.obj).X 0 := fun z ↦
    S.X₂.obj.map (Pi.π (fun l ↦ U (z l)) 0).left.op (t (z 0))
  have ha (z : Fin 1 → Fin n) : ((cechComplex U).map S.g.hom).f 0 a z =
      S.X₃.obj.map (cechNerveObj U z).hom.op s := by
    rw [cechComplex_map_f_apply, NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Over.w]
  obtain ⟨e, he⟩ := exists_cechComplex_map_f_eq U S.f.hom S.g.hom (exists_app_f_eq hS) _
    (((cechComplex U).obj S.X₂.obj).d 0 1 a) (by
      rw [cechComplex_map_f_d_apply]
      exact cechComplex_d_zero_restrict U _ s _ ha)
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ 0).1 hU e
    (cechComplex_map_f_injective U _ (injective_app_f hS) _ (by
      rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  have hda : ((cechComplex U).obj S.X₂.obj).d 0 1
      (a - ((cechComplex U).map S.f.hom).f 0 b) = 0 := by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self]
  -- the members of the Čech nerve in degree `0` generate a covering sieve
  have hcov' : Sieve.ofArrows (fun z : Fin 1 → Fin n ↦ (cechNerveObj U z).left)
      (fun z ↦ (cechNerveObj U z).hom) ∈ J V := by
    refine J.superset_covering (fun Y g hg ↦ ?_) hcov
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, h ≫ (Pi.lift fun _ ↦ 𝟙 (U i)).left, ?_⟩
    rw [Category.assoc, Over.w]
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows S.X₂ _ hcov') (fun z ↦ (a - ((cechComplex U).map S.f.hom).f 0 b) z)
    fun z z' Z g₁ g₂ hg ↦ map_eq_of_cechComplex_d_zero U _ _ hda z z' g₁ g₂ hg
  refine ⟨σ, (isSheafFor_ofArrows S.X₃ _ hcov').isSeparatedFor.ext fun Y f ⟨z⟩ ↦ ?_⟩
  change S.X₃.obj.map _ (S.g.hom.app _ σ) = S.X₃.obj.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  rw [cechComplex_sub_apply, map_sub, cechComplex_map_f_apply, app_g_app_f, sub_zero, ← ha]
  rfl

section

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})] {T : C} (hT : IsTerminal T)

open Abelian

/-- Let `0 → F → I → Q → 0` be a short exact sequence of abelian sheaves with `I` injective. If
the connecting map `H^q(Q) → H^{q + 1}(F)` vanishes, then `H^{q + 1}(F) = 0`. -/
lemma subsingleton_H_succ_of_comp_extClass {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})}
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (h : ∀ y : Sheaf.H S.X₃ q, y.comp hS.extClass rfl = 0) :
    Subsingleton (Sheaf.H S.X₁ (q + 1)) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim _ _) rfl
  exact h y

include hT in
/-- If `I(T) → Q(T)` is surjective, then the connecting map `H^0(Q) → H^1(F)` vanishes. -/
lemma comp_extClass_eq_zero_of_surjective {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})}
    (hS : S.ShortExact) (h : Function.Surjective (S.g.hom.app (op T)))
    (y : Sheaf.H S.X₃ 0) : y.comp hS.extClass rfl = 0 := by
  obtain ⟨t, ht⟩ := h (Sheaf.H.equiv₀ S.X₃ hT y)
  obtain rfl : y = Sheaf.H.map S.g 0 ((Sheaf.H.equiv₀ S.X₂ hT).symm t) := by
    rw [Sheaf.H.equiv₀_symm_naturality, ht, AddEquiv.symm_apply_apply]
  rw [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

variable [∀ V : C, HasFiniteProducts (Over V)]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]

include hT in
/-- **The Čech criterion for the vanishing of cohomology.** Let `B` be a class of objects of the
site containing a terminal object `T`, such that every covering sieve of a member `V` of `B`
contains a finite family `U` generating a covering sieve, whose Čech nerve
`U (y 0) ×_V ⋯ ×_V U (y k)` lies in `B`. If the Čech complexes of the abelian sheaf `F` on all
these families are exact in positive degrees, then `H^q(F) = 0` for `q > 0`. -/
@[stacks 03F7]
theorem subsingleton_H_succ_of_exactAt_cechComplex (B : C → Prop) (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (F : Sheaf J AddCommGrpCat.{max w v})
    (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
    (q : ℕ) : Subsingleton (Sheaf.H F (q + 1)) := by
  -- for a short exact sequence `0 → F → I → Q → 0`, sections of `Q` over members of `B` lift
  have hsurj (F : Sheaf J AddCommGrpCat.{max w v})
      (hF : ∀ V, B V → ∀ {n : ℕ} (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) →
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
        ∀ q : ℕ, ((cechComplex U).obj F.obj).ExactAt (q + 1))
      {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})} (hS : S.ShortExact) (hSF : S.X₁ = F)
      (V : C) (hV : B V) : Function.Surjective (S.g.hom.app (op V)) := by
    subst hSF
    refine surjective_app_of_exactAt_cechComplex_one hS fun R hR ↦ ?_
    obtain ⟨n, U, hUB, hUR, hUJ⟩ := hcov V hV R hR
    exact ⟨n, U, hUR, hUJ, hF V hV U hUB hUJ 0⟩
  induction q generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    exact subsingleton_H_succ_of_comp_extClass hS 0
      (comp_extClass_eq_zero_of_surjective hT hS (hsurj F hF hS rfl T hBT))
  | succ q ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
    have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have := ih S.X₃ fun V hV n U hUB hUJ q ↦ exactAt_cechComplex_of_sectionwise U S.f.hom S.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj F hF hS rfl _ (hUB k y)) q (hF V hV U hUB hUJ (q + 1))
      (exactAt_cechComplex_of_injective S.X₂ U q)
    exact subsingleton_H_succ_of_comp_extClass hS (q + 1) fun y ↦ by
      rw [Subsingleton.elim y 0, Ext.zero_comp]


include hT in
/-- **The Čech criterion in degree two.** Let `T` be a terminal object and `F` an abelian sheaf
such that, for every short exact sequence `0 → F → I → Q → 0`, sections of `Q` lift to `I` over
the members of a class `B` of objects. If every covering sieve of `T` contains a finite family
`U` generating a covering sieve, whose Čech nerve lies in `B` and on which the second Čech
cohomology of `F` vanishes, then `H²(F) = 0`.

Embedding `F` into an injective sheaf `I` with cokernel `Q`, the Čech complexes of `F`, `I` and
`Q` on the families form a short exact sequence, so the first Čech cohomology of `Q` vanishes on
them, hence `H¹(Q) = 0`, and `H²(F)` is a quotient of `H¹(Q)`. -/
theorem subsingleton_H_two_of_exactAt_cechComplex (B : C → Prop)
    (F : Sheaf J AddCommGrpCat.{max w v})
    (hsurj : ∀ {S : ShortComplex (Sheaf J AddCommGrpCat.{max w v})}, S.ShortExact →
      S.X₁ = F → ∀ V, B V → Function.Surjective (S.g.hom.app (op V)))
    (hcov : ∀ R ∈ J T, ∃ (n : ℕ) (U : Fin n → Over T),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J T ∧
      ((cechComplex U).obj F.obj).ExactAt 2) :
    Subsingleton (Sheaf.H F 2) := by
  let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)
  have hS : S.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  -- `H¹(Q) = 0` for the cokernel `Q` of `F → I`
  have hQ : Subsingleton (Sheaf.H S.X₃ 1) := by
    let S' := ShortComplex.mk (Injective.ι S.X₃) (cokernel.π (Injective.ι S.X₃))
      (cokernel.condition _)
    have hS' : S'.ShortExact := .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    refine subsingleton_H_succ_of_comp_extClass hS' 0
      (comp_extClass_eq_zero_of_surjective hT hS' ?_)
    refine surjective_app_of_exactAt_cechComplex_one hS' fun R hR ↦ ?_
    obtain ⟨n, U, hUB, hUR, hUJ, hU⟩ := hcov R hR
    exact ⟨n, U, hUR, hUJ, exactAt_cechComplex_of_sectionwise U S.f.hom S.g.hom
      app_g_app_f (injective_app_f hS) (exists_app_f_eq hS)
      (fun k y ↦ hsurj hS rfl _ (hUB k y)) 0 hU (exactAt_cechComplex_of_injective S.X₂ U 0)⟩
  exact subsingleton_H_succ_of_comp_extClass hS 1 fun y ↦ by
    rw [Subsingleton.elim y 0, Ext.zero_comp]
end

end Sheaf

end CategoryTheory
