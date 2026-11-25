/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.Mathlib.CategoryTheory.Filtered.Basic

/-!
# Cohomology on a site commutes with filtered colimits on quasi-compact objects

Let `(C, J)` be a site and `B` a class of objects of `C` containing a terminal object `T`, such
that every covering sieve of a member `V` of `B` contains a finite family `U` generating a
covering sieve, whose Čech nerve `U (y 0) ×_V ⋯ ×_V U (y k)` lies in `B` (the hypothesis of the
Čech criterion `CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`). Typically,
`B` is the class of quasi-compact quasi-separated objects. Then the cohomology `Hᵠ(T, -)` of
abelian sheaves commutes with filtered colimits ([Stacks 03Q6], [Stacks 0738]).

## Main definitions

- `CategoryTheory.Functor.toInjectiveExtension`: a functorial monomorphism
  `D ⟶ D.injectiveExtension` of a diagram in a Grothendieck abelian category into a diagram of
  injective objects.

## Main statements

- `AddCommGrpCat.exists_ι_apply_eq_of_isColimit`, `AddCommGrpCat.exists_map_eq_zero_of_isColimit`:
  elements of filtered colimits of abelian groups of arbitrary size.
- `CategoryTheory.Sheaf.exists_map_eq_zero_of_isColimit_of_finite`,
  `CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite`: sections over members of `B` of a
  filtered colimit of abelian sheaves come from a finite stage and are separated at a finite
  stage.
- `CategoryTheory.Sheaf.exactAt_cechComplex_of_isColimit`: Čech complexes on finite families
  with Čech nerve in `B` of a filtered colimit of sheaves with exact Čech complexes are exact.
- `CategoryTheory.Sheaf.subsingleton_H_succ_of_isColimit_of_injective`: a filtered colimit of
  injective abelian sheaves has no higher cohomology.
- `CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small`: cohomology commutes with filtered
  colimits.
- `CategoryTheory.Sheaf.subsingleton_H_of_isColimit_of_isFiltered`: a filtered colimit of
  sheaves with vanishing `Hᵠ` has vanishing `Hᵠ`.

## Implementation notes

The small étale site version `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered_small` is a
special case. Sections over members of `B` commute with filtered colimits, hence so do the Čech
complexes on the finite families; a filtered colimit of injective sheaves thus has vanishing
higher cohomology by the Čech criterion, and we conclude by dimension shifting along the
functorial injective embedding `CategoryTheory.Functor.toInjectiveExtension`, filtered colimits
being exact.
-/

@[expose] public section

universe w' v w w₁ w₂

open CategoryTheory Limits Opposite Presheaf

namespace AddCommGrpCat

variable {𝒥 : Type w₁} [Category.{w₂} 𝒥] [IsFiltered 𝒥] {G : 𝒥 ⥤ AddCommGrpCat.{w}}
  {d : Cocone G}

/-- Every element of a colimit of a filtered diagram of abelian groups of arbitrary size comes
from some member of the diagram (the colimit is preserved by the universe lift, after which it
is computed on the underlying types). -/
lemma exists_ι_apply_eq_of_isColimit (hd : IsColimit d) (x : d.pt) :
    ∃ (j : 𝒥) (y : G.obj j), d.ι.app j y = x := by
  have : PreservesFilteredColimitsOfSize.{w₂, w₁}
      (CategoryTheory.forget AddCommGrpCat.{max w w₁ w₂}) :=
    preservesFilteredColimitsOfSize_shrink.{w₁, max w w₁ w₂, w₂, max w w₁ w₂} _
  have hd' := isColimitOfPreserves AddCommGrpCat.uliftFunctor.{max w₁ w₂} hd
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep _ hd' (ULift.up x)
  exact ⟨j, y.down, congrArg ULift.down hy⟩

/-- An element of a member of a filtered diagram of abelian groups of arbitrary size which
vanishes in the colimit vanishes in a later member of the diagram. -/
lemma exists_map_eq_zero_of_isColimit (hd : IsColimit d) {j : 𝒥} (y : G.obj j)
    (hy : d.ι.app j y = 0) : ∃ (j' : 𝒥) (a : j ⟶ j'), G.map a y = 0 := by
  have : PreservesFilteredColimitsOfSize.{w₂, w₁}
      (CategoryTheory.forget AddCommGrpCat.{max w w₁ w₂}) :=
    preservesFilteredColimitsOfSize_shrink.{w₁, max w w₁ w₂, w₂, max w w₁ w₂} _
  have hd' := isColimitOfPreserves AddCommGrpCat.uliftFunctor.{max w₁ w₂} hd
  obtain ⟨j', a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq _ hd'
    (ULift.up y : (G ⋙ AddCommGrpCat.uliftFunctor.{max w₁ w₂}).obj j)
    (0 : (G ⋙ AddCommGrpCat.uliftFunctor.{max w₁ w₂}).obj j)
    (congrArg ULift.up (hy.trans (map_zero _).symm))
  refine ⟨IsFiltered.coeq a b, a ≫ IsFiltered.coeqHom a b, ?_⟩
  have h₁ := congrArg ULift.down hab
  change G.map a y = G.map b 0 at h₁
  rw [map_zero] at h₁
  rw [G.map_comp, ConcreteCategory.comp_apply, h₁, map_zero]

end AddCommGrpCat

namespace CategoryTheory.Functor

section InjectiveFunctor

open ZeroObject

variable {C : Type*} [Category* C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  {K : Type*} [Category* K] (D : K ⥤ C)

/-- The diagram of the morphisms `D k ⟶ 0` to a zero object, as a diagram of arrows. -/
noncomputable def arrowToZero : K ⥤ Arrow C where
  obj k := Arrow.mk (0 : D.obj k ⟶ 0)
  map a := Arrow.homMk (D.map a) (𝟙 0) (by simp)

/-- A functorial injective object containing `D k`: the middle object of the functorial
factorization of `D k ⟶ 0` into a monomorphism followed by a morphism with the right lifting
property with respect to monomorphisms. -/
noncomputable def injectiveExtension : K ⥤ C :=
  D.arrowToZero ⋙
    (MorphismProperty.functorialFactorizationData (MorphismProperty.monomorphisms C)
      (MorphismProperty.monomorphisms C).rlp).Z

/-- The natural monomorphism `D ⟶ D.injectiveExtension` into a diagram of injectives. -/
noncomputable def toInjectiveExtension :
    D ⟶ D.injectiveExtension where
  app k := (MorphismProperty.functorialFactorizationData (MorphismProperty.monomorphisms C)
      (MorphismProperty.monomorphisms C).rlp).i.app (D.arrowToZero.obj k)
  naturality _ _ a := (MorphismProperty.functorialFactorizationData
    (MorphismProperty.monomorphisms C) (MorphismProperty.monomorphisms C).rlp).i.naturality
      (D.arrowToZero.map a)

instance (k : K) : Injective (D.injectiveExtension.obj k) :=
  inferInstanceAs (Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp
    (0 : D.obj k ⟶ 0)).Z)

instance (k : K) : Mono (D.toInjectiveExtension.app k) :=
  inferInstanceAs (Mono (IsGrothendieckAbelian.monoMapFactorizationDataRlp
    (0 : D.obj k ⟶ 0)).i)

end InjectiveFunctor

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max w v}] [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]

section Sections

variable {K : Type (max w v)} [SmallCategory K]
  {F : K ⥤ Sheaf J AddCommGrpCat.{max w v}} {c : Cocone F}

/-- The presheaf colimit of a diagram of abelian sheaves, with its comparison map to the sheaf
colimit: the comparison is locally surjective and locally injective, being the sheafification
map. -/
lemma exists_presheafColimit_ab (hc : IsColimit c) :
    ∃ (E : Cocone (F ⋙ sheafToPresheaf _ _)) (_ : IsColimit E) (φ : E.pt ⟶ c.pt.obj),
      Presheaf.IsLocallySurjective J φ ∧ Presheaf.IsLocallyInjective J φ ∧
      ∀ k, E.ι.app k ≫ φ = (c.ι.app k).hom := by
  let E := colimit.cocone (F ⋙ sheafToPresheaf J AddCommGrpCat.{max w v})
  let hE : IsColimit E := colimit.isColimit _
  let e := (Sheaf.isColimitSheafifyCocone E hE).coconePointUniqueUpToIso hc
  refine ⟨E, hE, toSheafify _ E.pt ≫ e.hom.hom, ?_, ?_, fun k ↦ ?_⟩
  · infer_instance
  · infer_instance
  · rw [← Category.assoc, ← Sheaf.sheafifyCocone_ι_app_val,
      ← ObjectProperty.FullSubcategory.comp_hom,
      IsColimit.comp_coconePointUniqueUpToIso_hom]

variable [IsFiltered K]

/-- **Sections of a filtered colimit of abelian sheaves are locally lifted.** Every section of
`c.pt` over `W` is, on the members of a covering sieve of `W`, the image of a section of some
`F k`. -/
lemma exists_mem_forall_exists_app_eq_of_isColimit (hc : IsColimit c) {W : C}
    (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ J W, ∀ ⦃V : C⦄ (f : V ⟶ W), R f →
      ∃ (k : K) (t : (F.obj k).obj.obj (op V)),
        (c.ι.app k).hom.app (op V) t = c.pt.obj.map f.op s := by
  obtain ⟨E, hE, φ, hs, -, hφ⟩ := exists_presheafColimit_ab hc
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  obtain ⟨k, t, rfl⟩ := AddCommGrpCat.exists_ι_apply_eq_of_isColimit hEV p
  refine ⟨k, t, Eq.trans ?_ hp⟩
  rw [← hφ k]
  rfl

/-- **Sections of a filtered colimit of abelian sheaves are locally separated.** A section of
`F k` over `W` which vanishes in `c.pt` vanishes, on the members of a covering sieve of `W`, in
some later `F k'`. -/
lemma exists_mem_forall_exists_map_eq_zero_of_isColimit (hc : IsColimit c) {W : C} {k : K}
    (t : (F.obj k).obj.obj (op W)) (h : (c.ι.app k).hom.app (op W) t = 0) :
    ∃ R ∈ J W, ∀ ⦃V : C⦄ (f : V ⟶ W), R f →
      ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op V) ((F.obj k).obj.map f.op t) = 0 := by
  obtain ⟨E, hE, φ, -, hi, hφ⟩ := exists_presheafColimit_ab hc
  have h' : φ.app (op W) ((E.ι.app k).app (op W) t) = φ.app (op W) 0 := by
    rw [map_zero, ← h, ← hφ k]
    rfl
  refine ⟨_, Presheaf.equalizerSieve_mem _ φ _ _ h', fun V f hf ↦ ?_⟩
  have hEV := isColimitOfPreserves ((CategoryTheory.evaluation _ _).obj (op V)) hE
  refine AddCommGrpCat.exists_map_eq_zero_of_isColimit hEV _ ?_
  refine (NatTrans.naturality_apply (E.ι.app k) f.op t).trans ?_
  exact hf.trans (map_zero _)

/-- **Sections over a quasi-compact object of a filtered colimit vanish at a finite stage.**
Let `W` be an object such that every covering sieve of `W` contains a finite family generating
a covering sieve. A section of `F k` over `W` which vanishes in `c.pt` vanishes in some later
`F k'`. -/
theorem exists_map_eq_zero_of_isColimit_of_finite (hc : IsColimit c) {W : C}
    (hW : ∀ R ∈ J W, ∃ (n : ℕ) (U : Fin n → Over W), (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J W)
    {k : K} (t : (F.obj k).obj.obj (op W)) (h : (c.ι.app k).hom.app (op W) t = 0) :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = 0 := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_map_eq_zero_of_isColimit hc t h
  obtain ⟨n, U, hUR, hUJ⟩ := hW R hR
  choose k₁ a₁ ha₁ using fun i ↦ hloc _ (hUR i)
  obtain ⟨k', A, b, hb⟩ := IsFiltered.exists_comp_eq_of_finite a₁
  refine ⟨k', A, (isSheafFor_ofArrows (F.obj k') _ hUJ).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨i⟩
  change (F.obj k').obj.map (U i).hom.op _ = (F.obj k').obj.map (U i).hom.op _
  rw [map_zero, ← NatTrans.naturality_apply, ← hb i, F.map_comp]
  change (F.map (b i)).hom.app _ ((F.map (a₁ i)).hom.app _ _) = 0
  rw [ha₁ i, map_zero]

/-- **Sections over a quasi-compact object of a filtered colimit are separated at a finite
stage.** Two sections of `F k` over `W` with the same image in `c.pt` agree in some later
`F k'`. -/
theorem exists_map_eq_of_isColimit_of_finite (hc : IsColimit c) {W : C}
    (hW : ∀ R ∈ J W, ∃ (n : ℕ) (U : Fin n → Over W), (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J W)
    {k : K} (t t' : (F.obj k).obj.obj (op W))
    (h : (c.ι.app k).hom.app (op W) t = (c.ι.app k).hom.app (op W) t') :
    ∃ (k' : K) (a : k ⟶ k'), (F.map a).hom.app (op W) t = (F.map a).hom.app (op W) t' := by
  obtain ⟨k', a, ha⟩ := exists_map_eq_zero_of_isColimit_of_finite hc hW (t - t')
    (by rw [map_sub, h, sub_self])
  exact ⟨k', a, sub_eq_zero.1 (by rw [← map_sub, ha])⟩

variable [∀ V : C, HasFiniteProducts (Over V)]

/-- **Sections over members of `B` of a filtered colimit come from a finite stage.** Let `B` be
a class of objects such that every covering sieve of a member `V` of `B` contains a finite
family generating a covering sieve, whose Čech nerve lies in `B`. Every section of `c.pt` over
a member `W` of `B` is the image of a section of some `F k` (Stacks 0738). -/
theorem exists_app_eq_of_isColimit_of_finite (hc : IsColimit c) (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {W : C} (hW : B W) (s : c.pt.obj.obj (op W)) :
    ∃ (k : K) (t : (F.obj k).obj.obj (op W)), (c.ι.app k).hom.app (op W) t = s := by
  obtain ⟨R, hR, hloc⟩ := exists_mem_forall_exists_app_eq_of_isColimit hc s
  obtain ⟨n, U, hUB, hUR, hUJ⟩ := hcov W hW R hR
  choose k₁ t₁ ht₁ using fun i ↦ hloc _ (hUR i)
  obtain ⟨k, ⟨b⟩⟩ := IsFiltered.exists_cocone_of_finite k₁
  -- the local lifts, as a Čech `0`-cochain of `F k`
  let t₂ (i : Fin n) : (F.obj k).obj.obj (op (U i).left) := (F.map (b i)).hom.app _ (t₁ i)
  have ht₂ (i : Fin n) : (c.ι.app k).hom.app _ (t₂ i) = c.pt.obj.map (U i).hom.op s := by
    rw [← ht₁ i, ← c.w (b i)]
    rfl
  let a : ((cechComplex U).obj (F.obj k).obj).X 0 := fun z ↦
    (F.obj k).obj.map (Pi.π (fun l ↦ U (z l)) 0).left.op (t₂ (z 0))
  have ha (z : Fin 1 → Fin n) : ((cechComplex U).map (c.ι.app k).hom).f 0 a z =
      c.pt.obj.map (cechNerveObj U z).hom.op s := by
    rw [cechComplex_map_f_apply, NatTrans.naturality_apply, ht₂]
    change c.pt.obj.map _ (c.pt.obj.map _ s) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w]
  -- its Čech differential vanishes at a later stage
  have hd (y : Fin 2 → Fin n) : ∃ (k' : K) (A : k ⟶ k'),
      (F.map A).hom.app _ (((cechComplex U).obj (F.obj k).obj).d 0 1 a y) = 0 := by
    refine exists_map_eq_zero_of_isColimit_of_finite hc (fun R hR ↦ ?_) _ ?_
    · obtain ⟨m, U', -, hU'R, hU'J⟩ := hcov _ (hUB 1 y) R hR
      exact ⟨m, U', hU'R, hU'J⟩
    · rw [← cechComplex_map_f_apply, cechComplex_map_f_d_apply]
      exact congrFun (cechComplex_d_zero_restrict U _ s _ ha) y
  choose k₂ a₂ ha₂ using hd
  obtain ⟨k', A, b', hb'⟩ := IsFiltered.exists_comp_eq_of_finite a₂
  let a' := ((cechComplex U).map (F.map A).hom).f 0 a
  have ha' : ((cechComplex U).obj (F.obj k').obj).d 0 1 a' = 0 := by
    funext y
    rw [← cechComplex_map_f_d_apply, cechComplex_map_f_apply, ← hb' y, F.map_comp]
    change (F.map (b' y)).hom.app _ ((F.map (a₂ y)).hom.app _ _) = 0
    rw [ha₂ y, map_zero]
  -- the members of the Čech nerve in degree `0` generate a covering sieve
  have hcov' : Sieve.ofArrows (fun z : Fin 1 → Fin n ↦ (cechNerveObj U z).left)
      (fun z ↦ (cechNerveObj U z).hom) ∈ J W := by
    refine J.superset_covering (fun Y g hg ↦ ?_) hUJ
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, h ≫ (Pi.lift fun _ ↦ 𝟙 (U i)).left, ?_⟩
    rw [Category.assoc, Over.w]
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_ofArrows (F.obj k') _ hcov') (fun z ↦ a' z)
    fun z z' Z g₁ g₂ hg ↦ map_eq_of_cechComplex_d_zero U _ _ ha' z z' g₁ g₂ hg
  refine ⟨k', σ, (isSheafFor_ofArrows c.pt _ hcov').isSeparatedFor.ext fun Y f ⟨z⟩ ↦ ?_⟩
  change c.pt.obj.map _ ((c.ι.app k').hom.app _ σ) = c.pt.obj.map _ s
  rw [← ha z, cechComplex_map_f_apply]
  erw [← NatTrans.naturality_apply (c.ι.app k').hom, hσ z]
  rw [← c.w A]
  rfl

end Sections

section Cech

variable [∀ V : C, HasFiniteProducts (Over V)] {K : Type (max w v)} [SmallCategory K]
  [IsFiltered K] {F : K ⥤ Sheaf J AddCommGrpCat.{max w v}} {c : Cocone F}

/-- Let `c` be a colimit of a filtered diagram of abelian sheaves `F k` whose Čech complexes on
a finite family `U` over `V` are exact in positive degrees. If the Čech nerve of `U` lies in a
class `B` of objects as in `CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite`, then
the Čech complex of `c.pt` on `U` is exact in positive degrees: Čech cochains of `c.pt` come
from a finite stage, and so do the relations between them. -/
lemma exactAt_cechComplex_of_isColimit (hc : IsColimit c) (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {V : C} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left)
    (q : ℕ) (hF : ∀ k, ((cechComplex U).obj (F.obj k).obj).ExactAt (q + 1)) :
    ((cechComplex U).obj c.pt.obj).ExactAt (q + 1) := by
  rw [exactAt_cechComplex_iff]
  intro z hz
  -- the cochain `z` comes from a finite stage `k`
  choose k₁ t₁ ht₁ using fun y : Fin (q + 2) → Fin n ↦
    exists_app_eq_of_isColimit_of_finite hc B hcov (hU (q + 1) y) (z y)
  obtain ⟨k, ⟨b⟩⟩ := IsFiltered.exists_cocone_of_finite k₁
  let z' : ((cechComplex U).obj (F.obj k).obj).X (q + 1) := fun y ↦
    (F.map (b y)).hom.app _ (t₁ y)
  have hz' : ((cechComplex U).map (c.ι.app k).hom).f (q + 1) z' = z := by
    funext y
    rw [cechComplex_map_f_apply, ← ht₁ y, ← c.w (b y)]
    rfl
  -- its differential vanishes at a later stage `k'`
  have hd (y : Fin (q + 3) → Fin n) : ∃ (k' : K) (a : k ⟶ k'),
      (F.map a).hom.app _ (((cechComplex U).obj (F.obj k).obj).d (q + 1) (q + 2) z' y) = 0 := by
    refine exists_map_eq_zero_of_isColimit_of_finite hc (fun R hR ↦ ?_) _ ?_
    · obtain ⟨m, U', -, hU'R, hU'J⟩ := hcov _ (hU (q + 2) y) R hR
      exact ⟨m, U', hU'R, hU'J⟩
    · rw [← cechComplex_map_f_apply, cechComplex_map_f_d_apply, hz']
      change ((cechComplex U).obj c.pt.obj).d (q + 1) (q + 2) z y = 0
      rw [hz]
      rfl
  choose k₂ a₂ ha₂ using hd
  obtain ⟨k', A, b', hb'⟩ := IsFiltered.exists_comp_eq_of_finite a₂
  let z'' := ((cechComplex U).map (F.map A).hom).f (q + 1) z'
  have hz'' : ((cechComplex U).obj (F.obj k').obj).d (q + 1) (q + 2) z'' = 0 := by
    funext y
    rw [← cechComplex_map_f_d_apply, cechComplex_map_f_apply, ← hb' y, F.map_comp]
    change (F.map (b' y)).hom.app _ ((F.map (a₂ y)).hom.app _ _) = 0
    rw [ha₂ y, map_zero]
  obtain ⟨e, he⟩ := (exactAt_cechComplex_iff U _ q).1 (hF k') z'' hz''
  refine ⟨((cechComplex U).map (c.ι.app k').hom).f q e,
    (cechComplex_map_f_d_apply U (c.ι.app k').hom q e).symm.trans ?_⟩
  rw [he, ← hz']
  funext y
  rw [cechComplex_map_f_apply, cechComplex_map_f_apply, ← c.w A]
  rfl

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})] {T : C}

/-- A filtered colimit of injective abelian sheaves has no higher cohomology, for a class `B`
of objects containing a terminal object `T` as in the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`. -/
theorem subsingleton_H_succ_of_isColimit_of_injective (hT : IsTerminal T) (B : C → Prop)
    (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    [∀ k, Injective (F.obj k)] (hc : IsColimit c) (q : ℕ) :
    Subsingleton (Sheaf.H c.pt (q + 1)) :=
  Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B hBT hcov c.pt
    (fun _ _ _ U hU _ q ↦ exactAt_cechComplex_of_isColimit hc B hcov U hU q
      fun k ↦ Sheaf.exactAt_cechComplex_of_injective (F.obj k) U q) q

end Cech

section DimensionShifting

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})] {K : Type (max w v)} [SmallCategory K]
  [IsFiltered K]

/-- The pointwise short complex `D k ⟶ I k ⟶ Q k` of a composable pair of morphisms of
diagrams with vanishing composite. -/
noncomputable abbrev shortComplexApp {D I Q : K ⥤ Sheaf J AddCommGrpCat.{max w v}}
    (ι : D ⟶ I) (π : I ⟶ Q) (h : ι ≫ π = 0) (k : K) :
    ShortComplex (Sheaf J AddCommGrpCat.{max w v}) :=
  ShortComplex.mk (ι.app k) (π.app k) (by rw [← NatTrans.comp_app, h, NatTrans.app_zero])

/-- The transition morphisms between the pointwise short complexes
`CategoryTheory.Sheaf.shortComplexApp`. -/
noncomputable def shortComplexAppMap {D I Q : K ⥤ Sheaf J AddCommGrpCat.{max w v}}
    (ι : D ⟶ I) (π : I ⟶ Q) (h : ι ≫ π = 0) {k k' : K} (a : k ⟶ k') :
    shortComplexApp ι π h k ⟶ shortComplexApp ι π h k' where
  τ₁ := D.map a
  τ₂ := I.map a
  τ₃ := Q.map a
  comm₁₂ := ι.naturality a
  comm₂₃ := π.naturality a

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}] in
/-- **Dimension shifting for filtered colimits.** Let `0 → D → I → Q → 0` be a short exact
sequence of diagrams of abelian sheaves with `I` pointwise injective, mapping to a short exact
sequence `0 → c.pt → cI.pt → cQ.pt → 0` of cocone points with `H^{n + 1}(cI.pt) = 0`. If
`Hⁿ(cI.pt)` is covered by the `Hⁿ(I k)` and `colim_k Hⁿ(Q k) ⟶ Hⁿ(cQ.pt)` is bijective, then
`colim_k H^{n + 1}(D k) ⟶ H^{n + 1}(c.pt)` is bijective. -/
lemma H_map_isColimit_succ_of_shortExact {D I Q : K ⥤ Sheaf J AddCommGrpCat.{max w v}}
    (ι : D ⟶ I) (π : I ⟶ Q) (h : ι ≫ π = 0) (hS : ∀ k, (shortComplexApp ι π h k).ShortExact)
    [∀ k, Injective (I.obj k)] {c : Cocone D} {cI : Cocone I} {cQ : Cocone Q}
    (f : c.pt ⟶ cI.pt) (g : cI.pt ⟶ cQ.pt) (hfg : f ≫ g = 0)
    (hS' : (ShortComplex.mk f g hfg).ShortExact)
    (hf : ∀ k, c.ι.app k ≫ f = ι.app k ≫ cI.ι.app k)
    (hg : ∀ k, cI.ι.app k ≫ g = π.app k ≫ cQ.ι.app k) (n : ℕ)
    (hI : Subsingleton (Sheaf.H cI.pt (n + 1)))
    (surjI : ∀ x : Sheaf.H cI.pt n, ∃ (k : K) (y : Sheaf.H (I.obj k) n),
      Sheaf.H.map (cI.ι.app k) n y = x)
    (surjQ : ∀ x : Sheaf.H cQ.pt n, ∃ (k : K) (y : Sheaf.H (Q.obj k) n),
      Sheaf.H.map (cQ.ι.app k) n y = x)
    (injQ : ∀ (k : K) (y : Sheaf.H (Q.obj k) n), Sheaf.H.map (cQ.ι.app k) n y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (Q.map a) n y = 0) :
    (∀ x : Sheaf.H c.pt (n + 1), ∃ (k : K) (y : Sheaf.H (D.obj k) (n + 1)),
      Sheaf.H.map (c.ι.app k) (n + 1) y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) (n + 1)), Sheaf.H.map (c.ι.app k) (n + 1) y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) (n + 1) y = 0 := by
  let S' := ShortComplex.mk f g hfg
  -- the morphisms from the pointwise short exact sequences to the colimit one
  let φ (k : K) : shortComplexApp ι π h k ⟶ S' :=
    { τ₁ := c.ι.app k
      τ₂ := cI.ι.app k
      τ₃ := cQ.ι.app k
      comm₁₂ := hf k
      comm₂₃ := hg k }
  have : Subsingleton (Sheaf.H S'.X₂ (n + 1)) := hI
  refine ⟨fun x ↦ ?_, fun k y hy ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := Sheaf.H.δSucc_surjective hS' n x
    obtain ⟨k, z', rfl⟩ := surjQ z
    exact ⟨k, Sheaf.H.δSucc (hS k) n z', Sheaf.H.map_δSucc (hS k) hS' (φ k) n z'⟩
  · have : Subsingleton (Sheaf.H (shortComplexApp ι π h k).X₂ (n + 1)) :=
      inferInstanceAs (Subsingleton (Sheaf.H (I.obj k) (n + 1)))
    obtain ⟨w, rfl⟩ := Sheaf.H.δSucc_surjective (hS k) n y
    have hw : Sheaf.H.δSucc hS' n (Sheaf.H.map (cQ.ι.app k) n w) = 0 := by
      rw [← hy]
      exact (Sheaf.H.map_δSucc (hS k) hS' (φ k) n w).symm
    obtain ⟨v, hv⟩ := ((Sheaf.H.exact_map_δSucc hS' n) _).1 hw
    obtain ⟨k₁, v₁, rfl⟩ := surjI v
    -- the images of `w` and of `v₁` agree in `Hⁿ(cQ.pt)`, hence at a finite stage
    let m := IsFiltered.max k k₁
    let a : k ⟶ m := IsFiltered.leftToMax k k₁
    let b : k₁ ⟶ m := IsFiltered.rightToMax k k₁
    have hm : Sheaf.H.map (cQ.ι.app m) n
        (Sheaf.H.map (Q.map a) n w - Sheaf.H.map (Q.map b) n (Sheaf.H.map (π.app k₁) n v₁)) =
          0 := by
      simp only [map_sub, sub_eq_zero, ← Sheaf.H.map_comp_apply,
        Category.assoc, cQ.w, ← hg]
      rw [Sheaf.H.map_comp_apply]
      exact hv.symm
    obtain ⟨k', a', ha'⟩ := injQ m _ hm
    refine ⟨k', a ≫ a', ?_⟩
    change Sheaf.H.map (shortComplexAppMap ι π h (a ≫ a')).τ₁ (n + 1) _ = 0
    rw [Sheaf.H.map_δSucc (hS k) (hS k') (shortComplexAppMap ι π h (a ≫ a')) n w]
    change Sheaf.H.δSucc (hS k') n (Sheaf.H.map (Q.map (a ≫ a')) n w) = 0
    simp only [map_sub, sub_eq_zero, ← Sheaf.H.map_comp_apply,
      Category.assoc, ← Q.map_comp, ← π.naturality] at ha'
    exact ((Sheaf.H.exact_map_δSucc (hS k') n) _).2
      ⟨_, by simpa only [Sheaf.H.map_comp_apply] using ha'.symm⟩

variable [∀ V : C, HasFiniteProducts (Over V)] {T : C}

/-- **Sections over `T` commute with filtered colimits**, in terms of `H⁰`, if every covering
sieve of `T` contains a finite family generating a covering sieve, whose Čech nerve lies in a
class `B` as in `CategoryTheory.Sheaf.exists_app_eq_of_isColimit_of_finite`. -/
lemma H_zero_map_isColimit (hT : IsTerminal T) (B : C → Prop) (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {D : K ⥤ Sheaf J AddCommGrpCat.{max w v}} {c : Cocone D} (hc : IsColimit c) :
    (∀ x : Sheaf.H c.pt 0, ∃ (k : K) (y : Sheaf.H (D.obj k) 0),
      Sheaf.H.map (c.ι.app k) 0 y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) 0), Sheaf.H.map (c.ι.app k) 0 y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) 0 y = 0 := by
  refine ⟨fun x ↦ ?_, fun k y hy ↦ ?_⟩
  · obtain ⟨k, t, ht⟩ := exists_app_eq_of_isColimit_of_finite hc B hcov hBT
      (Sheaf.H.equiv₀ c.pt hT x)
    refine ⟨k, (Sheaf.H.equiv₀ _ hT).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality, ht]
    exact (Sheaf.H.equiv₀ c.pt hT).symm_apply_apply x
  · have h0 : (c.ι.app k).hom.app (op T) (Sheaf.H.equiv₀ _ hT y) = 0 := by
      rw [Sheaf.H.equiv₀_naturality, hy, map_zero]
    obtain ⟨k', a, ha⟩ := exists_map_eq_zero_of_isColimit_of_finite hc (fun R hR ↦ by
      obtain ⟨m, U', -, hU'R, hU'J⟩ := hcov _ hBT R hR
      exact ⟨m, U', hU'R, hU'J⟩) _ h0
    refine ⟨k', a, (Sheaf.H.equiv₀ _ hT).injective ?_⟩
    rw [← Sheaf.H.equiv₀_naturality, ha, map_zero]

end DimensionShifting

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max w v})] [∀ V : C, HasFiniteProducts (Over V)]
  [IsGrothendieckAbelian.{max w v} (Sheaf J AddCommGrpCat.{max w v})] {T : C}

/-- **Cohomology commutes with filtered colimits.** Let `B` be a class of objects of the site
containing a terminal object `T`, such that every covering sieve of a member `V` of `B` contains
a finite family `U` generating a covering sieve, whose Čech nerve lies in `B`. Let `c` be a
colimit cocone of a filtered diagram `D` of abelian sheaves indexed by a small category. Then
for every `q` the canonical map `colim_k Hᵠ(D_k) ⟶ Hᵠ(c.pt)` is bijective, spelled out
elementwise.

Degree zero is `CategoryTheory.Sheaf.H_zero_map_isColimit`. In higher degrees, we embed `D` into
the diagram of injective sheaves `D.injectiveExtension` with cokernel `Q`; since filtered
colimits are exact, the colimit sequence `0 → c.pt → colim I → colim Q → 0` is short exact,
`colim I` has no higher cohomology
(`CategoryTheory.Sheaf.subsingleton_H_succ_of_isColimit_of_injective`), and we conclude by
`CategoryTheory.Sheaf.H_map_isColimit_succ_of_shortExact`. -/
@[stacks 03Q6]
theorem H_map_isColimit_of_isFiltered_small (hT : IsTerminal T) (B : C → Prop) (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {K : Type (max w v)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf J AddCommGrpCat.{max w v}} {c : Cocone D} (hc : IsColimit c) (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (k : K) (y : Sheaf.H (D.obj k) q),
      Sheaf.H.map (c.ι.app k) q y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) q), Sheaf.H.map (c.ι.app k) q y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) q y = 0 := by
  induction q generalizing D c with
  | zero => exact H_zero_map_isColimit hT B hBT hcov hc
  | succ n ih =>
    let I := D.injectiveExtension
    let ι := D.toInjectiveExtension
    let π := cokernel.π ι
    have h : ι ≫ π = 0 := cokernel.condition ι
    have : Mono ι := NatTrans.mono_of_mono_app ι
    have hSf : (ShortComplex.mk ι π h).ShortExact :=
      .mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
    have hS (k : K) : (shortComplexApp ι π h k).ShortExact :=
      hSf.map_of_exact ((CategoryTheory.evaluation K _).obj k)
    let f : c.pt ⟶ colimit I := hc.desc ((Cocone.precompose ι).obj (colimit.cocone I))
    let g : colimit I ⟶ colimit (cokernel ι) := colimMap π
    have hf (k : K) : c.ι.app k ≫ f = ι.app k ≫ colimit.ι I k := hc.fac _ k
    have hg (k : K) : colimit.ι I k ≫ g = π.app k ≫ colimit.ι _ k := ι_colimMap π k
    have hfg : f ≫ g = 0 := hc.hom_ext fun k ↦ by
      rw [reassoc_of% (hf k), hg, ← NatTrans.comp_app_assoc, h, NatTrans.app_zero, zero_comp,
        comp_zero]
    let e₁ : colimit D ≅ c.pt := (colimit.isColimit D).coconePointUniqueUpToIso hc
    have hS' : (ShortComplex.mk f g hfg).ShortExact := by
      let e : (ShortComplex.mk ι π h).map colim ≅ ShortComplex.mk f g hfg :=
        ShortComplex.isoMk e₁ (Iso.refl _) (Iso.refl _) (colimit.hom_ext fun k ↦ ?_)
          (colimit.hom_ext fun k ↦ ?_)
      · exact ShortComplex.shortExact_of_iso e (hSf.map_of_exact colim)
      · simp only [colimit.comp_coconePointUniqueUpToIso_hom_assoc, hf, ShortComplex.map_f,
          colim_map, Iso.refl_hom, Category.comp_id, ι_colimMap, e₁]
        rfl
      · simp only [Iso.refl_hom, Category.id_comp, ι_colimMap, ShortComplex.map_g, colim_map,
          Category.comp_id, g]
    exact H_map_isColimit_succ_of_shortExact ι π h hS f g hfg hS' hf hg n
      (subsingleton_H_succ_of_isColimit_of_injective hT B hBT hcov (colimit.isColimit I) n)
      (ih (colimit.isColimit I)).1 (ih (colimit.isColimit _)).1 (ih (colimit.isColimit _)).2

/-- **Vanishing of cohomology passes to filtered colimits.** In the situation of
`CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small`, if `Hᵠ(D_k) = 0` for every `k`,
then `Hᵠ(c.pt) = 0`. -/
theorem subsingleton_H_of_isColimit_of_isFiltered (hT : IsTerminal T) (B : C → Prop)
    (hBT : B T)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    {K : Type (max w v)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf J AddCommGrpCat.{max w v}} {c : Cocone D} (hc : IsColimit c) (q : ℕ)
    (hD : ∀ k, Subsingleton (Sheaf.H (D.obj k) q)) :
    Subsingleton (Sheaf.H c.pt q) := by
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨k, y, rfl⟩ := (H_map_isColimit_of_isFiltered_small hT B hBT hcov hc q).1 x
  rw [Subsingleton.elim y 0, map_zero]

end CategoryTheory.Sheaf
