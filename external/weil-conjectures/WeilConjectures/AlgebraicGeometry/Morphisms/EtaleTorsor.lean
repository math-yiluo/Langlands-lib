/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Torsors and étale `H^1`

Let `Y` be a scheme and `M` a finite abelian group. An `M`-torsor on the small étale site of
`Y` is the same thing as a finite étale surjective `Y`-scheme `P` carrying a simply
transitive action of `M` over `Y`; that is the form in which the notion is recorded here, as
`AlgebraicGeometry.Scheme.EtaleTorsor`. Simple transitivity is the statement that the
canonical morphism `∐_{m ∈ M} P ⟶ P ×_Y P` sending the `m`-th summand by `(m +ᵥ -, id)` is an
isomorphism, which is available because `M` is finite, hence `Small.{u}`.

Isomorphism of torsors is an equivalence relation
(`AlgebraicGeometry.Scheme.EtaleTorsor.setoid`), and the quotient by it is in canonical
bijection with `H^1(Y_ét, M)`, the first sheaf cohomology of the constant sheaf with value `M`.
A torsor has class `0` exactly when its structure morphism admits a section.

## Implementation notes

Naturality of the bijection in `Y` is stated, in terms of the pullback map
`AlgebraicGeometry.Etale.cohomologyMap` on sheaf cohomology, as
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`. The criterion
that, for `Y` connected and `M = ℤ/dℤ`, the torsor attached to a class is connected exactly when
the corresponding homomorphism out of the étale fundamental group is surjective is not
formalized, since Mathlib has no étale fundamental group.

A `AlgebraicGeometry.Scheme.GaloisCover` is not required to have connected total space; the
quotient `P / G ≅ Y` is a consequence of the torsor condition and is not recorded.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor`: an `M`-torsor over a scheme `Y`.
- `AlgebraicGeometry.Scheme.GaloisCover`: a finite étale Galois cover with group `G`, that is,
  a finite étale `G`-torsor, for a finite group `G` acting on the left.
- `AlgebraicGeometry.Scheme.EtaleTorsor.IsIsomorphic` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.setoid`: the isomorphism relation on torsors, and
  the fact that it is an equivalence relation.
- `AlgebraicGeometry.Scheme.EtaleTorsor.toSheafTorsor`: the functor of points `U ↦ Hom_Y(U, P)`
  of a torsor, as a torsor under the constant sheaf `M` on the small étale site.
- `AlgebraicGeometry.Scheme.EtaleTorsor.classH1`: the canonical map from isomorphism classes of
  `M`-torsors to `H¹(Y_ét, M)`, sending `P` to the class of its sheaf torsor.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.toSheafTorsor_equiv_toSheafTorsor_iff` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.nonempty_toSheafTorsor_sheaf_obj_iff`: two torsors are
  isomorphic if and only if their sheaf torsors are, and the global sections of the sheaf torsor
  are the sections of the structure morphism.
- `AlgebraicGeometry.Scheme.EtaleTorsor.injective_classH1` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.classH1_eq_zero_iff`: the canonical class map is
  injective, and the class of a torsor vanishes exactly when the torsor has a section.
- The bijectivity of the class map, `AlgebraicGeometry.Scheme.EtaleTorsor.bijective_classH1`, and
  the statements `exists_sheafTorsor` and `exists_quotientEquivSheafH` are in
  `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent`, since they rest on effective
  étale descent.

## References

- Stacks Project, Tag `02NE`, <https://stacks.math.columbia.edu/tag/02NE>
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

variable (M : Type (u + 1)) [AddCommGroup M] [Finite M]

/-- An `M`-torsor over a scheme `Y`: a finite étale surjective `Y`-scheme with a simply
transitive action of the finite abelian group `M`.

Simple transitivity is expressed by the isomorphism `M × P ≅ P ×_Y P`, in the form that the
morphism `∐_{m ∈ M} P ⟶ P ×_Y P` whose `m`-th component is `(m +ᵥ -, id)` is an isomorphism. -/
structure Scheme.EtaleTorsor (Y : Scheme.{u}) where
  /-- the total space of the torsor -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  [surjective : Surjective π]
  /-- the action of `M` on `P` over `Y` -/
  vadd : M → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  vadd_π (m : M) : vadd m ≫ π = π
  /-- the zero of `M` acts as the identity -/
  zero_vadd : vadd 0 = 𝟙 P
  /-- the action is additive in the acting variable -/
  add_vadd (m n : M) : vadd (m + n) = vadd m ≫ vadd n
  /-- the action is simply transitive: `∐_{m ∈ M} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun m : M ↦ pullback.lift (f := π) (g := π) (vadd m) (𝟙 P) (by simp [vadd_π]))

namespace Scheme.EtaleTorsor

variable {M} {Y : Scheme.{u}}

/-- Two `M`-torsors over `Y` are isomorphic when their total spaces are isomorphic over `Y`
by an isomorphism commuting with the `M`-actions. -/
def IsIsomorphic (t₁ t₂ : EtaleTorsor M Y) : Prop :=
  ∃ φ : t₁.P ≅ t₂.P, φ.hom ≫ t₂.π = t₁.π ∧
    ∀ m : M, t₁.vadd m ≫ φ.hom = φ.hom ≫ t₂.vadd m

lemma isIsomorphic_refl (t : EtaleTorsor M Y) : t.IsIsomorphic t :=
  ⟨Iso.refl _, by simp, by simp⟩

lemma IsIsomorphic.symm {t₁ t₂ : EtaleTorsor M Y} (h : t₁.IsIsomorphic t₂) :
    t₂.IsIsomorphic t₁ := by
  obtain ⟨φ, hπ, hv⟩ := h
  refine ⟨φ.symm, ?_, fun m ↦ ?_⟩
  · rw [Iso.symm_hom, ← hπ, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]

lemma IsIsomorphic.trans {t₁ t₂ t₃ : EtaleTorsor M Y} (h₁ : t₁.IsIsomorphic t₂)
    (h₂ : t₂.IsIsomorphic t₃) : t₁.IsIsomorphic t₃ := by
  obtain ⟨φ, hπ, hv⟩ := h₁
  obtain ⟨ψ, hπ', hv'⟩ := h₂
  refine ⟨φ ≪≫ ψ, ?_, fun m ↦ ?_⟩
  · rw [Iso.trans_hom, Category.assoc, hπ', hπ]
  · simp only [Iso.trans_hom, ← Category.assoc, hv]
    simp only [Category.assoc, hv']

lemma isIsomorphic_equivalence : Equivalence (IsIsomorphic (M := M) (Y := Y)) :=
  ⟨isIsomorphic_refl, IsIsomorphic.symm, IsIsomorphic.trans⟩

variable (M Y) in
/-- Isomorphism of `M`-torsors over `Y` as a setoid, so that the isomorphism classes are
the quotient `Quotient (EtaleTorsor.setoid M Y)`. -/
instance setoid : Setoid (EtaleTorsor M Y) := ⟨IsIsomorphic, isIsomorphic_equivalence⟩

/-! ### The sheaf torsor of a torsor -/

section SheafTorsor

/-- The total space of an `M`-torsor over `Y`, as an object of the small étale site of `Y`. -/
abbrev toEtale (t : EtaleTorsor M Y) : Y.Etale :=
  have := t.etale
  Etale.mk t.π

lemma vadd_comp_sigmaDesc (t : EtaleTorsor M Y) {Z : Scheme.{u}} (ψ : Z ⟶ t.P) (m : M) :
    ψ ≫ Sigma.ι (fun _ : M ↦ t.P) m ≫ Sigma.desc (fun m : M ↦ pullback.lift (f := t.π)
      (g := t.π) (t.vadd m) (𝟙 t.P) (by simp [t.vadd_π])) =
        pullback.lift (ψ ≫ t.vadd m) ψ (by simp [t.vadd_π]) := by
  ext <;> simp

/-- The action of `M` on a torsor is free: if `ψ ≫ m = ψ ≫ n` for a morphism `ψ` out of a
nonempty scheme, then `m = n`. -/
lemma eq_of_comp_vadd_eq (t : EtaleTorsor M Y) {Z : Scheme.{u}} (ψ : Z ⟶ t.P) {m n : M}
    (h : ψ ≫ t.vadd m = ψ ≫ t.vadd n) (z : Z) : m = n := by
  have := t.isIso_sigmaDesc
  have h' : ψ ≫ Sigma.ι (fun _ : M ↦ t.P) m = ψ ≫ Sigma.ι (fun _ : M ↦ t.P) n := by
    rw [← cancel_mono (Sigma.desc fun m : M ↦ pullback.lift (f := t.π) (g := t.π) (t.vadd m)
      (𝟙 t.P) (by simp [t.vadd_π])), Category.assoc, Category.assoc, vadd_comp_sigmaDesc,
      vadd_comp_sigmaDesc]
    congr 1
  have hz := congr_arg (fun g : Z ⟶ ∐ fun _ : M ↦ t.P ↦ g.base z) h'
  simp only [Scheme.Hom.comp_apply] at hz
  exact congr_arg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 hz)

omit [Finite M] in
/-- Morphisms in the small étale site are determined by their underlying morphisms of
schemes. -/
lemma etaleHom_ext {U V : Y.Etale} {f g : U ⟶ V} (h : f.left = g.left) : f = g :=
  (Etale.forget Y ⋙ Over.forget Y).map_injective h

variable [TopologicalSpace M] [DiscreteTopology M]

/-- The action of a continuous function `f : U → M` on a morphism `φ : U ⟶ P` of étale
`Y`-schemes into the total space of a torsor: on the open fibre `f⁻¹(m)` it is `φ` followed by
the action of `m`. -/
noncomputable def smulHom (t : EtaleTorsor M Y) {U : Y.Etale} (f : C(U.left, M))
    (φ : U ⟶ t.toEtale) : U ⟶ t.toEtale :=
  MorphismProperty.Over.homMk (U.left.glueOfContinuousMap f fun m ↦ φ.left ≫ t.vadd m) (by
    rw [Scheme.glueOfContinuousMap_comp]
    refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
    rw [Category.assoc]
    exact congr_arg _ ((congr_arg (φ.left ≫ ·) (t.vadd_π m)).trans (MorphismProperty.Over.w φ)))

lemma smulHom_left (t : EtaleTorsor M Y) {U : Y.Etale} (f : C(U.left, M)) (φ : U ⟶ t.toEtale) :
    (t.smulHom f φ).left = U.left.glueOfContinuousMap f fun m ↦ φ.left ≫ t.vadd m :=
  rfl

lemma ι_smulHom_left_of_le (t : EtaleTorsor M Y) {U : Y.Etale} (f : C(U.left, M))
    (φ : U ⟶ t.toEtale) {V : U.left.Opens} {m : M} (hV : V ≤ U.left.fiberOpens f m) :
    V.ι ≫ (t.smulHom f φ).left = V.ι ≫ φ.left ≫ t.vadd m := by
  rw [smulHom_left, ← U.left.homOfLE_ι hV, Category.assoc,
    Scheme.fiberOpens_ι_glueOfContinuousMap, ← Category.assoc, Scheme.homOfLE_ι]

/-- A constant function `c` acts as `c`. -/
lemma smulHom_const (t : EtaleTorsor M Y) {U : Y.Etale} (c : M) (φ : U ⟶ t.toEtale) :
    (t.smulHom (ContinuousMap.const _ c) φ).left = φ.left ≫ t.vadd c := by
  refine Scheme.glueOfContinuousMap_eq fun m ↦ ?_
  by_cases hm : c = m
  · rw [hm]
  · have : IsEmpty (U.left.fiberOpens (ContinuousMap.const _ c) m).toScheme :=
      ⟨fun x ↦ hm x.2⟩
    exact isInitialOfIsEmpty.hom_ext _ _

lemma smulHom_add (t : EtaleTorsor M Y) {U : Y.Etale} (f g : C(U.left, M))
    (φ : U ⟶ t.toEtale) : t.smulHom (f + g) φ = t.smulHom f (t.smulHom g φ) := by
  refine etaleHom_ext ?_
  refine U.left.hom_ext_fiberOpens (f.prodMk g) fun ⟨a, b⟩ ↦ ?_
  have hf : U.left.fiberOpens (f.prodMk g) (a, b) ≤ U.left.fiberOpens f a :=
    fun x hx ↦ (Prod.ext_iff.1 hx).1
  have hg : U.left.fiberOpens (f.prodMk g) (a, b) ≤ U.left.fiberOpens g b :=
    fun x hx ↦ (Prod.ext_iff.1 hx).2
  have hfg : U.left.fiberOpens (f.prodMk g) (a, b) ≤ U.left.fiberOpens (f + g) (a + b) :=
    fun x hx ↦ by
      have h₁ : f x = a := hf hx
      have h₂ : g x = b := hg hx
      change f x + g x = a + b
      rw [h₁, h₂]
  rw [ι_smulHom_left_of_le t _ _ hfg, ι_smulHom_left_of_le t _ _ hf,
    reassoc_of% (ι_smulHom_left_of_le t g φ hg), add_comm, t.add_vadd]

lemma comp_smulHom (t : EtaleTorsor M Y) {U V : Y.Etale} (h : V ⟶ U) (f : C(U.left, M))
    (φ : U ⟶ t.toEtale) :
    h ≫ t.smulHom f φ = t.smulHom (f.comp h.left.base.hom) (h ≫ φ) := by
  refine etaleHom_ext ?_
  change h.left ≫ U.left.glueOfContinuousMap f _ =
    V.left.glueOfContinuousMap _ fun m ↦ (h.left ≫ φ.left) ≫ t.vadd m
  rw [Scheme.comp_glueOfContinuousMap]
  simp

lemma smulHom_comp (t₁ t₂ : EtaleTorsor M Y) {U : Y.Etale} (f : C(U.left, M))
    (φ : U ⟶ t₁.toEtale) (Φ : t₁.toEtale ⟶ t₂.toEtale)
    (hΦ : ∀ m : M, t₁.vadd m ≫ Φ.left = Φ.left ≫ t₂.vadd m) :
    t₁.smulHom f φ ≫ Φ = t₂.smulHom f (φ ≫ Φ) := by
  refine etaleHom_ext ?_
  change U.left.glueOfContinuousMap f (fun m ↦ φ.left ≫ t₁.vadd m) ≫ Φ.left =
    U.left.glueOfContinuousMap f fun m ↦ (φ.left ≫ Φ.left) ≫ t₂.vadd m
  simp [Scheme.glueOfContinuousMap_comp, hΦ]

/-- The action is simply transitive. -/
lemma bijective_smulHom (t : EtaleTorsor M Y) {U : Y.Etale} (φ : U ⟶ t.toEtale) :
    Function.Bijective fun f : C(U.left, M) ↦ t.smulHom f φ := by
  have := t.isIso_sigmaDesc
  refine ⟨fun f g hfg ↦ ContinuousMap.ext fun x ↦ ?_, fun ψ ↦ ?_⟩
  · let W := U.left.fiberOpens (f.prodMk g) (f x, g x)
    have hf : W ≤ U.left.fiberOpens f (f x) := fun y hy ↦ (Prod.ext_iff.1 hy).1
    have hg : W ≤ U.left.fiberOpens g (g x) := fun y hy ↦ (Prod.ext_iff.1 hy).2
    have h := congr_arg (fun χ : U ⟶ t.toEtale ↦ W.ι ≫ χ.left) hfg
    simp only [ι_smulHom_left_of_le t _ _ hf, ι_smulHom_left_of_le t _ _ hg] at h
    rw [← Category.assoc, ← Category.assoc] at h
    exact t.eq_of_comp_vadd_eq _ h ⟨x, rfl⟩
  · let D := Sigma.desc fun m : M ↦ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by simp [t.vadd_π])
    let χ : U.left ⟶ pullback t.π t.π :=
      pullback.lift ψ.left φ.left
        ((MorphismProperty.Over.w ψ).trans (MorphismProperty.Over.w φ).symm)
    let κ : U.left ⟶ ∐ fun _ : M ↦ t.P := χ ≫ inv D
    have hκ (x : U.left) : ∃ m y, Sigma.ι (fun _ : M ↦ t.P) m y = κ x := by
      obtain ⟨m, y, hy⟩ := (sigmaOpenCover fun _ : M ↦ t.P).exists_eq (κ x)
      exact ⟨m, y, hy⟩
    let a₀ (x : U.left) : M := (hκ x).choose
    have ha₀ (x : U.left) (m : M) (y : t.P) (hy : Sigma.ι (fun _ : M ↦ t.P) m y = κ x) :
        a₀ x = m := by
      obtain ⟨y', hy'⟩ := (hκ x).choose_spec
      exact congr_arg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 (hy'.trans hy.symm))
    have hfib (m : M) : a₀ ⁻¹' {m} = κ.base ⁻¹' Set.range (Sigma.ι (fun _ : M ↦ t.P) m) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
      refine ⟨fun hx ↦ ?_, fun ⟨y, hy⟩ ↦ ha₀ x m y hy⟩
      obtain ⟨y, hy⟩ := (hκ x).choose_spec
      exact ⟨y, hx ▸ hy⟩
    let a : C(U.left, M) := ⟨a₀, (IsLocallyConstant.iff_isOpen_fiber.2 fun m ↦ by
      rw [hfib]
      exact (Sigma.ι (fun _ : M ↦ t.P) m).isOpenEmbedding.isOpenMap.isOpen_range.preimage
        κ.base.hom.continuous).continuous⟩
    refine ⟨a, etaleHom_ext ?_⟩
    refine U.left.hom_ext_fiberOpens a fun m ↦ ?_
    let V := U.left.fiberOpens a m
    have hrange : Set.range (V.ι ≫ κ).base ⊆ Set.range (Sigma.ι (fun _ : M ↦ t.P) m).base := by
      rintro _ ⟨v, rfl⟩
      have hv : v.1 ∈ a₀ ⁻¹' {m} := v.2
      rw [hfib] at hv
      obtain ⟨y, hy⟩ := hv
      exact ⟨y, hy.trans (Scheme.Hom.comp_apply _ _ _).symm⟩
    let k : V.toScheme ⟶ t.P := IsOpenImmersion.lift (Sigma.ι (fun _ : M ↦ t.P) m) _ hrange
    have hk : V.ι ≫ χ = pullback.lift (k ≫ t.vadd m) k (by simp [t.vadd_π]) := by
      have : V.ι ≫ κ = k ≫ Sigma.ι (fun _ : M ↦ t.P) m := (IsOpenImmersion.lift_fac _ _ _).symm
      rw [← vadd_comp_sigmaDesc t k m, ← Category.assoc k, ← this]
      simp [κ, D]
    have h₁ := congr_arg (· ≫ pullback.fst t.π t.π) hk
    have h₂ := congr_arg (· ≫ pullback.snd t.π t.π) hk
    simp only [Category.assoc, χ, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
    rw [ι_smulHom_left_of_le t _ _ le_rfl, ← Category.assoc, h₂, h₁]

/-- The torsor under the sheaf `U ↦ C(U, M)` of locally constant functions given by the functor
of points `U ↦ Hom_Y(U, P)` of a torsor `P`, on which `f` acts by
`AlgebraicGeometry.Scheme.EtaleTorsor.smulHom`. -/
noncomputable def toSheafTorsorContinuousMap (t : EtaleTorsor M Y) :
    Sheaf.Torsor (Etale.continuousMapSheaf Y M) where
  sheaf := Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj t.toEtale
  vadd U f φ := ⟨t.smulHom f φ.down⟩
  zero_vadd U φ := ULift.ext (etaleHom_ext
    ((t.smulHom_const 0 φ.down).trans (by rw [t.zero_vadd]; exact Category.comp_id _)))
  add_vadd U f g φ := ULift.ext (t.smulHom_add f g φ.down)
  map_vadd h f φ := ULift.ext (t.comp_smulHom h.unop f φ.down)
  bijective_vadd U φ := by
    refine (Equiv.ulift.symm.bijective).comp (t.bijective_smulHom φ.down)
  nonemptySieve_mem U := by
    have := t.etale
    have := t.surjective
    let V : Y.Etale := Etale.mk (pullback.fst U.hom t.π ≫ U.hom)
    let ι : V ⟶ U := MorphismProperty.Over.homMk (pullback.fst U.hom t.π) rfl
    refine Y.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : PUnit.{1} ↦ ι)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      exact ⟨⟨MorphismProperty.Over.homMk (pullback.snd U.hom t.π) pullback.condition.symm⟩⟩
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.2 (Surjective.surj (f := pullback.fst U.hom t.π))

lemma toSheafTorsorContinuousMap_vadd (t : EtaleTorsor M Y) (U : Y.Etaleᵒᵖ) (f : C(U.unop.left, M))
    (φ : U.unop ⟶ t.toEtale) :
    t.toSheafTorsorContinuousMap.vadd U f ⟨φ⟩ = ⟨t.smulHom f φ⟩ :=
  rfl

/-- Isomorphic torsors have isomorphic sheaf torsors. -/
lemma toSheafTorsorContinuousMap_equiv_of_isIsomorphic {t₁ t₂ : EtaleTorsor M Y}
    (h : t₁.IsIsomorphic t₂) : t₁.toSheafTorsorContinuousMap ≈ t₂.toSheafTorsorContinuousMap := by
  obtain ⟨φ, hπ, hv⟩ := h
  let Φ : t₁.toEtale ≅ t₂.toEtale := MorphismProperty.Over.isoMk φ hπ
  refine ⟨⟨Y.smallEtaleTopology.uliftYoneda.{u + 1}.mapIso Φ, fun U f x ↦ ULift.ext ?_⟩⟩
  exact t₁.smulHom_comp t₂ f x.down Φ.hom hv

/-- Torsors with isomorphic sheaf torsors are isomorphic. -/
lemma isIsomorphic_of_toSheafTorsorContinuousMap_equiv {t₁ t₂ : EtaleTorsor M Y}
    (h : t₁.toSheafTorsorContinuousMap ≈ t₂.toSheafTorsorContinuousMap) : t₁.IsIsomorphic t₂ := by
  obtain ⟨e⟩ := h
  let Φ : t₁.toEtale ⟶ t₂.toEtale := (e.iso.hom.hom.app (op t₁.toEtale) ⟨𝟙 _⟩).down
  let Ψ : t₂.toEtale ⟶ t₁.toEtale := (e.iso.inv.hom.app (op t₂.toEtale) ⟨𝟙 _⟩).down
  have hΦ {U : Y.Etale} (x : U ⟶ t₁.toEtale) : e.iso.hom.hom.app (op U) ⟨x⟩ = ⟨x ≫ Φ⟩ := by
    have h := ConcreteCategory.congr_hom (e.iso.hom.hom.naturality x.op) ⟨𝟙 _⟩
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have e₁ : (⟨x⟩ : ULift.{u + 1} (U ⟶ t₁.toEtale)) =
        (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj t₁.toEtale).obj.map x.op ⟨𝟙 _⟩ :=
      ULift.ext (Category.comp_id x).symm
    rw [e₁]
    exact h
  have hΨ {U : Y.Etale} (x : U ⟶ t₂.toEtale) : e.iso.inv.hom.app (op U) ⟨x⟩ = ⟨x ≫ Ψ⟩ := by
    have h := ConcreteCategory.congr_hom (e.iso.inv.hom.naturality x.op) ⟨𝟙 _⟩
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    have e₁ : (⟨x⟩ : ULift.{u + 1} (U ⟶ t₂.toEtale)) =
        (Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj t₂.toEtale).obj.map x.op ⟨𝟙 _⟩ :=
      ULift.ext (Category.comp_id x).symm
    rw [e₁]
    exact h
  have hΦΨ : Φ ≫ Ψ = 𝟙 _ := by
    have h₁ := (((sheafSections Y.smallEtaleTopology (Type (u + 1))).obj
      (op t₁.toEtale)).mapIso e.iso).hom_inv_id_apply (⟨𝟙 _⟩ : ULift.{u + 1} (t₁.toEtale ⟶ _))
    change e.iso.inv.hom.app _ (e.iso.hom.hom.app _ ⟨𝟙 _⟩) = ⟨𝟙 _⟩ at h₁
    rw [hΦ, Category.id_comp, hΨ] at h₁
    exact congr_arg ULift.down h₁
  have hΨΦ : Ψ ≫ Φ = 𝟙 _ := by
    have h₁ := (((sheafSections Y.smallEtaleTopology (Type (u + 1))).obj
      (op t₂.toEtale)).mapIso e.iso).inv_hom_id_apply (⟨𝟙 _⟩ : ULift.{u + 1} (t₂.toEtale ⟶ _))
    change e.iso.hom.hom.app _ (e.iso.inv.hom.app _ ⟨𝟙 _⟩) = ⟨𝟙 _⟩ at h₁
    rw [hΨ, Category.id_comp, hΦ] at h₁
    exact congr_arg ULift.down h₁
  refine ⟨⟨Φ.left, Ψ.left, ?_, ?_⟩, MorphismProperty.Over.w Φ, fun m ↦ ?_⟩
  · rw [← MorphismProperty.Comma.comp_left, hΦΨ]
    rfl
  · rw [← MorphismProperty.Comma.comp_left, hΨΦ]
    rfl
  · have h := e.map_vadd (op t₁.toEtale) (ContinuousMap.const t₁.P m) ⟨𝟙 _⟩
    have h₀ : t₁.toSheafTorsorContinuousMap.vadd (op t₁.toEtale) (ContinuousMap.const t₁.P m)
        ⟨𝟙 _⟩ = ⟨t₁.smulHom (ContinuousMap.const t₁.P m) (𝟙 _)⟩ := rfl
    rw [h₀, hΦ, hΦ, Category.id_comp] at h
    have h' : (t₁.smulHom (ContinuousMap.const t₁.P m) (𝟙 _) ≫ Φ).left =
        (t₂.smulHom (ContinuousMap.const t₁.P m) Φ).left := congr_arg (fun x ↦ x.down.left) h
    have e₁ := t₁.smulHom_const (U := t₁.toEtale) m (𝟙 _)
    have e₂ := t₂.smulHom_const (U := t₁.toEtale) m Φ
    change t₁.vadd m ≫ Φ.left = Φ.left ≫ t₂.vadd m
    calc t₁.vadd m ≫ Φ.left
      _ = ((𝟙 t₁.toEtale : t₁.toEtale ⟶ t₁.toEtale).left ≫ t₁.vadd m) ≫ Φ.left :=
        congr_arg (· ≫ Φ.left) (Category.id_comp (t₁.vadd m)).symm
      _ = (t₁.smulHom (ContinuousMap.const _ m) (𝟙 _)).left ≫ Φ.left :=
        congr_arg (· ≫ Φ.left) e₁.symm
      _ = (t₂.smulHom (ContinuousMap.const _ m) Φ).left := h'
      _ = Φ.left ≫ t₂.vadd m := e₂

end SheafTorsor

/-- **The sheaf torsor of an `M`-torsor.** The functor of points `U ↦ Hom_Y(U, P)` of an
`M`-torsor `P ⟶ Y`, as a torsor under the constant sheaf `M` on the small étale site of `Y`: the
constant section `m` acts by composition with the action of `m` on `P`, and a section of the
constant sheaf over `U`, which is a locally constant function `f: U → M`
(`AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheaf`), acts on `φ: U ⟶ P` as
`m` on the open fibre `f⁻¹(m)` (`AlgebraicGeometry.Scheme.EtaleTorsor.smulHom`). -/
noncomputable def toSheafTorsor (t : EtaleTorsor M Y) :
    Sheaf.Torsor ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) :=
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  Sheaf.Torsor.ofIso (Etale.constantSheafIsoContinuousMapSheaf Y M).symm
    t.toSheafTorsorContinuousMap

/-- The sections of the sheaf torsor of `t` over `U` are the `Y`-morphisms `U ⟶ P`. -/
lemma toSheafTorsor_sheaf (t : EtaleTorsor M Y) :
    t.toSheafTorsor.sheaf = Y.smallEtaleTopology.uliftYoneda.{u + 1}.obj t.toEtale :=
  rfl

/-- **Full faithfulness on isomorphism classes.** Two `M`-torsors are isomorphic if and only if
their sheaf torsors are. -/
theorem toSheafTorsor_equiv_toSheafTorsor_iff {t₁ t₂ : EtaleTorsor M Y} :
    t₁.toSheafTorsor ≈ t₂.toSheafTorsor ↔ t₁ ≈ t₂ := by
  let _ : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  rw [toSheafTorsor, toSheafTorsor, Sheaf.Torsor.ofIso_equiv_ofIso_iff]
  exact ⟨isIsomorphic_of_toSheafTorsorContinuousMap_equiv,
    toSheafTorsorContinuousMap_equiv_of_isIsomorphic⟩

/-- The global sections of the sheaf torsor of `t` are the sections of the structure morphism
of `t`. -/
theorem nonempty_toSheafTorsor_sheaf_obj_iff (t : EtaleTorsor M Y) {T : Y.Etale}
    (hT : IsTerminal T) :
    Nonempty (t.toSheafTorsor.sheaf.obj.obj (op T)) ↔ ∃ s : Y ⟶ t.P, s ≫ t.π = 𝟙 Y := by
  let e := hT.uniqueUpToIso (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale Y)
  rw [toSheafTorsor_sheaf]
  constructor
  · rintro ⟨⟨φ⟩⟩
    exact ⟨(e.inv ≫ φ).left, MorphismProperty.Over.w (e.inv ≫ φ)⟩
  · rintro ⟨s, hs⟩
    exact ⟨⟨e.hom ≫ MorphismProperty.Over.homMk s hs⟩⟩

variable (M Y) in
/-- The map from isomorphism classes of `M`-torsors to isomorphism classes of torsors under the
constant sheaf `M`, induced by `AlgebraicGeometry.Scheme.EtaleTorsor.toSheafTorsor`. -/
noncomputable def quotientToSheafTorsor :
    Quotient (EtaleTorsor.setoid M Y) → _root_.Quotient (Sheaf.Torsor.setoid (G :=
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M))) :=
  Quotient.map toSheafTorsor fun _ _ h ↦ toSheafTorsor_equiv_toSheafTorsor_iff.2 h

lemma injective_quotientToSheafTorsor : Function.Injective (quotientToSheafTorsor M Y) := by
  intro t₁ t₂ h
  induction t₁ using Quotient.inductionOn
  induction t₂ using Quotient.inductionOn
  exact Quotient.sound (toSheafTorsor_equiv_toSheafTorsor_iff.1 (Quotient.exact h))

variable (M Y) in
/-- **The class of an `M`-torsor in `H¹(Y_ét, M)`.** The canonical map from isomorphism classes
of `M`-torsors over `Y` to the first étale cohomology of the constant sheaf `M`: the class of
`P ⟶ Y` is the class (`CategoryTheory.Sheaf.Torsor.classH1`) of its sheaf torsor of points
(`AlgebraicGeometry.Scheme.EtaleTorsor.toSheafTorsor`). -/
noncomputable def classH1 :
    Quotient (EtaleTorsor.setoid M Y) → Sheaf.H
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of M)) 1 :=
  Sheaf.Torsor.classH1 _ terminalIsTerminal ∘ quotientToSheafTorsor M Y

lemma classH1_mk (t : EtaleTorsor M Y) :
    classH1 M Y ⟦t⟧ = Sheaf.Torsor.classH1 _ terminalIsTerminal ⟦t.toSheafTorsor⟧ :=
  rfl

/-- Non-isomorphic `M`-torsors have different classes in `H¹(Y_ét, M)`. -/
theorem injective_classH1 : Function.Injective (classH1 M Y) :=
  (Sheaf.Torsor.classH1 _ terminalIsTerminal).injective.comp injective_quotientToSheafTorsor

/-- An `M`-torsor has class `0` in `H¹(Y_ét, M)` if and only if its structure morphism has a
section. -/
theorem classH1_eq_zero_iff (t : EtaleTorsor M Y) :
    classH1 M Y ⟦t⟧ = 0 ↔ ∃ s : Y ⟶ t.P, s ≫ t.π = 𝟙 Y := by
  rw [classH1_mk, Sheaf.Torsor.classH1_eq_zero_iff,
    t.nonempty_toSheafTorsor_sheaf_obj_iff terminalIsTerminal]

end Scheme.EtaleTorsor

section GaloisCover

variable (G : Type (u + 1)) [Group G] [Finite G]

/-- A finite étale Galois cover of a scheme `Y` with group `G`: a finite étale surjective
`Y`-scheme `P` on which the finite group `G` acts on the left over `Y`, simply transitively,
that is, such that the morphism `∐_{g ∈ G} P ⟶ P ×_Y P` whose `g`-th component is
`(g • -, id)` is an isomorphism. In other words, `P` is a finite étale `G`-torsor over `Y`. -/
structure Scheme.GaloisCover (Y : Scheme.{u}) where
  /-- the total space of the cover -/
  P : Scheme.{u}
  /-- the structure morphism to the base -/
  π : P ⟶ Y
  [isFinite : IsFinite π]
  [etale : Etale π]
  [surjective : Surjective π]
  /-- the left action of `G` on `P` over `Y` -/
  smul : G → (P ⟶ P)
  /-- the action is by morphisms over `Y` -/
  smul_π (g : G) : smul g ≫ π = π
  /-- the unit of `G` acts as the identity -/
  one_smul : smul 1 = 𝟙 P
  /-- the action is a left action: `(g * h) • x = g • (h • x)` -/
  mul_smul (g h : G) : smul (g * h) = smul h ≫ smul g
  /-- the action is simply transitive: `∐_{g ∈ G} P ≅ P ×_Y P` -/
  isIso_sigmaDesc : IsIso (Sigma.desc
    fun g : G ↦ pullback.lift (f := π) (g := π) (smul g) (𝟙 P) (by simp [smul_π]))

end GaloisCover

namespace Scheme

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- An `M`-torsor, for `M` a finite abelian group, as a Galois cover with group
`Multiplicative M`. -/
@[simps]
def EtaleTorsor.toGaloisCover (t : EtaleTorsor M Y) : GaloisCover (Multiplicative M) Y where
  P := t.P
  π := t.π
  isFinite := t.isFinite
  etale := t.etale
  surjective := t.surjective
  smul g := t.vadd g.toAdd
  smul_π g := t.vadd_π _
  one_smul := t.zero_vadd
  mul_smul g h := by rw [toAdd_mul, add_comm, t.add_vadd]
  isIso_sigmaDesc := t.isIso_sigmaDesc

/-- A Galois cover with group `Multiplicative M`, for `M` a finite abelian group, as an
`M`-torsor. -/
@[simps]
def GaloisCover.toEtaleTorsor (t : GaloisCover (Multiplicative M) Y) : EtaleTorsor M Y where
  P := t.P
  π := t.π
  isFinite := t.isFinite
  etale := t.etale
  surjective := t.surjective
  vadd m := t.smul (.ofAdd m)
  vadd_π m := t.smul_π _
  zero_vadd := t.one_smul
  add_vadd m n := by rw [add_comm, ofAdd_add, t.mul_smul]
  isIso_sigmaDesc := t.isIso_sigmaDesc

end Scheme

end AlgebraicGeometry
