/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.EventuallyAffine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Eventual closed immersions in inverse systems

Source: Stacks Project, Limits, Lemma 0A0N
(blueprint: lem-weil-pbc-eventually-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

-- Stacks, Limits, Lemma 0A0N, affine-case proof: lift the images of finitely many
-- generators through q.app U. Each difference vanishes in the limit, hence at a
-- later stage by exists_app_map_eq_zero_of_isLimit. Induction on the finite set
-- carries the previously lifted generators forward through surjective transitions.
-- Surjectivity of ρ and Algebra.adjoin_induction then give surjectivity of p j.
private theorem exists_surjective_app_of_isLimit
    {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : J} (g : i ⟶ j), IsClosedImmersion (D.map g)]
    {T : Scheme.{u}} (p : ∀ i, D.obj i ⟶ T)
    (hp : ∀ {i j : J} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ i, LocallyOfFiniteType (p i)]
    (q : c.pt ⟶ T) (hq : ∀ i, c.π.app i ≫ p i = q) [IsClosedImmersion q]
    {U : T.Opens} (hU : IsAffineOpen U) (k : J)
    (hk : IsAffineOpen (p k ⁻¹ᵁ U)) :
    ∃ j : J, IsAffineOpen (p j ⁻¹ᵁ U) ∧ Function.Surjective ((p j).app U).hom := by
  classical
  have hle (j : J) : q ⁻¹ᵁ U ≤ c.π.app j ⁻¹ᵁ p j ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hq]
  let χ (j : J) := (c.π.app j).appLE (p j ⁻¹ᵁ U) (q ⁻¹ᵁ U) (hle j)
  have hφχ : (p k).app U ≫ χ k = q.app U := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_congr_hom (hq k) _ _ _ le_rfl, Scheme.Hom.appLE_eq_app]
  obtain ⟨s, hs⟩ : ∃ s : Finset Γ(D.obj k, p k ⁻¹ᵁ U),
      letI := ((p k).app U).hom.toAlgebra
      Algebra.adjoin Γ(T, U) (↑s : Set Γ(D.obj k, p k ⁻¹ᵁ U)) = ⊤ := by
    have h := (p k).finiteType_appLE hU hk le_rfl
    rw [Scheme.Hom.appLE_eq_app] at h
    let := ((p k).app U).hom.toAlgebra
    exact h.out
  have key : ∀ t : Finset Γ(D.obj k, p k ⁻¹ᵁ U), ∃ (j : J)
      (ρ : Γ(D.obj k, p k ⁻¹ᵁ U) ⟶ Γ(D.obj j, p j ⁻¹ᵁ U)),
      IsAffineOpen (p j ⁻¹ᵁ U) ∧ Function.Surjective ρ.hom ∧
      (p k).app U ≫ ρ = (p j).app U ∧ ρ ≫ χ j = χ k ∧
      ∀ x ∈ t, ρ.hom x ∈ ((p j).app U).hom.range := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      exact ⟨k, 𝟙 _, hk, (ConcreteCategory.bijective_of_isIso (𝟙 _)).2,
        Category.comp_id _, Category.id_comp _, by simp⟩
    | insert x t hxt IH =>
      obtain ⟨j, ρ, hjU, hρs, hρp, hρχ, hρt⟩ := IH
      obtain ⟨r, hr⟩ := q.app_surjective U hU ((χ k).hom x)
      change (q.app U).hom r = (χ k).hom x at hr
      have hx : (χ k).hom (x - ((p k).app U).hom r) = 0 := by
        rw [map_sub]
        change (χ k).hom x - ((p k).app U ≫ χ k).hom r = 0
        rw [hφχ]
        exact sub_eq_zero.mpr hr.symm
      let z := ρ.hom (x - ((p k).app U).hom r)
      have hz : ((c.π.app j).app (p j ⁻¹ᵁ U)).hom z = 0 := by
        have h1 : (χ j).hom z = 0 := by
          rw [show (χ j).hom z = (ρ ≫ χ j).hom
            (x - ((p k).app U).hom r) from rfl, hρχ]
          exact hx
        have h2 : (c.pt.presheaf.map (homOfLE (hle j)).op).hom
            (((c.π.app j).app (p j ⁻¹ᵁ U)).hom z) = 0 := h1
        have hinj : Function.Injective (c.pt.presheaf.map (homOfLE (hle j)).op).hom := by
          have heq : q ⁻¹ᵁ U = c.π.app j ⁻¹ᵁ p j ⁻¹ᵁ U := by
            rw [← Scheme.Hom.comp_preimage, hq]
          have : IsIso (homOfLE (hle j)).op := (eqToIso heq).op.isIso_hom
          exact (ConcreteCategory.bijective_of_isIso _).1
        exact hinj (h2.trans (map_zero _).symm)
      obtain ⟨j', g, hg⟩ := exists_app_map_eq_zero_of_isLimit D c hc hjU.isCompact z hz
      have hpre : D.map g ⁻¹ᵁ p j ⁻¹ᵁ U = p j' ⁻¹ᵁ U := by
        rw [← Scheme.Hom.comp_preimage, hp]
      let σ := (D.map g).appLE (p j ⁻¹ᵁ U) (p j' ⁻¹ᵁ U) hpre.ge
      have hσs : Function.Surjective σ.hom := by
        have : IsIso (homOfLE hpre.ge).op := (eqToIso hpre).op.isIso_inv
        exact (ConcreteCategory.bijective_of_isIso
          ((D.obj j').presheaf.map (homOfLE hpre.ge).op)).2.comp
          ((D.map g).app_surjective _ hjU)
      have hσz : σ.hom z = 0 := by
        change ((D.obj j').presheaf.map (homOfLE hpre.ge).op).hom
          (((D.map g).app (p j ⁻¹ᵁ U)).hom z) = 0
        rw [hg, map_zero]
      have hσp : (p j).app U ≫ σ = (p j').app U := by
        rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
          Scheme.Hom.appLE_congr_hom (hp g) _ _ _ le_rfl, Scheme.Hom.appLE_eq_app]
      refine ⟨j', ρ ≫ σ, hpre ▸ hjU.preimage (D.map g), hσs.comp hρs, ?_, ?_, ?_⟩
      · rw [← Category.assoc, hρp, hσp]
      · rw [Category.assoc, Scheme.Hom.appLE_comp_appLE,
          Scheme.Hom.appLE_congr_hom (c.w g) _ _ _ (hle j), hρχ]
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · refine ⟨r, ?_⟩
          have hσρ : (p k).app U ≫ ρ ≫ σ = (p j').app U := by
            rw [← Category.assoc, hρp, hσp]
          have hz' : (ρ ≫ σ).hom y = (ρ ≫ σ).hom (((p k).app U).hom r) := by
            simpa only [z, map_sub, sub_eq_zero, CommRingCat.hom_comp,
              RingHom.comp_apply] using hσz
          rw [hz']
          change ((p j').app U).hom r = ((p k).app U ≫ ρ ≫ σ).hom r
          rw [hσρ]
        · obtain ⟨r', hr'⟩ := hρt y hy
          refine ⟨r', ?_⟩
          rw [← hσp, CommRingCat.hom_comp]
          change σ.hom (((p j).app U).hom r') = σ.hom (ρ.hom y)
          rw [hr']
  obtain ⟨j, ρ, hjU, hρs, hρp, -, hρs'⟩ := key s
  refine ⟨j, hjU, fun y ↦ ?_⟩
  obtain ⟨a, rfl⟩ := hρs y
  let := ((p k).app U).hom.toAlgebra
  have ha : a ∈ Algebra.adjoin Γ(T, U) (↑s : Set Γ(D.obj k, p k ⁻¹ᵁ U)) := by
    rw [hs]; trivial
  have hrange : ρ.hom a ∈ ((p j).app U).hom.range := by
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact hρs' x hx
    | algebraMap r =>
      refine ⟨r, ?_⟩
      change ((p j).app U).hom r = ρ.hom (((p k).app U).hom r)
      change ((p j).app U).hom r = ((p k).app U ≫ ρ).hom r
      rw [hρp]
    | add x y _ _ hx hy =>
      rw [map_add]
      exact ((p j).app U).hom.range.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact ((p j).app U).hom.range.mul_mem hx hy
  exact hrange


/-- If an inverse system over a quasi-compact, quasi-separated base has closed immersion
transitions, quasi-compact and quasi-separated stages, and locally finite type structure
maps, and its limit structure map is a closed immersion, then all sufficiently late
structure maps are closed immersions.

Source: Stacks Project, Limits, Lemma 0A0N
(blueprint: lem-weil-pbc-eventually-closed-immersion).

Proof:
1. Closed immersions are affine (lem-weil-pbc-closed-immersion-integral-separated-uc).
   Apply eventually_affine (lem-weil-pbc-eventually-affine) to obtain an affine
   starting structure map. Choose a finite affine open cover of T.
2. On each cover open U, the starting preimage is affine and its section ring is
   finitely generated over Γ(T, U) (lem-weil-pbc-lft-affine-pairs). The limit
   structure-map section homomorphism is surjective
   (lem-weil-pbc-closed-immersion-affine-cover-criterion).
3. Induct on the finite generators, carrying a surjective comparison from the
   starting ring to the current stage ring. Lift the limit image of the next
   generator to Γ(T, U). Its difference from that lift vanishes in the limit.
   Mathlib's exists_app_map_eq_zero_of_isLimit makes this difference vanish at a
   later stage; it bundles the restricted-open limit and section eventual-zero
   arguments (lem-weil-pbc-limit-cone-affine-projections-opens and
   lem-weil-pbc-limit-global-sections-colimit). Closed-immersion transitions give
   affine preimages and surjective comparisons and preserve the previous lifts.
4. Algebra.adjoin_induction and surjectivity of the comparison show that the base
   section homomorphism is surjective at the selected stage. Affine preimages and
   section surjectivity persist under every later closed-immersion transition.
5. Choose a common upper bound for the finitely many selected stages, including
   the empty-cover case. The affine-cover closed-immersion criterion proves that
   every structure map at or beyond that bound is a closed immersion. -/
theorem eventually_isClosedImmersion_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]
    (h : D ⟶ (Functor.const Iᵒᵖ).obj T)
    [∀ i : Iᵒᵖ, LocallyOfFiniteType (h.app i)]
    (c : Cone D) (_hc : IsLimit c) (f : c.pt ⟶ T)
    (_hf : ∀ i : Iᵒᵖ, c.π.app i ≫ h.app i = f) [IsClosedImmersion f] :
    ∃ i : I, ∀ j : I, i ≤ j → IsClosedImmersion (h.app (op j)) := by
  classical
  obtain ⟨i₀, hi₀⟩ := eventually_affine T D h c _hc f _hf
  have : IsAffineHom (h.app (op i₀)) := hi₀ i₀ le_rfl
  let 𝒰 := T.affineCover.finiteSubcover
  have (a : 𝒰.I₀) : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
  let V (a : 𝒰.I₀) : T.affineOpens := ⟨(𝒰.f a).opensRange,
    isAffineOpen_opensRange (𝒰.f a)⟩
  let P (a : 𝒰.I₀) (i : Iᵒᵖ) : Prop :=
    IsAffineOpen (h.app i ⁻¹ᵁ (V a).1) ∧
      Function.Surjective ((h.app i).app (V a).1).hom
  have hPex (a : 𝒰.I₀) : ∃ i, P a i := by
    exact exists_surjective_app_of_isLimit D c _hc (fun i ↦ h.app i)
      (fun {i j} g ↦ by simpa only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        using h.naturality g) f _hf (V a).2
      (op i₀) ((V a).2.preimage (h.app (op i₀)))
  have hPmap (a : 𝒰.I₀) {i j : Iᵒᵖ} (g : j ⟶ i) (H : P a i) : P a j := by
    have hpre : D.map g ⁻¹ᵁ h.app i ⁻¹ᵁ (V a).1 = h.app j ⁻¹ᵁ (V a).1 := by
      rw [← Scheme.Hom.comp_preimage, h.naturality g]
      simp
    refine ⟨hpre ▸ H.1.preimage (D.map g), ?_⟩
    let σ := (D.map g).appLE (h.app i ⁻¹ᵁ (V a).1)
      (h.app j ⁻¹ᵁ (V a).1) hpre.ge
    have hσp : (h.app i).app (V a).1 ≫ σ = (h.app j).app (V a).1 := by
      rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
          Scheme.Hom.appLE_congr_hom (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
          Category.comp_id] using h.naturality g) _ _ _ le_rfl,
        Scheme.Hom.appLE_eq_app]
    have : IsIso (homOfLE hpre.ge).op := (eqToIso hpre).op.isIso_inv
    have hσs : Function.Surjective σ.hom :=
      (ConcreteCategory.bijective_of_isIso
        ((D.obj j).presheaf.map (homOfLE hpre.ge).op)).2.comp
        ((D.map g).app_surjective _ H.1)
    rw [← hσp, CommRingCat.hom_comp]
    exact hσs.comp H.2
  choose k hk using hPex
  obtain ⟨i, hi⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have gi (a : 𝒰.I₀) : i ⟶ k a := (hi (by simp)).some
  refine ⟨i.unop, fun j hij ↦ ?_⟩
  let g : op j ⟶ i := (homOfLE hij).op
  apply HasAffineProperty.of_iSup_eq_top (P := @IsClosedImmersion) V 𝒰.iSup_opensRange
  intro a
  have H := hPmap a (g ≫ gi a) (hk a)
  refine ⟨H.1, ?_⟩
  change Function.Surjective ((h.app (op j) ∣_ (V a).1).appTop).hom
  rw [morphismRestrict_appTop, CommRingCat.hom_comp]
  have key : ∀ W (_ : W = (V a).1), Function.Surjective ((h.app (op j)).app W).hom := by
    rintro W rfl
    exact H.2
  exact (ConcreteCategory.bijective_of_isIso ((D.obj (op j)).presheaf.map
    (eqToHom (image_morphismRestrict_preimage (h.app (op j)) (V a).1 ⊤)).op)).2.comp
      (key _ (Scheme.Opens.ι_image_top _))

end AlgebraicGeometry
