/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ModulePullbackSectionComparison
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionLift
import WeilConjectures.AlgebraicGeometry.EtaleSetSectionEventualEquality

/-! # Canonical sections of inverse images along an inverse system -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Continuity for a cocone whose arrows and legs are the canonical pullback section maps.
The diagram and its coherence are supplied as hypotheses; the conclusion is solely its
universal property, rather than the elementwise clauses of the parent statement.

Source: Stacks Project, Etale Cohomology, Theorem 09YQ (theorem-colimit), degree zero,
as applied in Lemma 09YU (lemma-category-is-colimit), proof, Fully faithful.
(blueprint: lem-weil-pbc-pullback-sections-is-colimit)

Proof: Restrict the scheme diagram to the directed tail i >= i0, which is nonempty
and cofinal, with the same limit. Base change every stage along V0 -> X_i0. The resulting
V_i and V are affine, since the transitions and limit projections are affine and V0 is
affine; base change of the scheme limit identifies V with their inverse limit. Put
w_i : V_i -> X_i0 and F_i = w_i inverse image of G. Their composition comparisons give
transition isomorphisms. On V these sheaves all identify with w inverse image of G;
associativity identifies the transitions with identities. The constant connected diagram
has that sheaf as its colimit. Forget to abelian sheaves, compatibly with inverse-image
units and composition, and apply Theorem 09YQ in degree zero. The natural degree-zero
cohomology/global-section comparison gives a colimit of the section groups. The etale
restriction isomorphisms identify these groups with S_i, and the cartesian-square
restriction/unit equation identifies their arrows and legs with mu and tau. The displayed
e_i and eB therefore transport this colimit cocone to B. Finally module filtered colimits
are created on underlying abelian groups (scalar multiplication is induced stagewise),
so B is a colimit also in ModuleCat. None of the elementwise colimit criterion is used. -/
theorem nonempty_isColimit_pullbackSections
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) [IsAffine V₀.left] :
    let J := {i : I // i₀ ≤ i}
    let S : J → ModuleCat.{u + 1} Λ := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)).obj.obj
          (op V₀)
    let T : ModuleCat.{u + 1} Λ := ((lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
      ((upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀)
    let μ : ∀ {i j : J}, (i ⟶ j) → (S i ⟶ S j) := fun {i j} f ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ)
          (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
          (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE j.property).op)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
            (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
    let τ : ∀ i : J, S i ⟶ T := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
          (D.map (homOfLE i.property).op) (c.π.app (op i₀))
          (c.w (homOfLE i.property).op).symm).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
            (D.map (homOfLE i.property).op) (c.π.app (op i₀))
            (c.w (homOfLE i.property).op).symm).inv.app G)).hom.app (op V₀)
    ∀ (F : J ⥤ ModuleCat.{u + 1} Λ) (B : Cocone F)
      (e : ∀ i : J, F.obj i ≅ S i) (eB : B.pt ≅ T),
      (∀ (i j : J) (f : i ⟶ j), (e i).inv ≫ F.map f ≫ (e j).hom = μ f) →
      (∀ i : J, (e i).inv ≫ B.ι.app i ≫ eB.hom = τ i) → Nonempty (IsColimit B) := by
  classical
  intro J S T μ τ F B e eB hm ht
  let : Nonempty J := ⟨⟨i₀, le_refl i₀⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  let : Nonempty I := ⟨i₀⟩
  let H := (sheafForget (D.obj (op i₀)).smallEtaleTopology).obj G
  let : CompactSpace V₀.left := inferInstance
  let : QuasiSeparatedSpace V₀.left := inferInstance
  let : QuasiCompact V₀.hom :=
    @quasiCompact_of_compactSpace V₀.left (D.obj (op i₀)) V₀.hom inferInstance inferInstance
  let : QuasiSeparated V₀.hom :=
    @QuasiSeparated.of_quasiSeparatedSpace V₀.left (D.obj (op i₀)) V₀.hom inferInstance
  obtain ⟨q, hq⟩ := exists_modulePullbackSectionComparison Λ (D.obj (op i₀)) G
  have hlift : ∀ t : T, ∃ (i : J) (s : S i), τ i s = t := by
    intro t
    obtain ⟨j, s, hs⟩ := etaleSetSectionLift D c hc i₀ H V₀
      (q c.pt (c.π.app (op i₀)) V₀ t)
    let i : J := ⟨j.left.unop, leOfHom j.hom.unop⟩
    refine ⟨i, (q (D.obj j.left) (D.map j.hom) V₀).symm s, ?_⟩
    apply (q c.pt (c.π.app (op i₀)) V₀).injective
    have hq' := hq (D.obj j.left) c.pt (c.π.app j.left) (D.map j.hom)
      (c.π.app (op i₀)) (c.w j.hom) V₀ ((q (D.obj j.left) (D.map j.hom) V₀).symm s)
    exact hq'.trans (by simpa only [Equiv.apply_symm_apply] using hs)
  have hzero : ∀ (i : J) (s : S i), τ i s = 0 →
      ∃ (j : J) (f : i ⟶ j), μ f s = 0 := by
    intro i s hs
    let a : Over (op i₀) := Over.mk (homOfLE i.property).op
    have hs' :
        etaleSetSectionComparison (c.π.app a.left) (D.map a.hom)
          (c.π.app (op i₀)) (c.w a.hom) H V₀ (q (D.obj a.left) (D.map a.hom) V₀ s) =
        etaleSetSectionComparison (c.π.app a.left) (D.map a.hom)
          (c.π.app (op i₀)) (c.w a.hom) H V₀ (q (D.obj a.left) (D.map a.hom) V₀ 0) := by
      have hx := hq (D.obj a.left) c.pt (c.π.app a.left) (D.map a.hom)
        (c.π.app (op i₀)) (c.w a.hom) V₀ s
      have h0 := hq (D.obj a.left) c.pt (c.π.app a.left) (D.map a.hom)
        (c.π.app (op i₀)) (c.w a.hom) V₀ 0
      have hz : τ i s = τ i 0 := by rw [hs, (τ i).hom.map_zero]
      exact hx.symm.trans ((congrArg (q c.pt (c.π.app (op i₀)) V₀) hz).trans h0)
    obtain ⟨l, f, g, hfg⟩ := etaleSetSectionEventualEquality D c hc i₀ H V₀ a a
      (q (D.obj a.left) (D.map a.hom) V₀ s)
      (q (D.obj a.left) (D.map a.hom) V₀ 0) hs'
    have hsame : f = g := by
      ext
      exact Subsingleton.elim _ _
    subst g
    let j : J := ⟨l.left.unop, leOfHom l.hom.unop⟩
    let b : i ⟶ j := homOfLE (leOfHom f.left.unop)
    refine ⟨j, b, ?_⟩
    apply (q (D.obj l.left) (D.map l.hom) V₀).injective
    rw [← (μ b).hom.map_zero]
    change q (D.obj l.left) (D.map l.hom) V₀ (μ b s) =
      q (D.obj l.left) (D.map l.hom) V₀ (μ b 0)
    have hk : D.map f.left ≫ D.map a.hom = D.map l.hom :=
      (D.map_comp f.left a.hom).symm.trans (congrArg D.map f.w)
    have he_s := hq (D.obj a.left) (D.obj l.left) (D.map f.left)
      (D.map a.hom) (D.map l.hom) hk V₀ s
    have he_zero := hq (D.obj a.left) (D.obj l.left) (D.map f.left)
      (D.map a.hom) (D.map l.hom) hk V₀ 0
    exact he_s.trans (hfg.trans he_zero.symm)
  have ht_apply (i : J) (s : F.obj i) :
      τ i ((e i).hom s) = eB.hom (B.ι.app i s) := by
    rw [← ht i]
    change eB.hom (B.ι.app i ((e i).inv ((e i).hom s))) = _
    have hs : (e i).inv ((e i).hom s) = s :=
      ConcreteCategory.congr_hom (e i).hom_inv_id s
    rw [hs]
  have hm_apply {i j : J} (f : i ⟶ j) (s : F.obj i) :
      μ f ((e i).hom s) = (e j).hom (F.map f s) := by
    rw [← hm i j f]
    change (e j).hom (F.map f ((e i).inv ((e i).hom s))) = _
    have hs : (e i).inv ((e i).hom s) = s :=
      ConcreteCategory.congr_hom (e i).hom_inv_id s
    rw [hs]
  have hkernel (i : J) (s : F.obj i) (hs : B.ι.app i s = 0) :
      ∃ (j : J) (f : i ⟶ j), F.map f s = 0 := by
    have hs' : τ i ((e i).hom s) = 0 := by
      rw [ht_apply, hs]
      exact eB.hom.hom.map_zero
    obtain ⟨j, f, hf⟩ := hzero i ((e i).hom s) hs'
    refine ⟨j, f, (ConcreteCategory.bijective_of_isIso (e j).hom).1 ?_⟩
    change (e j).hom (F.map f s) = (e j).hom 0
    rw [← hm_apply, hf, (e j).hom.hom.map_zero]
  let d := colimit.desc F B
  have hd (i : J) (s : F.obj i) : d (colimit.ι F i s) = B.ι.app i s :=
    ConcreteCategory.congr_hom (colimit.ι_desc B i) s
  have hsurj : Function.Surjective d := by
    intro t
    obtain ⟨i, s, hs⟩ := hlift (eB.hom t)
    refine ⟨colimit.ι F i ((e i).inv s), ((ConcreteCategory.bijective_of_isIso eB.hom).1 ?_)⟩
    change eB.hom (d (colimit.ι F i ((e i).inv s))) = eB.hom t
    rw [hd, ← ht_apply]
    have he : (e i).hom ((e i).inv s) = s :=
      ConcreteCategory.congr_hom (e i).inv_hom_id s
    rw [he, hs]
  have hinj : Function.Injective d := by
    apply (injective_iff_map_eq_zero d.hom).2
    intro x hx
    obtain ⟨i, s, rfl⟩ := Concrete.colimit_exists_rep F x
    have hs : B.ι.app i s = 0 := by simpa only [hd] using hx
    obtain ⟨j, f, hf⟩ := hkernel i s hs
    calc
      colimit.ι F i s = colimit.ι F j (F.map f s) := (colimit.w_apply F f s).symm
      _ = 0 := by rw [hf, (colimit.ι F j).hom.map_zero]
  have : IsIso d := (ConcreteCategory.isIso_iff_bijective d).2 ⟨hinj, hsurj⟩
  exact ⟨(colimit.isColimit F).ofIsoColimit
    (Cocone.ext (asIso d) (fun i ↦ colimit.ι_desc B i))⟩

end AlgebraicGeometry.Etale
