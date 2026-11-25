/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Span
import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
import all WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Data.Fintype.EquivFin
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Finite ideal generators cover the stalk-surjectivity locus on an affine

Source: Stacks Project, Properties, Lemma 01PM, proof; Schemes, Lemma 01IN.
(blueprint: lem-weil-pbc-affine-ideal-generator-cover).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- The affine section ideal has finite generators whose basic opens cover its unit locus.

Source: Stacks Project, Properties, Lemma 01PM, the choice of generators at the
start of the proof; Schemes, Lemma 01IN, quasi-coherent ideals on affine schemes.
(blueprint: lem-weil-pbc-affine-ideal-generator-cover).

Proof: Finite type on the affine V makes I(V) a finite module, hence its
image ideal J has a finite generating family g. The unit-module stalk
isomorphism identifies the stalk map with a linear map into O_X,x, carrying
germs of sections to the corresponding ring germs. If this map is surjective,
lift 1 and represent its preimage on a neighborhood of x. Shrinking makes its
image equal to 1. Choose a basic neighborhood D(f) within this neighborhood;
localization expresses the local I-section as a global section divided by a
power of f. Its image therefore has unit germ at x, giving a member of J whose
basic open contains x. Conversely such a member has unit germ, so the stalk
image ideal contains a unit and is the whole ring. Finally zeroLocus_span
identifies this locus with the union of D(g_i). The empty family, unit ideal,
and empty affine are included by the same argument. -/
theorem affine_ideal_generator_cover
    {X : Scheme.{u}} {I : X.Modules}
    (ι : I ⟶ SheafOfModules.unit X.ringCatSheaf) [Mono ι]
    [I.IsQuasicoherent] [I.IsFiniteType] (U : X.Opens)
    (hU : ∀ x : X, x ∈ U ↔ Function.Surjective
      ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map ι).hom)
    (V : X.affineOpens) :
    ∃ (t : ℕ) (g : Fin t → Γ(X, V.1)),
      (LinearMap.range (ι.val.app (op V.1)).hom : Ideal Γ(X, V.1)) =
        Ideal.span (Set.range g) ∧ U ⊓ V.1 = ⨆ i, X.basicOpen (g i) := by
  classical
  have : Module.Finite Γ(X, V.1) Γ(I, V.1) :=
    Modules.finite_sections_of_finiteType I V.2
  let J : Ideal Γ(X, V.1) := LinearMap.range (ι.val.app (op V.1)).hom
  let iV : Γ(I, V.1) →ₗ[Γ(X, V.1)] Γ(X, V.1) := (ι.val.app (op V.1)).hom
  obtain ⟨T, hT⟩ := Submodule.fg_range iV
  let g (i : Fin T.card) : Γ(X, V.1) := (T.equivFin.symm i).val
  have hgr : Set.range g = (T : Set Γ(X, V.1)) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩
      exact (T.equivFin.symm i).property
    · intro hr
      exact ⟨T.equivFin ⟨r, hr⟩, by simp [g]⟩
  have hg : J = Ideal.span (Set.range g) := by
    rw [hgr]
    exact hT.symm
  have hloc (x : X) (hxV : x ∈ V.1) :
      x ∈ U ↔ ∃ r ∈ J, x ∈ X.basicOpen r := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨e, he, _⟩ := ideal_module_product_stalk ι I x
    let q : S.obj I →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
      (S.map ι ≫ e.hom).hom
    have hqg (W : X.Opens) (hxW : x ∈ W) (b : Γ(I, W)) :
        q (I.presheaf.germ W x hxW b) =
          X.presheaf.germ W x hxW (ι.app W b) := by
      change e.hom ((TopCat.Presheaf.stalkFunctor Ab x).map ι.mapPresheaf
        (I.presheaf.germ W x hxW b)) = _
      rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      exact he W hxW (ι.app W b)
    have hs : Function.Surjective (S.map ι).hom ↔ Function.Surjective q := by
      constructor
      · intro h
        exact (ConcreteCategory.bijective_of_isIso e.hom).2.comp h
      · intro h m
        obtain ⟨b, hb⟩ := h (e.hom m)
        refine ⟨b, (ConcreteCategory.bijective_of_isIso e.hom).1 ?_⟩
        exact hb
    rw [hU x, hs]
    constructor
    · intro h
      obtain ⟨b, hb⟩ := h (1 : X.presheaf.stalk x)
      obtain ⟨W, hxW, b, rfl⟩ := I.presheaf.exists_germ_eq b
      rw [hqg] at hb
      have h1 : X.presheaf.germ V.1 x hxV (1 : Γ(X, V.1)) = 1 := map_one _
      obtain ⟨Z, hxZ, iZW, iZV, hz⟩ := X.presheaf.germ_eq x hxW hxV
        (ι.app W b) (1 : Γ(X, V.1)) (hb.trans h1.symm)
      obtain ⟨f, hfZ, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hxZ⟩ hxV
      have hfW : X.basicOpen f ≤ W := hfZ.trans (leOfHom iZW)
      have hb1 : (show Γ(X, X.basicOpen f) from ι.app (X.basicOpen f)
          (I.presheaf.map (homOfLE hfW).op b)) = 1 := by
        simp only [map_one] at hz
        have hh := congrArg (X.presheaf.map (homOfLE hfZ).op) hz
        rw [map_one, show iZW = homOfLE (leOfHom iZW) from Subsingleton.elim _ _] at hh
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh
        change X.presheaf.map (homOfLE hfW).op (ι.app W b) = 1 at hh
        have hn := ConcreteCategory.congr_hom
          (ι.mapPresheaf.naturality (homOfLE hfW).op) b
        change (show Γ(X, X.basicOpen f) from ι.app (X.basicOpen f)
          (I.presheaf.map (homOfLE hfW).op b)) =
            X.presheaf.map (homOfLE hfW).op (ι.app W b) at hn
        exact hn.trans hh
      obtain ⟨n, c, hc⟩ := Modules.exists_map_eq_pow_smul_of_isAffineOpen I V.2 f
        (I.presheaf.map (homOfLE hfW).op b)
      have hres : X.presheaf.map (homOfLE (X.basicOpen_le f)).op (ι.app V.1 c) =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n := by
        have hn := (ConcreteCategory.congr_hom
          (ι.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) c).symm
        change X.presheaf.map (homOfLE (X.basicOpen_le f)).op (ι.app V.1 c) =
          (show Γ(X, X.basicOpen f) from ι.app (X.basicOpen f)
            (I.presheaf.map (homOfLE (X.basicOpen_le f)).op c)) at hn
        rw [hn, hc, Modules.Hom.app_smul]
        change X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n *
          (show Γ(X, X.basicOpen f) from ι.app (X.basicOpen f)
            (I.presheaf.map (homOfLE hfW).op b)) = _
        rw [hb1, mul_one]
      refine ⟨ι.app V.1 c, ⟨c, rfl⟩, ?_⟩
      apply (X.mem_basicOpen _ x hxV).mpr
      have hu := ((X.mem_basicOpen f x hxV).mp hxf).pow n
      have hgem := congrArg (X.presheaf.germ (X.basicOpen f) x hxf) hres
      rw [X.presheaf.germ_res_apply] at hgem
      rw [map_pow, X.presheaf.germ_res_apply] at hgem
      rwa [hgem]
    · rintro ⟨r, ⟨b, rfl⟩, hx⟩
      have hu := (X.mem_basicOpen _ x hxV).mp hx
      have htop : LinearMap.range q = ⊤ :=
        Ideal.eq_top_of_isUnit_mem (LinearMap.range q)
          ⟨I.presheaf.germ V.1 x hxV b, hqg V.1 hxV b⟩ hu
      exact LinearMap.range_eq_top.mp htop
  refine ⟨T.card, g, hg, ?_⟩
  ext x
  constructor
  · rintro ⟨hxU, hxV⟩
    obtain ⟨r, hr, hxr⟩ := (hloc x hxV).mp hxU
    have hn : x ∉ X.zeroLocus (Set.range g) := by
      rw [← X.zeroLocus_span, ← hg]
      intro h
      exact ((X.mem_zeroLocus_iff J x).mp h r hr) hxr
    simp only [X.mem_zeroLocus_iff, Set.forall_mem_range, not_forall, not_not] at hn
    exact TopologicalSpace.Opens.mem_iSup.mpr hn
  · intro h
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
    have hxV := X.basicOpen_le (g i) hi
    refine ⟨(hloc x hxV).mpr ⟨g i, ?_, hi⟩, hxV⟩
    rw [hg]
    exact Ideal.subset_span ⟨i, rfl⟩

end AlgebraicGeometry.Scheme
