/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.FieldTheory.KrullTopology
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.FieldEquivariantGermsOnePoint

/-! # Realizing equivariant families of geometric germs as sections

Source: Stacks Project, Tags 04JM and 03QW, direct invariant-section argument.
(blueprint: lem-exc-field-equivariant-germ-family-section).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- On any base scheme, equal germs at a geometric point determine sections on an
etale object if its lifts cover every underlying point of that object.
Source: Stacks Project, Tag 03QW; equalizer-sieve and separatedness argument. -/
private theorem section_germ_ext_of_lifts (S : Scheme.{u}) (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (max (u + 1) v)))
    (U : S.Etale)
    (hlifts : ∀ y : U.left, ∃ l : Spec (.of Ω) ⟶ U.left,
      l ≫ U.hom = s ∧ l (default : Spec (.of Ω)) = y)
    (a b : F.obj.obj (op U))
    (h : ∀ x : (pointSmallEtale s).fiber.obj U,
      (pointSmallEtale s).toPresheafFiber U x F.obj a =
        (pointSmallEtale s).toPresheafFiber U x F.obj b) : a = b := by
  let p := pointSmallEtale s
  let R := Presheaf.equalizerSieve (F := F.obj) (X := op U) a b
  have hR : R ∈ S.smallEtaleTopology U := by
    obtain ⟨ι, Y, f, hf⟩ := R.exists_eq_ofArrows
    rw [hf, ofArrows_mem_smallEtaleTopology_iff]
    ext y
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨l, hl, hy⟩ := hlifts y
    let x : p.fiber.obj U := Over.homMk l hl
    obtain ⟨Z, g, t, ht, he⟩ := (p.toPresheafFiber_eq_iff' _ _ _ _).mp (h x)
    have hg : R g := he
    rw [hf] at hg
    obtain ⟨W, c, d, ⟨i⟩, hcd⟩ := hg
    refine ⟨i, c.left (t.left (default : Spec (.of Ω))), ?_⟩
    have hfac : g.left = c.left ≫ (f i).left := by
      exact congrArg (fun q ↦ q.left) hcd.symm
    have ht' : t.left ≫ g.left = x.left := congrArg (fun q ↦ q.left) ht
    rw [hfac] at ht'
    have := congrArg (fun q : Spec (.of Ω) ⟶ U.left ↦ q default) ht'
    change (f i).left (c.left (t.left (default : Spec (.of Ω)))) = l default at this
    exact this.trans hy
  exact Sheaf.isSeparated F U R hR _ _ (fun Y f hf ↦ hf)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, Tag 04JM, direct proof of lemma-global-sections-point,
and Tag 03QW, section-galois-action-stalks.
(blueprint: lem-exc-field-equivariant-germ-family-section).

Proof: By quasi-finiteness, the inverse image of the unique point of Spec K is
discrete; that inverse image is all of X. Cover X by its singleton open subschemes.
Each is nonempty and has exactly one point. Apply
field_equivariant_germ_family_section_onePoint to the restriction of f along
the inclusion of each singleton. Its covariance follows by composing the
change-of-lift equation with that inclusion.
To compare the resulting sections on overlaps, first prove that sections on any
etale K-scheme are determined by their germs at lifts from Spec Omega. Indeed,
equal germs admit a common pointed refinement on which the sections agree. Every
scheme point admits an Omega-lift, and these refinements make the equalizer sieve
covering. Sheaf separatedness gives equality. Apply this criterion to the two
restrictions on any common refinement of singleton components: their germs are
both f evaluated at the same lift of X, by germ naturality.
The sheaf axiom glues this compatible family over the singleton cover. Every lift
of X lifts through the covering sieve; germ naturality and the amalgamation
equations then give the prescribed germ. If X is empty, the singleton cover is
empty and the same sheaf axiom supplies its unique section. -/
theorem field_equivariant_germ_family_section
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosure K Ks] [Algebra Ks Ω] [Algebra K Ω]
    [IsScalarTower K Ks Ω] [IsAlgClosed Ω]
    (F : Sheaf (Spec (.of K)).smallEtaleTopology (Type (max (u + 1) v))) :
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ (ρ : Gal(Ks/K) → p.sheafFiber.obj F → p.sheafFiber.obj F),
      (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
        (algebraMap Ks Ω).comp g.toRingHom =
          τ.toRingHom.comp (algebraMap Ks Ω) →
        ∀ (Y : (Spec (.of K)).Etale) (y y' : p.fiber.obj Y),
        y'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ y.left →
        ∀ (z : F.obj.obj (op Y)),
        ρ g (p.toPresheafFiber Y y F.obj z) = p.toPresheafFiber Y y' F.obj z) →
      ∀ (X : (Spec (.of K)).Etale) (f : p.fiber.obj X → p.sheafFiber.obj F),
        (∀ (g : Gal(Ks/K)) (τ : Ω ≃ₐ[K] Ω),
          (algebraMap Ks Ω).comp g.toRingHom =
            τ.toRingHom.comp (algebraMap Ks Ω) →
          ∀ (x x' : p.fiber.obj X),
          x'.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ x.left →
          f x' = ρ g (f x)) →
        ∃ z : F.obj.obj (op X), ∀ x : p.fiber.obj X,
          p.toPresheafFiber X x F.obj z = f x := by
  classical
  intro p ρ hρ X f hf
  have : DiscreteTopology X.left := by
    apply isDiscrete_univ_iff.mp
    let d : X.left ⟶ Spec (.of K) := X.hom
    have h := d.isDiscrete_preimage_singleton (default : Spec (.of K))
    have heq : d ⁻¹' {default} = Set.univ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rwa [heq] at h
  let U (i : X.left) : X.left.Opens := ⟨{i}, isOpen_discrete _⟩
  let Y (i : X.left) : (Spec (.of K)).Etale := Etale.mk ((U i).ι ≫ X.hom)
  let a (i : X.left) : Y i ⟶ X := MorphismProperty.Over.homMk (U i).ι
  have one (i : X.left) : Subsingleton (Y i).left := by
    change Subsingleton (U i)
    refine ⟨fun x y ↦ Subtype.ext ?_⟩
    exact x.property.trans y.property.symm
  have inhabited (i : X.left) : Nonempty (Y i).left := ⟨⟨i, rfl⟩⟩
  have local_section (i : X.left) :
      ∃ z : F.obj.obj (op (Y i)), ∀ y : p.fiber.obj (Y i),
        p.toPresheafFiber (Y i) y F.obj z = f (p.fiber.map (a i) y) := by
    have := one i
    have := inhabited i
    apply field_equivariant_germ_family_section_onePoint K Ks Ω F (Y i) ρ hρ
      (fun y ↦ f (p.fiber.map (a i) y))
    intro g τ hτ y y' hy
    apply hf g τ hτ
    change y'.left ≫ (a i).left =
      Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ (y.left ≫ (a i).left)
    rw [hy, Category.assoc]
  choose z hz using local_section
  have hcover : Sieve.ofArrows Y a ∈ (Spec (.of K)).smallEtaleTopology X := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext i
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨i, ⟨i, rfl⟩, rfl⟩
  have compatible : ∀ ⦃W : (Spec (.of K)).Etale⦄ ⦃i j : X.left⦄
      (b : W ⟶ Y i) (c : W ⟶ Y j), b ≫ a i = c ≫ a j →
        (↾fun _ : PUnit ↦ z i) ≫ F.obj.map b.op =
          (↾fun _ : PUnit ↦ z j) ≫ F.obj.map c.op := by
    intro W i j b c hbc
    ext t
    apply section_germ_ext_of_lifts (Spec (.of K)) Ω _ F W
    · intro y
      have : AlgebraicGeometry.Etale W.hom := W.prop
      exact exists_fac_of_etale_of_isSepClosed W.hom
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) y
        (Subsingleton.elim (α := Spec (.of K)) _ _)
    intro w
    change p.toPresheafFiber W w F.obj (F.obj.map b.op (z i)) =
      p.toPresheafFiber W w F.obj (F.obj.map c.op (z j))
    rw [p.toPresheafFiber_w_apply, p.toPresheafFiber_w_apply, hz, hz]
    congr 1
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
      ConcreteCategory.congr_hom (congrArg p.fiber.map hbc) w
  obtain ⟨g, hg, -⟩ := F.property.existsUnique_amalgamation_ofArrows a hcover
    (fun i ↦ ↾fun _ : PUnit ↦ z i) compatible
  refine ⟨g PUnit.unit, ?_⟩
  intro x
  obtain ⟨Z, q, hq, w, rfl⟩ := p.jointly_surjective _ hcover x
  obtain ⟨V, b, c, ⟨i⟩, hbc⟩ := hq
  have hfac : b ≫ a i = q := hbc
  have hrestrict : F.obj.map (a i).op (g PUnit.unit) = z i :=
    ConcreteCategory.congr_hom (hg i) PUnit.unit
  rw [← hfac, Functor.map_comp, ConcreteCategory.comp_apply]
  rw [← p.toPresheafFiber_w_apply, hrestrict, hz]

end AlgebraicGeometry.Scheme
