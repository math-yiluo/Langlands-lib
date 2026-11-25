/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.RingTheory.ProEtale.HenselianLocalRing

/-!
# Sections over a strictly henselian local scheme and the geometric stalk

Source: literature/stacks-project/etale-cohomology.tex, Lemma Tag 03QO
(blueprint: lem-weil-pbc-strictly-henselian-sections-stalk).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option linter.style.haveILetI false in
set_option backward.isDefEq.respectTransparency false in
/-- The pointed form of the section construction in Stacks Tag 03QO. Shrink the
marked point to an affine Spec B, localize B at its marked prime q, and use Olivier's
theorem (Tag 092Z) to identify B_q with R. The geometric point's ring map extends
uniquely to B_q, so the resulting section passes through that geometric point. -/
private theorem strictlyHenselianSections_pointedSection
    {R : Type u} [CommRing R]
    (hR : IsStrictlyHenselianLocalRing R)
    {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [AlgebraicGeometry.Etale f]
    (a : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω) ⟶ Spec (.of R))
    (hat : a ≫ f = t) (ht : t default = IsLocalRing.closedPoint R) :
    ∃ σ : Spec (.of R) ⟶ X, σ ≫ f = 𝟙 _ ∧ t ≫ σ = a := by
  letI : IsStrictlyHenselianLocalRing R := hR
  obtain ⟨B, j, hj, haj, _⟩ :=
    exists_affine_mem_range_and_range_subset (x := a default) (U := ⊤) (by simp)
  let : IsOpenImmersion j := hj
  let l : Spec (.of Ω) ⟶ Spec B := IsOpenImmersion.lift j a (by
    rintro _ ⟨z, rfl⟩
    simpa only [Subsingleton.elim z default] using haj)
  have hl : l ≫ j = a := IsOpenImmersion.lift_fac j a _
  let φ : CommRingCat.of R ⟶ B := Spec.preimage (j ≫ f)
  have hφ : Spec.map φ = j ≫ f := Spec.map_preimage _
  have hφe : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale), hφ]
    infer_instance
  algebraize [φ.hom]
  let q : PrimeSpectrum B := l default
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal R := by
    have h : (Spec.map φ) q = IsLocalRing.closedPoint R := by
      rw [hφ]
      change (l ≫ (j ≫ f)) default = _
      rw [← Category.assoc, hl, hat, ht]
    exact congrArg PrimeSpectrum.asIdeal h
  let Bq := Localization.AtPrime q.asIdeal
  have : Algebra.WeaklyEtale R B := inferInstance
  have : Algebra.WeaklyEtale R Bq := Algebra.WeaklyEtale.trans R B Bq
  have : IsLocalHom (algebraMap R Bq) := by
    refine ⟨fun z hz ↦ ?_⟩
    rw [IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.AtPrime.isUnit_to_map_iff Bq q.asIdeal] at hz
    by_contra hn
    exact hz (by
      have : z ∈ IsLocalRing.maximalIdeal R := hn
      rw [← hq] at this
      exact this)
  let er : R ≃+* Bq := RingEquiv.ofBijective (algebraMap R Bq)
    (Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing (R := R) (S := Bq))
  let ψ : B ⟶ CommRingCat.of R :=
    CommRingCat.ofHom (er.symm.toRingHom.comp (algebraMap B Bq))
  have hψ : φ ≫ ψ = 𝟙 _ := by
    ext z
    change er.symm (algebraMap B Bq (algebraMap R B z)) = z
    rw [← IsScalarTower.algebraMap_apply R B Bq]
    exact er.symm_apply_apply z
  let χ : B ⟶ CommRingCat.of Ω := Spec.preimage l
  let θ : CommRingCat.of R ⟶ CommRingCat.of Ω := Spec.preimage t
  have hχ : Spec.map χ = l := Spec.map_preimage _
  have hθ : Spec.map θ = t := Spec.map_preimage _
  have hφχ : φ ≫ χ = θ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ, hφ, hθ, ← Category.assoc, hl, hat]
  have hunit : ∀ z : q.asIdeal.primeCompl, IsUnit (χ.hom z) := by
    intro z
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply z.property
    change z.val ∈ (l default).asIdeal
    rw [← hχ, Spec.map_apply]
    simpa only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, default_asIdeal,
      Ideal.mem_bot] using hz
  let χq : Bq →+* Ω := IsLocalization.lift hunit
  have hχq : χq.comp (algebraMap R Bq) = θ.hom := by
    ext z
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R B Bq,
      IsLocalization.lift_eq]
    exact congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of Ω ↦ m.hom z) hφχ
  have hψθ : ψ ≫ θ = χ := by
    ext z
    change θ.hom (er.symm (algebraMap B Bq z)) = χ.hom z
    rw [← hχq, RingHom.comp_apply]
    change χq (er (er.symm (algebraMap B Bq z))) = _
    rw [er.apply_symm_apply]
    exact IsLocalization.lift_eq hunit z
  refine ⟨Spec.map ψ ≫ j, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp, hψ, Spec.map_id]
  · rw [← hθ, ← Spec.map_comp_assoc, hψθ, hχ, hl]


set_option backward.isDefEq.respectTransparency false in
/-- For an abelian sheaf on a strictly henselian local scheme the global germ is an
isomorphism, natural in the sheaf. Source: Stacks Project, Lemma Tag 03QO.
(blueprint: lem-weil-pbc-strictly-henselian-sections-stalk)

Proof:
1. For each pointed etale neighbourhood, shrink around its marked point to an affine
   chart Spec B. Its etale ring map R → B has a marked prime q over the maximal ideal.
2. The local map R → B_q is weakly etale, so the proved Olivier theorem
   `Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing` identifies it with R.
   Invert it and compose with B → B_q to obtain a retraction B → R.
3. The marked map B → Ω extends to B_q because every element outside q maps to a
   unit. This extension shows that the retraction yields a section through the
   prescribed geometric point, not just through its underlying topological point.
4. Equality of global germs is witnessed on a common pointed neighbourhood by
   `Point.toPresheafFiber_eq_iff'`. Pull back along its pointed section to obtain
   equality of the original global sections. Every germ has a representative on
   some neighbourhood by `Point.toPresheafFiber_jointly_surjective`; pulling that
   representative back along the pointed section gives a global section with that
   germ. Thus the germ map is bijective and hence an isomorphism of abelian groups.
5. Naturality is `Point.toPresheafFiber_naturality`. The forgetful functor on abelian
   groups preserves filtered colimits, with its universes shrunk to those of the
   neighbourhood category to apply the elementwise Point API. -/
theorem strictlyHenselianSections_geometricStalk_isIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    (hR : IsStrictlyHenselianLocalRing R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of R))
    (hs : s default = IsLocalRing.closedPoint R) :
    (∀ (F : Sheaf (smallEtaleTopology (Spec (.of R)))
      (AddCommGrpCat.{(max u v) + 1})),
      IsIso ((Scheme.pointSmallEtale s).toPresheafFiber
        (Scheme.Etale.mk (𝟙 (Spec (.of R))))
        (Over.homMk s (Category.comp_id s)) F.obj)) ∧
    (∀ (F G : Sheaf (smallEtaleTopology (Spec (.of R)))
      (AddCommGrpCat.{(max u v) + 1})) (φ : F ⟶ G),
      (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) F.obj ≫
        (Scheme.pointSmallEtale s).sheafFiber.map φ =
      φ.hom.app (Opposite.op (Scheme.Etale.mk (𝟙 (Spec (.of R))))) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber
          (Scheme.Etale.mk (𝟙 (Spec (.of R))))
          (Over.homMk s (Category.comp_id s)) G.obj) := by
  let : IsStrictlyHenselianLocalRing R := hR
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget AddCommGrpCat.{(max u v) + 1}) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, (max u v) + 1, u, (max u v) + 1} _
  let Φ := pointSmallEtale s
  let T := Scheme.Etale.mk (𝟙 (Spec (.of R)))
  let t : Φ.fiber.obj T := Over.homMk s (Category.comp_id s)
  have hsec (X : (Spec (.of R)).Etale) (x : Φ.fiber.obj X) :
      ∃ g : T ⟶ X, Φ.fiber.map g t = x := by
    obtain ⟨σ, hσ, hsσ⟩ := strictlyHenselianSections_pointedSection hR X.hom x.left s x.w hs
    refine ⟨MorphismProperty.Over.homMk σ hσ, ?_⟩
    apply Over.OverMorphism.ext
    exact hsσ
  constructor
  · intro F
    apply (ConcreteCategory.isIso_iff_bijective _).2
    constructor
    · intro a b hab
      obtain ⟨Y, f, y, _, heq⟩ :=
        (Φ.toPresheafFiber_eq_iff' (P := F.obj) T t a b).mp hab
      obtain ⟨g, _⟩ := hsec Y y
      have hgf : g ≫ f = 𝟙 T := by
        apply MorphismProperty.Over.Hom.ext
        have hf' : f.left ≫ T.hom = Y.hom := f.w
        have hg' : g.left ≫ Y.hom = T.hom := g.w
        change g.left ≫ f.left = 𝟙 _
        have hf'' : f.left = Y.hom := by
          change f.left ≫ 𝟙 _ = Y.hom at hf'
          simpa only [Category.comp_id] using hf'
        rw [hf'']
        exact hg'
      have h := congrArg (F.obj.map g.op) heq
      simpa [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hgf] using h
    · intro z
      obtain ⟨X, x, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective (P := F.obj) z
      obtain ⟨g, hg⟩ := hsec X x
      refine ⟨F.obj.map g.op a, ?_⟩
      rw [Φ.toPresheafFiber_w_apply, hg]
  · intro F G φ
    exact Φ.toPresheafFiber_naturality φ.hom T t

end AlgebraicGeometry.Scheme
