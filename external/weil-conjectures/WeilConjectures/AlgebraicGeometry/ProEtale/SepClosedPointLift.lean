/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.IndEtale
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField

/-!
# Points with values in a separably closed field lift along pro-étale covers

A nonzero weakly étale algebra over a separably closed field `K` has a `K`-point, the residue
fields being separable algebraic over `K`. Hence a weakly étale scheme over `Spec K` with a point
has a section (`AlgebraicGeometry.exists_comp_eq_id_of_weaklyEtale_of_isSepClosed`), and every
`K`-point `y : Spec K ⟶ Y` of a scheme lifts along some member of any pro-étale cover of `Y`
(`AlgebraicGeometry.Scheme.Cover.exists_comp_eq_of_isSepClosed_of_proetale`): pull the cover
back along `y` and take a section of a member hit by the point of `Spec K`.

The residue field maps of a morphism which is surjective on stalks, such as an immersion, are
isomorphisms (`AlgebraicGeometry.Scheme.Hom.isIso_residueFieldMap`). Hence a field-valued point
lifts along such a morphism as soon as its image lies in the image of the morphism
(`AlgebraicGeometry.Scheme.exists_comp_eq_of_mem_range`).

Both lifting statements are also given for a commutative ring `K` which is a field
(`AlgebraicGeometry.Scheme.Cover.exists_comp_eq_of_isField`,
`AlgebraicGeometry.Scheme.exists_comp_eq_of_mem_range_of_isField`), with `Spec K` formed from
the ring structure of `K` itself rather than from a field structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- A nonzero weakly étale algebra over a separably closed field `K` has a `K`-algebra map to
`K`: the residue field at a maximal ideal is separable algebraic over `K`, hence equal to `K`. -/
theorem Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed {K R : Type u} [Field K]
    [CommRing R] [Algebra K R] [Algebra.WeaklyEtale K R] [IsSepClosed K] [Nontrivial R] :
    Nonempty (R →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have := Algebra.WeaklyEtale.indEtale_field K R
  have := Algebra.IndEtale.isSeparable_residueField_of_field (K := K) m
  let e := AlgEquiv.ofBijective (Algebra.ofId K m.ResidueField)
    ⟨(algebraMap K _).injective, IsSepClosed.algebraMap_surjective K _⟩
  exact ⟨e.symm.toAlgHom.comp (IsScalarTower.toAlgHom K R m.ResidueField)⟩

namespace AlgebraicGeometry

/-- A weakly étale scheme `V` over a separably closed field `K` with a point has a `K`-point:
a section of `f : V ⟶ Spec K`. -/
theorem exists_comp_eq_id_of_weaklyEtale_of_isSepClosed {K : Type u} [Field K] [IsSepClosed K]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of K)) [WeaklyEtale f] (v : V) :
    ∃ σ : Spec (.of K) ⟶ V, σ ≫ f = 𝟙 _ := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hv, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have : Nonempty U := ⟨⟨v, hv⟩⟩
  let φ := Spec.preimage (hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f)
  let := φ.hom.toAlgebra
  have : WeaklyEtale (Spec.map φ) := by
    rw [Spec.map_preimage]
    infer_instance
  have := weaklyEtale_SpecMap_algebraMap_iff (R := K) (S := Γ(V, U)).1 this
  obtain ⟨ψ⟩ := Algebra.WeaklyEtale.nonempty_algHom_of_isSepClosed (K := K) (R := Γ(V, U))
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hU.isoSpec.inv ≫ Scheme.Opens.ι U, ?_⟩
  have hφ : hU.isoSpec.inv ≫ Scheme.Opens.ι U ≫ f = Spec.map φ := (Spec.map_preimage _).symm
  rw [Category.assoc, Category.assoc, hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact ψ.commutes x

namespace Scheme

section Points

variable {W Z : Scheme.{u}} (p : W ⟶ Z) [SurjectiveOnStalks p]

/-- The residue field map of a morphism which is surjective on stalks is surjective. -/
lemma Hom.residueFieldMap_surjective (w : W) : Function.Surjective (p.residueFieldMap w) := by
  have h : Function.Surjective (Z.residue (p w) ≫ p.residueFieldMap w) := by
    rw [residue_residueFieldMap]
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨x, rfl⟩ := p.stalkMap_surjective w x
    exact ⟨x, by rw [CommRingCat.comp_apply]; rfl⟩
  intro y
  obtain ⟨x, hx⟩ := h y
  exact ⟨Z.residue (p w) x, by rw [CommRingCat.comp_apply] at hx; exact hx⟩

/-- The residue field map of a morphism which is surjective on stalks is an isomorphism, a
surjective map of fields being bijective. -/
lemma Hom.isIso_residueFieldMap (w : W) : IsIso (p.residueFieldMap w) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(p.residueFieldMap w).hom.injective, p.residueFieldMap_surjective w⟩

/-- **Field-valued points lift along a morphism which is surjective on stalks**: if the image
of `s : Spec K ⟶ Z` lies in the image of `p`, then `s` factors through `p`. -/
lemma exists_comp_eq_of_mem_range {K : Type u} [Field K] (s : Spec (.of K) ⟶ Z)
    (hs : s (IsLocalRing.closedPoint _) ∈ Set.range p) : ∃ s' : Spec (.of K) ⟶ W, s' ≫ p = s := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (SpecToEquivOfField K Z).symm.surjective s
  obtain ⟨w, hw⟩ := hs
  simp only [SpecToEquivOfField_symm_apply, Hom.comp_apply, fromSpecResidueField_apply] at hw
  subst hw
  have := p.isIso_residueFieldMap w
  refine ⟨Spec.map (inv (p.residueFieldMap w) ≫ φ) ≫ W.fromSpecResidueField w, ?_⟩
  simp only [SpecToEquivOfField_symm_apply]
  rw [Category.assoc, ← Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id_assoc]

end Points

end Scheme

/-- A point `y : Spec K ⟶ Y` with values in a separably closed field lifts along some member of
any pro-étale cover of `Y`. -/
theorem Scheme.Cover.exists_comp_eq_of_isSepClosed_of_proetale {K : Type u} [Field K]
    [IsSepClosed K] {Y : Scheme.{u}} (𝒰 : Y.Cover Scheme.proetalePrecoverage)
    (y : Spec (.of K) ⟶ Y) :
    ∃ (i : 𝒰.I₀) (g : Spec (.of K) ⟶ 𝒰.X i), g ≫ 𝒰.f i = y := by
  have h𝒰 := (Scheme.presieve₀_mem_precoverage_iff _).1
    (Scheme.propQCPrecoverage_le_precoverage (P := @WeaklyEtale) _ 𝒰.mem₀)
  obtain ⟨i, z, hz⟩ := h𝒰.1 (y (IsLocalRing.closedPoint K))
  have : WeaklyEtale (𝒰.f i) := h𝒰.2 i
  obtain ⟨v, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := 𝒰.f i)
    (IsLocalRing.closedPoint K) z hz.symm
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale_of_isSepClosed (pullback.fst y (𝒰.f i)) v
  exact ⟨i, σ ≫ pullback.snd _ _, by
    rw [Category.assoc, ← pullback.condition, reassoc_of% hσ]⟩

/-- `Scheme.exists_comp_eq_of_mem_range` for a commutative ring `K` which is a field, stated
with the ring structure of `K` itself: a point `s : Spec K ⟶ Z` whose image lies in the image
of a morphism `p` surjective on stalks factors through `p`. -/
lemma Scheme.exists_comp_eq_of_mem_range_of_isField {W Z : Scheme.{u}} (p : W ⟶ Z)
    [SurjectiveOnStalks p] {K : Type u} [CommRing K] (hK : IsField K) (s : Spec (.of K) ⟶ Z)
    (z : Spec (.of K)) (hs : s z ∈ Set.range p) : ∃ s' : Spec (.of K) ⟶ W, s' ≫ p = s := by
  let := hK.toField
  exact Scheme.exists_comp_eq_of_mem_range p s
    (Subsingleton.elim z (IsLocalRing.closedPoint K) ▸ hs)

/-- `Scheme.Cover.exists_comp_eq_of_isSepClosed_of_proetale` for a commutative ring `K` which is
a separably closed field, stated with the ring structure of `K` itself: a point `y : Spec K ⟶ Y`
lifts along some member of any pro-étale cover of `Y`. -/
theorem Scheme.Cover.exists_comp_eq_of_isField {K : Type u} [CommRing K] (hK : IsField K)
    (hsep : letI := hK.toField; IsSepClosed K) {Y : Scheme.{u}}
    (𝒰 : Y.Cover Scheme.proetalePrecoverage) (y : Spec (.of K) ⟶ Y) :
    ∃ (i : 𝒰.I₀) (g : Spec (.of K) ⟶ 𝒰.X i), g ≫ 𝒰.f i = y := by
  let := hK.toField
  exact 𝒰.exists_comp_eq_of_isSepClosed_of_proetale y

end AlgebraicGeometry
