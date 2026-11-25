/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Category
import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts

/-! # Comparing geometric stalks over the same scheme point

Source: Stacks Project, Tag 04FN; the generic submodule paragraph of Tag 09BH (3).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem geometricPoint_fieldExtension_lifts_bijective
    {X : Scheme.{u}} {K Ω : Type u}
    [Field K] [IsSepClosed K] [Field Ω] [IsSepClosed Ω]
    (ι : K →+* Ω) (r : Spec (.of K) ⟶ X) (U : X.Etale) :
    Function.Bijective
      (fun v : (pointSmallEtale r).fiber.obj U ↦
        (Over.homMk (Spec.map (CommRingCat.ofHom ι)) :
          Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ r) ⟶ Over.mk r) ≫ v) := by
  constructor
  · intro v w h
    apply Over.OverMorphism.ext
    apply SpecMap_comp_injective (CommRingCat.ofHom ι)
    exact congrArg (fun z ↦ z.left) h
  · intro v
    obtain ⟨g, hg, hr⟩ := U.hom.exists_SpecMap_comp_eq_of_isSepClosed
      (CommRingCat.ofHom ι) r v.left (Over.w v)
    refine ⟨Over.homMk g hr, ?_⟩
    apply Over.OverMorphism.ext
    exact hg

private theorem fieldExtension_fiberIso
    {X : Scheme.{u}} {K Ω : Type u}
    [Field K] [IsSepClosed K] [Field Ω] [IsSepClosed Ω]
    (ι : K →+* Ω) (r : Spec (.of K) ⟶ X) :
    Nonempty ((pointSmallEtale r).fiber ≅
      (pointSmallEtale (Spec.map (CommRingCat.ofHom ι) ≫ r)).fiber) := by
  let a : Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ r) ⟶ Over.mk r :=
    Over.homMk (Spec.map (CommRingCat.ofHom ι))
  let τ : (pointSmallEtale r).fiber ⟶
      (pointSmallEtale (Spec.map (CommRingCat.ofHom ι) ≫ r)).fiber :=
    { app := fun U ↦ ↾(fun v ↦ a ≫ v)
      naturality := fun U V f ↦ by
        ext v
        exact (Category.assoc a v f.hom).symm }
  have hτ : ∀ U, IsIso (τ.app U) := fun U ↦
    (CategoryTheory.isIso_iff_bijective _).mpr
      (geometricPoint_fieldExtension_lifts_bijective ι r U)
  have : IsIso τ := (NatTrans.isIso_iff_isIso_app τ).mpr hτ
  exact ⟨asIso τ⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pointHom_constant
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    [Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
    {Φ Ψ : X.smallEtaleTopology.Point.{u}} (f : Φ ⟶ Ψ)
    (M : ModuleCat.{u + 1} Λ) :
    f.sheafFiber.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
      (Φ.sheafFiberConstantSheafIso M).hom =
      (Ψ.sheafFiberConstantSheafIso M).hom := by
  let P := (Functor.const X.Etaleᵒᵖ).obj M
  let η := toSheafify X.smallEtaleTopology P
  apply (cancel_epi (Ψ.presheafFiber.map η)).mp
  change Ψ.presheafFiber.map η ≫ f.presheafFiber.app _ ≫ _ = _
  rw [f.presheafFiber.naturality_assoc η]
  dsimp only [GrothendieckTopology.Point.sheafFiberConstantSheafIso,
    Iso.trans_hom, Iso.symm_hom, asIso_inv]
  dsimp [η, P]
  rw [IsIso.hom_inv_id_assoc, IsIso.hom_inv_id_assoc]
  apply Ψ.presheafFiber_hom_ext
  intro U v
  simp [GrothendieckTopology.Point.Hom.presheafFiber]

/-- Geometric stalk functors at two points with the same image admit an isomorphism
which acts as the identity on the value of every constant module sheaf.
Source: Stacks Project, Tag 04FN, and Tag 09BH (3), generic submodule paragraph.
(blueprint: corollary-cohomology-geometric-fibres--2).

Proof: Let x be the common image and choose a separable closure K of its residue field.
The residue-field embeddings defining s and t extend to embeddings of K into their
separably closed fields. Both geometric points therefore factor through Spec K over X.
Precomposition with either resulting morphism of geometric points is a bijection on
pointed etale lifts: the residue fields of etale neighbourhoods are finite separable
extensions of the residue field at their image, and their embeddings factor uniquely
through the separably closed subfield. These bijections form natural isomorphisms of
point fibre functors, hence equivalences of pointed neighbourhood categories compatible
with forgetting the lift. The induced colimit isomorphisms give isomorphisms of module
stalk functors, natural in the sheaf. Compose one with the inverse of the other.
A constant section is unchanged by precomposition with a point morphism; since every
constant-presheaf germ is represented by such a section, the comparison is the identity
under the constant-stalk isomorphisms. Sheafification preserves the stalk and its germ
map, so the displayed normalization also holds for constant sheaves. No genericity,
monomorphism, finiteness, or irreducibility is needed. -/
theorem exists_geometricStalkComparison_constant
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    [Limits.PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ))]
    {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
    (s : Spec (.of Ω) ⟶ X) (t : Spec (.of Ω') ⟶ X)
    (h : s (IsLocalRing.closedPoint Ω) = t (IsLocalRing.closedPoint Ω')) :
    ∃ β : (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) ≅
        (pointSmallEtale t).sheafFiber,
      ∀ M : ModuleCat.{u + 1} Λ,
        β.hom.app ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≫
          ((pointSmallEtale t).sheafFiberConstantSheafIso M).hom =
          ((pointSmallEtale s).sheafFiberConstantSheafIso M).hom := by
  classical
  obtain ⟨⟨x, a⟩, rfl⟩ := (SpecToEquivOfField Ω X).symm.surjective s
  obtain ⟨⟨y, b⟩, rfl⟩ := (SpecToEquivOfField Ω' X).symm.surjective t
  have hxy : x = y := by simpa [SpecToEquivOfField] using h
  subst y
  let K := SeparableClosure (X.residueField x)
  let r : Spec (.of K) ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫
      X.fromSpecResidueField x
  let : Algebra (X.residueField x) Ω := a.hom.toAlgebra
  let : Algebra (X.residueField x) Ω' := b.hom.toAlgebra
  let α : K →ₐ[X.residueField x] Ω := IsSepClosed.lift
  let α' : K →ₐ[X.residueField x] Ω' := IsSepClosed.lift
  have hs : Spec.map (CommRingCat.ofHom α.toRingHom) ≫ r =
      Spec.map a ≫ X.fromSpecResidueField x := by
    dsimp [r]
    rw [← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    ext z
    exact α.commutes z
  have ht : Spec.map (CommRingCat.ofHom α'.toRingHom) ≫ r =
      Spec.map b ≫ X.fromSpecResidueField x := by
    dsimp [r]
    rw [← Spec.map_comp_assoc]
    congr 1
    apply congrArg Spec.map
    ext z
    exact α'.commutes z
  obtain ⟨es⟩ := fieldExtension_fiberIso α.toRingHom r
  obtain ⟨et⟩ := fieldExtension_fiberIso α'.toRingHom r
  rw [hs] at es
  rw [ht] at et
  let e := GrothendieckTopology.Point.isoMk (es.symm ≪≫ et)
  refine ⟨GrothendieckTopology.Point.sheafFiberIso e, ?_⟩
  intro M
  exact pointHom_constant e.inv M

end AlgebraicGeometry.Scheme
