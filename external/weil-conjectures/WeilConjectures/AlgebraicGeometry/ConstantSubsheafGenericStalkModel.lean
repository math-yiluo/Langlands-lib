/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.GeometricStalkComparisonConstant

/-! # The constant model of the generic stalk image

Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generic submodule paragraph.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- A subobject of a constant module sheaf has a constant model of its generic stalk,
with the same inclusion into the ambient constant sheaf at every geometric generic point.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), the submodule M' of M.
(blueprint: lem-weil-pbc-constant-subsheaf-generic-stalk-model).

Proof: Choose G isomorphic to the constant sheaf M and a geometric point above eta.
Under the constant-stalk identification with M, take N to be the range of the stalk
map of phi. Exactness of the stalk functor makes this map injective. The inclusion
N into M induces a monomorphism alpha from the constant N sheaf into G, because
constant presheaves and sheafification preserve monomorphisms. The range factorization
is an isomorphism from N to the stalk of F at the chosen point. To compare any other
geometric point over eta, compare the two separably closed residue-field extensions
through compatible separable closures. Base extension does not change an etale stalk;
these identifications are natural in F and G, and on constant M they identify the same
elements of M. Thus the range is N at every such point, giving the asserted compatible
isomorphisms. No finiteness, Noetherianity, or open-neighbourhood extension is used here.
If the range is zero, take N to be the zero module and the same range factorization. -/
theorem exists_constant_generic_stalk_model_of_mono_constant
    {X : Scheme.{u}} [IrreducibleSpace X]
    {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (hG : G.IsConstant X.smallEtaleTopology)
    (η : X) (hη : IsGenericPoint η Set.univ) :
    ∃ (N : ModuleCat.{u + 1} Λ)
      (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N ⟶ G),
      Mono α ∧
      ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        s (IsLocalRing.closedPoint Ω) = η →
        ∃ e : (pointSmallEtale s).sheafFiber.obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N) ≅
            (pointSmallEtale s).sheafFiber.obj F,
          e.hom ≫ (pointSmallEtale s).sheafFiber.map φ =
            (pointSmallEtale s).sheafFiber.map α := by
  have _ := hη
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : CategoryTheory.AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    CategoryTheory.AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  obtain ⟨M, ⟨i⟩⟩ := hG.mem_essImage
  let K := SeparableClosure (X.residueField η)
  let s₀ : Spec (.of K) ⟶ X :=
    (SpecToEquivOfField K X).symm ⟨η, CommRingCat.ofHom (algebraMap (X.residueField η) K)⟩
  have hs₀ : s₀ (IsLocalRing.closedPoint K) = η := by
    simp [s₀]
  let p := pointSmallEtale s₀
  let L := p.sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : Limits.PreservesFiniteLimits L := by
    dsimp [L, p]
    infer_instance
  have : L.PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape L
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let N := L.obj F
  let j : N ⟶ M := L.map φ ≫ L.map i.inv ≫
    (p.sheafFiberConstantSheafIso M).hom
  have hmφ : Mono (L.map φ) := L.map_mono φ
  have hmi : IsIso (L.map i.inv) := inferInstance
  have hj : Mono j := by
    dsimp only [j]
    infer_instance
  let α : C.obj N ⟶ G := C.map j ≫ i.hom
  have hC : C.PreservesMonomorphisms := by
    dsimp [C, constantSheaf]
    infer_instance
  have hα : Mono α := by dsimp [α]; infer_instance
  refine ⟨N, α, hα, ?_⟩
  intro Ω _ _ s hs
  obtain ⟨β, hβ⟩ := exists_geometricStalkComparison_constant (Λ := Λ) s₀ s (hs₀.trans hs.symm)
  let q := pointSmallEtale s
  let R := q.sheafFiber (A := ModuleCat.{u + 1} Λ)
  let e : R.obj (C.obj N) ≅ R.obj F :=
    q.sheafFiberConstantSheafIso N ≪≫ β.app F
  refine ⟨e, ?_⟩
  dsimp [e, α]
  rw [R.map_comp,
    q.sheafFiber_map_constantSheaf_map (A := ModuleCat.{u + 1} Λ) j]
  simp only [Category.assoc]
  dsimp only [j]
  rw [← hβ M]
  dsimp only [q]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← β.hom.naturality i.hom]
  change _ = _ ≫ L.map φ ≫ L.map i.inv ≫ L.map i.hom ≫ β.hom.app G
  rw [← L.map_comp_assoc i.inv i.hom, i.inv_hom_id, L.map_id, Category.id_comp]
  exact congrArg ((q.sheafFiberConstantSheafIso N).hom ≫ ·)
    (β.hom.naturality φ).symm

end AlgebraicGeometry.Scheme
