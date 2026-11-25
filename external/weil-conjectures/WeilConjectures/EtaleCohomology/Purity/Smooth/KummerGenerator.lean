/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.ConstructibleTorsion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineRelative
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
import WeilConjectures.SixFunctors.Etale.Derived.Point

/-!
# Detecting generators of direct images at geometric points

Tools to show that a class `κ ∈ Hom(Λ_X, K)` on the source of a morphism `π : X ⟶ Y`
generates a cohomology sheaf of `Rπ_* K`, by pulling back to geometric points of `Y`:

* the derived base change map `Lg^* Rπ_* ⟶ Rπ'_* Lg'^*` carries the pullback of the adjoint
  `Λ_Y ⟶ Rπ_* K` of a class to the adjoint of the pulled-back class
  (`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_homEquiv`);
* over a separably closed field, a morphism `β : Λ ⟶ N` with `c • β ≠ 0` for every `c ≠ 0`
  induces a monomorphism `H⁰(β)` (`AlgebraicGeometry.Etale.mono_homologyFunctor_zero_map`);
* over a separably closed field, a monomorphism of sheaves between sheaves with finite global
  sections of the same cardinality is an isomorphism
  (`AlgebraicGeometry.Etale.isIso_of_mono_of_card_sections`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Mate

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived base change map carries the pullback of the adjoint `M ⟶ Rf_* K` of a morphism
`α : Lf^* M ⟶ K` to the adjoint of the pulled-back morphism `Lf'^* Lg^* M ≅ Lg'^* Lf^* M ⟶
Lg'^* K`. -/
lemma derivedBaseChangeMap_app_homEquiv (sq : CommSq g' f' f g)
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (α : (L((f)^*[ModuleCat.{u + 1} Λ])).obj M ⟶ K) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv _ _ α) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).app K =
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f').homEquiv _ _
      ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app M ≫
        (L((g')^*[ModuleCat.{u + 1} Λ])).map α) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  have h := (derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq).naturality α
  simp only [Functor.comp_map] at h
  rw [h, ← Category.assoc, map_unit_derivedBaseChangeMap_app, Category.assoc,
    ← Functor.map_comp]

end Mate

section SepClosed

variable {K : Type u} [Field K] [IsSepClosed K]

variable (K) in
/-- The global sections functor on `Spec K`, `K` separably closed: an equivalence. -/
noncomputable abbrev sepClosedSections :
    Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ ModuleCat.{u + 1} Λ :=
  (sheafSections (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (etalePoint K))

/-- Over a separably closed field, a monomorphism of étale sheaves of `Λ`-modules whose
global sections are finite of the same cardinality is an isomorphism. -/
theorem isIso_of_mono_of_card_sections
    {F G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)} (ψ : F ⟶ G) [Mono ψ]
    [Finite ((sepClosedSections Λ K).obj F)] [Finite ((sepClosedSections Λ K).obj G)]
    (h : Nat.card ((sepClosedSections Λ K).obj G) ≤
      Nat.card ((sepClosedSections Λ K).obj F)) :
    IsIso ψ := by
  have hinj : Function.Injective ((sepClosedSections Λ K).map ψ) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : IsIso ((sepClosedSections Λ K).map ψ) :=
    (LinearEquiv.ofBijective ((sepClosedSections Λ K).map ψ).hom
      (hinj.bijective_of_nat_card_le h)).toModuleIso.isIso_hom
  exact isIso_of_reflects_iso ψ (sepClosedSections Λ K)

/-- Over a separably closed field, a morphism `f : Λ ⟶ G` out of the constant sheaf `Λ` with
`c • f ≠ 0` for every `c ≠ 0` is a monomorphism. -/
theorem mono_of_smul_eq_zero
    {G : Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (constantSheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ) ⟶ G) (hf : ∀ c : Λ, c • f = 0 → c = 0) : Mono f := by
  let E := constantSheafEquivalenceOfIsSepClosed Λ (k := K)
  let S := sepClosedSections Λ K
  let eU : ModuleCat.of Λ Λ ≅ S.obj ((constantSheaf (Spec (.of K)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) := E.unitIso.app (ModuleCat.of Λ Λ)
  have hsmul : ∀ (c : Λ) x, S.map (c • f) x = c • S.map f x := fun _ _ ↦ rfl
  have hgen : ∀ d : Λ, eU.hom d = d • eU.hom (1 : Λ) := fun d ↦ by
    rw [← map_smul, smul_eq_mul, mul_one]
  suffices hinj : Function.Injective (S.map f) from
    Functor.mono_of_mono_map S ((ModuleCat.mono_iff_injective _).2 hinj)
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨c, rfl⟩ : ∃ c₀ : Λ, eU.hom c₀ = m := ⟨eU.inv m, by simp⟩
  have hc : S.map (c • f) = 0 := by
    ext x
    obtain ⟨d, rfl⟩ : ∃ d₀ : Λ, eU.hom d₀ = x := ⟨eU.inv x, by simp⟩
    rw [hsmul, hgen d, map_smul, smul_comm, ← map_smul, ← hgen c, hm, smul_zero]
    rfl
  rw [hf c (S.map_injective (by rw [hc, Functor.map_zero]))]
  simp

/-- Over a separably closed field, a morphism `β : Λ ⟶ N` in `D((Spec K)_ét, Λ)` with
`c • β ≠ 0` for every `c ≠ 0` induces a monomorphism `H⁰(β) : Λ ⟶ H⁰(N)`: the constant sheaf
`Λ` is projective, so `β` is determined by `H⁰(β)`. -/
theorem mono_homologyFunctor_zero_map
    {N : _root_.DerivedCategory (Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (β : constantComplex Λ (Spec (.of K)) ⟶ N) (hβ : ∀ c : Λ, c • β = 0 → c = 0) :
    Mono ((_root_.DerivedCategory.homologyFunctor _ 0).map β) := by
  let H := _root_.DerivedCategory.homologyFunctor
    (Sheaf (Spec (.of K)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  let e := homologyZeroConstantComplexIso Λ (Spec (.of K))
  suffices h : Mono (e.inv ≫ H.map β) by
    have : H.map β = e.hom ≫ (e.inv ≫ H.map β) := by simp
    rw [this]
    infer_instance
  refine mono_of_smul_eq_zero Λ _ fun c hc ↦ hβ c ?_
  have hH : H.map (c • β) = 0 := by
    rw [Functor.map_smul, ← cancel_epi e.inv, comp_zero, Linear.comp_smul, hc]
  have := projective_unit_of_iso Λ (Iso.refl (Spec (.of K)))
  let u := constantComplexIsoSingleFunctor Λ (Spec (.of K))
  have h0 : _root_.DerivedCategory.homSingleEquivOfProjective (𝟙_ _) 0 N (u.inv ≫ (c • β)) =
      _root_.DerivedCategory.homSingleEquivOfProjective (𝟙_ _) 0 N 0 := by
    simp only [_root_.DerivedCategory.homSingleEquivOfProjective_apply,
      _root_.DerivedCategory.homSingleToHomology, Functor.map_comp, Functor.map_zero,
      comp_zero]
    change _ ≫ _ ≫ H.map (c • β) = 0
    rw [hH, comp_zero, comp_zero]
  have h1 := (_root_.DerivedCategory.homSingleEquivOfProjective (𝟙_ _) 0 N).injective h0
  rw [← cancel_epi u.inv, h1, comp_zero]

/-- The global sections over `Spec K`, `K` separably closed, of the pullback of a sheaf `L`
along a geometric point `x` are the stalk of `L` at `x`. -/
lemma nonempty_sepClosedSections_upperStar_iso {Y : Scheme.{u}}
    (L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ))
    (x : Spec (.of K) ⟶ Y) :
    Nonempty ((sepClosedSections Λ K).obj ((x)^*[ModuleCat.{u + 1} Λ].obj L) ≅
      ModuleCat.of Λ Λ) := by
  obtain ⟨e⟩ := hL K (𝟙 _ ≫ x)
  exact ⟨((Sheaf.ΓNatIsoSheafSections _ _ isTerminalEtalePoint).app _).symm ≪≫
    ΓIsoSheafFiberOfIsSepClosed _ ≪≫
      (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) x (𝟙 _)).app L ≪≫ e⟩

/-- The sections over `Spec K` of `H⁰(Lx^* N)` are the stalk of `H⁰(N)` at the geometric point
`x`. -/
lemma nonempty_sepClosedSections_homology_iso {Y : Scheme.{u}}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {L : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : (_root_.DerivedCategory.homologyFunctor _ 0).obj N ≅ L)
    (hL : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ))
    (x : Spec (.of K) ⟶ Y) :
    Nonempty ((sepClosedSections Λ K).obj ((_root_.DerivedCategory.homologyFunctor _ 0).obj
      ((L((x)^*[ModuleCat.{u + 1} Λ])).obj N)) ≅ ModuleCat.of Λ Λ) := by
  obtain ⟨e'⟩ := nonempty_sepClosedSections_upperStar_iso Λ L hL x
  exact ⟨(sepClosedSections Λ K).mapIso
    (((leftDerivedUpperStarHomologyFunctorIso _ x 0).app N).symm ≪≫
      (x)^*[ModuleCat.{u + 1} Λ].mapIso e) ≪≫ e'⟩

end SepClosed

/-- The coordinate of the complement of the zero section pulls back to the coordinate. -/
lemma units_map_unitLineCoord {S S' G G' : Scheme.{u}} (g : S' ⟶ S)
    (j : G ⟶ 𝔸(ULift.{u} (Fin 1); S)) [IsOpenImmersion j]
    (hj : Set.range j.base = (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S).base)ᶜ)
    (j' : G' ⟶ 𝔸(ULift.{u} (Fin 1); S')) [IsOpenImmersion j']
    (hj' : Set.range j'.base =
      (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S').base)ᶜ)
    (q : G' ⟶ G) (hq : q ≫ j = j' ≫ AffineSpace.map (ULift.{u} (Fin 1)) g) :
    Units.map q.appTop.hom.toMonoidHom (AffineSpace.unitLineCoord j hj) =
      AffineSpace.unitLineCoord j' hj' := by
  ext
  simp only [Units.coe_map, AffineSpace.val_unitLineCoord]
  change (j.appTop ≫ q.appTop) _ = _
  rw [← Scheme.Hom.comp_appTop, hq, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.map_appTop_coord]

end Etale

end AlgebraicGeometry
