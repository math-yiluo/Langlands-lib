/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.FiniteFreeConstantMapEtaleFactorization
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective

/-! # Extending a stalk factorization of a finite constant map

Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A stalk factorization from a finite free constant module extends to an open.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent.
(blueprint: lem-weil-pbc-finite-free-constant-map-open-factorization).

Proof: For each standard basis vector, represent its image under l by a section of F
on a pointed etale neighbourhood. Refine finitely many times so that all representatives
are on one neighbourhood V and their images under phi equal the corresponding images
under alpha. Equality of germs is witnessed after refinement. The open image U of V
contains x. On V times_U V the two pulled back representatives have equal images in G,
since both images come from alpha. Monicity makes them equal in F. Descent for the
surjective etale cover V to U gives one section of F on U for each basis vector.
The universal property of the free module gives a linear map from Λ^(Fin n) into
these global sections. The constant-sheaf/global-sections adjunction and the constant
pullback comparison give the desired map. Equality of its composite with phi and alpha
is checked on the standard basis. For n=0 both maps from the zero constant sheaf are
zero, and U=X suffices. No relations have to be checked in this free-module statement. -/
theorem exists_open_factorization_of_finite_free_constant_map
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] (n : ℕ)
    (α : (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Fin n → Λ)) ⟶ G)
    (x : X)
    (l : (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
        (pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj F)
    (hl : l ≫ (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map φ =
      (pointSmallEtale (X.algClosurePoint x)).sheafFiber.map α) :
    ∃ (U : X.Opens) (_hU : x ∈ U)
      (ψ : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ (Fin n → Λ))) ⟶
          (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
      ψ ≫ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map φ =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).map α := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨V, hxV, β, hβ⟩ :=
      exists_etale_factorization_of_finite_free_constant_map φ n α x l hl
    let U : X.Opens := ⟨Set.range V.hom, V.hom.isOpenMap.isOpen_range⟩
    have hVU : Set.range V.hom ⊆ Set.range U.ι := by
      rw [U.range_ι]
      exact le_rfl
    let q : V.left ⟶ U.toScheme := IsOpenImmersion.lift U.ι V.hom hVU
    have hq : q ≫ U.ι = V.hom := IsOpenImmersion.lift_fac U.ι V.hom hVU
    have hsurj : Function.Surjective q.base := by
      intro y
      obtain ⟨v, hv⟩ := y.property
      refine ⟨v, ?_⟩
      apply Subtype.ext
      change U.ι (q v) = y.val
      rw [← Scheme.Hom.comp_apply, hq]
      exact hv
    let R := Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι
    let T := Etale.upperStar (ModuleCat.{u + 1} Λ) q
    let E := Etale.upperStar (ModuleCat.{u + 1} Λ) V.hom
    let e : E ≅ R ⋙ T :=
      Etale.upperStarComp (ModuleCat.{u + 1} Λ) q U.ι V.hom hq.symm
    have hT : T.Faithful := Etale.faithful_upperStar_of_surjective Λ q hsurj
    let β' : T.obj (R.obj ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ)))) ⟶ T.obj (R.obj F) :=
      (e.app _).inv ≫ β ≫ (e.app F).hom
    have hβ' : β' ≫ T.map (R.map φ) = T.map (R.map α) := by
      dsimp only [β']
      change (e.app _).inv ≫ β ≫ e.hom.app F ≫ (R ⋙ T).map φ = (R ⋙ T).map α
      rw [← e.hom.naturality φ,
        ← Category.assoc β, hβ, e.hom.naturality α]
      simp
    have hz : R.map α ≫ CategoryTheory.Limits.cokernel.π (R.map φ) = 0 := by
      apply T.map_injective
      rw [Functor.map_zero, Functor.map_comp,
        ← CategoryTheory.Limits.π_comp_cokernelComparison (R.map φ) T, ← hβ']
      simp only [Category.assoc, CategoryTheory.Limits.cokernel.condition_assoc,
        CategoryTheory.Limits.zero_comp, CategoryTheory.Limits.comp_zero]
    refine ⟨U, hxV, CategoryTheory.Abelian.monoLift (R.map φ) (R.map α) hz, ?_⟩
    exact CategoryTheory.Abelian.monoLift_comp (R.map φ) (R.map α) hz

end AlgebraicGeometry.Scheme
