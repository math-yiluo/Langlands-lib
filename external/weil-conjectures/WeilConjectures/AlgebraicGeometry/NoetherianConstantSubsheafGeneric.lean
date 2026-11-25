/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.ConstantSubsheafGenericStalkModel
import WeilConjectures.AlgebraicGeometry.FiniteConstantMapOpenFactorization

/-! # Generic generation in a submodule of a finite constant module sheaf -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Generic generators of a submodule of a finite constant sheaf extend to a finite
locally constant subsystem on an open neighbourhood of the generic point.
Source: Stacks Project, Tag 09BH, Proposition 59.74.1 (3), generator lifting and descent
on the irreducible constant base, before the final equality of sheaves.
(blueprint: lem-weil-pbc-noetherian-constant-subsheaf-generic).

Proof: Write G as the constant sheaf with value M. Its geometric stalk at the generic
point is M, so M is a finitely generated module by finiteness of G. Exactness of geometric
stalks identifies the generic stalk of F with a submodule N of M. Since the coefficient
ring is Noetherian, N has finitely many generators. Represent them on one common pointed
étale neighbourhood and refine until their images are their constant sections in M.
On the fibre product the two lifts coincide, because their images in G coincide and
F embeds into G. Sheaf descent therefore makes them sections over the open image of
that neighbourhood. Every relation between the generators vanishes in F because it
vanishes in M. Hence they define a morphism from the constant N sheaf to F there.
Its composite into constant M is the constant inclusion N into M, which is mono:
constant presheaves and sheafification preserve monomorphisms. Thus the morphism into F
is mono. The constant N sheaf is finite locally constant since N is finitely generated.
Its map on the chosen generic stalk is surjective by construction. The stalks at
separably closed extensions of the generic residue field are identified by compatible
separable closures. Those identifications commute with the maps into constant M, so
surjectivity holds at every geometric point above the generic point. For N = 0 use the
zero constant sheaf and the empty list of generators. No equality with F away from the
generic point is asserted; neither X nor the underlying set of M must be Noetherian. -/
theorem exists_open_generic_generating_subsheaf_of_mono_constant
    {X : Scheme.{u}} [IrreducibleSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsFiniteSheaf G]
    (hG : G.IsConstant X.smallEtaleTopology)
    (η : X) (hη : IsGenericPoint η Set.univ) :
    ∃ (U : X.Opens) (_hU : η ∈ U),
      ∃ (H : Sheaf U.toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (ψ : H ⟶ (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F),
        Mono ψ ∧ IsFiniteLocallyConstantSheaf H ∧
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.toScheme),
          s (IsLocalRing.closedPoint Ω) = (⟨η, _hU⟩ : U.toScheme) →
          Epi ((pointSmallEtale s).sheafFiber.map ψ) := by
  classical
  have : Limits.PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    Limits.preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : AB5OfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_shrink.{u, u, u + 1, u + 1} _
  obtain ⟨N, α, hα, hmodel⟩ :=
    exists_constant_generic_stalk_model_of_mono_constant φ hG η hη
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  let := hα
  obtain ⟨e, he⟩ := hmodel _ (X.algClosurePoint η) (by simp)
  let S := (pointSmallEtale (X.algClosurePoint η)).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have : Module.Finite Λ (S.obj G) := (ModuleCat.isFinitelyGenerated_iff _).mp
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (F := G) _ _)
  have hfin : Module.Finite Λ (S.obj C) :=
    Module.Finite.of_injective (S.map α).hom
      ((ModuleCat.mono_iff_injective (S.map α)).mp inferInstance)
  have hN : Module.Finite Λ N := (ModuleCat.isFinitelyGenerated_iff N).mp
    (((ModuleCat.isFinitelyGenerated_iff (S.obj C)).mpr hfin).of_iso
      ((pointSmallEtale (X.algClosurePoint η)).sheafFiberConstantSheafIso N))
  let := hN
  have hC : IsFiniteLocallyConstantSheaf C := {
    toIsLocallyConstantSheaf :=
      (Sheaf.isConstant_of_iso X.smallEtaleTopology (Iso.refl C)).isLocallyConstantSheaf
    toIsFiniteSheaf := ⟨fun Ω _ _ s ↦
      ((ModuleCat.isFinitelyGenerated_iff N).mpr hN).of_iso
        ((pointSmallEtale s).sheafFiberConstantSheafIso N).symm⟩ }
  let := hC
  obtain ⟨U, hU, ψ, hψ⟩ :=
    exists_open_factorization_of_finite_constant_map φ N α η e.hom he
  let P := Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι
  have hmono : Mono ψ := by
    have : Mono (ψ ≫ P.map φ) := hψ.symm ▸ inferInstanceAs (Mono (P.map α))
    exact mono_of_mono ψ (P.map φ)
  refine ⟨U, hU, P.obj C, ψ, hmono,
    IsFiniteLocallyConstantSheaf.upperStar U.ι C, ?_⟩
  intro Ω _ _ s hs
  have hsη : (s ≫ U.ι) (IsLocalRing.closedPoint Ω) = η := by
    rw [Scheme.Hom.comp_apply, hs]
    rfl
  obtain ⟨i, hi⟩ := hmodel Ω (s ≫ U.ι) hsη
  let c := Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.ι s
  let j := (c.app C) ≪≫ i ≪≫ (c.app F).symm
  have hj : j.hom ≫ (pointSmallEtale s).sheafFiber.map (P.map φ) =
      (pointSmallEtale s).sheafFiber.map (P.map α) := by
    dsimp [j]
    have hφ := c.inv.naturality φ
    have hα' := c.hom.naturality α
    dsimp only [Functor.comp_map] at hφ hα'
    rw [Category.assoc, Category.assoc, ← hφ]
    rw [← Category.assoc i.hom, hi, ← Category.assoc, ← hα']
    simp [P]
  have hψj : (pointSmallEtale s).sheafFiber.map ψ = j.hom := by
    apply (cancel_mono ((pointSmallEtale s).sheafFiber.map (P.map φ))).mp
    rw [← (pointSmallEtale s).sheafFiber.map_comp, hψ, hj]
  rw [hψj]
  infer_instance

end AlgebraicGeometry.Scheme
