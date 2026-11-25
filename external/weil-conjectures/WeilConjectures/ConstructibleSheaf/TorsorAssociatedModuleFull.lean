/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleDiagonalEvaluation
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleRecoverLinear

/-!
# Fullness of the associated module functor

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-full)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
open Etale

/-- Associated module sheaves on a connected torsor remember precisely the
intertwining maps of representations.
Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-associated-module-full)

Proof:
Pull a sheaf map back to the torsor and use evaluation at the diagonal to identify
both associated sheaves with constant module sheaves. On a nonempty connected
scheme a map between constant module sheaves is induced by a unique linear map
of values: the image of each constant section is locally constant and hence
constant, and arbitrary locally constant sections are locally constant sections
of this form. Commutation with the canonical descent isomorphism on each group
component of the double overlap says that the recovered linear map intertwines
the representation actions. Its pointwise map on equivariant sections descends
to the original sheaf map, since equality is detected by the etale surjective
cover. This proves fullness. The zero module and trivial group need no exception;
no finite-dimensionality is used. -/
theorem Scheme.GaloisCover.associatedModuleFunctor_full
    {V : Scheme.{u}} [ConnectedSpace V] (ℓ : ℕ) [Fact ℓ.Prime]
    (P : Type u) [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P] :
    (c.associatedModuleFunctor ℓ).Full := by
  classical
  let := c.etale
  have hfull : (c.equivariantModulePresheafFunctor ℓ).Full := by
    constructor
    intro N N' η
    obtain ⟨f, hf, _⟩ := c.equivariantModulePresheaf_recoverLinear ℓ N N' η
    obtain ⟨x⟩ := ‹ConnectedSpace c.P›.toNonempty
    let W : V.Etale := Etale.mk c.π
    let d : c.sectionSpace W :=
      (pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x
    have hcomm : ∀ g n, f (N.ρ g n) = N'.ρ g (f n) := by
      intro g n
      obtain ⟨s, hs⟩ := c.equivariantSections_diagonalEvaluation_surjective ℓ N x n
      change s.val d = n at hs
      calc
        f (N.ρ g n) = f (s.val (c.sectionAction W g d)) := by rw [s.property, hs]
        _ = (η.app (op W) s).val (c.sectionAction W g d) := (hf W s _).symm
        _ = N'.ρ g ((η.app (op W) s).val d) := (η.app (op W) s).property g d
        _ = N'.ρ g (f n) := by
          exact congrArg (N'.ρ g) ((hf W s d).trans (congrArg f hs))
    let φ : N ⟶ N' :=
      ConcreteCategory.ofHom (f.intertwiningMap_of_isIntertwiningMap N.ρ N'.ρ hcomm)
    refine ⟨φ, ?_⟩
    apply NatTrans.ext
    funext W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    apply LocallyConstant.ext
    intro y
    exact (hf W.unop s y).symm
  let := hfull
  let R := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv.toRingHom : ULift.{u + 1} (ZMod ℓ) →+* ZMod ℓ)
  let F := c.equivariantModulePresheafFunctor ℓ ⋙
    (Functor.whiskeringRight V.Etaleᵒᵖ _ _).obj R
  let _ : R.IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv
      (ULift.ringEquiv : ULift.{u + 1} (ZMod ℓ) ≃+* ZMod ℓ)
  have hF : F.Full := by dsimp [F]; infer_instance
  let := hF
  have hsheaf : ∀ N, Presheaf.IsSheaf V.smallEtaleTopology (F.obj N) := by
    intro N
    exact c.equivariantModulePresheaf_isSheaf ℓ P N
  constructor
  intro N N' η
  let i := isoSheafify V.smallEtaleTopology (hsheaf N)
  let i' := isoSheafify V.smallEtaleTopology (hsheaf N')
  let θ : F.obj N ⟶ F.obj N' := i.hom ≫ η.hom ≫ i'.inv
  obtain ⟨φ, hφ⟩ := F.map_surjective θ
  refine ⟨φ, ?_⟩
  apply Sheaf.hom_ext
  change sheafifyMap V.smallEtaleTopology (F.map φ) = η.hom
  apply (cancel_epi i.hom).1
  rw [isoSheafify_hom, ← toSheafify_naturality, hφ]
  change (i.hom ≫ η.hom ≫ i'.inv) ≫ i'.hom = i.hom ≫ η.hom
  simp


end AlgebraicGeometry
