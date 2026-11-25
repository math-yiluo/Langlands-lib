/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import WeilConjectures.AlgebraicGeometry.CoherentStalkMapExtends
import WeilConjectures.AlgebraicGeometry.CoherentLocalIsomorphism
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleStalkFinite
import WeilConjectures.AlgebraicGeometry.FiniteFreeModuleStalkEquiv
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.CoherentIntegralGenericFreeNeighbourhood

/-! # A local free model along an integral closed subscheme

Source: Stacks Project, Tag 01YE, the argument before clearing denominators.
(blueprint: lem-pc-c3-coherent-generic-local-free-model)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private noncomputable def affine_restrict_sections {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(M.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) where
  toFun x := M.presheaf.map (homOfLE (by rw [Hom.image_top_eq_opensRange,
    hU.opensRange_fromSpec])).op ((M.restrictAppIso hU.fromSpec ⊤).hom x)
  invFun y := (M.restrictAppIso hU.fromSpec ⊤).inv
    (M.presheaf.map (homOfLE (hU.fromSpec_image_le ⊤)).op y)
  map_add' x y := by simp
  map_smul' r x := by
    dsimp only
    rw [restrictAppIso_fromSpec_smul, map_smul, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, RingHom.id_apply]
  left_inv x := by
    dsimp only
    rw [← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op (hU.fromSpec ''ᵁ ⊤) ⟶ _) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply, Iso.hom_inv_id_apply]
  right_inv y := by
    dsimp only
    rw [Iso.inv_hom_id_apply, ← Functor.map_comp_apply,
      Subsingleton.elim (_ ≫ _ : Opposite.op U ⟶ Opposite.op U) (𝟙 _),
      CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

private theorem sections_fraction {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {W O : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (hO : X.basicOpen g = O) (hOW : O ≤ W) (s : Γ(E, O)) :
    ∃ n : ℕ, ∃ t : Γ(E, W), E.presheaf.map (homOfLE hOW).op t =
      X.presheaf.map (homOfLE hOW).op g ^ n • s := by
  subst hO
  exact exists_map_eq_pow_smul_of_isAffineOpen E hW g s

private theorem sections_vanishing {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {W O : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W))
    (hO : X.basicOpen g = O) (hOW : O ≤ W) (t : Γ(E, W))
    (ht : E.presheaf.map (homOfLE hOW).op t = 0) : ∃ n : ℕ, g ^ n • t = 0 := by
  subst hO
  exact exists_pow_smul_eq_zero_of_isAffineOpen E hW g t ht

/-- The pushforward of a finite free module along a closed immersion is coherent
on a locally Noetherian target.

Source: Stacks Project Tag 01Y6 (finite pushforward) and Tag 01XZ (coherence).

Proof: Work on an affine open Spec A of X. Its preimage is Spec B, where B is
an A-algebra quotient because i is a closed immersion. The finite free sheaf on I
restricts to the sheaf associated with the finite free B-module B^I. Viewed as an
A-module it is finite: B is cyclic over A, and I is finite. On an affine target,
closed pushforward agrees with the associated sheaf of this restricted-scalar
module: over every basic open D(f), both sheaves have the sections (B^I)_f, with
the same restriction maps and A_f-action. These identifications glue on the basic
open basis and commute on overlaps. Thus the pushforward is quasi-coherent and
of finite type. Since A is Noetherian, the finite A-module is finitely presented;
equivalently the locally Noetherian coherence criterion makes its associated
sheaf coherent. Coherence is local, so these affine calculations give coherence
on X. For I empty the module and its pushforward are zero and the same argument
applies. No integrality or pointwise annihilation hypothesis is needed. -/
private theorem isCoherent_closedImmersion_finiteFree {X Z : Scheme.{u}}
    [IsLocallyNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (I : Type u) [Finite I] :
    RingedSpace.IsCoherent X.toRingedSpace
      ((pushforward i).obj (SheafOfModules.free (R := Z.ringCatSheaf) I)) := by
  classical
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) I
  let P := SheafOfModules.presentationOfIsCokernelFree
    (0 : SheafOfModules.free (PEmpty.{u + 1}) ⟶ E)
    (𝟙 E) (by simp) (CokernelCofork.IsColimit.ofId _ rfl)
  have : P.IsFinite := ⟨⟨inferInstanceAs (Finite I)⟩,
    ⟨inferInstanceAs (Finite (PEmpty.{u + 1}))⟩⟩
  have : E.IsFinitePresentation := P.isFinitePresentation
  have : ((pushforward i).obj E).IsQuasicoherent := by
    refine isQuasicoherent_of_forall_isAffineOpen _
      (fun W hW g s ↦ ?_) (fun W hW g t ht ↦ ?_)
    · obtain ⟨n, t, ht⟩ := sections_fraction E
        (hW.preimage i) (i.app W g) (i.preimage_basicOpen g).symm
        (i.preimage_mono (X.basicOpen_le g)) s
      refine ⟨n, t, ht.trans ?_⟩
      have h : i.app (X.basicOpen g) (X.presheaf.map (homOfLE (X.basicOpen_le g)).op g) =
          Z.presheaf.map (homOfLE (i.preimage_mono (X.basicOpen_le g))).op (i.app W g) := by
        rw [← ConcreteCategory.comp_apply, i.naturality]
        rfl
      rw [← h, ← map_pow]
      rfl
    · obtain ⟨n, hn⟩ := sections_vanishing E
        (hW.preimage i) (i.app W g) (i.preimage_basicOpen g).symm
        (i.preimage_mono (X.basicOpen_le g)) t ht
      rw [← map_pow] at hn
      exact ⟨n, hn⟩
  let A := {V : X.Opens // IsAffineOpen V}
  have finite_sections (V : A) : Module.Finite Γ(X, V.1)
      Γ((pushforward i).obj E, V.1) := by
    have : Module.Finite Γ(Z, i ⁻¹ᵁ V.1) Γ(E, i ⁻¹ᵁ V.1) :=
      finite_sections_of_isFinitePresentation E (V.2.preimage i)
    let := (i.app V.1).hom.toAlgebra
    let : Module Γ(X, V.1) Γ(E, i ⁻¹ᵁ V.1) := Module.compHom _ (i.app V.1).hom
    have : IsScalarTower Γ(X, V.1) Γ(Z, i ⁻¹ᵁ V.1) Γ(E, i ⁻¹ᵁ V.1) :=
      ⟨fun a b m ↦ mul_smul _ _ _⟩
    have : Module.Finite Γ(X, V.1) Γ(Z, i ⁻¹ᵁ V.1) :=
      Module.Finite.of_surjective (Algebra.linearMap _ _) (i.app_surjective V.1 V.2)
    have := Module.Finite.trans Γ(Z, i ⁻¹ᵁ V.1) Γ(E, i ⁻¹ᵁ V.1)
      (R := Γ(X, V.1))
    exact Module.Finite.equiv
      { AddEquiv.refl _ with map_smul' _ _ := rfl :
        Γ(E, i ⁻¹ᵁ V.1) ≃ₗ[Γ(X, V.1)] Γ((pushforward i).obj E, V.1) }
  have (V : A) : IsNoetherianRing Γ(X, V.1) :=
    IsLocallyNoetherian.component_noetherian ⟨V.1, V.2⟩
  have (V : A) : Module.Finite Γ(X, V.1)
      Γ(((pushforward i).obj E).restrict V.2.fromSpec, ⊤) :=
    Module.Finite.equiv (affine_restrict_sections _ V.2).symm
  choose Q hQ using fun V : A ↦
    exists_presentation_isFinite (((pushforward i).obj E).restrict V.2.fromSpec)
  have : ((pushforward i).obj E).IsFinitePresentation := by
    refine isFinitePresentation_of_iSup_opensRange_eq_top _ (fun V : A ↦ V.2.fromSpec) ?_ Q
    refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    obtain ⟨V, hV, hxV, _⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (U := ⊤) (Set.mem_univ x)
    exact ⟨⟨V, hV⟩, by rwa [IsAffineOpen.opensRange_fromSpec]⟩
  exact (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
    ⟨inferInstance, inferInstance⟩


/-- Extend a coherent stalk isomorphism by Tag 01Y4, shrink by Tag 01Y3,
then transport the resulting open in the open subscheme back to X. -/
private theorem coherent_stalk_iso_near {X : Scheme.{u}} [IsLocallyNoetherian X]
    (F G : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hG : RingedSpace.IsCoherent X.toRingedSpace G) (x : X)
    (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj G ≅
      (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty (G.restrict U.ι ≅ F.restrict U.ι) := by
  obtain ⟨U, hx, φ, hφ⟩ := exists_open_hom_of_coherent_stalk_map F G hF hG x ψ.hom
  let y : U.toScheme := ⟨x, hx⟩
  let s := restrictStalkNatIso U.ι y
  let f := (RingedSpace.moduleStalkFunctor U.toScheme.toRingedSpace y).map φ
  have heq : (fun m ↦ ConcreteCategory.hom (s.hom.app F)
      (f (ConcreteCategory.hom (s.inv.app G) m))) = ψ.hom := by
    funext m
    exact (hφ m).symm
  have hb : Function.Bijective f := by
    have hb : Function.Bijective (fun m ↦ ConcreteCategory.hom (s.hom.app F)
        (f (ConcreteCategory.hom (s.inv.app G) m))) := by
      rw [heq]
      exact ConcreteCategory.bijective_of_isIso ψ.hom
    exact ((ConcreteCategory.bijective_of_isIso (s.hom.app F)).of_comp_iff' _).mp
      (((Function.Bijective.of_comp_iff _
        (ConcreteCategory.bijective_of_isIso (s.inv.app G))).mp hb))
  have hFU := (coherent_module_local_on_open_cover X F (ULift.{u} PUnit)
    (fun _ ↦ ⊤) iSup_const).1 hF U
  have hGU := (coherent_module_local_on_open_cover X G (ULift.{u} PUnit)
    (fun _ ↦ ⊤) iSup_const).1 hG U
  obtain ⟨W, hy, hW⟩ := (coherent_local_isomorphism U.toScheme
    (F.restrict U.ι) (G.restrict U.ι) hFU hGU φ y).2.2.2 hb
  have : IsIso (φ.over W) := hW
  let e := ((overFunctorEquiv W).app (G.restrict U.ι)).symm ≪≫
    (overEquiv W).functor.mapIso (asIso (φ.over W)) ≪≫
    ((overFunctorEquiv W).app (F.restrict U.ι))
  let g : W.toScheme ⟶ X := W.ι ≫ U.ι
  let e' : G.restrict g ≅ F.restrict g :=
    (restrictFunctorComp W.ι U.ι).app G ≪≫ e ≪≫
      ((restrictFunctorComp W.ι U.ι).app F).symm
  refine ⟨g.opensRange, ?_, ⟨?_⟩⟩
  · exact ⟨⟨y, hy⟩, rfl⟩
  · exact restrictCompIso G g g.isoOpensRange.inv g.opensRange.ι
      g.isoOpensRange_inv_comp ≪≫
      (restrictFunctor g.isoOpensRange.inv).mapIso e' ≪≫
      (restrictCompIso F g g.isoOpensRange.inv g.opensRange.ι
        g.isoOpensRange_inv_comp).symm

/-- Package the canonical closed-pushforward germ comparison as a linear isomorphism
by restriction of scalars. Its inverse is determined by the bijective comparison. -/
private noncomputable def closed_pushforward_stalk_iso {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (G : Z.Modules) (z : Z) :
    (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).obj
      ((pushforward i).obj G) ≅
    (ModuleCat.restrictScalars (i.stalkMap z).hom).obj
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G) := by
  obtain ⟨hb, _, hl⟩ := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 z
  let f : (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base z)).obj
      ((pushforward i).obj G) →ₗ[X.presheaf.stalk (i.base z)]
      (ModuleCat.restrictScalars (i.stalkMap z).hom).obj
        ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj G) :=
    { ConcreteCategory.hom
        (TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z) with
      map_smul' := hl }
  exact (LinearEquiv.ofBijective f hb).toModuleIso

/-- A maximal-ideal-annihilated generic stalk has a local model by the closed
pushforward of a finite free module. This asserts no global map or ideal lattice.

Source: Stacks Project, Tag 01YE, first paragraphs through the local free map.
(blueprint: lem-pc-c3-coherent-generic-local-free-model)

Proof: let x be the image of the generic point of Z. The closed-immersion stalk
map O_X,x -> O_Z,xi is surjective, and O_Z,xi is a field by integrality. Its kernel
is therefore the maximal ideal of O_X,x. The annihilation hypothesis gives the
actual stalk F_x a module action over this quotient, hence over O_Z,xi. Coherence
makes F_x finite over O_X,x; the identity semilinear map makes it finite over the
field as well. A finite basis identifies F_x with the stalk of the finite free
sheaf E = O_Z^{direct sum r}. The canonical closed-pushforward comparison transports
this to an O_X,x-linear isomorphism (i_*E)_x -> F_x.

The private affine calculation proves i_*E coherent: closed immersion gives affine
preimages and surjective coordinate-ring maps, basic-open localization gives
quasi-coherence, and finite sections over the quotient ring are finite over the
ambient Noetherian ring. Finite affine presentations then give coherence. Extend
the stalk isomorphism between these coherent sheaves to a map on a neighbourhood,
and shrink until it is an isomorphism (Tags 01Y4 and 01Y3). Transport the nested
open restrictions back to an ambient open and reindex the free sheaf by Fin r.
The same construction includes r = 0 and needs no support hypothesis on F. -/
theorem coherent_generic_local_free_model
    {X Z : Scheme.{u}} [IsNoetherian X]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hkill : ∀ a ∈ IsLocalRing.maximalIdeal
      (X.presheaf.stalk (i.base (genericPoint Z))),
      ∀ m : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint Z))).obj F, a • m = 0) :
    ∃ (r : ℕ) (U : X.Opens), i.base (genericPoint Z) ∈ U ∧
      Nonempty ((restrictFunctor U.ι).obj
        ((pushforward i).obj (∐ fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf)) ≅
        (restrictFunctor U.ι).obj F) := by
  classical
  let ξ := genericPoint Z
  let R := X.presheaf.stalk (i.base ξ)
  let K := Z.presheaf.stalk ξ
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base ξ)).obj F
  let φ : R →+* K := (i.stalkMap ξ).hom
  have hφ : Function.Surjective φ := i.stalkMap_surjective ξ
  have hker : RingHom.ker φ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.ker_eq_maximalIdeal φ hφ
  have ht : Module.IsTorsionBySet R M (RingHom.ker φ) := by
    intro m a
    exact hkill a (hker ▸ a.property) m
  let q : R ⧸ RingHom.ker φ ≃+* K := RingHom.quotientKerEquivOfSurjective hφ
  let : Module (R ⧸ RingHom.ker φ) M := ht.module
  let : Module K M := Module.compHom M q.symm.toRingHom
  have hsmul (a : R) (m : M) : φ a • m = a • m := by
    change q.symm (φ a) • m = a • m
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply]
    rfl
  let f : M →ₛₗ[φ] M :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a m ↦ (hsmul a m).symm }
  have : F.IsFiniteType := hF.1
  have : Module.Finite R M := finite_moduleStalk_of_isFiniteType X F (i.base ξ)
  have : Module.Finite K M := Module.Finite.of_surjective f Function.surjective_id
  let b := Module.finBasis K M
  let r := Module.finrank K M
  let E : Z.Modules := SheafOfModules.free (R := Z.ringCatSheaf) (ULift.{u} (Fin r))
  obtain ⟨e⟩ := exists_finite_free_moduleStalk_linearEquiv Z (ULift.{u} (Fin r)) ξ
  let bg := b.reindex Equiv.ulift.symm
  let ψ := (e.trans bg.equivFun.symm).toModuleIso
  let T := ModuleCat.restrictScalars φ
  let a : T.obj (ModuleCat.of K M) ≅
      (RingedSpace.moduleStalkFunctor X.toRingedSpace (i.base ξ)).obj F :=
    (show T.obj (ModuleCat.of K M) ≃ₗ[R] M from
      { AddEquiv.refl M with map_smul' := hsmul }).toModuleIso
  let ψ' := closed_pushforward_stalk_iso i E ξ ≪≫ T.mapIso ψ ≪≫ a
  have hEi := isCoherent_closedImmersion_finiteFree i (ULift.{u} (Fin r))
  obtain ⟨U, hx, eU⟩ := coherent_stalk_iso_near F ((pushforward i).obj E)
    hF hEi (i.base ξ) ψ'
  let c : (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) ≅ E :=
    Sigma.whiskerEquiv (f := fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf)
      (g := fun _ : ULift.{u} (Fin r) ↦ SheafOfModules.unit Z.ringCatSheaf)
      (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r))
      (fun _ ↦ Iso.refl _)
  exact ⟨r, U, hx, ⟨(restrictFunctor U.ι).mapIso ((pushforward i).mapIso c) ≪≫
    eU.some⟩⟩

end AlgebraicGeometry.Scheme.Modules
