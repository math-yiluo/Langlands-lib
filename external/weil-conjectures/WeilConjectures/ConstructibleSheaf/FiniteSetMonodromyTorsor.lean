/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
import WeilConjectures.ConstructibleSheaf.RepresentablePullbackConstantOfEvaluation
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension

/-!
# Connected monodromy torsors for finite sheaves of sets

Source: Stacks Project, Tags 0DV5 (1), 0DV6, and Section 03SF.
(blueprint: lem-weil-pbc-finite-set-monodromy-torsor)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite locally constant sheaf of sets becomes constant on its connected monodromy
 torsor. Source: Stacks Project, Tags 0DV5 (1), 0DV6, and Section 03SF.
(blueprint: lem-weil-pbc-finite-set-monodromy-torsor)

Proof: choose a geometric point of the nonempty connected scheme U. The finite etale
and finite locally constant equivalence and the fundamental-group equivalence identify F
with a finite discrete set S acted on continuously by the fundamental group. The image
Q in the permutation group of S is finite. Its kernel is open: it is the intersection
of the finitely many open stabilizers of elements of S. It is normal because it is a
kernel. Shrink Q to Type u and transport its group structure. Under the Galois
correspondence, the regular transitive action on Q gives a connected finite etale
cover. Commuting right translations, converted to a left action by inversion, give
a Q-torsor. Transport this latter action to ULift Q. Base change to this cover restricts
the action on S to the kernel, where it is trivial. Compatibility of the equivalences with
inverse image
identifies this pullback with the constant sheaf of S. For the empty set S the image
is the trivial group and the cover is the identity; the same argument applies. -/
theorem exists_connected_torsor_constant_set_pullback
    {U : Scheme.{u}} [ConnectedSpace U]
    (F : Sheaf U.smallEtaleTopology (Type (u + 1)))
    (hF : IsLisseEtaleSheafOfSets F) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q)
      (c : GaloisCover (ULift.{u + 1} Q) U) (_ : ConnectedSpace c.P),
      ((etaleSetPullback c.π).obj F).IsConstant c.P.smallEtaleTopology := by
  classical
  obtain ⟨Φ, ⟨α⟩, -, -⟩ := exists_finiteEtale_flc_equivalence_sheaf U
  let P := Φ.inverse.obj ⟨F, hF⟩
  let e : U.smallEtaleTopology.uliftYoneda.{u + 1}.obj P.obj ≅ F :=
    (α.app P).symm ≪≫ (ObjectProperty.ι _).mapIso (Φ.counitIso.app ⟨F, hF⟩)
  obtain ⟨x⟩ := (inferInstance : Nonempty U)
  let Ω := AlgebraicClosure (U.residueField x)
  let s : Spec (.of Ω) ⟶ U :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.residueField x) Ω)) ≫
      U.fromSpecResidueField x
  obtain ⟨A, a, hA, heval⟩ :=
    PreGaloisCategory.exists_galois_representative (FiniteEtale.fiber s) P
  have : PreGaloisCategory.IsGalois A := hA
  have : ConnectedSpace A.obj.left := FiniteEtale.connectedSpace_of_isConnected A
  let Q := Aut A
  let δ : ULift.{u + 1} Q ≃* Aut A := MulEquiv.ulift
  -- Use the underlying morphisms of the automorphisms to define the torsor action.
  let v (q : ULift.{u + 1} Q) : A ⟶ A := (δ q).asIso.hom
  have hv (b d : (FiniteEtale.fiber s).obj A) :
      ∃! q, (FiniteEtale.fiber s).map (v q) b = d := by
    have hb := PreGaloisCategory.evaluation_aut_bijective_of_isGalois
      (FiniteEtale.fiber s) A b
    have hbij := hb.comp δ.bijective
    obtain ⟨q, hq⟩ := hbij.2 d
    exact ⟨q, hq, fun r hr ↦ hbij.1 (hr.trans hq.symm)⟩
  let c : GaloisCover (ULift.{u + 1} Q) U :=
    { P := A.obj.left
      π := A.obj.hom
      isFinite := A.property
      etale := A.obj.prop
      surjective := FiniteEtale.surjective_of_nonempty_fiber s A ⟨a⟩
      smul q := (v q).hom.left
      smul_π q := FiniteEtale.hom_left_comp (v q)
      one_smul := by
        change ((δ 1).asIso.hom).hom.left = _
        rw [map_one]
        rfl
      mul_smul q r := by
        change ((δ (q * r)).asIso.hom).hom.left = _
        rw [map_mul]
        rfl
      isIso_sigmaDesc := FiniteEtale.isIso_sigmaDesc_of_existsUnique s A v hv }
  have hc : ((etaleSetPullback c.π).obj
      (U.smallEtaleTopology.uliftYoneda.{u + 1}.obj P.obj)).IsConstant
        c.P.smallEtaleTopology :=
    FiniteEtale.representable_pullback_isConstant_of_evaluation_bijective s A P a heval
  exact ⟨Q, inferInstance, inferInstance, c, inferInstance,
    Sheaf.isConstant_congr _ ((etaleSetPullback c.π).mapIso e)⟩

end AlgebraicGeometry.Scheme
