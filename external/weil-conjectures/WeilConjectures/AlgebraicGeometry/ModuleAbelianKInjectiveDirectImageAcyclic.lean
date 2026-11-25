/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition

/-! # Underlying abelian direct-image acyclicity of module K-injectives

Source: Stacks Project, Cohomology on Sites, Tag 0D6J(3).
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Abelian replacement of a module K-injective remains a quasi-isomorphism after direct image.
This asserts acyclicity for the indicated direct image, without asserting that forgetting
preserves K-injectivity.

Source: Stacks Project, Cohomology on Sites, Tag 0D6J(3), including its resolution
normalization; equivalently apply Tag 0D6E to coefficient restriction and direct image.
(auxiliary; not a blueprint node).

Proof: Use the constant-ring module equivalence, retaining the underlying additive
sheaf. Encode abelian sheaves as modules over the constant integers; ULift of the
integers supplies the coefficient universe when necessary. The coefficient forgetful
functor is the module direct image of the identity-topos ring map from the constant
integers to the constant Lambda sheaf. The geometric morphism induced by v, equipped
with its constant-integer structural map, gives a second ringed-topos morphism. Its
module direct image is ordinary abelian direct image under the integer encoding.
The structural maps preserve the ring operations, and the direct-image scalar action
is sectionwise, so the generalized-element module-linearity identities hold.

For the abstract ringed-topos interface, replace each etale site by AsSmall,
with morphisms lifted to the object universe and the induced topology. Precomposition
by the site equivalence transports rings, modules, and underlying additive sheaves.
Its unit and counit give exact inverse equivalences. Conjugate base change and the
set inverse-image adjunction by these equivalences; finite-limit preservation is
retained. Thus the site, ring and module universes match the abstract theorem.

Transport I, J, and j through these exact equivalences. K-injectivity is preserved:
the inverse equivalence is exact, so the adjunction transports null-homotopies from
acyclic complexes. Quasi-isomorphisms are preserved and reflected by the homology
comparison for an exact equivalence. Apply the final resolution-normalization clause
of ringedToposDerivedPushforwardComposition (Tag 0D6E) to the two morphisms above.
It asserts directly that the second module direct image of j is a quasi-isomorphism.
The underlying-sheaf identifications turn that map into v_*j, proving the claim.
The identity morphism, zero ring, zero complex, empty etale objects, and arbitrary
shifts are included; no boundedness or finite cohomological dimension is used.
-/
theorem moduleAbelianForget_kInjective_directImage_quasiIso
    (Λ : Type (u + 1)) [CommRing Λ] {A B : Scheme.{u}} (v : A ⟶ B)
    (I : CochainComplex (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf A.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : ((moduleAbelianForget Λ A).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j] :
    QuasiIso ((((v)_*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).map j) := by
  obtain ⟨C, D, hC, hD, T, S, R, Z, W, eM, eA, eB, r, p, ⟨α⟩, ⟨β⟩⟩ :=
    etaleModuleAbelianRingedPresentation Λ v
  let := hC
  let := hD
  have : eM.functor.Additive := eM.functor.additive_of_preserves_binary_products
  have : eA.functor.Additive := eA.functor.additive_of_preserves_binary_products
  have : eB.functor.Additive := eB.functor.additive_of_preserves_binary_products
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose T (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj Z))
  let := HasDerivedCategory.standard
    (SheafOfModules.{u + 1}
      ((sheafCompose S (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj W))
  let Mc := eM.functor.mapHomologicalComplex (.up ℤ)
  let Ac := eA.functor.mapHomologicalComplex (.up ℤ)
  let Bc := eB.functor.mapHomologicalComplex (.up ℤ)
  let rc := r.modules.mapHomologicalComplex (.up ℤ)
  let pc := p.modules.mapHomologicalComplex (.up ℤ)
  let vc := ((v)_*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)
  let αc := NatIso.mapHomologicalComplex α (.up ℤ)
  let βc := NatIso.mapHomologicalComplex β (.up ℤ)
  let j' : rc.obj (Mc.obj I) ⟶ Ac.obj J := αc.hom.app I ≫ Ac.map j
  have : QuasiIso j' := by dsimp [j', Ac]; infer_instance
  obtain ⟨Rf, Rg, Rgf, ηf, ηg, ηgf, hf, hg, hgf, hIf, hIg, κ, hκ, _⟩ :=
    ringedToposDerivedPushforwardComposition T T S R Z W r p
  have : QuasiIso (pc.map j') :=
    (hκ.2 (Mc.obj I) inferInstance (Ac.obj J) inferInstance j').1
  have : QuasiIso (pc.map (Ac.map j)) := by
    have : QuasiIso (pc.map (αc.hom.app I) ≫ pc.map (Ac.map j)) := by
      rw [← pc.map_comp]
      exact inferInstanceAs (QuasiIso (pc.map j'))
    exact quasiIso_of_comp_left (pc.map (αc.hom.app I)) _
  have : QuasiIso (βc.hom.app _ ≫ Bc.map (vc.map j)) := by
    have hn : pc.map (Ac.map j) ≫ βc.hom.app J =
        βc.hom.app _ ≫ Bc.map (vc.map j) := βc.hom.naturality j
    rw [← hn]
    exact quasiIso_comp (pc.map (Ac.map j)) (βc.hom.app J)
  have : QuasiIso (Bc.map (vc.map j)) :=
    quasiIso_of_comp_left (βc.hom.app _) _
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (vc.map j) eB.functor).mp inferInstance

end AlgebraicGeometry.Etale
