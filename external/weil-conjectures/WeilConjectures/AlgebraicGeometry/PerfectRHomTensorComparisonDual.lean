/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedInternalHomAdjunction

import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen
import WeilConjectures.AlgebraicGeometry.StrictlyPerfectFiniteFreeRefinement
import WeilConjectures.AlgebraicGeometry.FiniteFreeDerivedDualModel
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh

/-! The quasi-coherent perfect dual underlying the tensor-Hom comparison. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A perfect complex has a quasi-coherent perfect internal dual.
Source: Stacks Project, Cohomology, Tag 08DQ.
Proof: at each point take a strictly perfect representative supplied by IsPerfect.
Refine it to an affine bounded finite free representative. The finite free dual-model
lemma constructs its ordinary Hom complex with O[0], proves that it is bounded finite
free, and compares it with local RHom into the restriction of the actual tensor unit.
Compose this comparison with the first-variable image of the representative isomorphism
and the RHom open-restriction isomorphism. The resulting local models show that the
actual object RHom(K,O) is perfect: each finite free identification gives a retraction
by its inverse. The same models are bounded above finite free, so the actual dual is
pseudo-coherent. Apply schemeDerivedQCohProperty_of_isPseudoCoherent to obtain its
quasi-coherent cohomology. Equip this actual object with that proof in the full
subcategory; the required equality of underlying objects is reflexivity.
(blueprint: lem-pc-perfect-rhom-tensor-comparison-dual) -/
theorem exists_perfect_rhom_dual
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj) :
    ∃ Kdual : schemeDerivedQCohCategory X,
      Kdual.obj =
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X)) ∧
      Scheme.IsPerfect X Kdual.obj := by
  let D := (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
    X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X))
  have hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ P : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → Limits.IsZero (P.X n)) ∧
        (∀ n : ℤ, ∃ r : ℕ, Nonempty (P.X n ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj D ≅
            DerivedCategory.Q.obj P) := by
    intro x
    obtain ⟨U, hxU, P, hP, hKP⟩ := hK x
    obtain ⟨V, hxV, _, hV, F, hFb, hFf, ⟨eF⟩⟩ :=
      Scheme.exists_finiteFree_refinement_of_isStrictlyPerfect X K.obj U P hP hKP x hxU
    let : IsAffine V.toScheme := hV
    obtain ⟨G, hGb, hGf, ⟨eG⟩⟩ :=
      Scheme.exists_bounded_finiteFree_derived_dual_model X V F hFb hFf
    obtain ⟨eR⟩ := derivedInternalHom_restrict_open X.toRingedSpace V
      K.obj (𝟙_ (schemeDerivedCategory X))
    let C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)
    let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
        ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over V)
          (forget₂ CommRingCat RingCat)).obj (X.toRingedSpace.sheaf.over V))) _ _
        (inferInstanceAs (HasDerivedCategory.{w} C))) :=
      inferInstanceAs (Category.{w} (DerivedCategory C))
    let H := @derivedInternalHom.{u, w} (Over V) _
      ((Opens.grothendieckTopology X.toRingedSpace).over V)
      (X.toRingedSpace.sheaf.over V) (inferInstanceAs (HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))))
    refine ⟨V, hxV, G, hGb, hGf, ?_⟩
    exact ⟨eR.symm ≪≫ H.mapIso (eF.symm.op.prod (Iso.refl _)) ≪≫ eG.symm⟩
  have hperfect : Scheme.IsPerfect X D := by
    intro x
    obtain ⟨U, hxU, P, hPb, hPf, eP⟩ := hlocal x
    refine ⟨U, hxU, P, ⟨hPb, ?_⟩, eP⟩
    intro n
    obtain ⟨r, ⟨e⟩⟩ := hPf n
    exact ⟨r, e.hom, e.inv, e.hom_inv_id⟩
  have hpseudo : Scheme.IsPseudoCoherent X D := by
    intro x
    obtain ⟨U, hxU, P, ⟨a, b, hPb⟩, hPf, eP⟩ := hlocal x
    refine ⟨U, hxU, P, ⟨b, ?_⟩, hPf, eP⟩
    intro n hn
    exact hPb n (Or.inr hn)
  exact ⟨⟨D, Scheme.schemeDerivedQCohProperty_of_isPseudoCoherent X D hpseudo⟩,
    rfl, hperfect⟩

end AlgebraicGeometry
