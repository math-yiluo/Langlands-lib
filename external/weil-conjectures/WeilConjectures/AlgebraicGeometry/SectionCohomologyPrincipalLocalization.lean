/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalDenominators
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalTorsion

/-! # Principal localization of the cohomology presheaf

Source: Stacks Project, Tag 09MR, tensor-unit specialization.
(blueprint: lem-pc-section-cohomology-principal-localization).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The cohomology presheaf of a pushed-forward injective resolution localizes on
principal opens of an affine base open.

Source: Stacks Project, Tag 09MR, Lemma 30.17.3, and Tag 01E4.
(blueprint: lem-pc-section-cohomology-principal-localization).

Proof: put Y = f⁻¹W and pull a back to a function b on Y. Y is quasi-compact
and quasi-separated and f⁻¹D(a) = D(b). Restriction of the injective resolution
computes module cohomology on these opens. Apply invertS_cohomology to the
unit invertible module on Y. Its tensor powers and their tensor products with
F identify with F. Under these identifications the fractions are the ordinary
localization of H^q(Y,F) at b, and the restriction map is its numerator map.
The formula x/b^n ↦ b^(-n) res(x) is linear for Γ(T,W): the scalar action is
through f^♯ and restriction commutes with multiplication. The formula therefore
identifies the displayed linear map with the localization at a. In particular
it gives invertibility of a on the target, fraction surjectivity, and equality
of numerators after multiplying by a power, the three IsLocalizedModule fields.
For a = 0 both localized cohomology and cohomology on the empty open vanish;
for a a unit restriction is an isomorphism. The argument applies also in degree
zero and when W or F is zero. -/
theorem sectionCohomologyPresheaf_isLocalized_away {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom := by
  dsimp only
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : P.obj (op (T.basicOpen a)) ↦
      (T.presheaf.map (homOfLE (T.basicOpen_le a)).op a) • x)
    exact (T.toRingedSpace.isUnit_res_basicOpen a).smul_bijective
  · exact sectionCohomologyPresheaf_pow_lifts f F I q W hW a
  · exact sectionCohomologyPresheaf_pow_annihilates f F I q W hW a

end AlgebraicGeometry.Scheme.Modules
