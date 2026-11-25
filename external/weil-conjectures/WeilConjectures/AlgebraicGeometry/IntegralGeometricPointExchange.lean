/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Square
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.IntegralGeometricFibreSections
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Integral exchange over a geometric point

Source: Stacks Project, Tag 0EYP, specialized to a geometric point; the strict-henselian
proof uses Tags 03Q9, 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-geometric-point-exchange).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Integral exchange for base change to the spectrum of an algebraically closed field.

Source: Stacks Project, Tag 0EYP, specialized to a geometric point; the strict-henselian
argument combines Tags 03Q9, 09XK, 09ZH and 0A3I.
(blueprint: lem-sbc-integral-geometric-point-exchange).

Proof: work over an affine neighbourhood of the image of s. By Tag 03Q9 the direct-image
stalk is the module of sections over X times_Y Spec A, where A is the strict henselization
at s. As f is integral, this pullback is Spec B for an integral A-algebra B. Write m for
the maximal ideal of A and kappa for its separably closed residue field. Tag 09XK makes
(B, mB) a henselian pair, and Tag 09ZH makes restriction of sections from Spec B to
Spec (B/mB) bijective. Equivalently, apply the existing henselian degree-zero theorem
for proper schemes to the identity of Spec B: this requires no properness of f. The
embedding kappa -> Omega furnished by s identifies X times_Y Spec Omega with the base
change of Spec (B/mB) to Omega. Tag 0A3I makes this further restriction on sections
bijective, even if Omega is transcendental over kappa.

Identify the source stalk of the exchange at the identity point of Spec Omega with
(f_* F)_s using the inverse-image stalk isomorphism. Identify its target stalk with
the sections of g'^* F over X' using the terminal-object stalk formula on Spec Omega.
For a germ represented by a section on X times_Y V, expand the unit-square-counit
formula for base change: it sends that section to its pullback on X' times_SpecOmega
(Spec Omega times_Y V), and then to its restriction on X'. This is exactly the composite
of the two restriction maps above. Thus the actual exchange is bijective on the unique
geometric stalk. Geometric stalks detect isomorphisms, and the forgetful functor from
module sheaves reflects them, proving the result. If the fibre is empty, all section
modules in the comparison are zero. No torsion or finite-type assumption is used. -/
theorem isIso_baseChangeMap_app_of_isIntegralHom_geometricPoint
    (Λ : Type (u + 1)) [CommRing Λ] {X' X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of Ω)} {f : X ⟶ Y}
    {s : Spec (.of Ω) ⟶ Y} (sq : IsPullback g' f' f s) [IsIntegralHom f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F)  := by
  obtain ⟨Θ, hΘ, hGerms⟩ := integralGeometricFibreSections Λ sq F
  let : IsIso Θ := hΘ
  obtain ⟨b, hb⟩ := geometricFibreExchange_germs Λ sq F Θ hGerms
  let φ := (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F
  let p := Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))
  have hφ : IsIso (p.sheafFiber.map φ) := by
    have hcomp : IsIso (p.sheafFiber.map φ ≫ b.hom) := by
      rw [hb]
      infer_instance
    exact (isIso_comp_right_iff _ b.hom).mp hcomp
  have hcover : (⋃ _ : PUnit.{u + 1}, Set.range (𝟙 (Spec (.of Ω)))) = Set.univ := by
    ext x
    simp
  have hc := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale_of_iUnion_range_eq_univ
    (Spec (.of Ω)) (Ω := fun _ : PUnit.{u + 1} ↦ Ω) (fun _ ↦ 𝟙 _) hcover
  apply ((hc.jointlyReflectIsomorphisms (ModuleCat.{u + 1} Λ)).isIso_iff φ).2
  rintro ⟨_, ⟨i⟩⟩
  rw [NatIso.isIso_map_iff ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).uliftSheafFiberIso
    (ModuleCat.{u + 1} Λ))]
  exact hφ

end AlgebraicGeometry.Etale
