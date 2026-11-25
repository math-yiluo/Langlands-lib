/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tags 09ZB, 03RV and 09ZA (the geometric step).
(blueprint: lem-weil-pbc-gabber-h1-torsors-trivial).

Proof: Local trivializations identify the underlying sheaf of each torsor with the
finite constant sheaf M. Hence it is finite locally constant. By Tag 03RV it is the
sheaf of sections of a finite etale scheme V over Z; Yoneda transports the M-action.
The morphism V to Z is surjective, since a torsor is locally nonempty. The spectrum
of R is affine, integral and normal, and its function field is FractionRing R, which
is separably closed. Z is affine as a closed subscheme; V is affine as a finite scheme
over Z. Apply Tag 09ZA to obtain a section of V to Z. Under representability this is
a global torsor section t. On each object of the site, the map m to m + t is an
M-equivariant bijection by simple transitivity, and these maps commute with restriction.
They form an equivariant sheaf isomorphism from the trivial torsor to the given one.
This argument also covers the empty scheme and the trivial coefficient group. -/
theorem torsors_trivial_of_finite_etale_sections
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsSepClosed (FractionRing R)] (Z : Scheme.{u})
    (i : Z ⟶ Spec (CommRingCat.of R)) [IsClosedImmersion i]
    (M : Type (u + 1)) [AddCommGroup M] [Finite M] :
    ∀ T : CategoryTheory.Sheaf.Torsor
      ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of M)), T ≈ CategoryTheory.Sheaf.Torsor.trivial _ := by
  intro T
  obtain ⟨t, ht⟩ := Scheme.EtaleTorsor.exists_toSheafTorsor_equiv T
  have := t.isFinite
  have := t.etale
  have := t.surjective
  let X := Spec (CommRingCat.of R)
  have : IsSepClosed X.functionField := by
    let : Algebra (CommRingCat.of R) X.functionField :=
      instAlgebraCarrierFunctionFieldSpec (CommRingCat.of R)
    have := functionField_isFractionRing_of_affine (CommRingCat.of R)
    exact IsSepClosed.of_ringEquiv
      (IsLocalization.algEquiv (nonZeroDivisors (CommRingCat.of R))
        (FractionRing R) X.functionField).toRingEquiv
  have hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x) :=
    fun x ↦ ⟨inferInstance, Scheme.isIntegrallyClosed_stalk_Spec R x⟩
  have : IsAffine Z := isAffine_of_isAffineHom i
  have : IsAffine t.P := isAffine_of_isAffineHom t.π
  obtain ⟨s, hs⟩ :=
    (exists_finite_clopen_opens_and_section_of_closedImmersion hX i t.π).2
      inferInstance inferInstance
  have hn : Nonempty (t.toSheafTorsor.sheaf.obj.obj (Opposite.op (⊤_ Z.Etale))) :=
    (t.nonempty_toSheafTorsor_sheaf_obj_iff terminalIsTerminal).2 ⟨s, hs⟩
  have hT := (CategoryTheory.Sheaf.Torsor.nonempty_iff_of_equiv ht
    (Opposite.op (⊤_ Z.Etale))).1 hn
  obtain ⟨x⟩ := hT
  let G := (constantSheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of M)
  let f : (CategoryTheory.Sheaf.Torsor.trivial G).sheaf ⟶ T.sheaf :=
    ObjectProperty.homMk
      { app U := TypeCat.ofHom fun a ↦
          T.vadd U a (T.sheaf.obj.map (terminal.from U.unop).op x)
        naturality U V g := by
          ext a
          change T.vadd V (G.obj.map g a)
              (T.sheaf.obj.map (terminal.from V.unop).op x) =
            T.sheaf.obj.map g (T.vadd U a
              (T.sheaf.obj.map (terminal.from U.unop).op x))
          rw [T.map_vadd]
          congr 1
          change _ = T.sheaf.obj.map g.unop.op
            (T.sheaf.obj.map (terminal.from U.unop).op x)
          rw [T.map_map_apply]
          simp }
  let e : CategoryTheory.Sheaf.Torsor.Iso (CategoryTheory.Sheaf.Torsor.trivial G) T :=
    CategoryTheory.Sheaf.Torsor.Iso.ofHom f fun U a b ↦ by
      change T.vadd U (a + (show G.obj.obj U from b)) _ =
        T.vadd U a (T.vadd U b _)
      exact T.add_vadd U a (show G.obj.obj U from b) _
  exact ⟨e.symm⟩

end AlgebraicGeometry.Etale
