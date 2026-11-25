/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs
public import WeilConjectures.AlgebraicGeometry.GeometricallyConnected
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Abelian varieties are geometrically integral, and commutative

An abelian variety, defined as a proper smooth connected group scheme over a field, is
automatically irreducible and geometrically integral; combined with Mathlib's
`AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` this makes it a
commutative group scheme.

The converse direction — a proper connected smooth group scheme is an abelian variety — is true
by definition, so together the statements below say that abelian varieties and complete group
varieties are the same thing.

## Main statements

- `AlgebraicGeometry.IsAbelianVariety.geometricallyIntegral`: an abelian variety is
  geometrically integral over the base field.
- `AlgebraicGeometry.IsAbelianVariety.irreducibleSpace`: its underlying space is irreducible.
- `AlgebraicGeometry.IsAbelianVariety.isCommMonObj`: an abelian variety is commutative.
- `AlgebraicGeometry.isAbelianVariety_iff_geometricallyConnected`: abelian varieties are the
  proper smooth geometrically connected group schemes.
- `AlgebraicGeometry.IsAbelianVariety.pullback`: the base change of an abelian variety to an
  extension field is an abelian variety.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

variable {K : Type u} [Field K]

/-- Blueprint `lemma-abelian-variety-commutative--1`: Abelian varieties are the complete group
varieties.

Let `G` be a group scheme over a field `K` which is proper, connected and smooth over `K`, that
is, an abelian variety in the sense of `AlgebraicGeometry.IsAbelianVariety`. Then `G` is
geometrically integral over `K`: it is proper and has a rational point, the unit, so connectedness
gives geometric connectedness (`GeometricallyConnected.of_universallyClosed_of_section`); a smooth
morphism with geometrically connected fibres is geometrically irreducible; and smoothness gives
geometric reducedness.

This is also blueprint `lemma-abelian-variety-commutative--1`. -/
instance IsAbelianVariety.geometricallyIntegral (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianVariety G] : GeometricallyIntegral G.hom := by
  have hη : η[G].left ≫ G.hom = 𝟙 _ := by simp
  have := GeometricallyConnected.of_universallyClosed_of_section G.hom η[G].left hη
  have := GeometricallyIrreducible.of_smooth_of_geometricallyConnected G.hom
  exact .of_geometricallyReduced_of_geometricallyIrreducible _

/-- Blueprint `lemma-abelian-variety-commutative--1`: Abelian varieties are the complete group
varieties.

The underlying space of an abelian variety is irreducible, being geometrically irreducible over
the one-point space `Spec K`.

This is also blueprint `lemma-abelian-variety-commutative--1`. -/
instance IsAbelianVariety.irreducibleSpace (G : Over (Spec (.of K))) [GrpObj G]
    [IsAbelianVariety G] : IrreducibleSpace G.left :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.hom

/-- Blueprint `lemma-abelian-variety-commutative--2`: Abelian varieties are commutative

Let `A` be an abelian variety over `K`. Then `m ∘ s = m`, where `s` is the swap of the two
factors of `A ⊗ A`; that is, `A` is a commutative group object, and in particular `A(K)` is an
abelian group. This is also blueprint `lemma-abelian-variety-commutative--2`.

This is Mathlib's `AlgebraicGeometry.isCommMonObj_of_isProper_of_geometricallyIntegral` applied
to `AlgebraicGeometry.IsAbelianVariety.geometricallyIntegral`. The blueprint instead deduces it
from the rigidity lemma `AlgebraicGeometry.exists_eq_snd_comp`, which is recorded in
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity`, whose hypotheses on `X` an abelian
variety satisfies (see Stacks 04KV for geometric connectedness). -/
instance IsAbelianVariety.isCommMonObj (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] : IsCommMonObj A :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A

/-- Blueprint `definition-abelian-variety--1`: an abelian variety is geometrically connected over
the base field.

It is proper and connected with a rational point, the unit, so this is Stacks 04KV
(`GeometricallyConnected.of_universallyClosed_of_section`). -/
instance IsAbelianVariety.geometricallyConnected (A : Over (Spec (.of K))) [GrpObj A]
    [IsAbelianVariety A] : GeometricallyConnected A.hom :=
  GeometricallyConnected.of_universallyClosed_of_section A.hom η[A].left (by simp)

/-- Blueprint `definition-abelian-variety--1`: Finite fields, Frobenius and abelian varieties.

This is also blueprint `definition-abelian-variety--1`, which defines an abelian variety over `K` as
a proper, smooth, geometrically connected, commutative group scheme of finite type over `K`. For a
group scheme `A` over `K` this agrees with `AlgebraicGeometry.IsAbelianVariety` (proper, smooth and
connected): a geometrically connected scheme over the one-point space `Spec K` is connected, and
conversely an abelian variety is geometrically connected
(`AlgebraicGeometry.IsAbelianVariety.geometricallyConnected`). Finite type is part of
properness, and commutativity is automatic (`AlgebraicGeometry.IsAbelianVariety.isCommMonObj`). -/
theorem isAbelianVariety_iff_geometricallyConnected (A : Over (Spec (.of K))) [GrpObj A] :
    IsAbelianVariety A ↔ IsProper A.hom ∧ Smooth A.hom ∧ GeometricallyConnected A.hom := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance, inferInstance⟩, fun ⟨_, _, _⟩ ↦ ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty (Spec (.of K)))
  have h := A.hom.isConnected_preimage_singleton x
  rw [Set.eq_univ_of_forall (s := A.hom ⁻¹' {x}) fun y ↦ Subsingleton.elim (A.hom y) x] at h
  exact { toConnectedSpace := connectedSpace_iff_univ.mpr h }

/-- The base change `A_L` of an abelian variety `A` over `K` along a field extension
`Spec L ⟶ Spec K` is an abelian variety over `L`: properness and smoothness are stable under base
change, and `A_L` is connected because `A`, being proper and connected with a rational point (the
unit), is geometrically connected (Stacks 04KV,
`GeometricallyConnected.of_universallyClosed_of_section`).

This is used in the proof of blueprint `proposition-multiplication-n--2`. -/
instance IsAbelianVariety.pullback {L : Type u} [Field L] (g : Spec (.of L) ⟶ Spec (.of K))
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A] :
    IsAbelianVariety ((Over.pullback g).obj A) := by
  have hη : η[A].left ≫ A.hom = 𝟙 _ := by simp
  have := GeometricallyConnected.of_universallyClosed_of_section A.hom η[A].left hη
  exact { toIsProper := inferInstanceAs (IsProper (pullback.snd _ _))
          toSmooth := inferInstanceAs (Smooth (pullback.snd _ _))
          toConnectedSpace := pullback_of_geometrically
            (GeometricallyConnected.geometrically_connectedSpace (f := A.hom)) _ _ }

end AlgebraicGeometry
