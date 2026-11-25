/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Strictly henselian singleton neighbourhoods in dimension zero

Source: Stacks Project, Algebra, Tags 00KH, 00FV and 06RS.
(blueprint: lem-weil-pbc-zero-dimensional-singleton-neighbourhoods)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A geometric point on a zero-dimensional finite-type scheme has a singleton open
neighbourhood which is the spectrum of a strictly henselian local ring.
Source: Stacks Project, Tags 00KH, 00FV and 06RS.
(blueprint: lem-weil-pbc-zero-dimensional-singleton-neighbourhoods)

Proof: The geometry theorem `zeroDimensional_baseChange_geometry` makes C discrete.
Set U_c = {c} with its open subscheme structure. The unique-point source of s_c
and hs show that its range is contained in U_c, so the open immersion lift
constructs t_c and its factorization. A singleton scheme is affine (Mathlib's
instance in AlgebraicGeometry.Limits); set R_c = Gamma(U_c, top) and use isoSpec.
Its spectrum is a nonempty singleton, hence R_c is nonzero and has only one maximal
ideal. `IsLocalRing.of_singleton_maximalSpectrum` gives its local-ring structure,
and `ringKrullDimZero_iff_ringKrullDim_eq_zero` gives dimension zero from this spectrum. The
composite Spec R_c -> U_c -> C -> Spec k is locally of finite type. Apply
`residueFieldIsoBase` at the closed point (closed in this singleton spectrum), then
`stalkClosedPointIso` and `IsLocalRing.ResidueField.mapEquiv`: they identify the
local-ring residue field with k. Transfer algebraic closedness along the resulting
ring equivalence; in particular the residue field is separably closed. Apply
`isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero` (Tag 06RS). Finally the
lifted geometric point lands at the unique point of Spec R_c, its closed point.
If C is empty all indexed data are empty functions and the conditions are vacuous. -/
theorem zeroDimensional_singleton_neighbourhoods
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))]
    [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))] (hdim : topologicalKrullDim C ≤ 0)
    (Ω : C → Type u) [∀ c, Field (Ω c)] [∀ c, IsAlgClosed (Ω c)]
    (s : ∀ c, Spec (.of (Ω c)) ⟶ C) (hs : ∀ c, s c default = c) :
    ∃ (U : C → C.Opens) (t : ∀ c, Spec (.of (Ω c)) ⟶ (U c).toScheme),
      ∀ c, t c ≫ (U c).ι = s c ∧ (U c : Set C) = {c} ∧
        ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R),
          IsStrictlyHenselianLocalRing R ∧
            ∃ e : (U c).toScheme ≅ Spec (.of R),
              (t c ≫ e.hom) default = IsLocalRing.closedPoint R := by
  classical
  let : DiscreteTopology C := (AlgebraicGeometry.zeroDimensional_baseChange_geometry
    k C hdim).2.1
  let U : C → C.Opens := fun c ↦ ⟨{c}, isOpen_discrete _⟩
  have hrange (c : C) : Set.range (s c) ⊆ Set.range (U c).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x = default := Subsingleton.elim _ _
    rw [hx, hs]
    exact Set.mem_singleton c
  let t := fun c ↦ IsOpenImmersion.lift (U c).ι (s c) (hrange c)
  refine ⟨U, t, fun c ↦ ⟨IsOpenImmersion.lift_fac _ _ (hrange c), rfl, ?_⟩⟩
  let : Subsingleton (U c).toScheme := ⟨fun a b ↦ by
    apply Subtype.ext
    exact (Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm⟩
  let : IsAffine (U c).toScheme := inferInstance
  let R := Γ((U c).toScheme, ⊤)
  let e : (U c).toScheme ≅ Spec R := (U c).toScheme.isoSpec
  let : Subsingleton (Spec R) := ⟨fun a b ↦
    e.inv.homeomorph.injective (Subsingleton.elim _ _)⟩
  let : Subsingleton (PrimeSpectrum R) := inferInstanceAs (Subsingleton (Spec R))
  let : Nontrivial R := PrimeSpectrum.nontrivial (e.hom ⟨c, rfl⟩)
  let : Subsingleton (MaximalSpectrum R) := ⟨fun a b ↦
    MaximalSpectrum.toPrimeSpectrum_injective (Subsingleton.elim _ _)⟩
  let : IsLocalRing R := IsLocalRing.of_singleton_maximalSpectrum
  have hzero : ringKrullDim R = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
    (inferInstance : Ring.KrullDimLE 0 R)
  let f : Spec R ⟶ Spec (.of k) := e.inv ≫ (U c).ι ≫ (C ↘ Spec (.of k))
  let : LocallyOfFiniteType f := inferInstance
  let : DiscreteTopology (Spec R) := inferInstance
  let efield := residueFieldIsoBase f (IsLocalRing.closedPoint R) (isClosed_discrete _)
  let er := IsLocalRing.ResidueField.mapEquiv
    (stalkClosedPointIso R).commRingCatIsoToRingEquiv
  have hres : IsAlgClosed (IsLocalRing.ResidueField R) :=
    IsAlgClosed.of_ringEquiv k _ (efield.symm.commRingCatIsoToRingEquiv.trans er)
  let : IsAlgClosed (IsLocalRing.ResidueField R) := hres
  have hstrict := (isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero.{u, u} R hzero).1
  refine ⟨R, inferInstance, inferInstance, hstrict, e, ?_⟩
  exact Subsingleton.elim _ _

end AlgebraicGeometry.Scheme
