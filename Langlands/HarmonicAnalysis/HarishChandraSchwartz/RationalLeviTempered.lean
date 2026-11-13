import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitCoefficientBound
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Coefficient growth on the Levi scheme and the actual Levi subgroup

Pullback along a topological group isomorphism preserves tempered coefficient bounds for
pulled-back weights. For the standard Levi scheme, the canonical pullback identifies
`IsRationalTempered` with `IsRationalLeviTempered`, using the published Xi and height comparisons.
The same pullback also identifies pure Xi coefficient bounds, without any height or matrix
representation.
-/

noncomputable section

universe u uG uH uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Pure Xi coefficient bounds are invariant under topological group isomorphisms when the
weight is pulled back along the same isomorphism. -/
theorem hasXiBoundedCoefficients_comp_continuousMulEquiv_iff
    (Ξ : G → ℝ) (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    HasXiBoundedCoefficients (Ξ ∘ e) (ρ.comp e.toMonoidHom) ↔
      HasXiBoundedCoefficients Ξ ρ := by
  constructor
  · intro h v ℓ
    let ℓ' : SmoothDual (ρ.comp e.toMonoidHom) :=
      ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mpr ℓ.property⟩
    obtain ⟨c, hc, hb⟩ := h v ℓ'
    refine ⟨c, hc, fun g => ?_⟩
    have hg := hb (e.symm g)
    change ‖ℓ.val (ρ (e (e.symm g)) v)‖ ≤ c * Ξ (e (e.symm g)) at hg
    simpa only [e.apply_symm_apply] using hg
  · intro h v ℓ
    let ℓ' : SmoothDual ρ :=
      ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mp ℓ.property⟩
    obtain ⟨c, hc, hb⟩ := h v ℓ'
    exact ⟨c, hc, fun g => hb (e g)⟩

/-- Tempered coefficient bounds are invariant under topological group isomorphisms when the
weights are pulled back along the same isomorphism. -/
theorem hasTemperedCoefficients_comp_continuousMulEquiv_iff
    (Ξ σ : G → ℝ) (ρ : Representation ℂ G V) (e : H ≃ₜ* G) :
    HasTemperedCoefficients (Ξ ∘ e) (σ ∘ e) (ρ.comp e.toMonoidHom) ↔
      HasTemperedCoefficients Ξ σ ρ := by
  constructor
  · intro h v ℓ
    let ℓ' : SmoothDual (ρ.comp e.toMonoidHom) :=
      ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mpr ℓ.property⟩
    obtain ⟨c, r, hb⟩ := h v ℓ'
    refine ⟨c, r, fun g => ?_⟩
    have hg := hb (e.symm g)
    change ‖ℓ.val (ρ (e (e.symm g)) v)‖ ≤
      c * Ξ (e (e.symm g)) * (1 + σ (e (e.symm g))) ^ r at hg
    simpa only [e.apply_symm_apply] using hg
  · intro h v ℓ
    let ℓ' : SmoothDual ρ :=
      ⟨ℓ.val, (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e ℓ.val).mp ℓ.property⟩
    obtain ⟨c, r, hb⟩ := h v ℓ'
    exact ⟨c, r, fun g => hb (e g)⟩

end Transport

section Levi

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance leviTemperedIsAffineHom (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J

local instance leviTemperedLocallyOfFiniteType (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (J : Set (characterLattice S)) : LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) (J : Set (characterLattice S))

/-- A smooth representation of the actual Levi subgroup, read as a representation of the
Levi group scheme's rational points, by canonical same-carrier pullback. -/
def leviSchemeRepresentation (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) :
    SmoothRep.{0, u, uV} ℂ (rationalPoints (Standard.leviScheme i ν J)) :=
  SmoothRep.pullback (leviSchemePointsEquiv i ν J) A

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem leviSchemeRepresentation_apply
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J))
    (x : rationalPoints (Standard.leviScheme i ν J)) (v : A) :
    (leviSchemeRepresentation i ν J A).representation x v =
      A.representation (leviSchemePointsEquiv i ν J x) v := rfl

variable {i ν J}

/-- The pure Xi bound agrees for the Levi scheme and the actual standard Levi subgroup,
using the canonical representation pullback and the matching compact subgroup. -/
theorem hasXiBoundedCoefficients_leviSchemeRepresentation_iff
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) :
    HasXiBoundedCoefficients
      (rationalXi (isCompact_leviSchemeCompact hKc)
        (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM))
      (leviSchemeRepresentation i ν J A).representation ↔
      HasXiBoundedCoefficients (rationalLeviXi hKc hM) A.representation := by
  have hΞ : rationalXi (isCompact_leviSchemeCompact hKc)
      (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM) =
      rationalLeviXi hKc hM ∘ leviSchemePointsEquiv i ν J :=
    funext (rationalXi_leviScheme hG hi hν hJ hKo hKc hM)
  rw [hΞ]
  exact hasXiBoundedCoefficients_comp_continuousMulEquiv_iff _ A.representation
    (leviSchemePointsEquiv i ν J)

/-- Temperedness agrees for the Levi scheme and the actual standard Levi subgroup, for the
corresponding compact subgroup and the restricted matrix representation. -/
theorem isRationalTempered_leviSchemeRepresentation_iff
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
      (K.subgroupOf (standardLeviPoints i ν J)))
    (A : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν J)) :
    IsRationalTempered (isCompact_leviSchemeCompact hKc)
      (ρ.restrict (Standard.leviHom i ν J)) (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM)
      (leviSchemeRepresentation i ν J A) ↔ IsRationalLeviTempered hKc ρ hM A := by
  have hΞ : rationalXi (isCompact_leviSchemeCompact hKc)
      (isIwasawaPair_leviSchemeCompact hG hi hν hJ hM) =
      rationalLeviXi hKc hM ∘ leviSchemePointsEquiv i ν J :=
    funext (rationalXi_leviScheme hG hi hν hJ hKo hKc hM)
  have hσ : rationalHeight (F := F) (ρ.restrict (Standard.leviHom i ν J)) =
      (fun m : standardLeviPoints i ν J => rationalHeight (F := F) ρ m) ∘
        leviSchemePointsEquiv i ν J :=
    funext (rationalHeight_restrict_leviHom ρ)
  unfold IsRationalTempered IsRationalLeviTempered
  rw [hΞ, hσ]
  exact hasTemperedCoefficients_comp_continuousMulEquiv_iff _ _ A.representation
    (leviSchemePointsEquiv i ν J)

end Levi

end Langlands.HarishChandraSchwartz
