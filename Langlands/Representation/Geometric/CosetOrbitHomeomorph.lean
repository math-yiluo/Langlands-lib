import Langlands.Representation.Geometric.CosetAction
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Homeomorph.Lemmas

/-! The canonical identification of stabilizer cosets with a locally closed orbit. -/

noncomputable section

namespace Langlands.Geometric

universe uG

variable {G : Type uG} [Group G] (P Q : Subgroup G) (w : G)

/-- The canonical map from `Q` to the actual orbit of `P w⁻¹`. -/
def cosetOrbitMap (q : Q) : cosetOrbit P Q w :=
  ⟨Induction.quotientMap P (w⁻¹ * (q : G)), ⟨q, rfl⟩⟩

/-- Equality of orbit points is precisely the left-coset relation for the stabilizer. -/
theorem cosetOrbitMap_eq_iff (q r : Q) :
    cosetOrbitMap P Q w q = cosetOrbitMap P Q w r ↔
      QuotientGroup.rightRel (orbitStabilizer P Q w) q r := by
  rw [Subtype.ext_iff]
  change Induction.quotientMap P (w⁻¹ * (q : G)) =
    Induction.quotientMap P (w⁻¹ * (r : G)) ↔ _
  simp only [Induction.quotientMap, Quotient.eq, QuotientGroup.rightRel_apply]
  change (w⁻¹ * (r : G)) * (w⁻¹ * (q : G))⁻¹ ∈ P ↔
    (MulAut.conj w⁻¹) ((r * q⁻¹ : Q) : G) ∈ P
  simp [mul_assoc]

/-- The induced map on actual left cosets of `Q ∩ w P w⁻¹` in `Q`. -/
def cosetOrbitQuotientMap : Induction.LeftQuotient (orbitStabilizer P Q w) →
    cosetOrbit P Q w :=
  Quotient.lift (cosetOrbitMap P Q w) (fun q r h =>
    (cosetOrbitMap_eq_iff P Q w q r).mpr h)

@[simp] theorem cosetOrbitQuotientMap_mk (q : Q) :
    cosetOrbitQuotientMap P Q w (Induction.quotientMap (orbitStabilizer P Q w) q) =
      cosetOrbitMap P Q w q := rfl

/-- The canonical orbit map is bijective after passing to stabilizer cosets. -/
theorem cosetOrbitQuotientMap_bijective : Function.Bijective (cosetOrbitQuotientMap P Q w) := by
  constructor
  · intro x y
    induction x using Quotient.inductionOn with
    | h q =>
      induction y using Quotient.inductionOn with
      | h r =>
        intro h
        exact Quotient.sound ((cosetOrbitMap_eq_iff P Q w q r).mp h)
  · rintro ⟨x, q, rfl⟩
    exact ⟨Induction.quotientMap (orbitStabilizer P Q w) q, rfl⟩

/-- The algebraic coset-orbit equivalence, before any topological assumptions. -/
def cosetOrbitEquiv : Induction.LeftQuotient (orbitStabilizer P Q w) ≃ cosetOrbit P Q w :=
  Equiv.ofBijective (cosetOrbitQuotientMap P Q w) (cosetOrbitQuotientMap_bijective P Q w)

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Closedness of the inducing subgroup gives closedness of the orbit stabilizer. -/
theorem isClosed_orbitStabilizer (hP : IsClosed (P : Set G)) :
    IsClosed (orbitStabilizer P Q w : Set Q) :=
  hP.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

/-- The map to the orbit with its ambient subspace topology is continuous. -/
theorem continuous_cosetOrbitMap : Continuous (cosetOrbitMap P Q w) :=
  (continuous_quotient_mk'.comp (continuous_const.mul continuous_subtype_val)).subtype_mk _

/-- The induced map on the topological left quotient is continuous. -/
theorem continuous_cosetOrbitQuotientMap : Continuous (cosetOrbitQuotientMap P Q w) :=
  continuous_quot_lift _ (continuous_cosetOrbitMap P Q w)

/-- On a locally closed orbit, the canonical map from a closed sigma-compact subgroup is open. -/
theorem isOpenMap_cosetOrbitMap [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) : IsOpenMap (cosetOrbitMap P Q w) := by
  let := leftQuotientAction P Q
  let := leftQuotientAction_continuousSMul P Q
  let := QuotientIntegration.leftQuotient_t2Space P hP
  let := QuotientIntegration.leftQuotient_locallyCompactSpace P
  let : SigmaCompactSpace Q := hQ.sigmaCompactSpace
  let x := Induction.quotientMap P w⁻¹
  have horb : MulAction.orbit Q x = cosetOrbit P Q w := leftQuotientAction_orbit P Q w
  have hloc : IsLocallyClosed (MulAction.orbit Q x) := horb.symm ▸ hw
  let : LocallyCompactSpace (MulAction.orbit Q x) := hloc.locallyCompactSpace
  let : ContinuousSMul Q (MulAction.orbit Q x) :=
    ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  let x₀ : MulAction.orbit Q x := ⟨x, MulAction.mem_orbit_self x⟩
  have hopen := (Homeomorph.setCongr horb).isOpenMap.comp
    ((isOpenMap_smul_of_sigmaCompact x₀).comp (isOpenMap_inv Q))
  convert hopen using 1
  funext q
  apply Subtype.ext
  change Induction.quotientMap P (w⁻¹ * (q : G)) =
    Induction.quotientMap P (w⁻¹ * ((q⁻¹ : Q) : G)⁻¹)
  simp only [InvMemClass.coe_inv, inv_inv]

/-- Stabilizer cosets carry exactly the subspace topology of a locally closed coset orbit. -/
def cosetOrbitHomeomorph [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) :
    Induction.LeftQuotient (orbitStabilizer P Q w) ≃ₜ cosetOrbit P Q w :=
  (cosetOrbitEquiv P Q w).toHomeomorphOfContinuousOpen
    (continuous_cosetOrbitQuotientMap P Q w) (by
      intro U hU
      have h := isOpenMap_cosetOrbitMap P Q w hP hQ hw _
        (hU.preimage continuous_quotient_mk')
      convert h using 1
      change cosetOrbitQuotientMap P Q w '' U =
        (cosetOrbitQuotientMap P Q w ∘ Induction.quotientMap (orbitStabilizer P Q w)) ''
          (Induction.quotientMap (orbitStabilizer P Q w) ⁻¹' U)
      rw [Set.image_comp, Set.image_preimage_eq _
        (show Function.Surjective (Induction.quotientMap (orbitStabilizer P Q w)) from
          Quotient.mk_surjective)])

@[simp] theorem cosetOrbitHomeomorph_mk [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) (q : Q) :
    (cosetOrbitHomeomorph P Q w hP hQ hw
      (Induction.quotientMap (orbitStabilizer P Q w) q) : Induction.LeftQuotient P) =
        Induction.quotientMap P (w⁻¹ * (q : G)) := rfl

/-- The inverse sends the orbit point represented by `q` back to its stabilizer coset. -/
@[simp] theorem cosetOrbitHomeomorph_symm_map [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) (q : Q) :
    (cosetOrbitHomeomorph P Q w hP hQ hw).symm (cosetOrbitMap P Q w q) =
      Induction.quotientMap (orbitStabilizer P Q w) q :=
  (cosetOrbitHomeomorph P Q w hP hQ hw).symm_apply_apply
    (Induction.quotientMap (orbitStabilizer P Q w) q)

/-- Forward continuity for the canonical identification. -/
theorem continuous_cosetOrbitHomeomorph [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) :
    Continuous (cosetOrbitHomeomorph P Q w hP hQ hw) :=
  (cosetOrbitHomeomorph P Q w hP hQ hw).continuous

/-- Inverse continuity for the canonical identification. -/
theorem continuous_cosetOrbitHomeomorph_symm [LocallyCompactSpace G] [SigmaCompactSpace G]
    (hP : IsClosed (P : Set G)) (hQ : IsClosed (Q : Set G))
    (hw : IsLocallyClosed (cosetOrbit P Q w)) :
    Continuous (cosetOrbitHomeomorph P Q w hP hQ hw).symm :=
  (cosetOrbitHomeomorph P Q w hP hQ hw).symm.continuous

end Langlands.Geometric
