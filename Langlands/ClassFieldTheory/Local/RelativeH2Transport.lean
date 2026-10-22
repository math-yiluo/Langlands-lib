import Langlands.ClassFieldTheory.Local.Cohomology

/-! # Relative H² transport across independent field universes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.ClassFieldTheory.Local

universe u v w

variable {K : Type u} {L : Type v} {M : Type w}
  [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- Pull an automorphism back along the actual algebra equivalence. -/
def relativeAutPullback (e : L ≃ₐ[K] M) : Gal(M/K) →* Gal(L/K) where
  toFun s := e.trans (s.trans e.symm)
  map_one' := by ext x; simp
  map_mul' s t := by ext x; simp

@[simp] theorem relativeAutPullback_apply (e : L ≃ₐ[K] M) (s : Gal(M/K)) (x : L) :
    relativeAutPullback e s x = e.symm (s (e x)) := rfl

@[simp] theorem relativeAutPullback_symm_apply (e : L ≃ₐ[K] M) (s : Gal(L/K)) :
    relativeAutPullback e (relativeAutPullback e.symm s) = s := by
  ext x
  simp

/-- The actual field equivalence on units, written additively. -/
def relativeUnitTransport (e : L ≃ₐ[K] M) : Additive Lˣ ≃+ Additive Mˣ :=
  (Units.mapEquiv e.toMulEquiv).toAdditive

@[simp] theorem relativeUnitTransport_apply_val (e : L ≃ₐ[K] M) (x : Additive Lˣ) :
    ((relativeUnitTransport e x).toMul : M) = e (x.toMul : L) := rfl

@[simp] theorem relativeUnitTransport_symm_apply (e : L ≃ₐ[K] M) (x : Additive Lˣ) :
    relativeUnitTransport e.symm (relativeUnitTransport e x) = x := by
  apply Units.ext
  exact e.symm_apply_apply _

/-- Equivariance for the unchanged Galois actions. -/
theorem relativeUnitTransport_action (e : L ≃ₐ[K] M) (s : Gal(M/K))
    (x : unitsRepresentation K L) :
    relativeUnitTransport e ((unitsRepresentation K L).ρ (relativeAutPullback e s) x) =
      (unitsRepresentation K M).ρ s (relativeUnitTransport e x) := by
  apply Units.ext
  exact e.apply_symm_apply _

/-- Transport one-cochains by conjugation and the actual map on units. -/
def relativeCochainOneTransport (e : L ≃ₐ[K] M)
    (b : Gal(L/K) → unitsRepresentation K L) : Gal(M/K) → unitsRepresentation K M :=
  fun s => relativeUnitTransport e (b (relativeAutPullback e s))

/-- Transport two-cochains, retaining their ordinary additive groups. -/
def relativeCochainTwoTransport (e : L ≃ₐ[K] M) :
    (Gal(L/K) × Gal(L/K) → unitsRepresentation K L) →+
      (Gal(M/K) × Gal(M/K) → unitsRepresentation K M) where
  toFun z st := relativeUnitTransport e
    (z (relativeAutPullback e st.1, relativeAutPullback e st.2))
  map_zero' := by funext st; exact map_zero (relativeUnitTransport e)
  map_add' z z' := by funext st; exact map_add (relativeUnitTransport e) _ _

@[simp] theorem relativeCochainTwoTransport_apply (e : L ≃ₐ[K] M)
    (z : Gal(L/K) × Gal(L/K) → unitsRepresentation K L) (s t : Gal(M/K)) :
    relativeCochainTwoTransport e z (s, t) =
      relativeUnitTransport e (z (relativeAutPullback e s, relativeAutPullback e t)) := rfl

/-- Transport commutes with the degree-one coboundary differential. -/
theorem relativeCochainTwoTransport_d₁₂ (e : L ≃ₐ[K] M)
    (b : Gal(L/K) → unitsRepresentation K L) :
    relativeCochainTwoTransport e (groupCohomology.d₁₂ (unitsRepresentation K L) b) =
      groupCohomology.d₁₂ (unitsRepresentation K M) (relativeCochainOneTransport e b) := by
  funext st
  rcases st with ⟨s, t⟩
  simp only [relativeCochainTwoTransport_apply,
    groupCohomology.d₁₂_hom_apply, map_add, map_sub, relativeUnitTransport_action,
    relativeCochainOneTransport, map_mul]

/-- Coboundaries are sent to coboundaries by an explicit transported primitive. -/
theorem relativeCochainTwoTransport_mem_coboundaries (e : L ≃ₐ[K] M)
    {z : Gal(L/K) × Gal(L/K) → unitsRepresentation K L}
    (hz : z ∈ groupCohomology.coboundaries₂ (unitsRepresentation K L)) :
    relativeCochainTwoTransport e z ∈ groupCohomology.coboundaries₂
      (unitsRepresentation K M) := by
  rcases hz with ⟨b, rfl⟩
  exact ⟨relativeCochainOneTransport e b, (relativeCochainTwoTransport_d₁₂ e b).symm⟩

/-- The public additive transport of actual two-cocycles. -/
def relativeCocycleTransport (e : L ≃ₐ[K] M) :
    groupCohomology.cocycles₂ (unitsRepresentation K L) →+
      groupCohomology.cocycles₂ (unitsRepresentation K M) where
  toFun z := ⟨relativeCochainTwoTransport e z, by
    apply (groupCohomology.mem_cocycles₂_iff _).2
    intro s t r
    have h := congrArg (relativeUnitTransport e)
      ((groupCohomology.mem_cocycles₂_iff z).1 z.2
        (relativeAutPullback e s) (relativeAutPullback e t) (relativeAutPullback e r))
    simpa only [relativeCochainTwoTransport_apply,
      map_add, map_mul, relativeUnitTransport_action] using h⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_add' z z' := by apply Subtype.ext; exact map_add _ _ _

@[simp] theorem relativeCocycleTransport_apply (e : L ≃ₐ[K] M)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) (s t : Gal(M/K)) :
    relativeCocycleTransport e z (s, t) =
      relativeUnitTransport e (z (relativeAutPullback e s, relativeAutPullback e t)) := rfl

@[simp] theorem relativeCocycleTransport_symm_apply (e : L ≃ₐ[K] M)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeCocycleTransport e.symm (relativeCocycleTransport e z) = z := by
  apply groupCohomology.cocycles₂_ext
  intro s t
  simp only [relativeCocycleTransport_apply, relativeAutPullback_symm_apply]
  exact relativeUnitTransport_symm_apply e _

/-- Equal cohomology classes have equal transported classes. -/
theorem relativeCocycleTransport_H2π_eq (e : L ≃ₐ[K] M)
    {z z' : groupCohomology.cocycles₂ (unitsRepresentation K L)}
    (h : groupCohomology.H2π (unitsRepresentation K L) z =
      groupCohomology.H2π (unitsRepresentation K L) z') :
    groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z) =
      groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z') := by
  apply (groupCohomology.H2π_eq_iff _ _).2
  have h' := relativeCochainTwoTransport_mem_coboundaries e
    ((groupCohomology.H2π_eq_iff z z').1 h)
  change relativeCochainTwoTransport e (z : _) -
    relativeCochainTwoTransport e (z' : _) ∈ _
  simpa only [map_sub] using h'

private theorem relativeH2Representative_exists (x : relativeCohomology K L 2) :
    ∃ z : groupCohomology.cocycles₂ (unitsRepresentation K L),
      groupCohomology.H2π (unitsRepresentation K L) z = x :=
  groupCohomology.H2_induction_on x fun z => ⟨z, rfl⟩

private def relativeH2Representative (x : relativeCohomology K L 2) :
    groupCohomology.cocycles₂ (unitsRepresentation K L) :=
  Classical.choose (relativeH2Representative_exists x)

private theorem relativeH2Representative_spec (x : relativeCohomology K L 2) :
    groupCohomology.H2π (unitsRepresentation K L) (relativeH2Representative x) = x :=
  Classical.choose_spec (relativeH2Representative_exists x)

private def relativeH2TransportFun (e : L ≃ₐ[K] M) (x : relativeCohomology K L 2) :
    relativeCohomology K M 2 :=
  groupCohomology.H2π (unitsRepresentation K M)
    (relativeCocycleTransport e (relativeH2Representative x))

private theorem relativeH2TransportFun_H2π (e : L ≃ₐ[K] M)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeH2TransportFun e (groupCohomology.H2π (unitsRepresentation K L) z) =
      groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z) :=
  relativeCocycleTransport_H2π_eq e (relativeH2Representative_spec _)

/-- Transport on the existing relative H², descended from explicit cocycle transport. -/
def relativeH2Transport (e : L ≃ₐ[K] M) :
    relativeCohomology K L 2 →+ relativeCohomology K M 2 where
  toFun := relativeH2TransportFun e
  map_zero' := by
    have h := relativeH2TransportFun_H2π e 0
    simpa only [map_zero] using h
  map_add' x y := by
    induction x using groupCohomology.H2_induction_on with | h z =>
      induction y using groupCohomology.H2_induction_on with | h z' =>
        rw [← map_add, relativeH2TransportFun_H2π, map_add, map_add,
          relativeH2TransportFun_H2π, relativeH2TransportFun_H2π]

/-- The descended map sends a cocycle class to the class of the transported cocycle. -/
@[simp] theorem relativeH2Transport_H2π (e : L ≃ₐ[K] M)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeH2Transport e (groupCohomology.H2π (unitsRepresentation K L) z) =
      groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z) :=
  relativeH2TransportFun_H2π e z

/-- Transport along the inverse field equivalence is a genuine inverse on H². -/
@[simp] theorem relativeH2Transport_symm_apply (e : L ≃ₐ[K] M)
    (x : relativeCohomology K L 2) :
    relativeH2Transport e.symm (relativeH2Transport e x) = x := by
  induction x using groupCohomology.H2_induction_on with | h z =>
    rw [relativeH2Transport_H2π, relativeH2Transport_H2π,
      relativeCocycleTransport_symm_apply]

/-- Relative H² is additively equivalent across independent field universes. -/
def relativeH2Equiv (e : L ≃ₐ[K] M) :
    relativeCohomology K L 2 ≃+ relativeCohomology K M 2 where
  toFun := relativeH2Transport e
  invFun := relativeH2Transport e.symm
  left_inv := relativeH2Transport_symm_apply e
  right_inv := by
    intro x
    simpa only [AlgEquiv.symm_symm] using relativeH2Transport_symm_apply e.symm x
  map_add' := map_add (relativeH2Transport e)

@[simp] theorem relativeH2Equiv_H2π (e : L ≃ₐ[K] M)
    (z : groupCohomology.cocycles₂ (unitsRepresentation K L)) :
    relativeH2Equiv e (groupCohomology.H2π (unitsRepresentation K L) z) =
      groupCohomology.H2π (unitsRepresentation K M) (relativeCocycleTransport e z) :=
  relativeH2Transport_H2π e z

@[simp] theorem relativeH2Equiv_symm (e : L ≃ₐ[K] M) :
    (relativeH2Equiv e).symm = relativeH2Equiv e.symm := by
  ext x
  rfl

end Langlands.ClassFieldTheory.Local
