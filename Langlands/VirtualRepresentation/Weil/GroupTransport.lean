import Langlands.VirtualRepresentation.Weil.ExactCoefficients
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.Weil.Representation.UnitaryRestriction

/-!
# Transport of irreducible lattices along an isomorphism of topological groups

For `e : G ≃ₜ* H`, restriction along `e` is a rank-preserving bijection from the
continuous irreducible classes of `H` to those of `G`. It preserves unitarity
and extends to integral lattice equivalences that are compatible with the exact
realization and with continuous restriction of exact virtual representations.
-/

noncomputable section

universe uG uH uV

namespace Langlands.FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- Invariant subspaces are unchanged by restriction along a surjective
homomorphism. -/
def restrictSubrepresentationOrderIso (φ : G →* H) (hφ : Function.Surjective φ)
    (A : FiniteRepresentation.{0, uH, uV} ℂ H) :
    Subrepresentation (restrict φ A).representation ≃o
      Subrepresentation A.representation where
  toFun S := ⟨S.toSubmodule, fun h v hv => by
    obtain ⟨g, rfl⟩ := hφ h
    exact S.apply_mem_toSubmodule g hv⟩
  invFun S := ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (φ g) hv⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Restriction along a surjective homomorphism preserves and reflects
irreducibility. -/
theorem isIrreducible_restrict_iff (φ : G →* H) (hφ : Function.Surjective φ)
    (A : FiniteRepresentation.{0, uH, uV} ℂ H) :
    (restrict φ A).IsIrreducible ↔ A.IsIrreducible :=
  (restrictSubrepresentationOrderIso φ hφ A).isSimpleOrder_iff

/-- Restriction preserves rank on genuine classes. -/
@[simp]
theorem classRank_restrictClass (φ : G →* H)
    (c : IsomorphismClasses.{0, uH, uV} ℂ H) :
    classRank (restrictClass φ c) = classRank c := by
  induction c using Quotient.inductionOn with
  | h A => rfl

@[simp]
theorem restrictClass_classOf (φ : G →* H) (A : FiniteRepresentation.{0, uH, uV} ℂ H) :
    restrictClass φ (classOf A) = classOf (restrict φ A) := rfl

section Topological

variable [TopologicalSpace G] [TopologicalSpace H]

/-- Restricting along `e` and then along `e.symm` returns the original action on
the same vector space. -/
def restrictSymmRestrictEquiv (e : G ≃ₜ* H) (A : FiniteRepresentation.{0, uH, uV} ℂ H) :
    Equiv (restrict (e.symm : H →ₜ* G).toMonoidHom (restrict (e : G →ₜ* H).toMonoidHom A))
      A where
  toLinearEquiv := LinearEquiv.refl ℂ A
  isIntertwining' h := by
    ext v
    change A.representation (e (e.symm h)) v = A.representation h v
    rw [e.apply_symm_apply]

/-- Restriction of an actual continuous irreducible representation along a
topological group isomorphism. -/
def continuousIrreducibleRestrict (e : G ≃ₜ* H)
    (A : {A : FiniteRepresentation.{0, uH, uV} ℂ H // A.IsContinuous ∧ A.IsIrreducible}) :
    {B : FiniteRepresentation.{0, uG, uV} ℂ G // B.IsContinuous ∧ B.IsIrreducible} :=
  ⟨restrict (e : G →ₜ* H).toMonoidHom A.val,
    isContinuous_restrict (e : G →ₜ* H).toMonoidHom (e : G →ₜ* H).continuous A.property.1,
    (isIrreducible_restrict_iff (e : G →ₜ* H).toMonoidHom e.surjective A.val).mpr
      A.property.2⟩

/-- Descend restriction along `e` through the continuous irreducible quotient. -/
def continuousIrreducibleRestrictClass (e : G ≃ₜ* H) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
      A.IsContinuous ∧ A.IsIrreducible) →
    IsomorphismClassesWith (fun B : FiniteRepresentation.{0, uG, uV} ℂ G =>
      B.IsContinuous ∧ B.IsIrreducible) :=
  Quotient.map (continuousIrreducibleRestrict e)
    (fun _ _ ⟨f⟩ => ⟨restrictEquiv (e : G →ₜ* H).toMonoidHom f⟩)

/-- Forgetting the conditions intertwines the class map with `restrictClass`. -/
@[simp]
theorem forget_continuousIrreducibleRestrictClass (e : G ≃ₜ* H)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    forgetPropertyClass _ (continuousIrreducibleRestrictClass e c) =
      restrictClass (e : G →ₜ* H).toMonoidHom (forgetPropertyClass _ c) := by
  induction c using Quotient.inductionOn with
  | h A => rfl

/-- Restriction along `e.symm` undoes restriction along `e` on classes. -/
@[simp]
theorem continuousIrreducibleRestrictClass_symm_apply (e : G ≃ₜ* H)
    (c : IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
      A.IsContinuous ∧ A.IsIrreducible)) :
    continuousIrreducibleRestrictClass e.symm (continuousIrreducibleRestrictClass e c) = c := by
  induction c using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨restrictSymmRestrictEquiv e A.val⟩

/-- Restriction along `e` undoes restriction along `e.symm` on classes. -/
@[simp]
theorem continuousIrreducibleRestrictClass_apply_symm (e : G ≃ₜ* H)
    (c : IsomorphismClassesWith (fun B : FiniteRepresentation.{0, uG, uV} ℂ G =>
      B.IsContinuous ∧ B.IsIrreducible)) :
    continuousIrreducibleRestrictClass e (continuousIrreducibleRestrictClass e.symm c) = c := by
  simpa only [ContinuousMulEquiv.symm_symm] using
    continuousIrreducibleRestrictClass_symm_apply e.symm c

/-- Restriction along `e` as a bijection of continuous irreducible rank-`n`
classes. The inverse is restriction along `e.symm`. -/
def continuousIrreducibleRestrictEquiv (e : G ≃ₜ* H) (n : ℕ) :
    ContinuousIrreducibleClasses.{uH, uV} H n ≃ ContinuousIrreducibleClasses.{uG, uV} G n where
  toFun c := ⟨continuousIrreducibleRestrictClass e c.val, by
    have hc := c.property
    change classRank (forgetPropertyClass _ c.val) = n at hc
    change classRank (forgetPropertyClass _ (continuousIrreducibleRestrictClass e c.val)) = n
    rw [forget_continuousIrreducibleRestrictClass, classRank_restrictClass, hc]⟩
  invFun c := ⟨continuousIrreducibleRestrictClass e.symm c.val, by
    have hc := c.property
    change classRank (forgetPropertyClass _ c.val) = n at hc
    change classRank (forgetPropertyClass _ (continuousIrreducibleRestrictClass e.symm c.val)) = n
    rw [forget_continuousIrreducibleRestrictClass, classRank_restrictClass, hc]⟩
  left_inv c := Subtype.ext (continuousIrreducibleRestrictClass_symm_apply e c.val)
  right_inv c := Subtype.ext (continuousIrreducibleRestrictClass_apply_symm e c.val)

/-- Forgetting the conditions intertwines the bijection with `restrictClass`. -/
@[simp]
theorem forget_continuousIrreducibleRestrictEquiv (e : G ≃ₜ* H) (n : ℕ)
    (c : ContinuousIrreducibleClasses.{uH, uV} H n) :
    forgetPropertyClass _ (continuousIrreducibleRestrictEquiv e n c).val =
      restrictClass (e : G →ₜ* H).toMonoidHom (forgetPropertyClass _ c.val) :=
  forget_continuousIrreducibleRestrictClass e c.val

end Topological

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

/-- Restrict each continuous irreducible class of `H` along `e : G ≃ₜ* H`,
retaining its positive rank. -/
def restrictBasisEquiv (e : G ≃ₜ* H) :
    IrreducibleBasis.{uH, uV} H ≃ IrreducibleBasis.{uG, uV} G :=
  Equiv.sigmaCongrRight (fun n =>
    FiniteRepresentation.continuousIrreducibleRestrictEquiv e (n : ℕ))

@[simp]
theorem restrictBasisEquiv_rank (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H) :
    (restrictBasisEquiv e b).1 = b.1 := rfl

@[simp]
theorem restrictBasisEquiv_symm (e : G ≃ₜ* H) :
    (restrictBasisEquiv.{uG, uH, uV} e).symm = restrictBasisEquiv e.symm := by
  apply Equiv.ext
  rintro ⟨n, b⟩
  rfl

/-- Forgetting the certificates recovers the restricted isomorphism class. -/
@[simp]
theorem underlyingClass_restrictBasisEquiv (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H) :
    underlyingClass G (restrictBasisEquiv e b) =
      restrictClass (e : G →ₜ* H).toMonoidHom (underlyingClass H b) :=
  forget_continuousIrreducibleRestrictEquiv e _ b.2

/-- On representatives, the basis bijection is restriction along `e`. -/
theorem restrictBasisEquiv_basisClass (e : G ≃ₜ* H)
    (A : FiniteRepresentation.{0, uH, uV} ℂ H)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    restrictBasisEquiv e (basisClass A hc hi n hn) =
      basisClass (restrict (e : G →ₜ* H).toMonoidHom A)
        (isContinuous_restrict (e : G →ₜ* H).toMonoidHom (e : G →ₜ* H).continuous hc)
        ((isIrreducible_restrict_iff (e : G →ₜ* H).toMonoidHom e.surjective A).mpr hi)
        n ((rank_restrict _ A).trans hn) := rfl

/-- The retained continuous class of a restricted basis class is the
continuous restriction of the original continuous class. -/
theorem basisContinuousClass_restrictBasisEquiv (e : G ≃ₜ* H)
    (b : IrreducibleBasis.{uH, uV} H) :
    basisContinuousClass G (restrictBasisEquiv e b) =
      continuousRestrictClass (e : G →ₜ* H).toMonoidHom (e : G →ₜ* H).continuous
        (basisContinuousClass H b) := by
  obtain ⟨n, c, hc⟩ := b
  induction c using Quotient.inductionOn with
  | h A => rfl

/-- Restriction along `e` carries unitary classes to unitary classes. -/
theorem isUnitaryClass_restrictBasisEquiv (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H)
    (hb : IsUnitaryClass H b) : IsUnitaryClass G (restrictBasisEquiv e b) := by
  obtain ⟨A, hA, hAb⟩ := hb
  refine ⟨restrict (e : G →ₜ* H).toMonoidHom A,
    isUnitary_restrict (e : G →ₜ* H).toMonoidHom hA, ?_⟩
  rw [underlyingClass_restrictBasisEquiv, ← hAb]
  rfl

/-- Restriction along `e` preserves and reflects the actual unitary subset. -/
theorem isUnitaryClass_restrictBasisEquiv_iff (e : G ≃ₜ* H)
    (b : IrreducibleBasis.{uH, uV} H) :
    IsUnitaryClass G (restrictBasisEquiv e b) ↔ IsUnitaryClass H b := by
  constructor
  · intro h
    have hi := isUnitaryClass_restrictBasisEquiv e.symm (restrictBasisEquiv e b) h
    rw [← restrictBasisEquiv_symm] at hi
    simpa only [Equiv.symm_apply_apply] using hi
  · exact isUnitaryClass_restrictBasisEquiv e b

/-- Restrict the basis bijection to the actual unitary bases. -/
def restrictUnitaryBasisEquiv (e : G ≃ₜ* H) :
    UnitaryBasis.{uH, uV} H ≃ UnitaryBasis.{uG, uV} G :=
  (restrictBasisEquiv e).subtypeEquiv (fun b =>
    (isUnitaryClass_restrictBasisEquiv_iff e b).symm)

@[simp]
theorem restrictUnitaryBasisEquiv_val (e : G ≃ₜ* H) (b : UnitaryBasis.{uH, uV} H) :
    (restrictUnitaryBasisEquiv e b).val = restrictBasisEquiv e b.val := rfl

@[simp]
theorem restrictUnitaryBasisEquiv_symm (e : G ≃ₜ* H) :
    (restrictUnitaryBasisEquiv.{uG, uH, uV} e).symm = restrictUnitaryBasisEquiv e.symm := by
  apply Equiv.ext
  intro b
  apply Subtype.ext
  exact Equiv.congr_fun (restrictBasisEquiv_symm e) b.val

/-- On an actual unitary representative, the unitary basis bijection is
restriction along `e`. -/
theorem restrictUnitaryBasisEquiv_unitaryBasisClass (e : G ≃ₜ* H)
    (A : FiniteRepresentation.{0, uH, uV} ℂ H)
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (hu : A.IsUnitary)
    (n : ℕ+) (hn : A.rank = (n : ℕ)) :
    restrictUnitaryBasisEquiv e (unitaryBasisClass A hc hi hu n hn) =
      unitaryBasisClass (restrict (e : G →ₜ* H).toMonoidHom A)
        (isContinuous_restrict (e : G →ₜ* H).toMonoidHom (e : G →ₜ* H).continuous hc)
        ((isIrreducible_restrict_iff (e : G →ₜ* H).toMonoidHom e.surjective A).mpr hi)
        (isUnitary_restrict (e : G →ₜ* H).toMonoidHom hu)
        n ((rank_restrict _ A).trans hn) := rfl

/-- Restriction along `e` on the full irreducible lattices. -/
def restrictLatticeEquiv (e : G ≃ₜ* H) :
    IrreducibleLattice.{uH, uV} H ≃ₗ[ℤ] IrreducibleLattice.{uG, uV} G :=
  reindex (restrictBasisEquiv e)

@[simp]
theorem restrictLatticeEquiv_single (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H) (m : ℤ) :
    restrictLatticeEquiv e (Finsupp.single b m) = Finsupp.single (restrictBasisEquiv e b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem restrictLatticeEquiv_generator (e : G ≃ₜ* H) (b : IrreducibleBasis.{uH, uV} H) :
    restrictLatticeEquiv e (generator b) = generator (restrictBasisEquiv e b) :=
  restrictLatticeEquiv_single e b 1

@[simp]
theorem restrictLatticeEquiv_coefficient (e : G ≃ₜ* H)
    (x : IrreducibleLattice.{uH, uV} H) (b : IrreducibleBasis.{uH, uV} H) :
    restrictLatticeEquiv e x (restrictBasisEquiv e b) = x b := by
  change x ((restrictBasisEquiv e).symm (restrictBasisEquiv e b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp]
theorem restrictLatticeEquiv_symm (e : G ≃ₜ* H) :
    (restrictLatticeEquiv.{uG, uH, uV} e).symm = restrictLatticeEquiv e.symm := by
  simp [restrictLatticeEquiv, reindex]

/-- Restriction along `e` on the unitary lattices. -/
def restrictUnitaryLatticeEquiv (e : G ≃ₜ* H) :
    UnitaryLattice.{uH, uV} H ≃ₗ[ℤ] UnitaryLattice.{uG, uV} G :=
  reindex (restrictUnitaryBasisEquiv e)

@[simp]
theorem restrictUnitaryLatticeEquiv_single (e : G ≃ₜ* H) (b : UnitaryBasis.{uH, uV} H)
    (m : ℤ) :
    restrictUnitaryLatticeEquiv e (Finsupp.single b m) =
      Finsupp.single (restrictUnitaryBasisEquiv e b) m :=
  Finsupp.domLCongr_single _ _ _

@[simp]
theorem restrictUnitaryLatticeEquiv_generator (e : G ≃ₜ* H) (b : UnitaryBasis.{uH, uV} H) :
    restrictUnitaryLatticeEquiv e (generator b) = generator (restrictUnitaryBasisEquiv e b) :=
  restrictUnitaryLatticeEquiv_single e b 1

@[simp]
theorem restrictUnitaryLatticeEquiv_coefficient (e : G ≃ₜ* H)
    (x : UnitaryLattice.{uH, uV} H) (b : UnitaryBasis.{uH, uV} H) :
    restrictUnitaryLatticeEquiv e x (restrictUnitaryBasisEquiv e b) = x b := by
  change x ((restrictUnitaryBasisEquiv e).symm (restrictUnitaryBasisEquiv e b)) = x b
  rw [Equiv.symm_apply_apply]

@[simp]
theorem restrictUnitaryLatticeEquiv_symm (e : G ≃ₜ* H) :
    (restrictUnitaryLatticeEquiv.{uG, uH, uV} e).symm = restrictUnitaryLatticeEquiv e.symm := by
  simp [restrictUnitaryLatticeEquiv, reindex]

/-- Inclusion of the unitary lattices intertwines the two restrictions. -/
@[simp]
theorem includeUnitary_restrictUnitaryLatticeEquiv (e : G ≃ₜ* H)
    (x : UnitaryLattice.{uH, uV} H) :
    includeUnitary G (restrictUnitaryLatticeEquiv e x) =
      restrictLatticeEquiv e (includeUnitary H x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m => simp [includeUnitary, includeSubset, map]

/-- Restriction preserves the rank-weighted integral degree. -/
@[simp]
theorem degree_restrictLatticeEquiv (e : G ≃ₜ* H) (x : IrreducibleLattice.{uH, uV} H) :
    degree G (restrictLatticeEquiv e x) = degree H x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    simp [degree, rankedDegree, VirtualRepresentation.degree, extend]

@[simp]
theorem unitaryDegree_restrictUnitaryLatticeEquiv (e : G ≃ₜ* H)
    (x : UnitaryLattice.{uH, uV} H) :
    unitaryDegree G (restrictUnitaryLatticeEquiv e x) = unitaryDegree H x := by
  simp [unitaryDegree]

/-- Restriction preserves the coefficient pairing. -/
theorem multiplicityPairing_restrictLatticeEquiv (e : G ≃ₜ* H)
    (x y : IrreducibleLattice.{uH, uV} H) :
    multiplicityPairing G (restrictLatticeEquiv e x) (restrictLatticeEquiv e y) =
      multiplicityPairing H x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [multiplicityPairing, pairing, extend, coefficient]

/-- Restriction preserves the unitary coefficient pairing. -/
theorem unitaryPairing_restrictUnitaryLatticeEquiv (e : G ≃ₜ* H)
    (x y : UnitaryLattice.{uH, uV} H) :
    unitaryPairing G (restrictUnitaryLatticeEquiv e x) (restrictUnitaryLatticeEquiv e y) =
      unitaryPairing H x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [hx, hz]
  | single b m =>
    simp [unitaryPairing, pairing, extend, coefficient]

/-- The exact realization intertwines lattice restriction with continuous
restriction of exact virtual representations. -/
theorem realizeExact_restrictLatticeEquiv (e : G ≃ₜ* H) (x : IrreducibleLattice.{uH, uV} H) :
    realizeExact G (restrictLatticeEquiv e x) =
      ExactGrothendieckGroup.continuousRestrict (e : G →ₜ* H) (realizeExact H x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single b m =>
    have hs : ∀ c : IrreducibleBasis.{uH, uV} H,
        Finsupp.single c m = m • generator c := fun c => by simp [generator]
    have hg : realizeExact G (restrictLatticeEquiv e (generator b)) =
        ExactGrothendieckGroup.continuousRestrict (e : G →ₜ* H)
          (realizeExact H (generator b)) := by
      rw [restrictLatticeEquiv_generator, realizeExact_generator, realizeExact_generator,
        basisContinuousClass_restrictBasisEquiv]
      obtain ⟨n, c, hc⟩ := b
      induction c using Quotient.inductionOn with
      | h A =>
        exact (ExactGrothendieckGroup.restrict_ofClass _ _ _ _ _).symm
    rw [hs, LinearEquiv.map_smul, LinearMap.map_smul, hg, LinearMap.map_smul,
      LinearMap.map_smul]

/-- The same compatibility on the unitary lattices. -/
theorem realizeExact_includeUnitary_restrictUnitaryLatticeEquiv (e : G ≃ₜ* H)
    (x : UnitaryLattice.{uH, uV} H) :
    realizeExact G (includeUnitary G (restrictUnitaryLatticeEquiv e x)) =
      ExactGrothendieckGroup.continuousRestrict (e : G →ₜ* H)
        (realizeExact H (includeUnitary H x)) := by
  rw [includeUnitary_restrictUnitaryLatticeEquiv, realizeExact_restrictLatticeEquiv]

/-- An identity of exact virtual representations between a unitary element of
`G` and the restriction of a unitary element of `H` along `e` holds exactly
when the lattice restriction of the second element is the first. -/
theorem continuousRestrict_realizeExact_includeUnitary_eq_iff (e : G ≃ₜ* H)
    (y : UnitaryLattice.{uH, uV} H) (x : UnitaryLattice.{uG, uV} G) :
    ExactGrothendieckGroup.continuousRestrict (e : G →ₜ* H)
        (realizeExact H (includeUnitary H y)) =
        realizeExact G (includeUnitary G x) ↔
      restrictUnitaryLatticeEquiv e y = x := by
  rw [← realizeExact_includeUnitary_restrictUnitaryLatticeEquiv]
  exact ((realizeExact_injective G).comp
    (Finsupp.mapDomain_injective Subtype.val_injective :
      Function.Injective (includeUnitary.{uG, uV} G))).eq_iff

end Langlands.VirtualRepresentation.Weil
