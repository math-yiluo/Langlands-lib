import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Global.Factors.RelativeWeilLocalEuler
import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.Weil.Local.ExtensionWeilEquiv
import Langlands.LocalFactor.WeilDeligneTransport
import Langlands.Global.Factors.RelativeWeilLocalEpsilon
import Langlands.Correspondence.AssemblyLTwistedSupercuspidal

/-!
# Weil-side determinants and pair L-factors along an isomorphism of p-adic fields
-/

noncomputable section

universe uF uE uV w

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (g : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- An isomorphism of p-adic fields has residue degree one. -/
@[simp]
theorem extensionResidueDegree_algEquiv : extensionResidueDegree F E g.toAlgHom = 1 := by
  have h := extensionResidueDegree_comp F E F g.toAlgHom g.symm.toAlgHom
  have hid : g.symm.toAlgHom.comp g.toAlgHom = AlgHom.id (Padic p) F.Carrier := by
    ext x
    simp
  rw [hid, extensionResidueDegree_id] at h
  exact Nat.eq_one_of_mul_eq_one_right h.symm

/-- The local Weil map of an isomorphism preserves the integral degree. -/
@[simp]
theorem localDegreeInt_extensionWeilEquiv (w : localWeilGroup E) :
    localDegreeInt F (extensionWeilEquiv F E g w) = localDegreeInt E w := by
  rw [extensionWeilEquiv_apply, localDegreeInt_extensionWeilMap, extensionResidueDegree_algEquiv]
  simp

end Langlands.Weil.Local

namespace Langlands.FiniteRepresentation

/-- The determinant character of a restricted class is the composite with the
restriction map. -/
theorem determinantCharacterClass_restrictClass {G : Type*} {H : Type*} [Group G] [Group H]
    (φ : H →* G) (c : IsomorphismClasses.{0, _, uV} ℂ G) :
    determinantCharacterClass (restrictClass φ c) = (determinantCharacterClass c).comp φ := by
  induction c using Quotient.inductionOn with
  | h A =>
    ext h
    rfl

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.LocalWeil

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} q)

local instance {G : Type*} [Group G] : AddCommMonoid (Additive (G →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (G →* ℂˣ))).toAddCommMonoid

/-- The determinant of a restricted unitary virtual Weil class is the composite
of the original determinant with the group isomorphism. -/
theorem unitaryDeterminant_restrictUnitaryLatticeEquiv
    (Φ : Weil.Local.localWeilGroup E ≃ₜ* Weil.Local.localWeilGroup F)
    (x : UnitaryLattice.{uF, uV} F) (w : Weil.Local.localWeilGroup E) :
    Additive.toMul (unitaryDeterminant E (Weil.restrictUnitaryLatticeEquiv Φ x)) w =
      Additive.toMul (unitaryDeterminant F x) (Φ w) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [map_add, toMul_add, hx, hy]
  | single b m =>
    have hs : (Finsupp.single b m : UnitaryLattice.{uF, uV} F) = m • generator b := by
      simp [generator]
    rw [Weil.restrictUnitaryLatticeEquiv_single]
    have hs' : (Finsupp.single (Weil.restrictUnitaryBasisEquiv Φ b) m :
        UnitaryLattice.{uE, uV} E) = m • generator (Weil.restrictUnitaryBasisEquiv Φ b) := by
      simp [generator]
    rw [hs, hs', map_zsmul, map_zsmul, toMul_zsmul, toMul_zsmul, MonoidHom.zpow_apply,
      MonoidHom.zpow_apply, unitaryDeterminant_generator, unitaryDeterminant_generator,
      Weil.restrictUnitaryBasisEquiv_val, Weil.underlyingClass_restrictBasisEquiv,
      FiniteRepresentation.determinantCharacterClass_restrictClass]
    rfl

end Langlands.VirtualRepresentation.LocalWeil

namespace Langlands.FiniteRepresentation

/-- Restriction along a group isomorphism `e : H ≃ G` identifies the invariants of
`J = e⁻¹(I)` with those of `I`; an element `h` of `H` then acts on them as any
`g ∈ G` with `g⁻¹ e(h) ∈ I`, so the two Euler polynomials agree. -/
theorem eulerPolynomial_invariants_restrict {K : Type*} [Field K] {G : Type*} {H : Type*}
    [Group G] [Group H] (e : H ≃* G) (R : FiniteRepresentation.{_, _, uV} K G)
    (I : Subgroup G) [I.Normal] (J : Subgroup H) [J.Normal]
    (hJ : J = I.comap e.toMonoidHom) (h : H) (g : G) (hg : g⁻¹ * e h ∈ I) :
    LocalFactor.eulerPolynomial ((invariants J (restrict e.toMonoidHom R)).representation h) =
      LocalFactor.eulerPolynomial ((invariants I R).representation g) := by
  subst hJ
  have hp := LocalFactor.eulerPolynomial_conj
    (LocalFactor.WeilDeligne.Transport.invariantsEquiv e R I).toLinearEquiv
    ((invariants (I.comap e.toMonoidHom) (restrict e.toMonoidHom R)).representation h)
  rw [Representation.Equiv.conj_apply_self] at hp
  rw [← hp]
  change LocalFactor.eulerPolynomial ((invariants I R).representation (e h)) = _
  have hgh : e h = g * (g⁻¹ * e h) := by group
  rw [hgh, map_mul]
  have htriv : (invariants I R).representation (g⁻¹ * e h) = 1 := by
    ext x
    exact Representation.isTrivial_apply ((invariants I R).representation.comp I.subtype)
      ⟨g⁻¹ * e h, hg⟩ x
  rw [htriv, mul_one]

end Langlands.FiniteRepresentation

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime]

theorem mem_localInertia_iff (F : PadicField.{uF} p) (w : localWeilGroup F) :
    w ∈ localInertia F ↔ localDegreeInt F w = 0 := by
  change localDegree F w = 1 ↔ (localDegree F w).toAdd = 0
  exact ⟨fun h => by rw [h]; rfl, fun h => by
    rw [← ofAdd_toAdd (localDegree F w), h]; rfl⟩

theorem localDegreeInt_mul (F : PadicField.{uF} p) (w w' : localWeilGroup F) :
    localDegreeInt F (w * w') = localDegreeInt F w + localDegreeInt F w' := by
  change (localDegree F (w * w')).toAdd = _
  rw [map_mul, toAdd_mul]
  rfl

theorem localDegreeInt_inv (F : PadicField.{uF} p) (w : localWeilGroup F) :
    localDegreeInt F w⁻¹ = -localDegreeInt F w := by
  change (localDegree F w⁻¹).toAdd = _
  rw [map_inv, toAdd_inv]
  rfl

theorem localDegreeInt_localGeometricFrobenius (F : PadicField.{uF} p) :
    localDegreeInt F (localGeometricFrobenius F) = 1 := by
  change (localDegree F (localGeometricFrobenius F)).toAdd = 1
  rw [localGeometricFrobenius_degree]
  rfl

namespace InertiaEuler

variable {q : ℕ} [Fact q.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} q)

/-- Restriction along a degree-preserving isomorphism of local Weil groups keeps
the Euler polynomial on inertia invariants. -/
theorem eulerPolynomial_restrict (Φ : localWeilGroup E ≃* localWeilGroup F)
    (hΦ : ∀ w, localDegreeInt F (Φ w) = localDegreeInt E w)
    (T : LocalWeilRepresentation.{uF, uV} F) :
    eulerPolynomial E (FiniteRepresentation.restrict Φ.toMonoidHom T) = eulerPolynomial F T := by
  apply FiniteRepresentation.eulerPolynomial_invariants_restrict Φ T
  · ext w
    simp only [Subgroup.mem_comap, mem_localInertia_iff]
    exact (hΦ w).symm ▸ Iff.rfl
  · rw [mem_localInertia_iff, localDegreeInt_mul, localDegreeInt_inv,
      hΦ, localDegreeInt_localGeometricFrobenius,
      localDegreeInt_localGeometricFrobenius]
    simp

end InertiaEuler

end Langlands.Weil.Local

namespace Langlands.VirtualRepresentation.LocalWeil

open Langlands.Weil.Local FiniteRepresentation WeilDeligneRepresentation

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} q)

/-- The pair class of a unitary basis class is the zero-monodromy class of any
representative. -/
theorem unitaryBasisPairClass_eq_classOf (c : UnitaryBasis.{uF, uV} F)
    (V : LocalWeilRepresentation.{uF, uV} F)
    (hV : FiniteRepresentation.classOf V = Weil.underlyingClass (localWeilGroup F) c.val) :
    unitaryBasisPairClass F c =
      WeilDeligneRepresentation.classOf
        (zeroMonodromy (localNormCharacter F).toMonoidHom V) :=
  Correspondence.weilPairClass_eq_classOf F c.val.2 V hV

/-- The pair class of a restricted unitary basis class is the zero-monodromy class
of the restricted representative. -/
theorem unitaryBasisPairClass_restrictUnitaryBasisEquiv
    (Φ : localWeilGroup E ≃ₜ* localWeilGroup F) (c : UnitaryBasis.{uF, uV} F)
    (V : LocalWeilRepresentation.{uF, uV} F)
    (hV : FiniteRepresentation.classOf V = Weil.underlyingClass (localWeilGroup F) c.val) :
    unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv Φ c) =
      WeilDeligneRepresentation.classOf (zeroMonodromy (localNormCharacter E).toMonoidHom
        (FiniteRepresentation.restrict
          (Φ : localWeilGroup E →ₜ* localWeilGroup F).toMonoidHom V)) := by
  apply unitaryBasisPairClass_eq_classOf
  rw [Weil.restrictUnitaryBasisEquiv_val, Weil.underlyingClass_restrictBasisEquiv, ← hV]
  rfl

/-- Restriction along a degree-preserving isomorphism of local Weil groups keeps the
arithmetic pair L-factor of two unitary basis classes. -/
theorem arithmeticPairLFactor_restrictUnitaryBasisEquiv
    (Φ : localWeilGroup E ≃ₜ* localWeilGroup F)
    (hΦ : ∀ w, localDegreeInt F (Φ w) = localDegreeInt E w) (a b : UnitaryBasis.{uF, uV} F) :
    Correspondence.arithmeticPairLFactor E
        (unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv Φ a))
        (unitaryBasisPairClass E (Weil.restrictUnitaryBasisEquiv Φ b)) =
      Correspondence.arithmeticPairLFactor F (unitaryBasisPairClass F a)
        (unitaryBasisPairClass F b) := by
  obtain ⟨V, hV⟩ := Quotient.exists_rep (Weil.underlyingClass (localWeilGroup F) a.val)
  obtain ⟨W, hW⟩ := Quotient.exists_rep (Weil.underlyingClass (localWeilGroup F) b.val)
  rw [unitaryBasisPairClass_restrictUnitaryBasisEquiv F E Φ a V hV,
    unitaryBasisPairClass_restrictUnitaryBasisEquiv F E Φ b W hW,
    unitaryBasisPairClass_eq_classOf F a V hV, unitaryBasisPairClass_eq_classOf F b W hW,
    InertiaEuler.arithmeticPairLFactor_zeroMonodromy E _ _ _
      (FiniteRepresentation.restrictTensorIdEquiv _ V W),
    InertiaEuler.arithmeticPairLFactor_zeroMonodromy F V W _ (Representation.Equiv.refl _),
    InertiaEuler.coe_lFactorUnit, InertiaEuler.coe_lFactorUnit]
  exact congrArg (fun P => (algebraMap (Polynomial ℂ) (RatFunc ℂ) P)⁻¹)
    (InertiaEuler.eulerPolynomial_restrict F E Φ.toMulEquiv hΦ (FiniteRepresentation.tensor V W))

/-- Restriction along a degree-preserving isomorphism of local Weil groups keeps the
virtual pair L-factor. -/
theorem unitaryPairLFactor_restrictUnitaryLatticeEquiv
    (Φ : localWeilGroup E ≃ₜ* localWeilGroup F)
    (hΦ : ∀ w, localDegreeInt F (Φ w) = localDegreeInt E w) (x y : UnitaryLattice.{uF, uV} F) :
    unitaryPairLFactor E (Weil.restrictUnitaryLatticeEquiv Φ x)
        (Weil.restrictUnitaryLatticeEquiv Φ y) = unitaryPairLFactor F x y := by
  simp only [unitaryPairLFactor, Weil.restrictUnitaryLatticeEquiv, reindex,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.prod_equivMapDomain,
    arithmeticPairLFactor_restrictUnitaryBasisEquiv F E Φ hΦ]

end Langlands.VirtualRepresentation.LocalWeil
