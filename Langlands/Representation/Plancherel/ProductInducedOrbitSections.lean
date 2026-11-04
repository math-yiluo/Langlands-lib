import Langlands.Representation.Plancherel.ProductInducedSmoothFamilies

/-!
# Actual sections over all representatives in a unitary twist orbit

Canonical coefficient transport descends the dependent parameter-cover families
to all actual irreducible admissible inducing representatives in the orbit.
-/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))

/-- Every actual irreducible admissible representative whose canonical class
is in the unitary unramified twist orbit of the given inducing object. -/
abbrev UnitaryOrbitRepresentative :=
  {A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M) |
    ∃ χ : unitaryUnramifiedCharacters ν,
      SmoothDualClass.twist (unitaryUnramifiedInclusion ν χ).val.toMonoidHom
        (unramifiedCharacter_isOpen_ker ν (unitaryUnramifiedInclusion ν χ))
        (Quotient.mk _ π : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) =
      (Quotient.mk _ A : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M))}

variable {J : Type uJ} (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))

/-- The literal inducing representative at a torus parameter, with its actual
orbit membership proof. -/
def unitaryOrbitParameterRepresentative (z : J → Circle) :
    UnitaryOrbitRepresentative ν π :=
  ⟨IrreducibleAdmissibleRep.twist
      (unitaryTorusParameter ν e z).val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν (unitaryTorusParameter ν e z)) π,
    e.symm z, rfl⟩

/-- An auxiliary parameter for a representative, chosen from its actual orbit
membership. The descended section will be independent of this choice. -/
def unitaryOrbitRepresentativeParameter
    (A : UnitaryOrbitRepresentative ν π) : J → Circle :=
  e (Classical.choose A.property)

/-- An actual inducing equivalence from the chosen parameter representative. -/
def unitaryOrbitRepresentativeEquiv (A : UnitaryOrbitRepresentative ν π) :
    (unitaryOrbitParameterRepresentative ν π e
      (unitaryOrbitRepresentativeParameter ν π e A)).val.obj.representation.Equiv
        A.val.obj.representation := by
  have hclass :
      (Quotient.mk _ (unitaryOrbitParameterRepresentative ν π e
        (unitaryOrbitRepresentativeParameter ν π e A)).val :
        SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M)) = Quotient.mk _ A.val := by
    simpa only [unitaryOrbitParameterRepresentative, unitaryOrbitRepresentativeParameter,
      unitaryTorusParameter, e.symm_apply_apply, SmoothDualClass.twist_mk,
      SmoothDualClass] using
      Classical.choose_spec A.property
  exact SmoothRep.equivOfIso
    ((irreducibleAdmissibleProperty (k := ℂ) (G := M)).ι.mapIso
      (Classical.choice (Quotient.exact hclass)))

/-- Isomorphic parameter representatives differ by an actual unitary
class-stabilizer element. -/
theorem exists_unitaryStabilizer_of_parameter_equiv (z w : J → Circle)
    (a :
      (unitaryOrbitParameterRepresentative ν π e z).val.obj.representation.Equiv
        (unitaryOrbitParameterRepresentative ν π e w).val.obj.representation) :
    ∃ s : unitaryClassTwistStabilizer ν (Quotient.mk _ π),
      w = z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s := by
  let χ := e.symm z
  let η := e.symm w
  let ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := M) := Quotient.mk _ π
  have hclass :
      unitaryUnramifiedInclusion ν χ • ω =
        unitaryUnramifiedInclusion ν η • ω :=
    Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso a)⟩
  have hs : χ⁻¹ * η ∈ unitaryClassTwistStabilizer ν (Quotient.mk _ π) := by
    change unitaryUnramifiedInclusion ν (χ⁻¹ * η) • ω = ω
    rw [map_mul, map_inv, mul_smul, ← hclass, inv_smul_smul]
  refine ⟨⟨χ⁻¹ * η, hs⟩, ?_⟩
  change w = z * e (χ⁻¹ * η)
  rw [map_mul, map_inv]
  simp only [χ, η, e.apply_symm_apply, mul_inv_cancel_left]

variable [LocallyCompactSpace G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))

/-- Actual sections, with one normalized product-induced value at every
representative in the unitary twist orbit. -/
abbrev ProductInducedOrbitSections :=
  ∀ A : UnitaryOrbitRepresentative ν π,
    productInducedCoefficientObject h hU A.val.obj

/-- Coherence is equality under every actual inducing equivalence. -/
def coherentProductInducedOrbitSections :
    Submodule ℂ (ProductInducedOrbitSections ν π h hU) where
  carrier := {q | ∀ (A B : UnitaryOrbitRepresentative ν π)
    (a : A.val.obj.representation.Equiv B.val.obj.representation),
    q B = productInducedCoefficientTransport h hU a (q A)}
  zero_mem' := by
    intro A B a
    exact (map_zero (productInducedCoefficientTransport h hU a)).symm
  add_mem' := by
    intro q r hq hr A B a
    exact (congrArg₂ (· + ·) (hq A B a) (hr A B a)).trans (map_add _ _ _).symm
  smul_mem' := by
    intro c q hq A B a
    exact (congrArg (c • ·) (hq A B a)).trans (map_smul _ c _).symm

/-- Restrict an all-representative section to the literal parameter
representatives. -/
def productInducedOrbitPullback :
    ProductInducedOrbitSections ν π h hU →ₗ[ℂ]
      ProductInducedTorusFamilies ν e h hU π.obj where
  toFun q z := q (unitaryOrbitParameterRepresentative ν π e z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  [Fintype J]

/-- Stabilizer covariance implies compatibility with any actual equivalence
between any two parameter representatives. -/
theorem productInducedSmoothFamily_transport
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π)
    (z w : J → Circle)
    (a :
      (unitaryOrbitParameterRepresentative ν π e z).val.obj.representation.Equiv
        (unitaryOrbitParameterRepresentative ν π e w).val.obj.representation) :
    F.val w = productInducedCoefficientTransport h hU a (F.val z) := by
  obtain ⟨s, rfl⟩ := exists_unitaryStabilizer_of_parameter_equiv ν π e z w a
  exact ((mem_productInducedSmoothFamilies_iff ν e h K hP hK hν hr hU hPK π F.val).mp
    F.property).2 s z |>.trans
      (congrArg (fun T => T (F.val z))
        (unitaryTorusInducedFiberEquiv_eq_transport ν e h hU π s z a))

/-- Extend a smooth parameter family using actual inducing transport from an
auxiliary parameter at each representative. -/
def productInducedOrbitExtension :
    productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π →ₗ[ℂ]
      ProductInducedOrbitSections ν π h hU where
  toFun F A := productInducedCoefficientTransport h hU
    (unitaryOrbitRepresentativeEquiv ν π e A)
    (F.val (unitaryOrbitRepresentativeParameter ν π e A))
  map_add' F H := by
    funext A
    exact map_add _ _ _
  map_smul' c F := by
    funext A
    exact map_smul _ c _

/-- The extension can be evaluated using any parameter and any actual
inducing equivalence to the representative. This proves independence of both
auxiliary choices. -/
theorem productInducedOrbitExtension_of_equiv
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π)
    (A : UnitaryOrbitRepresentative ν π) (z : J → Circle)
    (a : (unitaryOrbitParameterRepresentative ν π e z).val.obj.representation.Equiv
      A.val.obj.representation) :
    productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F A =
      productInducedCoefficientTransport h hU a (F.val z) := by
  let b := unitaryOrbitRepresentativeEquiv ν π e A
  let w := unitaryOrbitRepresentativeParameter ν π e A
  have hF := productInducedSmoothFamily_transport ν π e h hU K hP hK hν hr hPK
    F z w (a.trans b.symm)
  calc
    _ = productInducedCoefficientTransport h hU b
        (productInducedCoefficientTransport h hU (a.trans b.symm) (F.val z)) :=
      congrArg (productInducedCoefficientTransport h hU b) hF
    _ = productInducedCoefficientTransport h hU ((a.trans b.symm).trans b)
        (F.val z) :=
      (productInducedCoefficientTransport_trans h hU (a.trans b.symm) b (F.val z)).symm
    _ = productInducedCoefficientTransport h hU a (F.val z) := by
      exact congrArg (fun T => T (F.val z))
        (productInducedCoefficientTransport_independent h hU
          (unitaryOrbitParameterRepresentative ν π e z).val.property.2
          (unitaryOrbitParameterRepresentative ν π e z).val.property.1
          ((a.trans b.symm).trans b) a)

/-- The extension is coherent under every actual equivalence between orbit
representatives. -/
theorem productInducedOrbitExtension_coherent
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :
    productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F ∈
      coherentProductInducedOrbitSections ν π h hU := by
  intro A B a
  exact (productInducedOrbitExtension_of_equiv ν π e h hU K hP hK hν hr hPK F B
    (unitaryOrbitRepresentativeParameter ν π e A)
    ((unitaryOrbitRepresentativeEquiv ν π e A).trans a)).trans
      (productInducedCoefficientTransport_trans h hU
        (unitaryOrbitRepresentativeEquiv ν π e A) a _)

/-- Pullback of the extension recovers the entire original dependent family. -/
theorem productInducedOrbitPullback_extension
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π) :
    productInducedOrbitPullback ν π e h hU
      (productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F) = F.val := by
  funext z
  exact (productInducedOrbitExtension_of_equiv ν π e h hU K hP hK hν hr hPK F
    (unitaryOrbitParameterRepresentative ν π e z) z
    (Representation.Equiv.refl _)).trans
      (productInducedCoefficientTransport_refl h hU (F.val z))

/-- There is exactly one coherent extension of a given smooth parameter
family, even among coherent sections for which smoothness was not required. -/
theorem productInducedOrbitExtension_unique
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π)
    (q : coherentProductInducedOrbitSections ν π h hU)
    (hq : productInducedOrbitPullback ν π e h hU q.val = F.val) :
    q.val = productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F := by
  funext A
  exact (q.property
    (unitaryOrbitParameterRepresentative ν π e
      (unitaryOrbitRepresentativeParameter ν π e A))
    A (unitaryOrbitRepresentativeEquiv ν π e A)).trans
      (congrArg (productInducedCoefficientTransport h hU
        (unitaryOrbitRepresentativeEquiv ν π e A))
        (congrFun hq (unitaryOrbitRepresentativeParameter ν π e A)))

/-- Evaluation is the actual vector and inverse-functional tensor transport
at every point of the product group. -/
theorem productInducedOrbitExtension_eval_of_equiv
    (F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π)
    (A : UnitaryOrbitRepresentative ν π) (z : J → Circle)
    (a : (unitaryOrbitParameterRepresentative ν π e z).val.obj.representation.Equiv
      A.val.obj.representation)
    (x : G × G) :
    eval _ _ (productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F A) x =
      productCoefficientLeviEquiv a (eval _ _ (F.val z) x) := by
  rw [productInducedOrbitExtension_of_equiv ν π e h hU K hP hK hν hr hPK F A z a]
  exact productInducedCoefficientTransport_eval h hU a (F.val z) x

/-- Smooth orbit sections are coherent actual sections whose parameter
pullback has finite scalar-smooth compact restriction. -/
def productInducedSmoothOrbitSections :
    Submodule ℂ (ProductInducedOrbitSections ν π h hU) :=
  coherentProductInducedOrbitSections ν π h hU ⊓
    (finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)).comap
      ((productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).toLinearMap.comp
        (productInducedOrbitPullback ν π e h hU))

/-- Coherence supplies all stabilizer covariance, so pullback is a smooth
parameter family with the actual transport law. -/
def productInducedSmoothOrbitPullback :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ]
      productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π where
  toFun q := ⟨productInducedOrbitPullback ν π e h hU q.val, by
    apply (mem_productInducedSmoothFamilies_iff ν e h K hP hK hν hr hU hPK π _).mpr
    refine ⟨q.property.2, fun s z => ?_⟩
    exact q.property.1
      (unitaryOrbitParameterRepresentative ν π e z)
      (unitaryOrbitParameterRepresentative ν π e
        (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s))
      (unitaryTorusFiberEquiv ν e π s z)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

/-- The choice-independent extension lands in the coherent smooth section
space. Smoothness follows by exact recovery of the original parameter family. -/
def productInducedSmoothOrbitExtension :
    productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π →ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK where
  toFun F := ⟨productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F,
    productInducedOrbitExtension_coherent ν π e h hU K hP hK hν hr hPK F, by
      change productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU
          (productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F)) ∈
        finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj)
      rw [productInducedOrbitPullback_extension]
      exact F.property.1⟩
  map_add' F H := Subtype.ext
    ((productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK).map_add F H)
  map_smul' c F := Subtype.ext
    ((productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK).map_smul c F)

/-- Actual pullback is a linear equivalence between smooth sections over all
orbit representatives and smooth families on the unitary parameter cover. -/
def productInducedSmoothOrbitFamilyEquiv :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK ≃ₗ[ℂ]
      productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π where
  toLinearMap := productInducedSmoothOrbitPullback ν π e h hU K hP hK hν hr hPK
  invFun := productInducedSmoothOrbitExtension ν π e h hU K hP hK hν hr hPK
  left_inv q := by
    apply Subtype.ext
    funext A
    exact (q.property.1
      (unitaryOrbitParameterRepresentative ν π e
        (unitaryOrbitRepresentativeParameter ν π e A))
      A (unitaryOrbitRepresentativeEquiv ν π e A)).symm
  right_inv F := Subtype.ext
    (productInducedOrbitPullback_extension ν π e h hU K hP hK hν hr hPK F)

local instance orbitSmoothTensorAddCommGroup :
    AddCommGroup
      (smoothFiniteTorusFunctions J ⊗[ℂ] ProductInducedCompactPicture h K π.obj) :=
  TensorProduct.addCommGroup

/-- Waldspurger's diagonal invariant tensor model now gives actual coherent
smooth sections on every representative in the unitary twist orbit. -/
def productInducedSmoothTensorOrbitEquiv :
    (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants ≃ₗ[ℂ]
      productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK :=
  (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π).trans
    (productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK).symm

/-- At any representative the tensor model is the actual inducing transport
of its normalized parameter-fiber extension, through any realizing equivalence. -/
theorem productInducedSmoothTensorOrbitEquiv_apply_of_equiv
    (t : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants)
    (A : UnitaryOrbitRepresentative ν π) (z : J → Circle)
    (a : (unitaryOrbitParameterRepresentative ν π e z).val.obj.representation.Equiv
      A.val.obj.representation) :
    (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK t).val A =
      productInducedCoefficientTransport h hU a
        ((productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t).val z) :=
  productInducedOrbitExtension_of_equiv ν π e h hU K hP hK hν hr hPK
    (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t) A z a

/-- The forward map recovers the concrete tensor evaluation after pullback
and actual compact restriction. -/
@[simp]
theorem productInducedSmoothTensorOrbitEquiv_restriction
    (t : (productInducedSmoothTensorRepresentation ν e h K hP hK hν hr π).invariants)
    (z : J → Circle) :
    productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
      (productInducedOrbitPullback ν π e h hU
        (productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK t).val) z =
      smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj) t.val z := by
  exact (congrArg
    (fun F => productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj F z)
    (productInducedOrbitPullback_extension ν π e h hU K hP hK hν hr hPK
      (productInducedSmoothTensorFamilyEquiv ν e h K hP hK hν hr hU hPK π t))).trans
    (productInducedSmoothTensorFamilyEquiv_restriction ν e h K hP hK hν hr hU hPK π t z)

/-- The inverse tensor recovers the actual compact restriction of the
section at every literal parameter representative. -/
@[simp]
theorem productInducedSmoothTensorOrbitEquiv_symm_evaluation
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (z : J → Circle) :
    smoothTensorEvaluation J (ProductInducedCompactPicture h K π.obj)
      ((productInducedSmoothTensorOrbitEquiv ν π e h hU K hP hK hν hr hPK).symm q).val z =
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU q.val) z :=
  productInducedSmoothTensorFamilyEquiv_symm_evaluation ν e h K hP hK hν hr hU hPK π
    (productInducedSmoothOrbitPullback ν π e h hU K hP hK hν hr hPK q) z

end Langlands.Plancherel
