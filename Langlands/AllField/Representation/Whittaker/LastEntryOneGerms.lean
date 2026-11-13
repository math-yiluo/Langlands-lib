import Langlands.Representation.Whittaker.LastEntryOneGerms
import Langlands.AllField.Representation.Parabolic.JacquetCenterSpanProof
import Langlands.AllField.Representation.Whittaker.CoordinateJacquetKernelProof
import Langlands.AllField.Representation.Whittaker.JPSFunctionSpace
import Langlands.AllField.Representation.Whittaker.LastEntryOneAdapters
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof
/-!
# Root coefficient maps into the actual coordinate germs

The general Jacquet factorization below has an explicit kernel-vanishing
premise. The final Whittaker specialization discharges it using the published
kernel theorem and obtains finite operator spans from the published
Jacquet-center theorem.
-/

noncomputable section

namespace Langlands.AllField.WhittakerLastEntryOne
open Langlands.WhittakerLastEntryOne hiding assemble continuous_rootLiftHom coordinateBlockScalars coordinateJacquetRepresentation coordinateJacquetRepresentation_mk coordinateJacquetToRootGerm coordinateJacquetToRootGerm_surjective jacquetToRootGerm jacquetToRootGerm_mk jacquetToRootGerm_surjective pullback_injective rootCoefficientMap rootCoefficientMap_apply rootCoefficientSpace rootCoefficientSpace_finiteCoordinateOperatorSpan rootCoefficientSpace_finiteOperatorSpans rootCoefficientSpace_hasCoordinateUpperSupport rootCoefficientSpace_hasCoordinateUpperSupport_of_statement rootCoefficientSpace_isLocallyConstantSpace rootCoefficientSpace_locallyConstant rootCoefficientSpace_upper_support rootCoefficientToSpace rootCoefficientToSpace_surjective rootCoefficient_kernel rootGermMap rootGermMap_coordinate rootGermMap_eq_zero_iff rootGermMap_surjective rootHom_rootLift rootLiftHom rootLift_coordinateEmbedding rootLift_last rootLift_rootHom torus_rootLift_coordinateEmbedding upper_support_of_statement
open Langlands.AllField.WhittakerLastEntryOne

universe uF uV uW uG

section OperatorSpan

variable {G : Type uG} [Monoid G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

end OperatorSpan

section Germs

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)

/-- The actual coefficient map corestricted to its invariant image. -/
def rootCoefficientToSpace :
    Representation.IntertwiningMap (ρ.comp (torus.comp (rootLiftHom F T n)))
      (rootCoefficientSpace F T n V ρ ℓ).toRepresentation where
  toLinearMap := (rootCoefficientMap F T n V ρ ℓ).toLinearMap.rangeRestrict
  isIntertwining' x := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun a => a v) ((rootCoefficientMap F T n V ρ ℓ).isIntertwining' x)

theorem rootCoefficientToSpace_surjective :
    Function.Surjective (rootCoefficientToSpace F T n V ρ ℓ) := by
  intro f
  obtain ⟨v, hv⟩ := f.property
  exact ⟨v, Subtype.ext hv⟩

/-- The canonical surjection from the original carrier to a coordinate germ. -/
def rootGermMap (i : Fin n) :
    Representation.IntertwiningMap (ρ.comp (torus.comp (rootLiftHom F T n)))
      (Langlands.AllField.Whittaker.JPSFunctionSpace.germRepresentation (rootCoefficientSpace F T n V ρ ℓ) T i) :=
  (Langlands.AllField.Whittaker.JPSFunctionSpace.germMap (rootCoefficientSpace F T n V ρ ℓ) T i).comp
    (rootCoefficientToSpace F T n V ρ ℓ)

theorem rootGermMap_surjective (i : Fin n) :
    Function.Surjective (rootGermMap F T n V ρ ℓ i) :=
  (Langlands.AllField.Whittaker.JPSFunctionSpace.germMap_surjective _ T i).comp (rootCoefficientToSpace_surjective F T n V ρ ℓ)

theorem rootGermMap_eq_zero_iff (i : Fin n) (v : V) :
    rootGermMap F T n V ρ ℓ i v = 0 ↔
      Langlands.AllField.Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
        (fun x => ℓ (ρ (torus (rootLift x)) v)) :=
  Langlands.AllField.Whittaker.JPSFunctionSpace.germMap_eq_zero_iff _ T i _

/-- Pulling back along the coordinate embedding gives the literal dilation action. -/
theorem rootGermMap_coordinate (i : Fin n) (b : Fˣ) (v : V) :
    rootGermMap F T n V ρ ℓ i
        (ρ (torus (rootLift (Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b))) v) =
      Langlands.AllField.Whittaker.JPSFunctionSpace.sigma (rootCoefficientSpace F T n V ρ ℓ) T i b
        (rootGermMap F T n V ρ ℓ i v) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (rootGermMap F T n V ρ ℓ i) (Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b) v

include T in
/-- A single root-coordinate dilation scales exactly the initial diagonal block. -/
theorem rootLift_coordinateEmbedding (i : Fin n) (b : Fˣ) :
    rootLift (Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b) =
      fun j => if j.val ≤ i.val then b else 1 := by
  classical
  let a : Fin (n + 1) → Fˣ := fun j => if j.val ≤ i.val then b else 1
  have ha : a (Fin.last n) = 1 := by
    simp [a, show ¬ n ≤ i.val by omega]
  have hroot : rootHom a = Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b := by
    funext j
    rcases lt_trichotomy j.val i.val with h | h | h
    · have hne : j ≠ i := by intro hij; subst i; omega
      simp [rootHom, a, Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding, hne,
        show j.val ≤ i.val by omega, show j.val + 1 ≤ i.val by omega]
    · have hij : j = i := Fin.ext h
      subst j
      simp [rootHom, a, Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding]
    · have hne : j ≠ i := by intro hij; subst i; omega
      simp [rootHom, a, Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding, hne,
        show ¬ j.val ≤ i.val by omega, show ¬ j.val + 1 ≤ i.val by omega]
  rw [← hroot]
  exact rootLift_rootHom F T n a ha

/-- The scalar tuple `(b,1)` in that actual product Levi. -/
def coordinateBlockScalars (i : Fin n) :
    Fˣ →* (Fin (coordinateBlock n i).length → Fˣ) where
  toFun b j := if j.val = 0 then b else 1
  map_one' := by ext j; simp
  map_mul' b c := by ext j; by_cases hj : j.val = 0 <;> simp [hj]

include T in
/-- The actual diagonal root lift equals the embedded two-block scalar. -/
theorem torus_rootLift_coordinateEmbedding (i : Fin n) (b : Fˣ) :
    torus (rootLift (Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b)) =
      (coordinateBlock n i).blockScalar F (coordinateBlockScalars F n i b) := by
  classical
  apply Units.ext
  change Matrix.diagonal (fun j => (rootLift
    (Langlands.AllField.Whittaker.JPSFunctionSpace.coordinateEmbedding i b) j : F)) = _
  rw [rootLift_coordinateEmbedding F T n i b,
    GeneralLinear.BlockShape.coe_blockScalar]
  congr 1
  funext j
  obtain ⟨⟨k, r⟩, rfl⟩ := (coordinateBlock n i).indexEquiv.surjective j
  rw [(coordinateBlock n i).indexEquiv.symm_apply_apply]
  apply congrArg (fun u : Fˣ => (u : F))
  change ((if ((coordinateBlock n i).index k r).val ≤ i.val then b else 1) : Fˣ) =
    (coordinateBlockScalars F n i b k : Fˣ)
  fin_cases k
  · have hr : r.val ≤ i.val := by
      have := r.isLt
      simpa [coordinateBlock, CuspidalSupport.LeviAdmissibility.twoBlock] using
        Nat.le_of_lt_succ this
    change (if ((coordinateBlock n i).index ⟨0, by simp [coordinateBlock,
      CuspidalSupport.LeviAdmissibility.twoBlock]⟩ r).val ≤ i.val then b else 1) = b
    rw [CuspidalSupport.LeviAdmissibility.index_val]
    simp [hr]
  · have hr : ¬ i.val + 1 + r.val ≤ i.val := by omega
    change (if ((coordinateBlock n i).index ⟨1, by simp [coordinateBlock,
      CuspidalSupport.LeviAdmissibility.twoBlock]⟩ r).val ≤ i.val then b else 1) = 1
    rw [CuspidalSupport.LeviAdmissibility.index_val]
    simp [coordinateBlock, CuspidalSupport.LeviAdmissibility.twoBlock, hr]

variable (B : GeneralLinear.BlockShape (n + 1)) (i : Fin n)
    (hkernel : ∀ v : V, B.jacquetMk ρ v = 0 →
      Langlands.AllField.Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
        (fun x => ℓ (ρ (torus (rootLift x)) v)))

/-- The actual Jacquet quotient maps to coordinate germs once its kernel vanishes. -/
def jacquetToRootGerm :
    B.JacquetModule ρ →ₗ[ℂ]
      Langlands.AllField.Whittaker.JPSFunctionSpace.CoordinateGerm (rootCoefficientSpace F T n V ρ ℓ) T i :=
  (B.jacquetMk ρ).ker.liftQ (rootGermMap F T n V ρ ℓ i).toLinearMap
    (fun v hv => (rootGermMap_eq_zero_iff F T n V ρ ℓ i v).mpr (hkernel v hv))
    ∘ₗ ((B.jacquetMk ρ).quotKerEquivOfSurjective
      (B.jacquetMk_surjective ρ)).symm.toLinearMap

@[simp]
theorem jacquetToRootGerm_mk (v : V) :
    jacquetToRootGerm F T n V ρ ℓ B i hkernel (B.jacquetMk ρ v) =
      rootGermMap F T n V ρ ℓ i v := by
  simp only [jacquetToRootGerm, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem jacquetToRootGerm_surjective :
    Function.Surjective (jacquetToRootGerm F T n V ρ ℓ B i hkernel) := by
  intro q
  obtain ⟨v, rfl⟩ := rootGermMap_surjective F T n V ρ ℓ i q
  exact ⟨B.jacquetMk ρ v, jacquetToRootGerm_mk F T n V ρ ℓ B i hkernel v⟩

end Germs

section CoordinateAction

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V) (i : Fin n)

/-- The unnormalized actual two-block Jacquet action restricted to `(b,1)`. -/
def coordinateJacquetRepresentation :
    Representation ℂ Fˣ ((coordinateBlock n i).JacquetModule ρ) :=
  (Parabolic.leviCoinvariants (coordinateBlock n i)
    (ρ.comp ((coordinateBlock n i).parabolic F).subtype)).comp
      (((coordinateBlock n i).blockScalarLevi F).comp
        (coordinateBlockScalars F n i))

@[simp]
theorem coordinateJacquetRepresentation_mk (b : Fˣ) (v : V) :
    coordinateJacquetRepresentation F n V ρ i b
        ((coordinateBlock n i).jacquetMk ρ v) =
      (coordinateBlock n i).jacquetMk ρ
        (ρ ((coordinateBlock n i).blockScalar F
          (coordinateBlockScalars F n i b)) v) := rfl

variable (hkernel : ∀ v : V, (coordinateBlock n i).jacquetMk ρ v = 0 →
  Langlands.AllField.Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
    (fun x => ℓ (ρ (torus (rootLift x)) v)))

/-- The actual Jacquet-to-germ quotient map is equivariant for coordinate dilation. -/
def coordinateJacquetToRootGerm :
    Representation.IntertwiningMap (coordinateJacquetRepresentation F n V ρ i)
      (Langlands.AllField.Whittaker.JPSFunctionSpace.sigma (rootCoefficientSpace F T n V ρ ℓ) T i) where
  toLinearMap := jacquetToRootGerm F T n V ρ ℓ (coordinateBlock n i) i hkernel
  isIntertwining' b := by
    apply LinearMap.ext
    intro q
    obtain ⟨v, rfl⟩ := (coordinateBlock n i).jacquetMk_surjective ρ q
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      coordinateJacquetRepresentation_mk,
      jacquetToRootGerm_mk, jacquetToRootGerm_mk,
      ← torus_rootLift_coordinateEmbedding F T n i b]
    exact rootGermMap_coordinate F T n V ρ ℓ i b v

theorem coordinateJacquetToRootGerm_surjective :
    Function.Surjective (coordinateJacquetToRootGerm F T n V ρ ℓ i hkernel) :=
  jacquetToRootGerm_surjective F T n V ρ ℓ (coordinateBlock n i) i hkernel

include hkernel in
/-- All-block-scalar finite span descends to the actual coordinate-germ action,
provided the actual Jacquet kernel has the stated vanishing property. -/
theorem rootCoefficientSpace_finiteCoordinateOperatorSpan
    (hspan : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun a =>
      (Parabolic.leviCoinvariants (coordinateBlock n i)
        (ρ.comp ((coordinateBlock n i).parabolic F).subtype))
          ((coordinateBlock n i).blockScalarLevi F a)))) :
    Langlands.AllField.Whittaker.JPSFunctionSpace.HasFiniteCoordinateOperatorSpan
      (rootCoefficientSpace F T n V ρ ℓ) T i := by
  apply operatorSpan_finite_of_surjective
    (coordinateJacquetToRootGerm F T n V ρ ℓ i hkernel)
    (coordinateJacquetToRootGerm_surjective F T n V ρ ℓ i hkernel)
  exact operatorSpan_finite_comp
    ((Parabolic.leviCoinvariants (coordinateBlock n i)
      (ρ.comp ((coordinateBlock n i).parabolic F).subtype)).comp
        ((coordinateBlock n i).blockScalarLevi F))
    (coordinateBlockScalars F n i) hspan

end CoordinateAction

section StatementBridges

open scoped BigOperators

variable (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F) V)
    (ℓ : Module.Dual ℂ V)

/-- The source's separate local-constancy predicate holds for the actual
root coefficient image, without a topology on the original carrier. -/
theorem rootCoefficientSpace_isLocallyConstantSpace :
    letI := T.topology
    IsSmooth ρ →
      Langlands.AllField.Whittaker.JPSFunctionSpace.IsLocallyConstantSpace
        (rootCoefficientSpace F T n V ρ ℓ) T :=
  rootCoefficientSpace_locallyConstant F T n V ρ ℓ

/-- The raw upper-support adapter implies the published coordinatewise support
predicate, with the same bound uniform in every other coordinate. -/
theorem rootCoefficientSpace_hasCoordinateUpperSupport_of_statement
    (hsupport : Langlands.AllField.Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (ψ : AddChar F ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Langlands.AllField.Whittaker.JPSFunctionSpace.HasCoordinateUpperSupport
        (rootCoefficientSpace F T n V ρ ℓ) T := by
  let := T.topology
  intro ψ hc hne hu hρ hℓ f i
  obtain ⟨R, hR, hbound⟩ :=
    rootCoefficientSpace_upper_support F T n hsupport V ρ ψ hc hne hu hρ ℓ hℓ f
  exact ⟨R, hR, fun x hx => hbound x i hx⟩

/-- Published simple-root support gives the JPS upper-support hypothesis for
the actual root coefficient image of every smooth Whittaker functional. -/
theorem rootCoefficientSpace_hasCoordinateUpperSupport :
    letI := T.topology
    ∀ (ψ : AddChar F ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Langlands.AllField.Whittaker.JPSFunctionSpace.HasCoordinateUpperSupport
        (rootCoefficientSpace F T n V ρ ℓ) T :=
  rootCoefficientSpace_hasCoordinateUpperSupport_of_statement F T n V ρ ℓ
    (Langlands.AllField.Whittaker.smoothSimpleRootSupport F T n)

/-- The published full-diagonal kernel theorem supplies exactly the actual
root-coordinate vanishing premise used by the Jacquet-to-germ map. -/
theorem rootCoefficient_kernel :
    letI := T.topology
    ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      ∀ (i : Fin n) (v : V), (coordinateBlock n i).jacquetMk ρ v = 0 →
        Langlands.AllField.Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
          (fun x => ℓ (ρ (torus (rootLift x)) v)) := by
  let := T.topology
  intro ψ hc hu hρ hℓ i v hv
  obtain ⟨ε, hε, hvanish⟩ :=
    Langlands.AllField.Whittaker.coordinateJacquetKernelStatement F T n V ρ
      ψ hc hu hρ ℓ hℓ i v hv
  refine ⟨ε, hε, ?_⟩
  intro x hx
  apply hvanish (rootLift x)
  change T.normalizedAbs (rootHom (rootLift x) i : F) < ε
  simpa only [rootHom_rootLift F T n] using hx

/-- The published kernel and all-block-scalar span proofs imply all
finite coordinate operator spans for the actual root coefficient image. -/
theorem rootCoefficientSpace_finiteOperatorSpans :
    letI := T.topology
    ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F)) ρ.asModule →
      (∀ g : GeneralLinear (n + 1) F,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Langlands.AllField.Whittaker.JPSFunctionSpace.HasFiniteOperatorSpans
        (rootCoefficientSpace F T n V ρ ℓ) T := by
  let := T.topology
  intro ψ hc hu hρ hfinite hℓ i
  apply rootCoefficientSpace_finiteCoordinateOperatorSpan F T n V ρ ℓ i
    (rootCoefficient_kernel F T n V ρ ℓ ψ hc hu hρ.1 hℓ i)
  exact Langlands.AllField.Parabolic.jacquetCenterSpan F T (n + 1) (coordinateBlock n i) V ρ hρ hfinite

end StatementBridges

end Langlands.AllField.WhittakerLastEntryOne
