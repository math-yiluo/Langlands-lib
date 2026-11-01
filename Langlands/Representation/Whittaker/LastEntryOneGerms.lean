import Langlands.Representation.Whittaker.LastEntryOneAdapters
import Langlands.Representation.Whittaker.JPSFunctionSpace
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Parabolic.LeviBridges
import Langlands.Representation.CuspidalSupport.LeviSplitContraction
import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Representation.Whittaker.CoordinateJacquetKernelProof
import Langlands.Representation.Parabolic.JacquetCenterSpanProof
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof

/-!
# Root coefficient maps into the actual coordinate germs

The general Jacquet factorization below has an explicit kernel-vanishing
premise. The final Whittaker specialization discharges it using the published
kernel theorem and obtains finite operator spans from the published
Jacquet-center theorem.
-/

noncomputable section

namespace Langlands.WhittakerLastEntryOne

universe uF uV uW uG

section OperatorSpan

variable {G : Type uG} [Monoid G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- A surjective equivariant image inherits finite-dimensional operator span. -/
theorem operatorSpan_finite_of_surjective
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f)
    (hρ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range σ)) := by
  let post : Module.End ℂ V →ₗ[ℂ] (V →ₗ[ℂ] W) :=
    { toFun := fun a => f.toLinearMap.comp a
      map_add' := by
        intro a b
        ext v
        exact map_add f.toLinearMap (a v) (b v)
      map_smul' := by
        intro c a
        ext v
        exact map_smul f.toLinearMap c (a v) }
  let pre : Module.End ℂ W →ₗ[ℂ] (V →ₗ[ℂ] W) :=
    { toFun := fun a => a.comp f.toLinearMap
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let A := (Submodule.span ℂ (Set.range ρ)).map post
  have hmem : Submodule.span ℂ (Set.range σ) ≤ A.comap pre := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    change pre (σ g) ∈ A
    refine ⟨ρ g, Submodule.subset_span ⟨g, rfl⟩, ?_⟩
    ext v
    exact congrArg (fun a : V →ₗ[ℂ] W => a v) (f.isIntertwining' g)
  let emb : (Submodule.span ℂ (Set.range σ)) →ₗ[ℂ] A :=
    { toFun := fun a => ⟨pre a.val, hmem a.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective emb := by
    intro a b hab
    apply Subtype.ext
    ext w
    obtain ⟨v, rfl⟩ := hf w
    exact congrArg (fun q : A => q.val v) hab
  let := hρ
  exact FiniteDimensional.of_injective emb hinj

/-- Restricting an action can only decrease its operator span. -/
theorem operatorSpan_finite_comp {H : Type*} [Monoid H]
    (ρ : Representation ℂ G V) (f : H →* G)
    (hρ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range ρ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (ρ.comp f))) := by
  let := hρ
  have hle : Submodule.span ℂ (Set.range (ρ.comp f)) ≤
      Submodule.span ℂ (Set.range ρ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, rfl⟩
    exact Submodule.subset_span ⟨f h, rfl⟩
  exact FiniteDimensional.of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)

end OperatorSpan

section Germs

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
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
      (Whittaker.JPSFunctionSpace.germRepresentation (rootCoefficientSpace F T n V ρ ℓ) T i) :=
  (Whittaker.JPSFunctionSpace.germMap (rootCoefficientSpace F T n V ρ ℓ) T i).comp
    (rootCoefficientToSpace F T n V ρ ℓ)

theorem rootGermMap_surjective (i : Fin n) :
    Function.Surjective (rootGermMap F T n V ρ ℓ i) :=
  (Whittaker.JPSFunctionSpace.germMap_surjective _ T i).comp (rootCoefficientToSpace_surjective F T n V ρ ℓ)

theorem rootGermMap_eq_zero_iff (i : Fin n) (v : V) :
    rootGermMap F T n V ρ ℓ i v = 0 ↔
      Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
        (fun x => ℓ (ρ (torus (rootLift x)) v)) :=
  Whittaker.JPSFunctionSpace.germMap_eq_zero_iff _ T i _

/-- Pulling back along the coordinate embedding gives the literal dilation action. -/
theorem rootGermMap_coordinate (i : Fin n) (b : F.Carrierˣ) (v : V) :
    rootGermMap F T n V ρ ℓ i
        (ρ (torus (rootLift (Whittaker.JPSFunctionSpace.coordinateEmbedding i b))) v) =
      Whittaker.JPSFunctionSpace.sigma (rootCoefficientSpace F T n V ρ ℓ) T i b
        (rootGermMap F T n V ρ ℓ i v) :=
  Representation.IntertwiningMap.isIntertwining _ _
    (rootGermMap F T n V ρ ℓ i) (Whittaker.JPSFunctionSpace.coordinateEmbedding i b) v

include T in
/-- A single root-coordinate dilation scales exactly the initial diagonal block. -/
theorem rootLift_coordinateEmbedding (i : Fin n) (b : F.Carrierˣ) :
    rootLift (Whittaker.JPSFunctionSpace.coordinateEmbedding i b) =
      fun j => if j.val ≤ i.val then b else 1 := by
  classical
  let a : Fin (n + 1) → F.Carrierˣ := fun j => if j.val ≤ i.val then b else 1
  have ha : a (Fin.last n) = 1 := by
    simp [a, show ¬ n ≤ i.val by omega]
  have hroot : rootHom a = Whittaker.JPSFunctionSpace.coordinateEmbedding i b := by
    funext j
    rcases lt_trichotomy j.val i.val with h | h | h
    · have hne : j ≠ i := by intro hij; subst i; omega
      simp [rootHom, a, Whittaker.JPSFunctionSpace.coordinateEmbedding, hne,
        show j.val ≤ i.val by omega, show j.val + 1 ≤ i.val by omega]
    · have hij : j = i := Fin.ext h
      subst j
      simp [rootHom, a, Whittaker.JPSFunctionSpace.coordinateEmbedding]
    · have hne : j ≠ i := by intro hij; subst i; omega
      simp [rootHom, a, Whittaker.JPSFunctionSpace.coordinateEmbedding, hne,
        show ¬ j.val ≤ i.val by omega, show ¬ j.val + 1 ≤ i.val by omega]
  rw [← hroot]
  exact rootLift_rootHom F T n a ha

/-- The two-block parabolic associated with root coordinate `i`. -/
def coordinateBlock (i : Fin n) : GeneralLinear.BlockShape (n + 1) :=
  CuspidalSupport.LeviAdmissibility.twoBlock (n + 1) i.val (by omega)

/-- The scalar tuple `(b,1)` in that actual product Levi. -/
def coordinateBlockScalars (i : Fin n) :
    F.Carrierˣ →* (Fin (coordinateBlock n i).length → F.Carrierˣ) where
  toFun b j := if j.val = 0 then b else 1
  map_one' := by ext j; simp
  map_mul' b c := by ext j; by_cases hj : j.val = 0 <;> simp [hj]

include T in
/-- The actual diagonal root lift equals the embedded two-block scalar. -/
theorem torus_rootLift_coordinateEmbedding (i : Fin n) (b : F.Carrierˣ) :
    torus (rootLift (Whittaker.JPSFunctionSpace.coordinateEmbedding i b)) =
      (coordinateBlock n i).blockScalar F.Carrier (coordinateBlockScalars F n i b) := by
  classical
  apply Units.ext
  change Matrix.diagonal (fun j => (rootLift
    (Whittaker.JPSFunctionSpace.coordinateEmbedding i b) j : F.Carrier)) = _
  rw [rootLift_coordinateEmbedding F T n i b,
    GeneralLinear.BlockShape.coe_blockScalar]
  congr 1
  funext j
  obtain ⟨⟨k, r⟩, rfl⟩ := (coordinateBlock n i).indexEquiv.surjective j
  rw [(coordinateBlock n i).indexEquiv.symm_apply_apply]
  apply congrArg (fun u : F.Carrierˣ => (u : F.Carrier))
  change ((if ((coordinateBlock n i).index k r).val ≤ i.val then b else 1) : F.Carrierˣ) =
    (coordinateBlockScalars F n i b k : F.Carrierˣ)
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
      Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
        (fun x => ℓ (ρ (torus (rootLift x)) v)))

/-- The actual Jacquet quotient maps to coordinate germs once its kernel vanishes. -/
def jacquetToRootGerm :
    B.JacquetModule ρ →ₗ[ℂ]
      Whittaker.JPSFunctionSpace.CoordinateGerm (rootCoefficientSpace F T n V ρ ℓ) T i :=
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

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V) (i : Fin n)

/-- The unnormalized actual two-block Jacquet action restricted to `(b,1)`. -/
def coordinateJacquetRepresentation :
    Representation ℂ F.Carrierˣ ((coordinateBlock n i).JacquetModule ρ) :=
  (Parabolic.leviCoinvariants (coordinateBlock n i)
    (ρ.comp ((coordinateBlock n i).parabolic F.Carrier).subtype)).comp
      (((coordinateBlock n i).blockScalarLevi F.Carrier).comp
        (coordinateBlockScalars F n i))

@[simp]
theorem coordinateJacquetRepresentation_mk (b : F.Carrierˣ) (v : V) :
    coordinateJacquetRepresentation F n V ρ i b
        ((coordinateBlock n i).jacquetMk ρ v) =
      (coordinateBlock n i).jacquetMk ρ
        (ρ ((coordinateBlock n i).blockScalar F.Carrier
          (coordinateBlockScalars F n i b)) v) := rfl

variable (hkernel : ∀ v : V, (coordinateBlock n i).jacquetMk ρ v = 0 →
  Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
    (fun x => ℓ (ρ (torus (rootLift x)) v)))

/-- The actual Jacquet-to-germ quotient map is equivariant for coordinate dilation. -/
def coordinateJacquetToRootGerm :
    Representation.IntertwiningMap (coordinateJacquetRepresentation F n V ρ i)
      (Whittaker.JPSFunctionSpace.sigma (rootCoefficientSpace F T n V ρ ℓ) T i) where
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
        (ρ.comp ((coordinateBlock n i).parabolic F.Carrier).subtype))
          ((coordinateBlock n i).blockScalarLevi F.Carrier a)))) :
    Whittaker.JPSFunctionSpace.HasFiniteCoordinateOperatorSpan
      (rootCoefficientSpace F T n V ρ ℓ) T i := by
  apply operatorSpan_finite_of_surjective
    (coordinateJacquetToRootGerm F T n V ρ ℓ i hkernel)
    (coordinateJacquetToRootGerm_surjective F T n V ρ ℓ i hkernel)
  exact operatorSpan_finite_comp
    ((Parabolic.leviCoinvariants (coordinateBlock n i)
      (ρ.comp ((coordinateBlock n i).parabolic F.Carrier).subtype)).comp
        ((coordinateBlock n i).blockScalarLevi F.Carrier))
    (coordinateBlockScalars F n i) hspan

end CoordinateAction

section StatementBridges

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ)
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (n + 1) F.Carrier) V)
    (ℓ : Module.Dual ℂ V)

/-- The actual root coefficient image satisfies the published smoothness
predicate whenever the original representation is smooth. -/
theorem rootCoefficientSpace_isSmoothSpace :
    letI := T.topology
    IsSmooth ρ →
      Whittaker.JPSFunctionSpace.IsSmoothSpace
        (rootCoefficientSpace F T n V ρ ℓ) T :=
  rootCoefficientSpace_smooth F T n V ρ ℓ

/-- The source's separate local-constancy predicate holds for the actual
root coefficient image, without a topology on the original carrier. -/
theorem rootCoefficientSpace_isLocallyConstantSpace :
    letI := T.topology
    IsSmooth ρ →
      Whittaker.JPSFunctionSpace.IsLocallyConstantSpace
        (rootCoefficientSpace F T n V ρ ℓ) T :=
  rootCoefficientSpace_locallyConstant F T n V ρ ℓ

/-- The raw upper-support adapter implies the published coordinatewise support
predicate, with the same bound uniform in every other coordinate. -/
theorem rootCoefficientSpace_hasCoordinateUpperSupport_of_statement
    (hsupport : Whittaker.SmoothSimpleRootSupportStatement.{uF,uV} F T n) :
    letI := T.topology
    ∀ (ψ : AddChar F.Carrier ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Whittaker.JPSFunctionSpace.HasCoordinateUpperSupport
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
    ∀ (ψ : AddChar F.Carrier ℂ), Continuous ψ → ψ ≠ 1 → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Whittaker.JPSFunctionSpace.HasCoordinateUpperSupport
        (rootCoefficientSpace F T n V ρ ℓ) T :=
  rootCoefficientSpace_hasCoordinateUpperSupport_of_statement F T n V ρ ℓ
    (Whittaker.smoothSimpleRootSupport F T n)

/-- The published full-diagonal kernel theorem supplies exactly the actual
root-coordinate vanishing premise used by the Jacquet-to-germ map. -/
theorem rootCoefficient_kernel :
    letI := T.topology
    ∀ (ψ : AddChar F.Carrier ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
      IsSmooth ρ →
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      ∀ (i : Fin n) (v : V), (coordinateBlock n i).jacquetMk ρ v = 0 →
        Whittaker.JPSFunctionSpace.VanishesNearCoordinateZero T i
          (fun x => ℓ (ρ (torus (rootLift x)) v)) := by
  let := T.topology
  intro ψ hc hu hρ hℓ i v hv
  obtain ⟨ε, hε, hvanish⟩ :=
    Whittaker.coordinateJacquetKernelStatement p inferInstance F T n V ρ
      ψ hc hu hρ ℓ hℓ i v hv
  refine ⟨ε, hε, ?_⟩
  intro x hx
  apply hvanish (rootLift x)
  change T.normalizedAbs (rootHom (rootLift x) i : F.Carrier) < ε
  simpa only [rootHom_rootLift F T n] using hx

/-- The published kernel and all-block-scalar span proofs imply all
finite coordinate operator spans for the actual root coefficient image. -/
theorem rootCoefficientSpace_finiteOperatorSpans :
    letI := T.topology
    ∀ (ψ : AddChar F.Carrier ℂ), Continuous ψ → (∀ x, ‖ψ x‖ = 1) →
      IsAdmissible ρ →
      Module.Finite (MonoidAlgebra ℂ (GeneralLinear (n + 1) F.Carrier)) ρ.asModule →
      (∀ g : GeneralLinear (n + 1) F.Carrier,
        ((∀ j k, k < j → g.val j k = 0) ∧ ∀ j, g.val j j = 1) →
        ∀ v, ℓ (ρ g v) = (∏ j : Fin n, ψ (g.val j.castSucc j.succ)) * ℓ v) →
      Whittaker.JPSFunctionSpace.HasFiniteOperatorSpans
        (rootCoefficientSpace F T n V ρ ℓ) T := by
  let := T.topology
  intro ψ hc hu hρ hfinite hℓ i
  apply rootCoefficientSpace_finiteCoordinateOperatorSpan F T n V ρ ℓ i
    (rootCoefficient_kernel F T n V ρ ℓ ψ hc hu hρ.1 hℓ i)
  exact Parabolic.jacquetCenterSpan p F T (n + 1) (coordinateBlock n i) V ρ hρ hfinite

end StatementBridges

end Langlands.WhittakerLastEntryOne
