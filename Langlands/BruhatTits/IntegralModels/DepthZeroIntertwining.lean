import Langlands.BruhatTits.IntegralModels.DepthZeroCompactOpen
import Langlands.Representation.Induction.OpenIntertwiningKernelProof
import Langlands.Representation.Induction.OpenIntertwiningDoubleCosetProof
import Langlands.Representation.Induction.OpenIntertwiningFiniteTypeProof

/-! # Intertwining kernels of depth-zero compact inductions for supplied KP models

Maps between the depth-zero compact inductions `c-Ind_{G^0(R)}^{G(K)} infl σ` of
`DepthZeroInduction` are described by intertwining kernels on `G(K)`, and, for compact
`G^0(R)`, by their values at double-coset representatives of
`G^0(R) \ G(K) / G^0(R)`. For finite-dimensional `σ` the kernels are supported on finitely
many double cosets. Over a nonarchimedean local field the topological premises are proved.
The general results used are the published proofs `compactInductionKernel`,
`compactInductionDoubleCoset` and `compactInductionFiniteTypeKernel`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u uk

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme Induction

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

section Topology

variable [IsLocalRing R] [TopologicalSpace (rationalPoints G)]
  [IsTopologicalGroup (rationalPoints G)]

namespace SpecialFibreQuotientData

variable {D : RelativeComponentModelData R K G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k]
  {V : Type u} [AddCommGroup V] [Module k V] {W : Type u} [AddCommGroup W] [Module k W]

/-- Maps `c-Ind infl σ ⟶ c-Ind infl τ` between depth-zero compact inductions correspond to
intertwining kernels `Φ : G(K) → Hom_k(V, W)` for the inflations, through
`Φ g v = T (i_v) g`. -/
def depthZeroInductionKernelEquiv
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W) :
    (Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ) ≃
      {Φ : rationalPoints G → V →ₗ[k] W //
        IsIntertwiningKernel D.neutral.integralPoints (Q.inflation σ) (Q.inflation τ) Φ} :=
  let h := compactInductionKernel.{uk, u, u} k (rationalPoints G) D.neutral.integralPoints hH
    (Q.inflationSmoothRep hC σ) (Q.inflationSmoothRep hC τ)
  { toFun := fun T => ⟨(h.1 T).choose, (h.1 T).choose_spec.1⟩
    invFun := fun Φ => (h.2 Φ.1 Φ.2).exists.choose
    left_inv := fun T =>
      (h.2 _ (h.1 T).choose_spec.1).unique
        ((h.2 _ (h.1 T).choose_spec.1).exists.choose_spec) (h.1 T).choose_spec.2
    right_inv := fun Φ => by
      apply Subtype.ext
      funext g
      apply LinearMap.ext
      intro v
      exact ((h.1 _).choose_spec.2 g v).trans ((h.2 Φ.1 Φ.2).exists.choose_spec g v).symm }

/-- The kernel of a map `T` is evaluation of `T` on the unit functions `i_v`. -/
theorem depthZeroInductionKernelEquiv_apply
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (T : Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ)
    (g : rationalPoints G) (v : V) :
    (Q.depthZeroInductionKernelEquiv hH hC σ τ T).1 g v =
      eval D.neutral.integralPoints (Q.inflation τ)
        (SmoothRep.hom T (unitFunction D.neutral.integralPoints hH (Q.inflation σ)
          (Q.isSmooth_inflation hC σ) v)).1 g :=
  ((compactInductionKernel.{uk, u, u} k (rationalPoints G) D.neutral.integralPoints hH
    (Q.inflationSmoothRep hC σ) (Q.inflationSmoothRep hC τ)).1 T).choose_spec.2 g v

/-- For compact open `G^0(R)`, intertwining kernels of inflations correspond to local
intertwiner families on the double cosets `G^0(R) \ G(K) / G^0(R)`, by restriction to a
choice `s` of representatives. -/
def depthZeroKernelDoubleCosetEquiv
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hK : IsCompact (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (s : DoubleCoset.Quotient (D.neutral.integralPoints : Set (rationalPoints G))
      (D.neutral.integralPoints : Set (rationalPoints G)) → rationalPoints G)
    (hs : ∀ q, DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints (s q) = q) :
    {Φ : rationalPoints G → V →ₗ[k] W //
        IsIntertwiningKernel D.neutral.integralPoints (Q.inflation σ) (Q.inflation τ) Φ} ≃
      {φ // IsLocalIntertwinerFamily D.neutral.integralPoints (Q.inflation σ)
        (Q.inflation τ) s φ} :=
  let h := compactInductionDoubleCoset.{uk, u, u, u} k (rationalPoints G)
    D.neutral.integralPoints hH hK (Q.inflation σ) (Q.inflation τ)
    (Q.isSmooth_inflation hC σ) s hs
  { toFun := fun Φ => ⟨fun q => Φ.1 (s q), h.1 Φ.1 Φ.2⟩
    invFun := fun φ => ⟨(h.2 φ.1 φ.2).exists.choose, (h.2 φ.1 φ.2).exists.choose_spec.1⟩
    left_inv := fun Φ =>
      Subtype.ext <| (h.2 _ (h.1 Φ.1 Φ.2)).unique
        (h.2 _ (h.1 Φ.1 Φ.2)).exists.choose_spec ⟨Φ.2, fun _ => rfl⟩
    right_inv := fun φ => Subtype.ext <| funext (h.2 φ.1 φ.2).exists.choose_spec.2 }

/-- The double-coset form of maps between depth-zero compact inductions: for compact open
`G^0(R)` and representatives `s`, maps `c-Ind infl σ ⟶ c-Ind infl τ` correspond to local
intertwiner families `φ`, with `φ q v = T (i_v) (s q)`. -/
def depthZeroInductionDoubleCosetEquiv
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hK : IsCompact (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (s : DoubleCoset.Quotient (D.neutral.integralPoints : Set (rationalPoints G))
      (D.neutral.integralPoints : Set (rationalPoints G)) → rationalPoints G)
    (hs : ∀ q, DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints (s q) = q) :
    (Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ) ≃
      {φ // IsLocalIntertwinerFamily D.neutral.integralPoints (Q.inflation σ)
        (Q.inflation τ) s φ} :=
  (Q.depthZeroInductionKernelEquiv hH hC σ τ).trans
    (Q.depthZeroKernelDoubleCosetEquiv hH hK hC σ τ s hs)

/-- The value of the double-coset family of `T` at `q` is `v ↦ T (i_v) (s q)`. -/
theorem depthZeroInductionDoubleCosetEquiv_apply
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hK : IsCompact (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (s : DoubleCoset.Quotient (D.neutral.integralPoints : Set (rationalPoints G))
      (D.neutral.integralPoints : Set (rationalPoints G)) → rationalPoints G)
    (hs : ∀ q, DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints (s q) = q)
    (T : Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ) (q) (v : V) :
    (Q.depthZeroInductionDoubleCosetEquiv hH hK hC σ τ s hs T).1 q v =
      eval D.neutral.integralPoints (Q.inflation τ)
        (SmoothRep.hom T (unitFunction D.neutral.integralPoints hH (Q.inflation σ)
          (Q.isSmooth_inflation hC σ) v)).1 (s q) :=
  Q.depthZeroInductionKernelEquiv_apply hH hC σ τ T (s q) v

omit [TopologicalSpace (rationalPoints G)] [IsTopologicalGroup (rationalPoints G)] in
/-- An inflation of a finite-dimensional representation is finitely generated over the
group algebra of `G^0(R)`. -/
theorem inflation_asModule_finite [Module.Finite k V]
    (σ : Representation k (rationalPoints Q.quotient) V) :
    Module.Finite (MonoidAlgebra k D.neutral.integralPoints) (Q.inflation σ).asModule :=
  Module.Finite.of_restrictScalars_finite k _ _

/-- For compact open `G^0(R)` and finite-dimensional `σ`, the kernel of every map
`c-Ind infl σ ⟶ c-Ind infl τ` is supported on finitely many double cosets
`G^0(R) g G^0(R)`. -/
theorem depthZeroInductionKernel_finite_doubleCosetSupport
    (hH : IsOpen (D.neutral.integralPoints : Set (rationalPoints G)))
    (hK : IsCompact (D.neutral.integralPoints : Set (rationalPoints G)))
    (hC : IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)))
    [Module.Finite k V]
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (T : Q.depthZeroInduction hC σ ⟶ Q.depthZeroInduction hC τ) :
    (DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints ''
      Function.support (Q.depthZeroInductionKernelEquiv hH hC σ τ T).1).Finite :=
  ((compactInductionFiniteTypeKernel.{uk, u, u, u} k (rationalPoints G)
    D.neutral.integralPoints hH hK (Q.inflation σ) (Q.inflation τ)
    (Q.inflation_asModule_finite σ) _).1
      (Q.depthZeroInductionKernelEquiv hH hC σ τ T).2).2

end SpecialFibreQuotientData

end Topology

section LocalField

open Langlands.AlgebraicGeometry.PointTopology
open scoped ValuativeRel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

namespace RelativeComponentModelData

/-- The level-one congruence subgroup of `G^0` is open in `G(F)` with its canonical
topology. -/
theorem localField_isOpen_congruenceSubgroup (D : RelativeComponentModelData 𝒪[F] F G) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsOpen (D.neutral.congruenceSubgroup : Set (rationalPoints G)) :=
  isOpen_congruenceSubgroup_of_congruenceBasis
    LocalFieldIntegralModel.congruenceNeighborhoodBasis_proof D

end RelativeComponentModelData

namespace SpecialFibreQuotientData

variable [LocallyOfFiniteType G.X.hom]
  {D : RelativeComponentModelData 𝒪[F] F G} (Q : SpecialFibreQuotientData D)
variable {k : Type uk} [CommRing k]
  {V : Type u} [AddCommGroup V] [Module k V] {W : Type u} [AddCommGroup W] [Module k W]

/-- Over a nonarchimedean local field, maps between depth-zero compact inductions
correspond to local intertwiner families on `G^0(𝒪) \ G(F) / G^0(𝒪)`. -/
def localFieldDepthZeroInductionDoubleCosetEquiv
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W)
    (s : DoubleCoset.Quotient (D.neutral.integralPoints : Set (rationalPoints G))
      (D.neutral.integralPoints : Set (rationalPoints G)) → rationalPoints G)
    (hs : ∀ q, DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints (s q) = q) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    (Q.depthZeroInduction D.localField_isOpen_congruenceSubgroup σ ⟶
        Q.depthZeroInduction D.localField_isOpen_congruenceSubgroup τ) ≃
      {φ // IsLocalIntertwinerFamily D.neutral.integralPoints (Q.inflation σ)
        (Q.inflation τ) s φ} :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  Q.depthZeroInductionDoubleCosetEquiv D.neutral.isOpen_integralPoints_localField
    D.neutral.isCompact_integralPoints_localField D.localField_isOpen_congruenceSubgroup
    σ τ s hs

/-- Over a nonarchimedean local field, for finite-dimensional `σ`, the kernel of every map
between depth-zero compact inductions is supported on finitely many double cosets. -/
theorem localField_depthZeroInductionKernel_finite_doubleCosetSupport
    [Module.Finite k V]
    (σ : Representation k (rationalPoints Q.quotient) V)
    (τ : Representation k (rationalPoints Q.quotient) W) :
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
    ∀ T : Q.depthZeroInduction D.localField_isOpen_congruenceSubgroup σ ⟶
        Q.depthZeroInduction D.localField_isOpen_congruenceSubgroup τ,
      (DoubleCoset.mk D.neutral.integralPoints D.neutral.integralPoints ''
        Function.support (Q.depthZeroInductionKernelEquiv
          D.neutral.isOpen_integralPoints_localField
          D.localField_isOpen_congruenceSubgroup σ τ T).1).Finite :=
  letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  letI : IsTopologicalGroup (rationalPoints G) := rationalPoint_isTopologicalGroup F G
  fun T => Q.depthZeroInductionKernel_finite_doubleCosetSupport
    D.neutral.isOpen_integralPoints_localField D.neutral.isCompact_integralPoints_localField
    D.localField_isOpen_congruenceSubgroup σ τ T

end SpecialFibreQuotientData

end LocalField

end Langlands.BruhatTits.IntegralModels
