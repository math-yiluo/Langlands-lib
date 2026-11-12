import Langlands.Representation.Exponents.UniformCompressionStabilizationStatement
import Langlands.Representation.Exponents.LeviJacquetOppositePairingStatement
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Compact.Definitions

/-! # Renard VI.9.1: the remarks after the Proposition, and the bound `b ≤ c(G, K)`

Statements only. Renard 2026, VI.9.1 (printed pp.196–198 / PDF pp.202–204). For a compact
open subgroup `K` with an Iwahori decomposition relative to `P = MN` and a contracting
element `t`, the Proposition of VI.9.1 (published `UniformCompressionStabilizationStatement`)
splits `V^K = V^K_0 ⊕ V^K_*` with `V^K_0 = ker A^b` and `V^K_* = Im A^b`, where `A` is the
action of `a_{t,K} = e_K ∗ δ_t ∗ e_K` on `V^K`.

* `GeneralizedJacquetRemarksStatement`, in the dynamic setting of the published VI.9.1
  statements: the exponent `b` can be taken to be any bound `c` for `dim V^K` over the
  irreducible representations (the constant `c(G, K)` of VI.2.3); Remark 1 (the
  decomposition does not depend on the contracting element); Remark 2 (there are compact
  open subgroups `C` of `N` and `C̄` of `N̄` with `V^K_0 = V^K ∩ ker e_C` and
  `V^K_* = e_K ∗ e_{C̄} · V` for every smooth `V`).
* `GeneralizedJacquetContractingRangeStatement`, for an actual rational parabolic with a
  root presentation of its split component `A`: Remark 3 (there is `ε > 0` such that
  `V^K_0 = ker π(a_{t,K})` and `V^K_* = Im π(a_{t,K})` on `V^K` for every `t ∈ A^+(ε)`).
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- Renard VI.9.1, the bound on `b` in the Proposition and Remarks 1–2. For the dynamic
parabolic of a cocharacter `χ`, with `N`, `M` and `N̄` the dynamic radical, the centralizer
and the opposite radical, every compact open `K` and every `M`-central `g` satisfying the
Iwahori contraction conditions, write `A` for the compressed action `v ↦ e_K(π(g) v)` on
`V^K`, `V^K_0` for its kernel supremum and `V^K_*` for its stable image. Then:

* (bound) for every `c` bounding `dim V^K` over the irreducible smooth representations,
  every power of `A` of exponent at least `c` has kernel `V^K_0` and range `V^K_*`, for
  every smooth representation;
* (Remark 1) every other `M`-central `g'` satisfying the same conditions gives the same
  `V^K_0` and `V^K_*`;
* (Remark 2) there are compact open subgroups `C` of `N` and `C̄` of `N̄` such that, for
  every smooth representation, `V^K_0` is the kernel of the average `e_C` on `V^K` and
  `V^K_*` is the image of `e_K ∘ e_{C̄}`. -/
def GeneralizedJacquetRemarksStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
      (g : rationalPoints G),
      let N := (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))
      let M := (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _))
      let Nbar := (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))
      (∀ m ∈ M, m * g = g * m) →
      Jacquet.IsIwahoriContraction K N M Nbar g →
      -- the bound `b ≤ c(G, K)`
      (∀ c : ℕ,
        (∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints G), A.IsIrreducible →
          Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c) →
        ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
          ∀ s : ℕ, c ≤ s →
            Jacquet.stableImage ρ hρ K hK g =
                LinearMap.range (Jacquet.compressedAction ρ hρ K hK g ^ s) ∧
              Jacquet.powerKernelSup ρ hρ K hK g =
                LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g ^ s)) ∧
      -- Remark 1
      (∀ g' : rationalPoints G, (∀ m ∈ M, m * g' = g' * m) →
        Jacquet.IsIwahoriContraction K N M Nbar g' →
        ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
          Jacquet.powerKernelSup ρ hρ K hK g' = Jacquet.powerKernelSup ρ hρ K hK g ∧
            Jacquet.stableImage ρ hρ K hK g' = Jacquet.stableImage ρ hρ K hK g) ∧
      -- Remark 2
      ∃ (C : OpenSubgroup N) (hC : IsCompact (C : Set N))
        (Cbar : OpenSubgroup Nbar) (hCbar : IsCompact (Cbar : Set Nbar)),
        ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
          (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
          let eC : V →ₗ[ℂ] V := Compact.averageMap (ρ.comp N.subtype)
            (isSmooth_comp N.subtype continuous_subtype_val hρ) C hC
          let eCbar : V →ₗ[ℂ] V := Compact.averageMap (ρ.comp Nbar.subtype)
            (isSmooth_comp Nbar.subtype continuous_subtype_val hρ) Cbar hCbar
          Jacquet.powerKernelSup ρ hρ K hK g =
              LinearMap.ker (eC.comp (fixedVectors ρ K.toSubgroup).subtype) ∧
            (Jacquet.stableImage ρ hρ K hK g).map (fixedVectors ρ K.toSubgroup).subtype =
              LinearMap.range ((Compact.averageMap ρ hρ K hK).comp eCbar)

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.1, Remark 3. For actual rational parabolics `P = MN` and `P̄ = M N̄` with
the same Levi and `P(F) ∩ P̄(F) = M(F)`, every compact open `K` and every `M`-central `t₀`
satisfying the Iwahori contraction conditions for `(N, M, N̄)`, and every split component
`a : A → M` with a compatible root presentation of `P` and restricted simple roots
`Δ(P)`, there is `ε > 0` such that for every `t ∈ A^+(ε) = {t ∈ A(F) | |α(t)|_F < ε for
α ∈ Δ(P)}` and every smooth representation, the kernel and the range of the compressed
action `v ↦ e_K(π(t) v)` on `V^K` are the kernel supremum `V^K_0` and the stable image
`V^K_*` of the compressed action of `t₀`. -/
def GeneralizedJacquetContractingRangeStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
      (_hp : IsParabolicSubgroup p) (_hm : IsRationalLeviSubgroup m)
      (_hn : LeviSubgroup.IsGeometricUnipotentRadical n)
      (_hmul : IsIso (subgroupMultiplication m n))
      (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
      (_hpbar : IsParabolicSubgroup pbar) (_hmbar : IsRationalLeviSubgroup mbar)
      (_hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
      (_hmulbar : IsIso (subgroupMultiplication mbar nbar)),
      mbar ≫ pbar = m ≫ p →
      pointImage p ⊓ pointImage pbar = pointImage (m ≫ p) →
      ∀ (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
        (t₀ : rationalPoints G),
        (∀ x ∈ pointImage (m ≫ p), x * t₀ = t₀ * x) →
        Jacquet.IsIwahoriContraction K (pointImage (n ≫ p)) (pointImage (m ≫ p))
          (pointImage (nbar ≫ pbar)) t₀ →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M)
          (pres : ParabolicRootPresentation p m a),
          let Δ : Set (characterLattice A) :=
            (fun α => pres.data.f ≫ α) ''
              (simpleRelativeRoots pres.data.i pres.data.ν \ pres.data.J)
          let incG : rationalPoints A.toGrp →* rationalPoints G :=
            rationalPoints.map (a ≫ m ≫ p)
          ∃ ε : ℝ, 0 < ε ∧
            ∀ t : rationalPoints A.toGrp,
              (∀ α ∈ Δ, CocharacterUniformizer.characterNorm k A α t < ε) →
              ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
                (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
                Jacquet.powerKernelSup ρ hρ K hK t₀ =
                    LinearMap.ker (Jacquet.compressedAction ρ hρ K hK (incG t)) ∧
                  Jacquet.stableImage ρ hρ K hK t₀ =
                    LinearMap.range (Jacquet.compressedAction ρ hρ K hK (incG t))

end Langlands.Aubert.General.RepresentedParabolic
