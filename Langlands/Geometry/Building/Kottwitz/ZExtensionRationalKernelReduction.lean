import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelReduction
import Langlands.Geometry.Building.Kottwitz.CharacterKernelReduction
import Langlands.Geometry.Building.Kottwitz.TorusMapDescentProof
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.GroupScheme.Torus.InducedQuotientPointSurjectivityStatement

/-! # Reducing the rational kernel clause of KP Proposition 11.5.3 to named inputs -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

section KernelTransport

variable {H G A B : Type*} [Group H] [Group G] [Group A] [Group B]

/-- Kernel transport where lifts are only required for classes in the image of `κH`. -/
theorem map_kernel_eq_of_image_lift
    (p : H →* G) (κH : H →* A) (κG : G →* B) (q : A →* B)
    (hp : Function.Surjective p)
    (hsquare : ∀ h, κG (p h) = q (κH h))
    (hlift : ∀ h, q (κH h) = 1 → ∃ h' ∈ p.ker, κH h' = κH h) :
    κH.ker.map p = κG.ker := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    change κG (p h) = 1
    rw [hsquare, (show κH h = 1 from hh), map_one]
  · intro g hg
    obtain ⟨h, rfl⟩ := hp g
    have hq : q (κH h) = 1 := by
      rw [← hsquare]
      exact hg
    obtain ⟨h', hh', he⟩ := hlift h hq
    refine ⟨h * h'⁻¹, ?_, ?_⟩
    · change κH (h * h'⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    · rw [map_mul, map_inv, (show p h' = 1 from hh'), inv_one, mul_one]

/-- Composing with an injective homomorphism does not change the kernel. -/
theorem ker_comp_eq_of_injective (f : H →* A) (g : A →* B) (hg : Function.Injective g) :
    (g.comp f).ker = f.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff g hg

end KernelTransport

/-- Coefficient extension from `k` to `L` commutes with the point maps of a homomorphism. -/
theorem extend_affinePointsTarget {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G H : GroupScheme (Spec (CommRingCat.of k))} (f : G ⟶ H)
    (y : G.affinePoints (CommAlgCat.of k k)) :
    GaloisPoint.extend k L H (G.affinePointsTarget f (CommAlgCat.of k k) y) =
      G.affinePointsTarget f (CommAlgCat.of k L) (GaloisPoint.extend k L G y) :=
  DFunLike.congr_fun (affinePointsTarget_naturality G f (CommAlgCat.ofHom (Algebra.ofId k L))) y

/-- The rational square of KP Lemma 11.5.1 after forgetting invariance: restriction
(from Descent) and functoriality over `K`. -/
theorem rationalKottwitz_map_of_inputs
    (hfunct : ReductiveKottwitzFunctorialityStatement.{u})
    (hdesc : ReductiveKottwitzDescentStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (S T : GroupScheme (Spec (CommRingCat.of F))) (hS : IsConnectedReductive S)
    (hT : IsConnectedReductive T) (f : S ⟶ T) (x : rationalPoints S) :
    (reductiveInvariantInclusion F T hT
        (reductiveKottwitzRational F T hT (rationalPoints.map f x))).toAdd =
      fundamentalInertiaMap F (UnramifiedClosure F) (SeparableClosure F) T hT S hS f
        (reductiveInvariantInclusion F S hS (reductiveKottwitzRational F S hS x)).toAdd := by
  rw [(hdesc.2 F T hT).2.2, (hdesc.2 F S hS).2.2, rationalCoeffEquiv_map,
    extend_affinePointsTarget]
  exact (hfunct F F).1 S T hS hT f _


/-- KP Proposition 11.5.3, kernel clause on `F`-rational points, reduced to KP Lemma 11.5.1
(functoriality and descent), right exactness of inertia coinvariants for a central torus
quotient, and three further inputs written out in full: injectivity of
`π₁(Z)_I → π₁(H)_I` for z-extensions over local fields (proof of KP Proposition 11.5.3),
KP Corollary 11.1.9 (`torusKottwitzRational` is surjective for induced tori), and
surjectivity of `H(F) → G(F)`. -/
def ZExtensionRationalKernelReductionStatement : Prop :=
  ReductiveKottwitzFunctorialityStatement.{u} →
  ReductiveKottwitzDescentStatement.{u} →
  CentralTorusInertiaExactnessStatement.{u} →
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (z : ZExtension G),
      Function.Injective
        (fundamentalInertiaMap F (UnramifiedClosure F) (SeparableClosure F) z.H
          z.isZExtension.source_reductive z.Z.toGrp
          z.isZExtension.induced.isTorus.isConnectedReductive_of_fieldSplitting z.i)) →
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsInducedTorus T),
      Function.Surjective (torusKottwitzRational F T hT.isTorus)) →
  ZExtensionPointSurjectivityStatement.{u} →
  ZExtensionRationalKottwitzKernelStatement.{u}

/-- Proof of the rational reduction: `map_kernel_eq_of_image_lift` for `H(F) → G(F)` and
the maps `incl ∘ κ^rat` into the inertia coinvariants. A kernel class lifts to `π₁(Z)_I`
by exactness; the lift is residually invariant by injectivity and equivariance of
`π₁(i)`, so Corollary 11.1.9 lifts it to `Z(F)`. -/
theorem zExtensionRationalKernelReduction :
    ZExtensionRationalKernelReductionStatement.{u} := by
  intro hfunct hdesc hexact hinj hcor hpoint F _ _ _ _ G hG z
  have hH : IsConnectedReductive z.H := z.isZExtension.source_reductive
  have hZt : IsTorus z.Z.toGrp := z.isZExtension.induced.isTorus
  have hZ : IsConnectedReductive z.Z.toGrp := hZt.isConnectedReductive_of_fieldSplitting
  rw [← ker_comp_eq_of_injective (reductiveKottwitzRational F G hG)
      (reductiveInvariantInclusion F G hG) (reductiveInvariantInclusion_injective F G hG),
    ← ker_comp_eq_of_injective (reductiveKottwitzRational F z.H hH)
      (reductiveInvariantInclusion F z.H hH) (reductiveInvariantInclusion_injective F z.H hH)]
  refine map_kernel_eq_of_image_lift (rationalPoints.map z.p)
    ((reductiveInvariantInclusion F z.H hH).comp (reductiveKottwitzRational F z.H hH))
    ((reductiveInvariantInclusion F G hG).comp (reductiveKottwitzRational F G hG))
    (fundamentalInertiaMap F (UnramifiedClosure F) (SeparableClosure F)
      G hG z.H hH z.p).toAddMonoidHom.toMultiplicative ?_ ?_ ?_
  · -- surjectivity of `H(F) → G(F)`
    intro g
    obtain ⟨y, hy⟩ := hpoint F F G z (rationalCoeffEquiv F G g)
    refine ⟨(rationalCoeffEquiv F z.H).symm y, ?_⟩
    apply (rationalCoeffEquiv F G).injective
    rw [rationalCoeffEquiv_map, MulEquiv.apply_symm_apply, hy]
  · -- the rational square for `z.p`
    intro h
    exact congrArg Multiplicative.ofAdd
      (rationalKottwitz_map_of_inputs hfunct hdesc F z.H G hH hG z.p h)
  · -- lifts through `Z(F)`
    intro h hq
    set a := (reductiveInvariantInclusion F z.H hH (reductiveKottwitzRational F z.H hH h)).toAdd
      with ha_def
    have ha_inv : ∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
        fundamentalGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F) z.H hH σ a =
          a :=
      (Representation.mem_invariants _ _).1
        (Multiplicative.toAdd (reductiveKottwitzRational F z.H hH h)).2
    have hker : a ∈ LinearMap.ker
        (fundamentalInertiaMap F (UnramifiedClosure F) (SeparableClosure F)
          G hG z.H hH z.p) := by
      rw [LinearMap.mem_ker]
      exact congrArg Multiplicative.toAdd hq
    rw [(hexact.zExtension F (UnramifiedClosure F) (SeparableClosure F) z).2] at hker
    obtain ⟨b, hb⟩ := hker
    have hinjZ := hinj F G z
    -- `b` is residually invariant
    have hb_inv : ∀ σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F,
        fundamentalGammaRepresentation F (UnramifiedClosure F) (SeparableClosure F)
          z.Z.toGrp hZ σ b = b := by
      intro σ
      apply hinjZ
      rw [((fundamentalInertiaMapStatement F (UnramifiedClosure F) (SeparableClosure F)).1
        z.Z.toGrp z.H hZ hH z.i).2.2 σ b, hb]
      exact ha_inv σ
    have hcomp := torusInertiaComparison_proof F (UnramifiedClosure F) (SeparableClosure F)
      z.Z hZt
    set c := torusInertiaComparison F (UnramifiedClosure F) (SeparableClosure F) z.Z hZt b
      with hc_def
    have hc : c ∈ TorusInvariantTarget F z.Z := by
      rw [Representation.mem_invariants]
      intro σ
      rw [hc_def, ← hcomp.2.2.2 σ b, hb_inv σ]
    obtain ⟨x, hx⟩ := hcor F z.Z z.isZExtension.induced (Multiplicative.ofAdd ⟨c, hc⟩)
    have hκZ : (reductiveInvariantInclusion F z.Z.toGrp hZ
        (reductiveKottwitzRational F z.Z.toGrp hZ x)).toAdd = b := by
      apply hcomp.2.2.1.1
      rw [(hdesc.2 F z.Z.toGrp hZ).2.2 x, (hfunct F F).2 z.Z hZt,
        ← (torusKottwitzDescent F z.Z hZt).2.2 x, hx]
      rfl
    refine ⟨rationalPoints.map z.i x, ?_, ?_⟩
    · rw [MonoidHom.mem_ker]
      apply (rationalCoeffEquiv F G).injective
      rw [rationalCoeffEquiv_map, rationalCoeffEquiv_map, map_one, affinePointsTarget_apply,
        affinePointsTarget_apply, Category.assoc]
      exact comp_quotient_eq_one z.isZExtension.quotient.2.2.2 _
    · apply Multiplicative.toAdd.injective
      change (reductiveInvariantInclusion F z.H hH
        (reductiveKottwitzRational F z.H hH (rationalPoints.map z.i x))).toAdd = a
      rw [rationalKottwitz_map_of_inputs hfunct hdesc F z.Z.toGrp z.H hZ hH z.i x, hκZ, hb]

end Langlands.Geometry.Building.Kottwitz
