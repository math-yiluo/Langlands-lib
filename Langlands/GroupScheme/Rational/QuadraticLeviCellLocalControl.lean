import Langlands.GroupScheme.Rational.QuadraticTorusCellLocalControl

/-! # Archimedean control of the middle coordinate of an open cell with a general middle
subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

open GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000
set_option maxRecDepth 3500

section Coefficients

variable {F Q M : Type u} [Field F] [Field Q] [Field M]
  [Algebra F Q] [Algebra F M] [Algebra Q M] [IsScalarTower F Q M]

variable [TopologicalSpace M] [IsTopologicalRing M]

local instance (G : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F M)) :=
  G.affinePointsTopologicalSpace _

/-- Topological pullback adjunction with the affine-scheme ring point topology
on points of the scalar extension. -/
private def leviCoefficientRingPointHomeomorph (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine (baseChanged F Q G).X.left] :
    G.affinePoints (CommAlgCat.of F M) ≃ₜ RingPoint Q (baseChanged F Q G).X M :=
  (G.affinePointsRingPointHomeomorph (CommAlgCat.of F M)).trans
    ((ringPointBaseChangeEquiv F Q M G.X).toHomeomorphOfIsInducing
      (isHomeomorph_ringPointBaseChangeEquiv F Q M G.X).isInducing)

private theorem leviCoefficientRingPointHomeomorph_apply
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [IsAffine (baseChanged F Q G).X.left] (x : G.affinePoints (CommAlgCat.of F M)) :
    leviCoefficientRingPointHomeomorph G x = affinePointsBaseChangeMulEquiv F Q M G x := by
  change ringPointBaseChangeEquiv F Q M G.X
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of F M) x) = _
  rw [affinePointsRingPointHomeomorph_apply, affinePointsBaseChangeMulEquiv_eq_ringPoint]

end Coefficients

private theorem exists_open_leviMiddleCoordinate
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (m : X → Y) (hmo : IsOpenMap m) (p : X → Z) (hp : Continuous p)
    (φ : Y → Y) (hφ : Continuous φ) (W : Set Z) (hW : IsOpen W)
    (a : Y) (o : X) (ho : m o = φ a) (hpo : p o ∈ W) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ f ∈ V, ∃ z, m z = φ f ∧ p z ∈ W := by
  refine ⟨φ ⁻¹' (m '' (p ⁻¹' W)), (hmo _ (hW.preimage hp)).preimage hφ,
    ⟨a, o, hpo, ho⟩, fun f hf => ?_⟩
  obtain ⟨z, hz, h⟩ := hf
  exact ⟨z, h, hz⟩

section LocalControl

variable {F Q K M : Type u} [Field F] [Field Q] [Field K] [NontriviallyNormedField M]
  [Algebra F Q] [Algebra F K] [Algebra F M] [Algebra Q M] [Algebra K M]
  [IsScalarTower F Q M] [IsScalarTower F K M] [FiniteDimensional F Q] [IsGalois F Q]
  [FiniteDimensional K M] [IsGalois K M]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {C : GroupScheme (Spec (CommRingCat.of F))} [IsAffine C.X.left]
  [IsAffine (baseChanged F Q G).X.left] [IsAffine (baseChanged F Q C).X.left]
  {X : Over (Spec (CommRingCat.of Q))} [IsAffine X.left]

local instance (H : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of F M)) :=
  H.affinePointsTopologicalSpace _

/-- Near a local trivializing cochain, the twisted value of a cocycle lies in the open cell,
and its middle coordinate trivializes over `K` every cocycle of the middle subgroup `C` with
that value, provided that the points `x` of an open neighbourhood of `1` in `C(M)` with
`x τ(x) = 1` are of the form `a τ(a)⁻¹`. -/
theorem exists_localLeviCellControl
    (hQ : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q)
    (hM : Module.finrank K M = 2) (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1)
    (hres : (τ.restrictScalars F).restrictNormal Q = σ) (hcτ : Continuous τ)
    (hCcb : ∃ W : Set (C.affinePoints (CommAlgCat.of F M)), IsOpen W ∧ 1 ∈ W ∧
      ∀ x ∈ W, x * GaloisPoint.relativeConjugate F K M C τ x = 1 →
        ∃ a, x = a * (GaloisPoint.relativeConjugate F K M C τ a)⁻¹)
    (m : X ⟶ (baseChanged F Q G).X) [IsOpenImmersion m.left]
    (p : X ⟶ (baseChanged F Q C).X)
    (o : RingPoint Q X M)
    (hom : o ≫ m = affinePointsBaseChangeMulEquiv F Q M G 1)
    (hop : o ≫ p = affinePointsBaseChangeMulEquiv F Q M C 1)
    (ξ : Cocycle G (cover F Q)) (hξ : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ V : Set (RingPoint Q (baseChanged F Q G).X M), IsOpen V ∧ V.Nonempty ∧
      ∀ f : rationalPoints (baseChanged F Q G),
        (rationalPointEquiv Q _ f).changeRing (Algebra.ofId Q M) ∈ V →
        ∃ z : RingPoint Q X M,
          z ≫ m = (rationalPointEquiv Q _ ((baseChangeCoeffEquiv F Q G).symm
            (value (ξ.twist (baseChangeCoeffEquiv F Q G f)) σ))).changeRing (Algebra.ofId Q M) ∧
          ∀ δ : Cocycle C (cover F Q),
            affinePointsBaseChangeMulEquiv F Q M C
              (GaloisPoint.relativeExtend F Q M C (value δ σ)) = z ≫ p →
            (δ.baseChangePullback (Spec.algebraMap F K)).IsTrivial := by
  let ψ (H : GroupScheme (Spec (CommRingCat.of F))) := GaloisPoint.relativeConjugate F K M H τ
  let ext (H : GroupScheme (Spec (CommRingCat.of F))) := GaloisPoint.relativeExtend F Q M H
  have hψ (H : GroupScheme (Spec (CommRingCat.of F))) : Continuous (ψ H) :=
    H.continuous_affinePointMap (CommAlgCat.ofHom (τ.restrictScalars F).toAlgHom) hcτ
  have hcomm (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffine H.X.left]
      (x : H.affinePoints (CommAlgCat.of F Q)) :
      ext H (GaloisPoint.conjugate F Q H σ x) = ψ H (ext H x) := by
    rw [← hres]
    exact GaloisPoint.relativeExtend_conjugate F Q M H (τ.restrictScalars F) x
  let EG := leviCoefficientRingPointHomeomorph (Q := Q) (M := M) G
  let ET := leviCoefficientRingPointHomeomorph (Q := Q) (M := M) C
  let twist (f : G.affinePoints (CommAlgCat.of F M)) :=
    f⁻¹ * ext G (value ξ σ) * ψ G f
  let : IsTopologicalGroup (G.affinePoints (CommAlgCat.of F M)) :=
    affinePointsIsTopologicalGroup G (CommAlgCat.of F M)
  have ht : Continuous twist :=
    (continuous_inv.mul continuous_const).mul (hψ G)
  obtain ⟨a, ha⟩ := (isTrivial_baseChangePullback_iff_quadratic_value ξ hM τ hτ).mp hξ
  rw [hres] at ha
  have ha' : twist a = 1 := by
    change a⁻¹ * ext G (value ξ σ) * ψ G a = 1
    rw [show ext G (value ξ σ) = a * (ψ G a)⁻¹ from ha]
    rw [inv_mul_cancel_left, inv_mul_cancel]
  obtain ⟨W, hW, hWo, hWc⟩ := hCcb
  let pm (z : RingPoint Q X M) : RingPoint Q (baseChanged F Q C).X M := z ≫ p
  let mm (z : RingPoint Q X M) : RingPoint Q (baseChanged F Q G).X M := z ≫ m
  let φ := EG ∘ twist ∘ EG.symm
  have hφ : Continuous φ := EG.continuous.comp (ht.comp EG.symm.continuous)
  have h₀ : pm o ∈ ET '' W := by
    refine ⟨1, hWo, ?_⟩
    exact (leviCoefficientRingPointHomeomorph_apply C 1).trans hop.symm
  have hmo : mm o = φ (EG a) := by
    change o ≫ m = EG (twist (EG.symm (EG a)))
    rw [EG.symm_apply_apply, ha']
    exact hom.trans (leviCoefficientRingPointHomeomorph_apply G 1).symm
  obtain ⟨V, hV, hVn, hVprop⟩ := exists_open_leviMiddleCoordinate mm
    (isOpenEmbedding_pointMap_of_isOpenImmersion (M := M) m).isOpenMap pm
    (continuous_affineSchemePointMap Q M p) φ hφ (ET '' W) (ET.isOpenMap W hW)
    (EG a) o hmo h₀
  refine ⟨V, hV, hVn, fun f hf => ?_⟩
  have hext (f' : rationalPoints (baseChanged F Q G)) :
      EG (ext G (baseChangeCoeffEquiv F Q G f')) =
        (rationalPointEquiv Q _ f').changeRing (Algebra.ofId Q M) := by
    rw [show EG _ = affinePointsBaseChangeMulEquiv F Q M G _ from
      leviCoefficientRingPointHomeomorph_apply G _]
    exact affinePointsBaseChange_relativeExtend G f'
  rw [← hext f] at hf
  obtain ⟨z, hz', hz⟩ := hVprop _ hf
  change z ≫ m = EG (twist (EG.symm (EG (ext G (baseChangeCoeffEquiv F Q G f))))) at hz'
  rw [EG.symm_apply_apply] at hz'
  have hval : ext G (value (ξ.twist (baseChangeCoeffEquiv F Q G f)) σ) =
      twist (ext G (baseChangeCoeffEquiv F Q G f)) := by
    let f' := baseChangeCoeffEquiv F Q G f
    change ext G ((𝟙 _ ≫ f')⁻¹ * value ξ σ * GaloisPoint.conjugate F Q G σ f') = _
    rw [Category.id_comp, map_mul, map_mul, map_inv, hcomm]
  refine ⟨z, ?_, fun δ hδ => ?_⟩
  · rw [← hext, (baseChangeCoeffEquiv F Q G).apply_symm_apply, hval]
    exact hz'
  · let x := ext C (value δ σ)
    have hx : x ∈ W := by
      obtain ⟨y, hy, hyz⟩ := hz
      have heq : ET y = ET x := hyz.trans (hδ.symm.trans
        (leviCoefficientRingPointHomeomorph_apply C x).symm)
      exact (ET.injective heq) ▸ hy
    have hcard := (IsGalois.card_aut_eq_finrank F Q).trans hQ
    have hs : σ * σ = 1 := by simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
    have hn : x * ψ C x = 1 := by
      have h := value_mul δ σ σ
      rw [hs] at h
      change δ.toFun (𝟙 _) (arrow F Q 1) = _ at h
      rw [arrow_one, Cocycle.toFun_self] at h
      change ext C (value δ σ) * ψ C (ext C (value δ σ)) = 1
      rw [← hcomm, ← map_mul, ← h, map_one]
    obtain ⟨a', ha'⟩ := hWc x hx hn
    apply (isTrivial_baseChangePullback_iff_quadratic_value δ hM τ hτ).mpr
    rw [hres]
    exact ⟨a', ha'⟩

end LocalControl

end Langlands.GroupScheme.GaloisCocycle
