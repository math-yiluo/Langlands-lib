import Langlands.GroupScheme.Rational.QuadraticRealCocycleComparison
import Langlands.GroupScheme.Rational.ComplexTorusCoboundaryNeighborhood
import Langlands.GroupScheme.AffinePointBaseChangeSmooth
import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.Torus.RelativeCentralizerReductiveProof
import Langlands.GroupScheme.Dynamic.RCLikeLeviIwasawa
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.Construction

/-! # Archimedean control of the middle coordinate in an open cell -/

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

section OpenCell

variable {Q M : Type u} [Field Q]
  {X Y : Over (Spec (CommRingCat.of Q))}

/-! Throughout, the test spectra and the open immersion are actual scheme morphisms. -/

theorem isOpenEmbedding_pointMap_of_isOpenImmersion
    [NontriviallyNormedField M] [Algebra Q M] [IsAffine X.left] [IsAffine Y.left]
    (m : X ⟶ Y) [IsOpenImmersion m.left] :
    IsOpenEmbedding (Y := RingPoint Q Y M) (fun z : RingPoint Q X M => z ≫ m) := by
  have h := isOpenEmbedding_schemePointMap Q M m
  rw [schemePointTopology_eq_affine Q X M, schemePointTopology_eq_affine Q Y M] at h
  exact h

theorem exists_point_factor_of_changeRing [Field M] [Algebra Q M]
    (m : X ⟶ Y) [IsOpenImmersion m.left] (q : RingPoint Q Y Q)
    (z : RingPoint Q X M) (hz : z ≫ m = q.changeRing (Algebra.ofId Q M)) :
    ∃ x : RingPoint Q X Q, x ≫ m = q := by
  apply Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.exists_lift_openImmersion m q
  let a := ringTestMap Q (Algebra.ofId Q M)
  have ha : Function.Surjective a.left := (fieldExtension_fpqc Q M).1.surj
  rintro _ ⟨s, rfl⟩
  obtain ⟨s', hs'⟩ := ha s
  refine ⟨z.left s', ?_⟩
  have h := congrArg (fun p : RingPoint Q Y M => p.left s') hz
  change m.left (z.left s') = q.left (a.left s') at h
  exact h.trans (congrArg q.left hs')

end OpenCell

section Coefficients

variable {F Q M : Type u} [Field F] [Field Q] [Field M]
  [Algebra F Q] [Algebra F M] [Algebra Q M] [IsScalarTower F Q M]

/-- Extending a rational point over the quadratic field as a ring point
agrees with extending its original group-valued coefficient. -/
theorem affinePointsBaseChange_relativeExtend (G : GroupScheme (Spec (CommRingCat.of F)))
    (x : rationalPoints (baseChanged F Q G)) :
    affinePointsBaseChangeMulEquiv F Q M G
      (GaloisPoint.relativeExtend F Q M G (baseChangeCoeffEquiv F Q G x)) =
      (rationalPointEquiv Q (baseChanged F Q G).X x).changeRing (Algebra.ofId Q M) := by
  apply (affinePointsBaseChangeMulEquiv F Q M G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (coverMap F Q M).left ≫ (baseChangeCoeffEquiv F Q G x).left =
    (ringTestMap Q (Algebra.ofId Q M)).left ≫ (rationalPointEquiv Q _ x).left ≫
      pullback.fst G.X.hom (baseMap F Q)
  rw [baseChangeCoeffEquiv_left, rationalPointEquiv_left]
  rfl

variable [TopologicalSpace M] [IsTopologicalRing M]

local instance (G : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F M)) :=
  G.affinePointsTopologicalSpace _

/-- Topological pullback adjunction with the affine-scheme ring point topology
on points of the scalar extension. -/
private def coefficientRingPointHomeomorph (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [IsAffine (baseChanged F Q G).X.left] :
    G.affinePoints (CommAlgCat.of F M) ≃ₜ RingPoint Q (baseChanged F Q G).X M :=
  (G.affinePointsRingPointHomeomorph (CommAlgCat.of F M)).trans
    ((ringPointBaseChangeEquiv F Q M G.X).toHomeomorphOfIsInducing
      (isHomeomorph_ringPointBaseChangeEquiv F Q M G.X).isInducing)

private theorem coefficientRingPointHomeomorph_apply
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [IsAffine (baseChanged F Q G).X.left] (x : G.affinePoints (CommAlgCat.of F M)) :
    coefficientRingPointHomeomorph G x = affinePointsBaseChangeMulEquiv F Q M G x := by
  change ringPointBaseChangeEquiv F Q M G.X
    (G.affinePointsRingPointHomeomorph (CommAlgCat.of F M) x) = _
  rw [affinePointsRingPointHomeomorph_apply, affinePointsBaseChangeMulEquiv_eq_ringPoint]

end Coefficients

section LocalTorus

variable {F M : Type u} [Field F] [Field M] [Algebra F M]
  [TopologicalSpace M] [IsTopologicalRing M] [IsAlgClosed M]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffine T.X.left]

local instance : TopologicalSpace (GroupScheme.affinePoints T.toGrp (CommAlgCat.of F M)) :=
  GroupScheme.affinePointsTopologicalSpace T.toGrp _

private theorem exists_localTorusCoboundaryNeighborhood (hT : IsTorus T.toGrp)
    (e : M ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F M) →*
      GroupScheme.affinePoints T.toGrp (CommAlgCat.of F M)) (hψ : Continuous ψ) :
    ∃ U : Set (GroupScheme.affinePoints T.toGrp (CommAlgCat.of F M)), IsOpen U ∧ 1 ∈ U ∧
      ∀ x ∈ U, x * ψ x = 1 → ∃ a, x = a * (ψ a)⁻¹ := by
  let TM := (CommGroupScheme.baseChange (Spec.algebraMap F M)).obj T
  let H := (GroupScheme.baseChange (Spec.algebraMap F M)).obj T.toGrp
  let : TopologicalSpace (H.affinePoints (CommAlgCat.of M M)) :=
    H.affinePointsTopologicalSpace _
  let E := affinePointsBaseChangeContinuousMulEquiv F M M T.toGrp
  let θ := E.toMulEquiv.toMonoidHom.comp (ψ.comp E.symm.toMulEquiv.toMonoidHom)
  have hθ : Continuous θ := E.continuous.comp (hψ.comp E.symm.continuous)
  have hTM : IsSplitTorus TM.toGrp :=
    ((hT.baseChange (K := M)).isRelativeTorus).isSplitTorus_of_isAlgClosed
  obtain ⟨V, hV, hVone, hVcb⟩ := exists_torusPoint_coboundaryNeighborhood TM hTM e he he' θ hθ
  refine ⟨E ⁻¹' V, hV.preimage E.continuous, ?_, fun x hx hn => ?_⟩
  · change E 1 ∈ V
    rwa [map_one]
  have hθE (z : GroupScheme.affinePoints T.toGrp (CommAlgCat.of F M)) : θ (E z) = E (ψ z) := by
    change E (ψ (E.symm (E z))) = E (ψ z)
    rw [E.symm_apply_apply]
  have hnorm : E x * θ (E x) = 1 := by rw [hθE, ← map_mul E, hn, map_one]
  obtain ⟨y, hy⟩ := hVcb (E x) hx hnorm
  obtain ⟨a, rfl⟩ := E.surjective y
  change E x = E a * (θ (E a))⁻¹ at hy
  refine ⟨a, E.injective ?_⟩
  rw [map_mul, map_inv, hy, hθE]

end LocalTorus

private theorem exists_open_middleCoordinate
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
  [FiniteDimensional K M] [IsGalois K M] [IsAlgClosed M]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  [IsAffine (baseChanged F Q G).X.left] [IsAffine (baseChanged F Q T.toGrp).X.left]
  {X : Over (Spec (CommRingCat.of Q))} [IsAffine X.left]

local instance (H : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of F M)) :=
  H.affinePointsTopologicalSpace _

/-- Near a local trivializing cochain, the twisted value lies in the open
cell and its middle coordinate trivializes any corresponding torus cocycle. -/
theorem exists_localCellControl
    (hQ : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q)
    (hM : Module.finrank K M = 2) (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1)
    (hres : (τ.restrictScalars F).restrictNormal Q = σ) (hcτ : Continuous τ)
    (e : M ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (hT : IsTorus T.toGrp)
    (m : X ⟶ (baseChanged F Q G).X) [IsOpenImmersion m.left]
    (p : X ⟶ (baseChanged F Q T.toGrp).X)
    (o : RingPoint Q X M)
    (hom : o ≫ m = affinePointsBaseChangeMulEquiv F Q M G 1)
    (hop : o ≫ p = affinePointsBaseChangeMulEquiv F Q M T.toGrp 1)
    (ξ : Cocycle G (cover F Q)) (hξ : (ξ.baseChangePullback (Spec.algebraMap F K)).IsTrivial) :
    ∃ V : Set (RingPoint Q (baseChanged F Q G).X M), IsOpen V ∧ V.Nonempty ∧
      ∀ f : rationalPoints (baseChanged F Q G),
        (rationalPointEquiv Q _ f).changeRing (Algebra.ofId Q M) ∈ V →
        ∃ z : RingPoint Q X M,
          z ≫ m = (rationalPointEquiv Q _ ((baseChangeCoeffEquiv F Q G).symm
            (value (ξ.twist (baseChangeCoeffEquiv F Q G f)) σ))).changeRing (Algebra.ofId Q M) ∧
          ∀ δ : Cocycle T.toGrp (cover F Q),
            affinePointsBaseChangeMulEquiv F Q M T.toGrp
              (GaloisPoint.relativeExtend F Q M T.toGrp (value δ σ)) = z ≫ p →
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
  let EG := coefficientRingPointHomeomorph (Q := Q) (M := M) G
  let ET := coefficientRingPointHomeomorph (Q := Q) (M := M) T.toGrp
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
  obtain ⟨W, hW, hWo, hWc⟩ :=
    exists_localTorusCoboundaryNeighborhood T hT e he he' (ψ T.toGrp) (hψ T.toGrp)
  let pm (z : RingPoint Q X M) : RingPoint Q (baseChanged F Q T.toGrp).X M := z ≫ p
  let mm (z : RingPoint Q X M) : RingPoint Q (baseChanged F Q G).X M := z ≫ m
  let φ := EG ∘ twist ∘ EG.symm
  have hφ : Continuous φ := EG.continuous.comp (ht.comp EG.symm.continuous)
  have h₀ : pm o ∈ ET '' W := by
    refine ⟨1, hWo, ?_⟩
    exact (coefficientRingPointHomeomorph_apply T.toGrp 1).trans hop.symm
  have hmo : mm o = φ (EG a) := by
    change o ≫ m = EG (twist (EG.symm (EG a)))
    rw [EG.symm_apply_apply, ha']
    exact hom.trans (coefficientRingPointHomeomorph_apply G 1).symm
  obtain ⟨V, hV, hVn, hVprop⟩ := exists_open_middleCoordinate mm
    (isOpenEmbedding_pointMap_of_isOpenImmersion (M := M) m).isOpenMap pm
    (continuous_affineSchemePointMap Q M p) φ hφ (ET '' W) (ET.isOpenMap W hW)
    (EG a) o hmo h₀
  refine ⟨V, hV, hVn, fun f hf => ?_⟩
  have hext (f' : rationalPoints (baseChanged F Q G)) :
      EG (ext G (baseChangeCoeffEquiv F Q G f')) =
        (rationalPointEquiv Q _ f').changeRing (Algebra.ofId Q M) := by
    rw [show EG _ = affinePointsBaseChangeMulEquiv F Q M G _ from
      coefficientRingPointHomeomorph_apply G _]
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
  · let x := ext T.toGrp (value δ σ)
    have hx : x ∈ W := by
      obtain ⟨y, hy, hyz⟩ := hz
      have heq : ET y = ET x := hyz.trans (hδ.symm.trans
        (coefficientRingPointHomeomorph_apply T.toGrp x).symm)
      exact (ET.injective heq) ▸ hy
    have hcard := (IsGalois.card_aut_eq_finrank F Q).trans hQ
    have hs : σ * σ = 1 := by simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
    have hn : x * ψ T.toGrp x = 1 := by
      have h := value_mul δ σ σ
      rw [hs] at h
      change δ.toFun (𝟙 _) (arrow F Q 1) = _ at h
      rw [arrow_one, Cocycle.toFun_self] at h
      change ext T.toGrp (value δ σ) * ψ T.toGrp (ext T.toGrp (value δ σ)) = 1
      rw [← hcomm, ← map_mul, ← h, map_one]
    obtain ⟨a', ha'⟩ := hWc x hx hn
    apply (isTrivial_baseChangePullback_iff_quadratic_value δ hM τ hτ).mpr
    rw [hres]
    exact ⟨a', ha'⟩

end LocalControl

end Langlands.GroupScheme.GaloisCocycle
