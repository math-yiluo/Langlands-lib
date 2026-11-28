import Langlands.GroupScheme.Rational.QuadraticLeviCellCocycleLift
import Langlands.GroupScheme.Rational.QuadraticTorusCellLocalControl
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Absolute.BorelExistence
import Langlands.GroupScheme.Absolute.BorelAlgClosedFieldExtensionProof
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Coboundaries near the identity of a connected reductive group over a complex quadratic
extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open GaloisPointComparison

/-- A connected reductive group over an algebraically closed field is quasi-split: it has a
Borel subgroup over the field, and a Borel subgroup stays Borel over an algebraic closure. -/
theorem IsConnectedReductive.isQuasiSplit_of_isAlgClosed {M : Type u} [Field M] [IsAlgClosed M]
    {G : GroupScheme (Spec (CommRingCat.of M))} (hG : IsConnectedReductive G) :
    IsQuasiSplit G := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨B, i, hi⟩ := BorelExistence.exists_isBorelSubgroup G
  exact ⟨hG, B, i, hi, borelAlgClosedFieldExtensionStatement M (AlgebraicClosure M) G
    hG.isAffineHom hG.smooth hG.connectedSpace B i hi⟩

section Comparison

variable (K M : Type u) [Field K] [Field M] [Algebra K M]

/-- The rational points of a base change, viewed as coefficient points and transported back
along the base-change comparison, are the ring points of the base change. -/
theorem affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv_eq_rationalPointEquiv
    (G : GroupScheme (Spec (CommRingCat.of K)))
    (q : rationalPoints ((GroupScheme.baseChange (algebraBaseMap K M)).obj G)) :
    (affinePointsBaseChangeMulEquiv K M M G (baseChangeCoeffEquiv K M G q) :
        RingPoint M ((GroupScheme.baseChange (algebraBaseMap K M)).obj G).X M) =
      rationalPointEquiv M _ q := by
  rw [← rationalCoeffEquiv_eq]
  apply (affinePointsBaseChangeMulEquiv K M M G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, rationalCoeffEquiv_left,
    baseChangeCoeffEquiv_left]

end Comparison

section LocalTorus

variable {K M : Type u} [Field K] [Field M] [Algebra K M]
  [TopologicalSpace M] [IsTopologicalRing M] [IsAlgClosed M]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) [IsAffine T.X.left]

private local instance : TopologicalSpace (GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M)) :=
  GroupScheme.affinePointsTopologicalSpace T.toGrp _

/-- For a torus over `K` and a field `M` topologically isomorphic to `ℂ`, every continuous
endomorphism `ψ` of the coefficient points has an open neighbourhood of `1` on which the
points with `x ψ(x) = 1` are of the form `a ψ(a)⁻¹`. -/
theorem exists_torusCoefficientCoboundaryNeighborhood (hT : IsTorus T.toGrp)
    (e : M ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (ψ : GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M) →*
      GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M)) (hψ : Continuous ψ) :
    ∃ U : Set (GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M)), IsOpen U ∧ 1 ∈ U ∧
      ∀ x ∈ U, x * ψ x = 1 → ∃ a, x = a * (ψ a)⁻¹ := by
  let TM := (CommGroupScheme.baseChange (Spec.algebraMap K M)).obj T
  let H := (GroupScheme.baseChange (Spec.algebraMap K M)).obj T.toGrp
  let : TopologicalSpace (H.affinePoints (CommAlgCat.of M M)) :=
    H.affinePointsTopologicalSpace _
  let E := affinePointsBaseChangeContinuousMulEquiv K M M T.toGrp
  let θ := E.toMulEquiv.toMonoidHom.comp (ψ.comp E.symm.toMulEquiv.toMonoidHom)
  have hθ : Continuous θ := E.continuous.comp (hψ.comp E.symm.continuous)
  have hTM : IsSplitTorus TM.toGrp :=
    ((hT.baseChange (K := M)).isRelativeTorus).isSplitTorus_of_isAlgClosed
  obtain ⟨V, hV, hVone, hVcb⟩ := exists_torusPoint_coboundaryNeighborhood TM hTM e he he' θ hθ
  refine ⟨E ⁻¹' V, hV.preimage E.continuous, ?_, fun x hx hn => ?_⟩
  · change E 1 ∈ V
    rwa [map_one]
  have hθE (z : GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M)) : θ (E z) = E (ψ z) := by
    change E (ψ (E.symm (E z))) = E (ψ z)
    rw [E.symm_apply_apply]
  have hnorm : E x * θ (E x) = 1 := by rw [hθE, ← map_mul E, hn, map_one]
  obtain ⟨y, hy⟩ := hVcb (E x) hx hnorm
  obtain ⟨a, rfl⟩ := E.surjective y
  change E x = E a * (θ (E a))⁻¹ at hy
  refine ⟨a, E.injective ?_⟩
  rw [map_mul, map_inv, hy, hθE]

end LocalTorus

section Reductive

variable {K M : Type u} [Field K] [NontriviallyNormedField M] [Algebra K M] [IsAlgClosed M]
  [FiniteDimensional K M] [IsGalois K M]

private local instance (H : GroupScheme (Spec (CommRingCat.of K))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of K M)) :=
  H.affinePointsTopologicalSpace _

/-- The open neighbourhood of the proof of Platonov–Rapinchuk, Lemma 6.28 (printed p. 370),
for a connected reductive group `H` instead of a torus: let `M/K` be a quadratic Galois
extension of an infinite field with `M` topologically isomorphic to `ℂ`, and let the generator
`τ` of `Gal(M/K)` act continuously. Then the points `x` of an open neighbourhood of `1` in
`H(M)` with `x τ(x) = 1` are all of the form `a τ(a)⁻¹`. The proof uses a maximal torus `T` over
`K` with `T_M = B ∩ τ(B)` for a Borel subgroup `B` of `H_M`, the open cell `U × T_M × τ(U)`,
and the torus case. -/
theorem exists_coboundaryNeighborhood_of_isConnectedReductive [Infinite K]
    (hM : Module.finrank K M = 2) (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1) (hcτ : Continuous τ)
    (e : M ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (H : GroupScheme (Spec (CommRingCat.of K))) (hH : IsConnectedReductive H) :
    ∃ U : Set (H.affinePoints (CommAlgCat.of K M)), IsOpen U ∧ 1 ∈ U ∧
      ∀ x ∈ U, x * GaloisPoint.conjugate K M H τ x = 1 →
        ∃ a, x = a * (GaloisPoint.conjugate K M H τ a)⁻¹ := by
  classical
  let b := algebraBaseMap K M
  let HM := (GroupScheme.baseChange b).obj H
  have hHM : IsConnectedReductive HM := connectedReductiveFieldExtensionStatement K M H hH
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let : IsAffineHom HM.X.hom := hHM.isAffineHom
  let : IsAffine HM.X.left := isAffine_of_isAffineHom HM.X.hom
  let : Smooth HM.X.hom := hHM.smooth
  obtain ⟨T, t, ht⟩ := exists_quadraticOppositeBorelTorus hM hH hHM.isQuasiSplit_of_isAlgClosed
  obtain ⟨σ, χ, hσ, hC, hU⟩ := ht.exists_dynamicData hH
  have hστ : σ = τ := (GaloisCocycle.quadratic_aut_eq_one_or hM τ hτ σ).resolve_left hσ
  subst hστ
  let ψ := GaloisPoint.conjugate K M H σ
  let ψT := GaloisPoint.conjugate K M T.toGrp σ
  let TM := (GroupScheme.baseChange b).obj T.toGrp
  let tM : TM ⟶ HM := (GroupScheme.baseChange b).map t
  let : IsAffineHom T.X.hom := ht.2.1.1.isRelativeTorus.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let : IsAffine TM.X.left := ringBaseChange_isAffine K M T.X
  let : IsClosedImmersion t.hom.hom.left := ht.2.1.2.1
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion tM.hom.hom.left := ht.2.1.2.1.baseChange b
  let : Mono tM.hom.hom := Over.mono_of_mono_left _
  have hC' : (Dynamic.centralizer χ).IsRepresentedBy tM := ⟨inferInstance, hC.symm⟩
  let U := Dynamic.Affine.unipotentScheme (G := HM) χ
  let V := Dynamic.Affine.unipotentScheme (G := HM) (Dynamic.oppositeCocharacter χ)
  let : IsAffineHom U.X.hom := Dynamic.OppositeEnvelope.unipotentScheme_isAffineHom (G := HM) χ
  let : IsAffineHom V.X.hom := Dynamic.OppositeEnvelope.unipotentScheme_isAffineHom
    (G := HM) (Dynamic.oppositeCocharacter χ)
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  let : IsAffine (TM.X ⊗ V.X).left := tensor_isAffine M TM.X V.X
  let : IsAffine (U.X ⊗ (TM.X ⊗ V.X)).left := tensor_isAffine M U.X _
  have hopen : IsOpenImmersion (Dynamic.leviOppositeCell (C := TM) χ tM).left :=
    Dynamic.isOpenImmersion_leviOppositeCell χ tM hC'
  let : Mono (Dynamic.leviOppositeCell (C := TM) χ tM) := Over.mono_of_mono_left _
  obtain ⟨A₀, posEquiv, negEquiv, hinj, hcell⟩ :=
    GaloisCocycle.exists_leviOppositeCell_coordinates (t := t) χ σ hU
  let p : U.X ⊗ (TM.X ⊗ V.X) ⟶ TM.X := snd U.X (TM.X ⊗ V.X) ≫ fst TM.X V.X
  have hψT : Continuous ψT :=
    GroupScheme.continuous_affinePointMap T.toGrp (CommAlgCat.ofHom σ.toAlgHom) hcτ
  obtain ⟨W, hW, hW₁, hWcb⟩ :=
    exists_torusCoefficientCoboundaryNeighborhood T ht.2.1.1 e he he' ψT hψT
  let EH : H.affinePoints (CommAlgCat.of K M) ≃ₜ RingPoint M HM.X M :=
    (affinePointsBaseChangeContinuousMulEquiv K M M H).toHomeomorph.trans
      (HM.affinePointsRingPointHomeomorph (CommAlgCat.of M M))
  let ET : GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M) ≃ₜ RingPoint M TM.X M :=
    (affinePointsBaseChangeContinuousMulEquiv K M M T.toGrp).toHomeomorph.trans
      (TM.affinePointsRingPointHomeomorph (CommAlgCat.of M M))
  have hEH (q : rationalPoints HM) :
      EH (baseChangeCoeffEquiv K M H q) = rationalPointEquiv M HM.X q := by
    change HM.affinePointsRingPointHomeomorph (CommAlgCat.of M M)
      (affinePointsBaseChangeMulEquiv K M M H (baseChangeCoeffEquiv K M H q)) = _
    rw [affinePointsRingPointHomeomorph_apply]
    exact affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv_eq_rationalPointEquiv K M H q
  have hET (q : rationalPoints TM) :
      ET (baseChangeCoeffEquiv K M T.toGrp q) = rationalPointEquiv M TM.X q := by
    change TM.affinePointsRingPointHomeomorph (CommAlgCat.of M M)
      (affinePointsBaseChangeMulEquiv K M M T.toGrp (baseChangeCoeffEquiv K M T.toGrp q)) = _
    rw [affinePointsRingPointHomeomorph_apply]
    exact affinePointsBaseChangeMulEquiv_baseChangeCoeffEquiv_eq_rationalPointEquiv K M T.toGrp q
  let mm (z : RingPoint M (U.X ⊗ (TM.X ⊗ V.X)) M) : RingPoint M HM.X M :=
    z ≫ Dynamic.leviOppositeCell (C := TM) χ tM
  let pm (z : RingPoint M (U.X ⊗ (TM.X ⊗ V.X)) M) : RingPoint M TM.X M := z ≫ p
  have hmo : IsOpenMap mm := by
    have h := @GaloisCocycle.isOpenEmbedding_pointMap_of_isOpenImmersion M M _
      (U.X ⊗ (TM.X ⊗ V.X)) HM.X _ (Algebra.id M) inferInstance inferInstance
      (Dynamic.leviOppositeCell (C := TM) χ tM) hopen
    exact h.isOpenMap
  have hpc : Continuous pm := continuous_affineSchemePointMap M M p
  let O : Set (RingPoint M (U.X ⊗ (TM.X ⊗ V.X)) M) := pm ⁻¹' (ET '' W)
  have hO : IsOpen O := (ET.isOpenMap W hW).preimage hpc
  refine ⟨EH ⁻¹' (mm '' O), (hmo O hO).preimage EH.continuous, ?_, fun x hx hn => ?_⟩
  · let o : RationalPoint M (U.X ⊗ (TM.X ⊗ V.X)) := lift 1 (lift 1 1)
    have hom : o ≫ Dynamic.leviOppositeCell (C := TM) χ tM = 1 := by
      simp only [o, Dynamic.lift_comp_leviOppositeCell, MonObj.one_comp, mul_one]
    have hop : o ≫ p = 1 := by simp only [o, p, lift_snd_assoc, lift_fst]
    refine ⟨rationalPointEquiv M _ o, ⟨1, hW₁, ?_⟩, ?_⟩
    · change ET 1 = rationalPointEquiv M _ o ≫ p
      rw [← rationalPointEquiv_natural, hop, ← hET, map_one (baseChangeCoeffEquiv K M T.toGrp)]
    · change rationalPointEquiv M _ o ≫ Dynamic.leviOppositeCell (C := TM) χ tM = EH 1
      rw [← rationalPointEquiv_natural, hom, ← hEH, map_one (baseChangeCoeffEquiv K M H)]
  · obtain ⟨z, hzO, hz⟩ := hx
    let z' : RationalPoint M (U.X ⊗ (TM.X ⊗ V.X)) := (rationalPointEquiv M _).symm z
    have hz' : z' ≫ Dynamic.leviOppositeCell (C := TM) χ tM =
        (baseChangeCoeffEquiv K M H).symm x := by
      apply (rationalPointEquiv M HM.X).injective
      rw [rationalPointEquiv_natural, ← hEH, MulEquiv.apply_symm_apply]
      change rationalPointEquiv M _ ((rationalPointEquiv M _).symm z) ≫ _ = EH x
      rw [Equiv.apply_symm_apply]
      exact hz
    let x₁ := z' ≫ fst U.X (TM.X ⊗ V.X)
    let x₂ := z' ≫ p
    let x₃ := z' ≫ snd U.X (TM.X ⊗ V.X) ≫ snd TM.X V.X
    have hx' : lift x₁ (lift x₂ x₃) = z' := by
      apply CartesianMonoidalCategory.hom_ext
      · exact lift_fst _ _
      rw [lift_snd]
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]
        simp only [x₂, p, Category.assoc]
      rw [lift_snd]
      simp only [x₃, Category.assoc]
    have hxcell : x = ((posEquiv.symm x₁ : A₀) : GroupScheme.affinePoints H (CommAlgCat.of K M)) *
        (baseChangeCoeffEquiv K M T.toGrp x₂ ≫ t.hom.hom) * ψ (negEquiv.symm x₃ : A₀) := by
      rw [← hcell, hx', hz', MulEquiv.apply_symm_apply]
    have hd : baseChangeCoeffEquiv K M T.toGrp x₂ ∈ W := by
      obtain ⟨w, hw, hwz⟩ := hzO
      have hpz : pm z = ET (baseChangeCoeffEquiv K M T.toGrp x₂) := by
        rw [hET, rationalPointEquiv_natural, Equiv.apply_symm_apply]
      rwa [ET.injective (hwz.trans hpz)] at hw
    let u : GaloisCocycle.cover K M ⟶ H.X :=
      ((posEquiv.symm x₁ : A₀) : GaloisCocycle.cover K M ⟶ H.X)
    set d := baseChangeCoeffEquiv K M T.toGrp x₂ with hd_def
    have hcard : Nat.card (M ≃ₐ[K] M) = 2 := (IsGalois.card_aut_eq_finrank K M).trans hM
    have hσ₂ : σ * σ = 1 := by
      simpa only [hcard, pow_two] using (pow_card_eq_one' (x := σ))
    have hψ₂ (y : GroupScheme.affinePoints H (CommAlgCat.of K M)) : ψ (ψ y) = y := by
      change GaloisPoint.conjugate K M H σ (GaloisPoint.conjugate K M H σ y) = y
      rw [← GaloisPoint.conjugate_mul, hσ₂, GaloisPoint.conjugate_one]
    have hc : x = (ψ x)⁻¹ := eq_inv_of_mul_eq_one_left hn
    have hj (y : GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M)) :
        ψ (y ≫ t.hom.hom) = ψT y ≫ t.hom.hom :=
      (Category.assoc _ y t.hom.hom).symm
    have hcoordinates : ((posEquiv.symm x₁ : A₀), d, (negEquiv.symm x₃ : A₀)) =
        ((negEquiv.symm x₃ : A₀)⁻¹, (ψT d)⁻¹, (posEquiv.symm x₁ : A₀)⁻¹) := by
      apply hinj
      change u * (d ≫ t.hom.hom) * ψ (negEquiv.symm x₃ : A₀) =
        (((negEquiv.symm x₃ : A₀)⁻¹ : A₀) : GroupScheme.affinePoints H (CommAlgCat.of K M)) *
          ((ψT d)⁻¹ ≫ t.hom.hom) * ψ (((posEquiv.symm x₁ : A₀)⁻¹ : A₀) : _)
      rw [← hxcell, hc, hxcell, map_mul, map_mul, hj, hψ₂]
      simp only [Subgroup.coe_inv, GrpObj.inv_comp, map_inv]
      group
    have hv : (negEquiv.symm x₃ : A₀) = (posEquiv.symm x₁ : A₀)⁻¹ :=
      congrArg (fun z : A₀ × GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M) × A₀ => z.2.2)
        hcoordinates
    have hd' : d = (ψT d)⁻¹ :=
      congrArg (fun z : A₀ × GroupScheme.affinePoints T.toGrp (CommAlgCat.of K M) × A₀ => z.2.1)
        hcoordinates
    have hdn : d * ψT d = 1 := by
      have h := inv_mul_cancel (ψT d)
      rwa [← hd'] at h
    obtain ⟨a, ha⟩ := hWcb d hd hdn
    show ∃ a, x = a * (ψ a)⁻¹
    refine ⟨((posEquiv.symm x₁ : A₀) : GaloisCocycle.cover K M ⟶ H.X) * (a ≫ t.hom.hom), ?_⟩
    rw [hxcell, hv, ha, map_mul ψ, hj a]
    simp only [Subgroup.coe_inv, GrpObj.inv_comp, map_inv, MonObj.mul_comp]
    group

end Reductive

section Relative

variable {F K M : Type u} [Field F] [Field K] [NontriviallyNormedField M]
  [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] [IsAlgClosed M]
  [FiniteDimensional K M] [IsGalois K M]

private local instance (H : GroupScheme (Spec (CommRingCat.of F))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of F M)) :=
  H.affinePointsTopologicalSpace _

private local instance (H : GroupScheme (Spec (CommRingCat.of K))) :
    TopologicalSpace (H.affinePoints (CommAlgCat.of K M)) :=
  H.affinePointsTopologicalSpace _

omit [IsAlgClosed M] [FiniteDimensional K M] [IsGalois K M] in
/-- The base-change comparison of coefficient points intertwines the relative Galois action
of `Gal(M/K)` on the points of a group over `F` with the Galois action on the points of its
base change to `K`. -/
theorem affinePointsBaseChangeMulEquiv_relativeConjugate
    (C : GroupScheme (Spec (CommRingCat.of F))) (τ : M ≃ₐ[K] M)
    (x : C.affinePoints (CommAlgCat.of F M)) :
    affinePointsBaseChangeMulEquiv F K M C (GaloisPoint.relativeConjugate F K M C τ x) =
      GaloisPoint.conjugate K M ((GroupScheme.baseChange (Spec.algebraMap F K)).obj C) τ
        (affinePointsBaseChangeMulEquiv F K M C x) := by
  exact (affinePointsBaseChangeMulEquiv_naturality F K M M C τ.toAlgHom x).symm

/-- The same open neighbourhood for a connected reductive group `C` over a field `F`, in the
coefficient points `C(M)` of an extension `M` of an intermediate infinite field `K`: if `M/K`
is quadratic Galois, `M` is topologically isomorphic to `ℂ` and the nonidentity element `τ`
of `Gal(M/K)` acts continuously, then the points `x` of an open neighbourhood of `1` in `C(M)`
with `x τ(x) = 1` are all of the form `a τ(a)⁻¹`. -/
theorem exists_relativeCoboundaryNeighborhood_of_isConnectedReductive [Infinite K]
    (hM : Module.finrank K M = 2) (τ : M ≃ₐ[K] M) (hτ : τ ≠ 1) (hcτ : Continuous τ)
    (e : M ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (C : GroupScheme (Spec (CommRingCat.of F))) (hC : IsConnectedReductive C) :
    ∃ W : Set (C.affinePoints (CommAlgCat.of F M)), IsOpen W ∧ 1 ∈ W ∧
      ∀ x ∈ W, x * GaloisPoint.relativeConjugate F K M C τ x = 1 →
        ∃ a, x = a * (GaloisPoint.relativeConjugate F K M C τ a)⁻¹ := by
  let CK := (GroupScheme.baseChange (Spec.algebraMap F K)).obj C
  have hCK : IsConnectedReductive CK := connectedReductiveFieldExtensionStatement F K C hC
  let : IsAffineHom C.X.hom := hC.isAffineHom
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let E := affinePointsBaseChangeContinuousMulEquiv F K M C
  obtain ⟨U, hU, hU₁, hUcb⟩ :=
    exists_coboundaryNeighborhood_of_isConnectedReductive hM τ hτ hcτ e he he' CK hCK
  have hE (x : C.affinePoints (CommAlgCat.of F M)) :
      E (GaloisPoint.relativeConjugate F K M C τ x) = GaloisPoint.conjugate K M CK τ (E x) :=
    affinePointsBaseChangeMulEquiv_relativeConjugate C τ x
  refine ⟨E ⁻¹' U, hU.preimage E.continuous, ?_, fun x hx hn => ?_⟩
  · change E 1 ∈ U
    rwa [map_one]
  have hn' : E x * GaloisPoint.conjugate K M CK τ (E x) = 1 := by
    rw [← hE, ← map_mul, hn, map_one]
  obtain ⟨y, hy⟩ := hUcb (E x) hx hn'
  obtain ⟨a, rfl⟩ := E.surjective y
  refine ⟨a, E.injective ?_⟩
  rw [map_mul, map_inv, hy, hE]

end Relative

end Langlands.GroupScheme
