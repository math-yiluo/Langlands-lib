import Langlands.GroupScheme.CocycleCohomology
import Langlands.GroupScheme.Rational.QuadraticTorusCellCocycleLift
import Langlands.GroupScheme.Rational.QuadraticTorusCellLocalControl
import Langlands.GroupScheme.Rational.ComplexPlaceGroupApproximation
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Real-controlled reduction to an opposite-Borel torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry NumberField Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NumberField.LiesOver

namespace Langlands.GroupScheme

open GaloisCocycle GaloisPointComparison

set_option maxHeartbeats 2800000
set_option maxRecDepth 4500
set_option synthInstance.maxHeartbeats 130000
set_option backward.isDefEq.respectTransparency false

private abbrev RealTrivial {F : Type u} [Field F] [NumberField F]
    {H : GroupScheme (Spec (CommRingCat.of F))} {U : Over (Spec (CommRingCat.of F))}
    (ξ : Cocycle H U) : Prop :=
  ∀ v : InfinitePlace F, v.IsReal →
    (ξ.baseChangePullback (algebraBaseMap F v.Completion)).IsTrivial

section SplitPlace

variable {F Q : Type u} [Field F] [NumberField F] [Field Q] [Algebra F Q]
  {H : GroupScheme (Spec (CommRingCat.of F))}

private abbrev belowPlace (w : InfinitePlace Q) : InfinitePlace F :=
  w.comap (algebraMap F Q)

omit [NumberField F] in
private theorem isTrivial_pullback_of_real_above (δ : Cocycle H (cover F Q))
    (w : InfinitePlace Q) (hw : w.IsReal) :
    (δ.baseChangePullback (algebraBaseMap F (belowPlace (F := F) w).Completion)).IsTrivial := by
  let v := belowPlace (F := F) w
  let K := v.Completion
  let M := w.Completion
  let : w.LiesOver v := ⟨rfl⟩
  let : IsScalarTower F Q M := infiniteCompletionScalarTower w
  let : Module.Free K M := Module.Free.of_divisionRing K M
  have hdeg : Module.finrank K M = 1 :=
    (InfinitePlace.isUnramified_iff.mpr (Or.inl hw) : w.IsUnramified F).finrank_eq_one v
  let e := AlgEquiv.ofBijective (Algebra.ofId K M)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdeg)
  let φ : Q →ₐ[F] K := (e.symm.restrictScalars F).toAlgHom.comp (IsScalarTower.toAlgHom F Q M)
  let b := algebraBaseMap F K
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (𝟙 _)
  let p : (Over.map b).obj P ⟶ ringTest F K := Over.homMk (𝟙 _) (by simp [P, b, ringTest])
  let s : P ⟶ (Over.pullback b).obj (cover F Q) :=
    (Over.mapPullbackAdj b).homEquiv _ _ (p ≫ ringTestMap F φ)
  exact Cocycle.isTrivial_of_section (δ.baseChangePullback b) s

private theorem realTrivial_of_complexPlacesAbove [FiniteDimensional F Q]
    (δ : Cocycle H (cover F Q))
    (h : ∀ w : InfinitePlace Q, w.IsComplex → (belowPlace (F := F) w).IsReal →
      (δ.baseChangePullback (algebraBaseMap F (belowPlace (F := F) w).Completion)).IsTrivial) :
    RealTrivial δ := by
  intro v hv
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := Q) v
  have he : belowPlace (F := F) w = v := hw
  have hv' : (belowPlace (F := F) w).IsReal := he.symm ▸ hv
  apply (congrArg (fun z : InfinitePlace F =>
    (δ.baseChangePullback (algebraBaseMap F z.Completion)).IsTrivial) he).mp
  rcases w.isReal_or_isComplex with hr | hc
  · exact isTrivial_pullback_of_real_above δ w hr
  · exact h w hc hv'

end SplitPlace

section OpenCell

variable {F Q : Type u} [Field F] [NumberField F] [Field Q] [NumberField Q]
  [Algebra F Q] [FiniteDimensional F Q] [IsGalois F Q]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  [IsAffine (baseChanged F Q G).X.left] [IsAffine (baseChanged F Q T.toGrp).X.left]
  {X : Over (Spec (CommRingCat.of Q))} [IsAffine X.left]

private def twistedValuePoint (ξ : Cocycle G (cover F Q)) (σ : Q ≃ₐ[F] Q)
    (f : rationalPoints (baseChanged F Q G)) : rationalPoints (baseChanged F Q G) :=
  (baseChangeCoeffEquiv F Q G).symm (value (ξ.twist (baseChangeCoeffEquiv F Q G f)) σ)

private theorem RingPoint.changeRing_comp
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y) (x : RingPoint k X k) :
    Langlands.AlgebraicGeometry.PointTopology.RingPoint.changeRing (Algebra.ofId k K)
      (x ≫ f : RingPoint k Y k) =
      x.changeRing (Algebra.ofId k K) ≫ f :=
  (Category.assoc _ _ _).symm

private def CellControlAt
    (m : X ⟶ (baseChanged F Q G).X) (p : X ⟶ (baseChanged F Q T.toGrp).X)
    (ξ : Cocycle G (cover F Q)) (σ : Q ≃ₐ[F] Q)
    (w : InfinitePlace Q) (V : Set (RingPoint Q (baseChanged F Q G).X w.Completion)) : Prop :=
  ∀ f : rationalPoints (baseChanged F Q G),
    (rationalPointEquiv Q _ f).changeRing (Algebra.ofId Q w.Completion) ∈ V →
    (∃ z : RingPoint Q X w.Completion, z ≫ m =
      (rationalPointEquiv Q _ (twistedValuePoint ξ σ f)).changeRing (Algebra.ofId Q w.Completion)) ∧
    ∀ (x : RationalPoint Q X), x ≫ m = twistedValuePoint ξ σ f →
      ∀ δ : Cocycle T.toGrp (cover F Q),
        value δ σ = baseChangeCoeffEquiv F Q T.toGrp (x ≫ p) →
        (δ.baseChangePullback (Spec.algebraMap F (belowPlace (F := F) w).Completion)).IsTrivial

omit [NumberField Q] in
private theorem exists_cellControl_at_realBelow
    (hQ : Module.finrank F Q = 2) (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1)
    (hT : IsTorus T.toGrp)
    (m : X ⟶ (baseChanged F Q G).X) [IsOpenImmersion m.left]
    (p : X ⟶ (baseChanged F Q T.toGrp).X)
    (o : RationalPoint Q X) (hom : o ≫ m = 1) (hop : o ≫ p = 1)
    (ξ : Cocycle G (cover F Q)) (hξ : RealTrivial ξ)
    (w : InfinitePlace Q) (hw : w.IsComplex) (hv : (belowPlace (F := F) w).IsReal) :
    ∃ V : Set (RingPoint Q (baseChanged F Q G).X w.Completion),
      IsOpen V ∧ V.Nonempty ∧ CellControlAt m p ξ σ w V := by
  let v := belowPlace (F := F) w
  let : w.LiesOver v := ⟨rfl⟩
  let : IsScalarTower F Q w.Completion := infiniteCompletionScalarTower w
  let := infiniteCompletionNontriviallyNormedField w
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let e' := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
  let : IsAlgClosed w.Completion := Langlands.Analytic.isAlgClosed_of_ringEquiv _ e.symm
  have hd := finrank_complexCompletion_of_real v w hv hw
  let : Module.Free v.Completion w.Completion := Module.Free.of_divisionRing _ _
  let : CharZero v.Completion := charZero_of_injective_ringHom
    (algebraMap F v.Completion).injective
  let : Algebra.IsQuadraticExtension v.Completion w.Completion := ⟨hd⟩
  let : FiniteDimensional v.Completion w.Completion :=
    FiniteDimensional.of_finrank_pos (by rw [hd]; decide)
  let : IsGalois v.Completion w.Completion := Algebra.IsQuadraticExtension.isGalois _ _
  let τ := realCompletionConjugation v w hv hw
  have hτ := realCompletionConjugation_ne_one v w hv hw hQ σ hσ
  have hres := realCompletionConjugation_restrictNormal v w hv hw hQ σ hσ
  have hcτ := continuous_realCompletionConjugation v w hv hw
  let o₀ := (rationalPointEquiv Q X o).changeRing (Algebra.ofId Q w.Completion)
  have hom' : o₀ ≫ m = affinePointsBaseChangeMulEquiv F Q w.Completion G 1 := by
    rw [← RingPoint.changeRing_comp, ← rationalPointEquiv_natural, hom, ←
      affinePointsBaseChange_relativeExtend, map_one, map_one]
  have hop' : o₀ ≫ p = affinePointsBaseChangeMulEquiv F Q w.Completion T.toGrp 1 := by
    rw [← RingPoint.changeRing_comp, ← rationalPointEquiv_natural, hop, ←
      affinePointsBaseChange_relativeExtend, map_one, map_one]
  obtain ⟨V, hVo, hVn, hV⟩ := exists_localCellControl hQ σ hd τ hτ hres hcτ
    e e'.continuous e'.symm.continuous hT m p o₀ hom' hop' ξ (hξ v hv)
  refine ⟨V, hVo, hVn, fun f hf => ?_⟩
  obtain ⟨z, hz, hzc⟩ := hV f hf
  refine ⟨⟨z, hz⟩, fun x hx δ hδ => ?_⟩
  let : Mono m := Over.mono_of_mono_left _
  have heq : (rationalPointEquiv Q X x).changeRing (Algebra.ofId Q w.Completion) = z := by
    apply (cancel_mono m).mp
    rw [hz, ← RingPoint.changeRing_comp, ← rationalPointEquiv_natural, hx]
    rfl
  apply hzc δ
  rw [hδ, affinePointsBaseChange_relativeExtend, rationalPointEquiv_natural,
    RingPoint.changeRing_comp, heq]

omit [NumberField F] [NumberField Q] [IsAffine G.X.left]
  [IsAffine (baseChanged F Q G).X.left] [IsAffine X.left] in
private theorem exists_twistedValue_in_cell
    (hG : IsConnectedReductive G) (ξ : Cocycle G (cover F Q)) (σ : Q ≃ₐ[F] Q)
    (hσ : σ ≠ 1) [Infinite F]
    (m : X ⟶ (baseChanged F Q G).X) [IsOpenImmersion m.left] (o : RationalPoint Q X) :
    ∃ (f : rationalPoints (baseChanged F Q G)) (x : RationalPoint Q X),
      x ≫ m = twistedValuePoint ξ σ f := by
  have hW : IsOpen (Set.range m.left) := IsOpenImmersion.isOpen_range m.left
  have hWn : (Set.range m.left).Nonempty := ⟨_, o.left (IsLocalRing.closedPoint Q), rfl⟩
  have hd := galoisTwistedPointDensity_of_isGalois F Q G hG σ hσ (value ξ σ)
  obtain ⟨x, hx, hxD⟩ := hd.inter_open_nonempty _ hW hWn
  obtain ⟨a, y, hy⟩ := Set.mem_iUnion.mp hxD
  let a₀ : G.affinePoints (CommAlgCat.of F Q) := a
  let f := (baseChangeCoeffEquiv F Q G).symm a₀
  have hval : value (ξ.twist (baseChangeCoeffEquiv F Q G f)) σ =
      a₀⁻¹ * value ξ σ * GaloisPoint.conjugate F Q G σ a₀ := by
    have ha : baseChangeCoeffEquiv F Q G f = a₀ := (baseChangeCoeffEquiv F Q G).apply_symm_apply _
    rw [ha]
    exact congrArg (fun z : G.affinePoints (CommAlgCat.of F Q) =>
      z⁻¹ * value ξ σ * GaloisPoint.conjugate F Q G σ a₀) (Category.id_comp a₀)
  have hy' : (twistedValuePoint ξ σ f).left y = x := by
    unfold twistedValuePoint
    rw [hval]
    exact hy
  have hW' : Set.range (twistedValuePoint ξ σ f).left ⊆ Set.range m.left := by
    rintro _ ⟨y', rfl⟩
    have : Subsingleton ↥(Over.mk (𝟙 (Spec (CommRingCat.of Q)))).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum Q))
    rw [show y' = y from Subsingleton.elim _ _, hy']
    exact hx
  obtain ⟨z, hz⟩ :=
    Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCover.exists_lift_openImmersion
      m (twistedValuePoint ξ σ f) hW'
  exact ⟨f, z, hz⟩

private theorem exists_twistedCellPoint_realLocallyTrivial
    (hQ : Module.finrank F Q = 2) (hG : IsConnectedReductive G) (hT : IsTorus T.toGrp)
    (m : X ⟶ (baseChanged F Q G).X) [IsOpenImmersion m.left]
    (p : X ⟶ (baseChanged F Q T.toGrp).X)
    (o : RationalPoint Q X) (hom : o ≫ m = 1) (hop : o ≫ p = 1)
    (ξ : Cocycle G (cover F Q)) (hξ : RealTrivial ξ)
    (σ : Q ≃ₐ[F] Q) (hσ : σ ≠ 1) :
    ∃ (f : rationalPoints (baseChanged F Q G)) (x : RationalPoint Q X),
      x ≫ m = twistedValuePoint ξ σ f ∧
      ∀ δ : Cocycle T.toGrp (cover F Q),
        value δ σ = baseChangeCoeffEquiv F Q T.toGrp (x ≫ p) → RealTrivial δ := by
  classical
  let s : Set (InfinitePlace Q) := {w | w.IsComplex ∧ (belowPlace (F := F) w).IsReal}
  by_cases hs : s.Nonempty
  · have hcontrolAt (w : s) := exists_cellControl_at_realBelow hQ σ hσ hT m p o hom hop
      ξ hξ w.val w.property.1 w.property.2
    choose V hVo hVn hcontrol using hcontrolAt
    have hGQ := connectedReductiveFieldExtensionStatement F Q G hG
    obtain ⟨a, ha⟩ := exists_reductivePoint_mem_complexCompletion_opens (baseChanged F Q G)
      hGQ s hs (fun w => w.property.1) V hVo hVn
    let f := (rationalPointEquiv Q _).symm a
    have hf (w : s) :
        (rationalPointEquiv Q _ f).changeRing (Algebra.ofId Q w.val.Completion) ∈ V w := by
      simpa only [f, Equiv.apply_symm_apply] using ha w
    obtain ⟨w, hw⟩ := hs
    obtain ⟨z, hz⟩ := (hcontrol ⟨w, hw⟩ f (hf ⟨w, hw⟩)).1
    obtain ⟨a₀, ha₀⟩ := exists_point_factor_of_changeRing m _ z hz
    let x := (rationalPointEquiv Q X).symm a₀
    have hx : x ≫ m = twistedValuePoint ξ σ f := by
      apply (rationalPointEquiv Q _).injective
      rw [rationalPointEquiv_natural, show rationalPointEquiv Q X x = a₀ from
        (rationalPointEquiv Q X).apply_symm_apply a₀]
      exact ha₀
    refine ⟨f, x, hx, fun δ hδ => realTrivial_of_complexPlacesAbove δ ?_⟩
    intro w hc hr
    exact (hcontrol ⟨w, hc, hr⟩ f (hf ⟨w, hc, hr⟩)).2 x hx δ hδ
  · obtain ⟨f, x, hx⟩ := exists_twistedValue_in_cell hG ξ σ hσ m o
    exact ⟨f, x, hx, fun δ _ => realTrivial_of_complexPlacesAbove δ
      (fun w hc hr => (hs ⟨w, hc, hr⟩).elim)⟩

end OpenCell

set_option maxHeartbeats 2400000 in
/-- A cocycle trivial at the real places has a cohomologous representative
in the supplied opposite-Borel torus, still trivial at the real places. -/
theorem IsQuadraticOppositeBorelTorus.exists_realLocallyTrivialRepresentative
    {F Q : Type u} [Field F] [NumberField F] [Field Q]
    [Algebra F Q] [FiniteDimensional F Q] [IsGalois F Q]
    {G : GroupScheme (Spec (CommRingCat.of F))} {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {t : T.toGrp ⟶ G} (ht : IsQuadraticOppositeBorelTorus Q t)
    (hG : IsConnectedReductive G) (ξ : Cocycle G (cover F Q))
    (hξ : ∀ v : InfinitePlace F, v.IsReal →
      (ξ.baseChangePullback (algebraBaseMap F v.Completion)).IsTrivial) :
    ∃ δ : Cocycle T.toGrp (cover F Q), (δ.map t).Cohomologous ξ ∧
      ∀ v : InfinitePlace F, v.IsReal →
        (δ.baseChangePullback (algebraBaseMap F v.Completion)).IsTrivial := by
  let : NumberField Q := NumberField.of_module_finite F Q
  have hQ := ht.1
  have hGQ := connectedReductiveFieldExtensionStatement F Q G hG
  let b := algebraBaseMap F Q
  let GQ := (GroupScheme.baseChange b).obj G
  let TQ := (CommGroupScheme.baseChange b).obj T
  let tQ := (GroupScheme.baseChange b).map t
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom GQ.X.hom := hGQ.isAffineHom
  let : IsAffine GQ.X.left := isAffine_of_isAffineHom GQ.X.hom
  let : Smooth GQ.X.hom := hGQ.smooth
  let : IsAffineHom T.X.hom := ht.2.1.1.isRelativeTorus.isAffineHom
  let : IsAffine T.X.left := isAffine_of_isAffineHom T.X.hom
  let : IsAffine TQ.X.left := ringBaseChange_isAffine F Q T.X
  let : IsClosedImmersion t.hom.hom.left := ht.2.1.2.1
  let : Mono t.hom.hom := Over.mono_of_mono_left _
  let : IsClosedImmersion tQ.hom.hom.left := (ht.2.1.2.1.baseChange b)
  let : Mono tQ.hom.hom := Over.mono_of_mono_left _
  obtain ⟨σ, χ, hσ, hC, hU⟩ := ht.exists_dynamicData hG
  change (Gm (Spec (CommRingCat.of Q))).toGrp ⟶ GQ at χ
  let U := Dynamic.Affine.unipotentScheme (G := GQ) χ
  let V := Dynamic.Affine.unipotentScheme (G := GQ) (Dynamic.oppositeCocharacter χ)
  let : IsAffineHom U.X.hom := Dynamic.OppositeEnvelope.unipotentScheme_isAffineHom (G := GQ) χ
  let : IsAffineHom V.X.hom := Dynamic.OppositeEnvelope.unipotentScheme_isAffineHom
    (G := GQ) (Dynamic.oppositeCocharacter χ)
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  let : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  let : IsAffine (TQ.X ⊗ V.X).left := tensor_isAffine Q TQ.X V.X
  let : IsAffine (U.X ⊗ (TQ.X ⊗ V.X)).left := tensor_isAffine Q U.X _
  let m : U.X ⊗ (TQ.X ⊗ V.X) ⟶ GQ.X :=
    Dynamic.torusOppositeCell (G := GQ) (T := TQ) χ tQ
  let p : U.X ⊗ (TQ.X ⊗ V.X) ⟶ TQ.X := snd U.X (TQ.X ⊗ V.X) ≫ fst TQ.X V.X
  have hC' : (Dynamic.centralizer χ).IsRepresentedBy tQ := ⟨inferInstance, hC.symm⟩
  let hmOpen : IsOpenImmersion m.left :=
    Dynamic.isOpenImmersion_torusOppositeCell (G := GQ) (T := TQ) χ tQ hC'
  let : IsOpenImmersion m.left := hmOpen
  let o : RationalPoint Q (U.X ⊗ (TQ.X ⊗ V.X)) := lift 1 (lift 1 1)
  have hm : o ≫ m = 1 := by
    simp only [o, m, Dynamic.lift_comp_torusOppositeCell, MonObj.one_comp, mul_one]
  have hp : o ≫ p = 1 := by simp only [o, p, lift_snd_assoc, lift_fst]
  obtain ⟨f, x, hx, hxc⟩ := exists_twistedCellPoint_realLocallyTrivial (F := F) (Q := Q)
    (G := G) (T := T) hQ hG ht.2.1.1 m p o hm hp ξ hξ σ hσ
  let x₁ : rationalPoints U := x ≫ fst U.X (TQ.X ⊗ V.X)
  let x₂ : rationalPoints TQ.toGrp := x ≫ p
  let x₃ : rationalPoints V := x ≫ snd U.X (TQ.X ⊗ V.X) ≫ snd TQ.X V.X
  have hx' : lift x₁ (lift x₂ x₃) = x := by
    apply CartesianMonoidalCategory.hom_ext
    · exact lift_fst _ _
    rw [lift_snd]
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      simp only [x₂, p, Category.assoc]
    rw [lift_snd]
    simp only [x₃, Category.assoc]
  have hcell : lift x₁ (lift x₂ x₃) ≫ m = twistedValuePoint ξ σ f := by
    rw [hx']
    exact hx
  obtain ⟨δ, hcoh, hδ⟩ := exists_torusCocycle_of_torusOppositeCell (F := F) (Q := Q)
    (G := G) (T := T) (t := t) χ hQ σ hσ hU hmOpen ξ (baseChangeCoeffEquiv F Q G f)
    x₁ x₂ x₃ hcell
  have hl : RealTrivial δ := hxc δ hδ
  exact ⟨δ, hcoh, hl⟩

end Langlands.GroupScheme
