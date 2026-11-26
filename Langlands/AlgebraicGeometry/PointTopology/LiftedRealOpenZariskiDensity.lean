import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Langlands.GroupScheme.SchemeActionOrbit
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Algebra.Field.ULift
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Open-set Zariski density over the universe lift of the reals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The scheme point underlying an actual real point. -/
def underlyingLiftedRealPoint (X : Over (Spec (CommRingCat.of (ULift.{u} ℝ))))
    (p : RingPoint (ULift.{u} ℝ) X (ULift.{u} ℝ)) : X.left :=
  p.left (IsLocalRing.closedPoint (ULift.{u} ℝ))

@[simp] theorem underlyingLiftedRealPoint_comp {X Y : Over (Spec (CommRingCat.of (ULift.{u} ℝ)))}
    (f : X ⟶ Y) (p : RingPoint (ULift.{u} ℝ) X (ULift.{u} ℝ)) :
    underlyingLiftedRealPoint Y (p ≫ f) = f.left (underlyingLiftedRealPoint X p) := rfl

private theorem vanishes_of_vanishes_on_realOpen {I : Type u} [Finite I]
    (p : MvPolynomial I (ULift.{u} ℝ)) (U : Set (I → (ULift.{u} ℝ))) (hU : IsOpen U) (hne : U.Nonempty)
    (hvanish : ∀ x ∈ U, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU x hx
  have hInf (i : I) : (V i).Infinite := by
    have ho : IsOpen (ULift.up ⁻¹' V i : Set ℝ) := (hV i).1.preimage continuous_uliftUp
    obtain ⟨a, b, hab, hsub⟩ := ho.exists_Ioo_subset ⟨(x i).down, (hV i).2⟩
    exact ((Set.Ioo_infinite hab).image ULift.up_injective.injOn).mono (Set.image_subset_iff.mpr hsub)
  apply MvPolynomial.funext_set V hInf
  intro y hy
  rw [map_zero]
  exact hvanish y (hVU (fun i _ => hy i (Set.mem_univ i)))

set_option backward.isDefEq.respectTransparency false in
private theorem dense_underlyingLiftedRealPoint_polynomialSpectrum
    (I : Type u) [Finite I] (W : Set (RingPoint (ULift.{u} ℝ) (ringTest (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ))) (ULift.{u} ℝ)))
    (hW : IsOpen W) (hne : W.Nonempty) :
    Dense (underlyingLiftedRealPoint (ringTest (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ))) '' W) := by
  let X := ringTest (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ))
  let e := (spectrumAlgebraPointHomeomorph (ULift.{u} ℝ) (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ))).trans
    (AlgPoint.polynomialPointHomeomorph (R := (ULift.{u} ℝ)) (S := (ULift.{u} ℝ)) I)
  have heq (q : RingPoint (ULift.{u} ℝ) X (ULift.{u} ℝ)) :
      underlyingLiftedRealPoint X q = PrimeSpectrum.comap (MvPolynomial.eval (e q))
        (IsLocalRing.closedPoint (ULift.{u} ℝ)) := by
    have hq : spectrumAlgebraPointEquiv (ULift.{u} ℝ) (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ)) q = MvPolynomial.aeval (e q) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rfl
    have hq' : q.left = Spec.map (CommRingCat.ofHom (MvPolynomial.eval (e q))) := by
      rw [← Spec.map_preimage q.left]
      congr 1
      apply CommRingCat.hom_ext
      exact congrArg (fun f : AlgPoint (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ)) (ULift.{u} ℝ) => f.toAlgHom.toRingHom) hq
    change q.left (IsLocalRing.closedPoint (ULift.{u} ℝ)) = _
    rw [hq']
    rfl
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨p, rfl⟩ ⟨x, hx⟩
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hx
  have he : ∃ z ∈ e '' W, MvPolynomial.eval z p ≠ 0 := by
    by_contra! h
    exact hp (vanishes_of_vanishes_on_realOpen p _ (e.isOpenMap W hW) (hne.image e) h)
  obtain ⟨_, ⟨q, hq, rfl⟩, hqp⟩ := he
  refine ⟨underlyingLiftedRealPoint X q, ?_, q, hq, rfl⟩
  rw [heq]
  change (MvPolynomial.eval (e q)) p ∉ IsLocalRing.maximalIdeal (ULift.{u} ℝ)
  rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty real open in affine space has Zariski-dense underlying points. -/
theorem dense_underlyingLiftedRealPoint_affineSpace (I : Type u) [Finite I]
    (W : Set (RingPoint (ULift.{u} ℝ)
      (Over.mk (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ))) ↘ Spec (CommRingCat.of (ULift.{u} ℝ)))) (ULift.{u} ℝ))) :
    letI : IsAffine (Over.mk (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ))) ↘ Spec (CommRingCat.of (ULift.{u} ℝ)))).left :=
      IsAffine.of_isIso (AffineSpace.SpecIso I (CommRingCat.of (ULift.{u} ℝ))).hom
    IsOpen W → W.Nonempty → Dense (underlyingLiftedRealPoint _ '' W) := by
  intro hW hne
  let X := ringTest (ULift.{u} ℝ) (MvPolynomial I (ULift.{u} ℝ))
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ))) ↘ Spec (CommRingCat.of (ULift.{u} ℝ)))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ)))))
  let e : X ≅ A := Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of (ULift.{u} ℝ))).symm
    (AffineSpace.SpecIso_inv_over _)
  let F : RingPoint (ULift.{u} ℝ) X (ULift.{u} ℝ) → RingPoint (ULift.{u} ℝ) A (ULift.{u} ℝ) := fun q => q ≫ e.hom
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap (ULift.{u} ℝ) (ULift.{u} ℝ) e.hom)
  have hne' : W'.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    use q ≫ e.inv
    change (q ≫ e.inv) ≫ e.hom ∈ W
    have hqid : ((q ≫ e.inv) ≫ e.hom : RingPoint (ULift.{u} ℝ) A (ULift.{u} ℝ)) = q := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hqid.symm ▸ hq
  have hD := dense_underlyingLiftedRealPoint_polynomialSpectrum I W' hW' hne'
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  apply e.hom.left.surjective.denseRange.dense_of_mapsTo e.hom.left.continuous hD
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨F q, hq, rfl⟩

/-- Every nonempty open subset of the real points of a unirational affine real group
has Zariski-dense underlying points. -/
def LiftedRealOpenZariskiDensityStatement : Prop :=
  ∀ (G : Langlands.GroupScheme (Spec (CommRingCat.of (ULift.{u} ℝ)))) [IsAffine G.X.left],
    IsUnirational (ULift.{u} ℝ) G.X → ∀ (W : Set (RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ))),
      IsOpen W → W.Nonempty → Dense (underlyingLiftedRealPoint G.X '' W)

set_option backward.isDefEq.respectTransparency false in
theorem liftedRealOpenZariskiDensity : LiftedRealOpenZariskiDensityStatement.{u} := by
  intro G _ hG W hW hne
  obtain ⟨I, hI, U, ⟨u, hu⟩, f, hf⟩ := hG
  let := hI
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ))) ↘ Spec (CommRingCat.of (ULift.{u} ℝ)))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of (ULift.{u} ℝ)))))
  let P := openOver (ULift.{u} ℝ) A U
  let : Nonempty U := ⟨⟨u, hu⟩⟩
  let : IrreducibleSpace P.left := inferInstanceAs (IrreducibleSpace U)
  obtain ⟨V, hV, huV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := P.left) (x := (⟨u, hu⟩ : U)) (U := ⊤) (by trivial)
  let : IsAffine V := hV
  let : Nonempty V := ⟨⟨⟨u, hu⟩, huV⟩⟩
  let Q := openOver (ULift.{u} ℝ) P V
  let : Nonempty Q.left := inferInstanceAs (Nonempty V)
  let j := openOverι (ULift.{u} ℝ) P V ≫ openOverι (ULift.{u} ℝ) A U
  let g : Q ⟶ G.X := openOverι (ULift.{u} ℝ) P V ≫ f
  have hdense : DenseRange g.left := hf.comp V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
    f.left.continuous
  have hd : HasDenseRationalPoints (ULift.{u} ℝ) Q := hasDenseRationalPoints_open P V
    (hasDenseRationalPoints_open A U (hasDenseRationalPoints_affineSpace (ULift.{u} ℝ) I))
  obtain ⟨q₀, _⟩ := Set.nonempty_iUnion.mp hd.nonempty
  let q := rationalPointEquiv (ULift.{u} ℝ) Q q₀
  obtain ⟨x, hx⟩ := hne
  let : Group (RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ)) := inferInstanceAs (Group (ringTest (ULift.{u} ℝ) (ULift.{u} ℝ) ⟶ G.X))
  let y : RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ) := q ≫ g
  let h : RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ) := x * y⁻¹
  let h₀ : 𝟙_ (Over (Spec (CommRingCat.of (ULift.{u} ℝ)))) ⟶ G.X := (ringTestSelfIso (ULift.{u} ℝ)).inv ≫ h
  let e := Langlands.GroupScheme.SchemeAction.translationIso (ModObj.regular G.X) h₀
  have hh : toUnit (ringTest (ULift.{u} ℝ) (ULift.{u} ℝ)) ≫ h₀ = h := by
    rw [show toUnit (ringTest (ULift.{u} ℝ) (ULift.{u} ℝ)) = (ringTestSelfIso (ULift.{u} ℝ)).hom from toUnit_unique _ _]
    simp only [h₀, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have he : y ≫ e.hom = x := by
    change y ≫ Langlands.GroupScheme.SchemeAction.translation (ModObj.regular G.X) h₀ = _
    rw [Langlands.GroupScheme.SchemeAction.comp_translation]
    let h' : RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ) := toUnit (ringTest (ULift.{u} ℝ) (ULift.{u} ℝ)) ≫ h₀
    change h' * y = x
    rw [show h' = h from hh]
    exact inv_mul_cancel_right x y
  let F : RingPoint (ULift.{u} ℝ) Q (ULift.{u} ℝ) → RingPoint (ULift.{u} ℝ) G.X (ULift.{u} ℝ) := fun p => p ≫ (g ≫ e.hom)
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap (ULift.{u} ℝ) (ULift.{u} ℝ) (g ≫ e.hom))
  have hne' : W'.Nonempty := by
    use q
    change q ≫ g ≫ e.hom ∈ W
    rw [← Category.assoc, show q ≫ g = y from rfl, he]
    exact hx
  let J : RingPoint (ULift.{u} ℝ) Q (ULift.{u} ℝ) → RingPoint (ULift.{u} ℝ) A (ULift.{u} ℝ) := fun p => p ≫ j
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι))
  let : ContinuousInv₀ (ULift.{u} ℝ) := ⟨fun x hx => by
    have h : x.down ≠ 0 := fun hz => hx (ULift.down_injective hz)
    exact continuous_uliftUp.continuousAt.comp
      ((continuousAt_inv₀ h).comp continuous_uliftDown.continuousAt)⟩
  have hJo : IsOpenMap J := by
    have h := isOpenEmbedding_schemePointMap (ULift.{u} ℝ) (ULift.{u} ℝ) j
    change @IsOpenEmbedding _ _ (schemePointTopology (ULift.{u} ℝ) Q (ULift.{u} ℝ)) (schemePointTopology (ULift.{u} ℝ) A (ULift.{u} ℝ)) J at h
    rw [schemePointTopology_eq_affine (ULift.{u} ℝ) Q (ULift.{u} ℝ), schemePointTopology_eq_affine (ULift.{u} ℝ) A (ULift.{u} ℝ)] at h
    exact h.isOpenMap
  have hD := dense_underlyingLiftedRealPoint_affineSpace I (J '' W') (hJo W' hW') (hne'.image J)
  have hDW : Dense (underlyingLiftedRealPoint Q '' W') := by
    apply (hD.preimage j.left.isOpenEmbedding.isOpenMap).mono
    intro z hz
    change j.left z ∈ underlyingLiftedRealPoint A '' (J '' W') at hz
    obtain ⟨_, ⟨p, hp, rfl⟩, heq⟩ := hz
    have hqz : underlyingLiftedRealPoint Q p = z := j.left.isOpenEmbedding.injective heq
    exact ⟨p, hp, hqz⟩
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hF : DenseRange (g ≫ e.hom).left :=
    e.hom.left.surjective.denseRange.comp hdense e.hom.left.continuous
  apply hF.dense_of_mapsTo (g ≫ e.hom).left.continuous hDW
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨F p, hp, rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
