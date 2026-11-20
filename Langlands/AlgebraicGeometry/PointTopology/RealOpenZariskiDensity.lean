import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Langlands.GroupScheme.SchemeActionOrbit
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Zariski density of real open sets in unirational groups -/

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The scheme point underlying an actual real point. -/
def underlyingRealPoint (X : Over (Spec (CommRingCat.of ℝ)))
    (p : RingPoint ℝ X ℝ) : X.left :=
  p.left (IsLocalRing.closedPoint ℝ)

@[simp] theorem underlyingRealPoint_comp {X Y : Over (Spec (CommRingCat.of ℝ))}
    (f : X ⟶ Y) (p : RingPoint ℝ X ℝ) :
    underlyingRealPoint Y (p ≫ f) = f.left (underlyingRealPoint X p) := rfl

private theorem vanishes_of_vanishes_on_realOpen {I : Type} [Finite I]
    (p : MvPolynomial I ℝ) (U : Set (I → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (hvanish : ∀ x ∈ U, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU x hx
  choose a b hab hsub using fun i => (hV i).1.exists_Ioo_subset ⟨x i, (hV i).2⟩
  apply MvPolynomial.funext_set (fun i => Set.Ioo (a i) (b i)) (fun i => Set.Ioo_infinite (hab i))
  intro y hy
  rw [map_zero]
  exact hvanish y (hVU (fun i hi => hsub i (hy i hi)))

set_option backward.isDefEq.respectTransparency false in
private theorem dense_underlyingRealPoint_polynomialSpectrum
    (I : Type) [Finite I] (W : Set (RingPoint ℝ (ringTest ℝ (MvPolynomial I ℝ)) ℝ))
    (hW : IsOpen W) (hne : W.Nonempty) :
    Dense (underlyingRealPoint (ringTest ℝ (MvPolynomial I ℝ)) '' W) := by
  let X := ringTest ℝ (MvPolynomial I ℝ)
  let e := (spectrumAlgebraPointHomeomorph ℝ ℝ (MvPolynomial I ℝ)).trans
    (AlgPoint.polynomialPointHomeomorph (R := ℝ) (S := ℝ) I)
  have heq (q : RingPoint ℝ X ℝ) :
      underlyingRealPoint X q = PrimeSpectrum.comap (MvPolynomial.eval (e q))
        (IsLocalRing.closedPoint ℝ) := by
    have hq : spectrumAlgebraPointEquiv ℝ ℝ (MvPolynomial I ℝ) q = MvPolynomial.aeval (e q) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rfl
    have hq' : q.left = Spec.map (CommRingCat.ofHom (MvPolynomial.eval (e q))) := by
      rw [← Spec.map_preimage q.left]
      congr 1
      apply CommRingCat.hom_ext
      exact congrArg (fun f : AlgPoint ℝ (MvPolynomial I ℝ) ℝ => f.toAlgHom.toRingHom) hq
    change q.left (IsLocalRing.closedPoint ℝ) = _
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
  refine ⟨underlyingRealPoint X q, ?_, q, hq, rfl⟩
  rw [heq]
  change (MvPolynomial.eval (e q)) p ∉ IsLocalRing.maximalIdeal ℝ
  rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

set_option backward.isDefEq.respectTransparency false in
/-- Any nonempty real open subset of affine space has Zariski-dense underlying points. -/
theorem dense_underlyingRealPoint_affineSpace (I : Type) [Finite I]
    (W : Set (RingPoint ℝ
      (Over.mk (𝔸(I; Spec (CommRingCat.of ℝ)) ↘ Spec (CommRingCat.of ℝ))) ℝ)) :
    letI : IsAffine (Over.mk (𝔸(I; Spec (CommRingCat.of ℝ)) ↘ Spec (CommRingCat.of ℝ))).left :=
      IsAffine.of_isIso (AffineSpace.SpecIso I (CommRingCat.of ℝ)).hom
    IsOpen W → W.Nonempty → Dense (underlyingRealPoint _ '' W) := by
  intro hW hne
  let X := ringTest ℝ (MvPolynomial I ℝ)
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of ℝ)) ↘ Spec (CommRingCat.of ℝ))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of ℝ))))
  let e : X ≅ A := Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of ℝ)).symm
    (AffineSpace.SpecIso_inv_over _)
  let F : RingPoint ℝ X ℝ → RingPoint ℝ A ℝ := fun q => q ≫ e.hom
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap ℝ ℝ e.hom)
  have hne' : W'.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    use q ≫ e.inv
    change (q ≫ e.inv) ≫ e.hom ∈ W
    have hqid : ((q ≫ e.inv) ≫ e.hom : RingPoint ℝ A ℝ) = q := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hqid.symm ▸ hq
  have hD := dense_underlyingRealPoint_polynomialSpectrum I W' hW' hne'
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  apply e.hom.left.surjective.denseRange.dense_of_mapsTo e.hom.left.continuous hD
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨F q, hq, rfl⟩

/-- Every nonempty open subset of the real points of a unirational affine real group
has Zariski-dense underlying points. -/
def RealOpenZariskiDensityStatement : Prop :=
  ∀ (G : Langlands.GroupScheme (Spec (CommRingCat.of ℝ))) [IsAffine G.X.left],
    IsUnirational ℝ G.X → ∀ (W : Set (RingPoint ℝ G.X ℝ)),
      IsOpen W → W.Nonempty → Dense (underlyingRealPoint G.X '' W)

set_option backward.isDefEq.respectTransparency false in
theorem realOpenZariskiDensity : RealOpenZariskiDensityStatement := by
  intro G _ hG W hW hne
  obtain ⟨I, hI, U, ⟨u, hu⟩, f, hf⟩ := hG
  let := hI
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of ℝ)) ↘ Spec (CommRingCat.of ℝ))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of ℝ))))
  let P := openOver ℝ A U
  let : Nonempty U := ⟨⟨u, hu⟩⟩
  let : IrreducibleSpace P.left := inferInstanceAs (IrreducibleSpace U)
  obtain ⟨V, hV, huV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := P.left) (x := (⟨u, hu⟩ : U)) (U := ⊤) (by trivial)
  let : IsAffine V := hV
  let : Nonempty V := ⟨⟨⟨u, hu⟩, huV⟩⟩
  let Q := openOver ℝ P V
  let : Nonempty Q.left := inferInstanceAs (Nonempty V)
  let j := openOverι ℝ P V ≫ openOverι ℝ A U
  let g : Q ⟶ G.X := openOverι ℝ P V ≫ f
  have hdense : DenseRange g.left := hf.comp V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
    f.left.continuous
  have hd : HasDenseRationalPoints ℝ Q := hasDenseRationalPoints_open P V
    (hasDenseRationalPoints_open A U (hasDenseRationalPoints_affineSpace ℝ I))
  obtain ⟨q₀, _⟩ := Set.nonempty_iUnion.mp hd.nonempty
  let q := rationalPointEquiv ℝ Q q₀
  obtain ⟨x, hx⟩ := hne
  let : Group (RingPoint ℝ G.X ℝ) := inferInstanceAs (Group (ringTest ℝ ℝ ⟶ G.X))
  let y : RingPoint ℝ G.X ℝ := q ≫ g
  let h : RingPoint ℝ G.X ℝ := x * y⁻¹
  let h₀ : 𝟙_ (Over (Spec (CommRingCat.of ℝ))) ⟶ G.X := (ringTestSelfIso ℝ).inv ≫ h
  let e := Langlands.GroupScheme.SchemeAction.translationIso (ModObj.regular G.X) h₀
  have hh : toUnit (ringTest ℝ ℝ) ≫ h₀ = h := by
    rw [show toUnit (ringTest ℝ ℝ) = (ringTestSelfIso ℝ).hom from toUnit_unique _ _]
    simp only [h₀, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have he : y ≫ e.hom = x := by
    change y ≫ Langlands.GroupScheme.SchemeAction.translation (ModObj.regular G.X) h₀ = _
    rw [Langlands.GroupScheme.SchemeAction.comp_translation]
    let h' : RingPoint ℝ G.X ℝ := toUnit (ringTest ℝ ℝ) ≫ h₀
    change h' * y = x
    rw [show h' = h from hh]
    exact inv_mul_cancel_right x y
  let F : RingPoint ℝ Q ℝ → RingPoint ℝ G.X ℝ := fun p => p ≫ (g ≫ e.hom)
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap ℝ ℝ (g ≫ e.hom))
  have hne' : W'.Nonempty := by
    use q
    change q ≫ g ≫ e.hom ∈ W
    rw [← Category.assoc, show q ≫ g = y from rfl, he]
    exact hx
  let J : RingPoint ℝ Q ℝ → RingPoint ℝ A ℝ := fun p => p ≫ j
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι))
  have hJo : IsOpenMap J := by
    have h := isOpenEmbedding_schemePointMap ℝ ℝ j
    change @IsOpenEmbedding _ _ (schemePointTopology ℝ Q ℝ) (schemePointTopology ℝ A ℝ) J at h
    rw [schemePointTopology_eq_affine ℝ Q ℝ, schemePointTopology_eq_affine ℝ A ℝ] at h
    exact h.isOpenMap
  have hD := dense_underlyingRealPoint_affineSpace I (J '' W') (hJo W' hW') (hne'.image J)
  have hDW : Dense (underlyingRealPoint Q '' W') := by
    apply (hD.preimage j.left.isOpenEmbedding.isOpenMap).mono
    intro z hz
    change j.left z ∈ underlyingRealPoint A '' (J '' W') at hz
    obtain ⟨_, ⟨p, hp, rfl⟩, heq⟩ := hz
    have hqz : underlyingRealPoint Q p = z := j.left.isOpenEmbedding.injective heq
    exact ⟨p, hp, hqz⟩
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hF : DenseRange (g ≫ e.hom).left :=
    e.hom.left.surjective.denseRange.comp hdense e.hom.left.continuous
  apply hF.dense_of_mapsTo (g ≫ e.hom).left.continuous hDW
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨F p, hp, rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
