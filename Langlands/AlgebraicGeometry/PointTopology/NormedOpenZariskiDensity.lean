import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.AlgebraicGeometry.PointTopology.SchemeTopologyExistenceProofs
import Langlands.AlgebraicGeometry.PointTopology.UnirationalDensity
import Langlands.GroupScheme.SchemeActionOrbit
import Mathlib.Analysis.Normed.Field.Basic

/-! # Zariski density of open sets of points over normed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Topology
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [NontriviallyNormedField k]

/-- The scheme point underlying a rational point over a normed field. -/
def underlyingNormedPoint (X : Over (Spec (CommRingCat.of k)))
    (p : RingPoint k X k) : X.left :=
  p.left (IsLocalRing.closedPoint k)

@[simp] theorem underlyingNormedPoint_comp {X Y : Over (Spec (CommRingCat.of k))}
    (f : X ⟶ Y) (p : RingPoint k X k) :
    underlyingNormedPoint Y (p ≫ f) = f.left (underlyingNormedPoint X p) := rfl

private theorem vanishes_of_vanishes_on_open {I : Type u} [Finite I]
    (p : MvPolynomial I k) (U : Set (I → k)) (hU : IsOpen U) (hne : U.Nonempty)
    (hvanish : ∀ x ∈ U, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU x hx
  have hInf (i : I) : (V i).Infinite :=
    infinite_of_mem_nhds (x i) ((hV i).1.mem_nhds (hV i).2)
  apply MvPolynomial.funext_set V hInf
  intro y hy
  rw [map_zero]
  exact hvanish y (hVU (fun i _ => hy i (Set.mem_univ i)))

set_option backward.isDefEq.respectTransparency false in
private theorem dense_underlyingNormedPoint_polynomialSpectrum
    (I : Type u) [Finite I] (W : Set (RingPoint k (ringTest k (MvPolynomial I k)) k))
    (hW : IsOpen W) (hne : W.Nonempty) :
    Dense (underlyingNormedPoint (ringTest k (MvPolynomial I k)) '' W) := by
  let X := ringTest k (MvPolynomial I k)
  let e := (spectrumAlgebraPointHomeomorph k k (MvPolynomial I k)).trans
    (AlgPoint.polynomialPointHomeomorph (R := k) (S := k) I)
  have heq (q : RingPoint k X k) :
      underlyingNormedPoint X q = PrimeSpectrum.comap (MvPolynomial.eval (e q))
        (IsLocalRing.closedPoint k) := by
    have hq : spectrumAlgebraPointEquiv k k (MvPolynomial I k) q = MvPolynomial.aeval (e q) := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      rfl
    have hq' : q.left = Spec.map (CommRingCat.ofHom (MvPolynomial.eval (e q))) := by
      rw [← Spec.map_preimage q.left]
      congr 1
      apply CommRingCat.hom_ext
      exact congrArg (fun f : AlgPoint k (MvPolynomial I k) k => f.toAlgHom.toRingHom) hq
    change q.left (IsLocalRing.closedPoint k) = _
    rw [hq']
    rfl
  apply PrimeSpectrum.isTopologicalBasis_basic_opens.dense_iff.mpr
  rintro _ ⟨p, rfl⟩ ⟨x, hx⟩
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hx
  have he : ∃ z ∈ e '' W, MvPolynomial.eval z p ≠ 0 := by
    by_contra! h
    exact hp (vanishes_of_vanishes_on_open p _ (e.isOpenMap W hW) (hne.image e) h)
  obtain ⟨_, ⟨q, hq, rfl⟩, hqp⟩ := he
  refine ⟨underlyingNormedPoint X q, ?_, q, hq, rfl⟩
  rw [heq]
  change (MvPolynomial.eval (e q)) p ∉ IsLocalRing.maximalIdeal k
  rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]

set_option backward.isDefEq.respectTransparency false in
/-- A nonempty analytic open in affine space has Zariski-dense underlying points. -/
theorem dense_underlyingNormedPoint_affineSpace (I : Type u) [Finite I]
    (W : Set (RingPoint k
      (Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))) k)) :
    letI : IsAffine (Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))).left :=
      IsAffine.of_isIso (AffineSpace.SpecIso I (CommRingCat.of k)).hom
    IsOpen W → W.Nonempty → Dense (underlyingNormedPoint _ '' W) := by
  intro hW hne
  let X := ringTest k (MvPolynomial I k)
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of k))))
  let e : X ≅ A := Over.isoMk (AffineSpace.SpecIso I (CommRingCat.of k)).symm
    (AffineSpace.SpecIso_inv_over _)
  let F : RingPoint k X k → RingPoint k A k := fun q => q ≫ e.hom
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap k k e.hom)
  have hne' : W'.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    use q ≫ e.inv
    change (q ≫ e.inv) ≫ e.hom ∈ W
    have hqid : ((q ≫ e.inv) ≫ e.hom : RingPoint k A k) = q := by
      rw [Category.assoc, e.inv_hom_id, Category.comp_id]
    exact hqid.symm ▸ hq
  have hD := dense_underlyingNormedPoint_polynomialSpectrum I W' hW' hne'
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  apply e.hom.left.surjective.denseRange.dense_of_mapsTo e.hom.left.continuous hD
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨F q, hq, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every nonempty analytic open subset of a unirational affine group's rational
points has Zariski-dense underlying points. -/
theorem dense_underlyingNormedPoint_of_unirational
    (G : Langlands.GroupScheme (Spec (CommRingCat.of k))) [IsAffine G.X.left]
    (hG : IsUnirational k G.X) (W : Set (RingPoint k G.X k))
    (hW : IsOpen W) (hne : W.Nonempty) : Dense (underlyingNormedPoint G.X '' W) := by
  obtain ⟨I, hI, U, ⟨u, hu⟩, f, hf⟩ := hG
  let := hI
  let A := Over.mk (𝔸(I; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  let : IsAffine A.left := inferInstanceAs (IsAffine (𝔸(I; Spec (CommRingCat.of k))))
  let P := openOver k A U
  let : Nonempty U := ⟨⟨u, hu⟩⟩
  let : IrreducibleSpace P.left := inferInstanceAs (IrreducibleSpace U)
  obtain ⟨V, hV, huV, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := P.left) (x := (⟨u, hu⟩ : U)) (U := ⊤) (by trivial)
  let : IsAffine V := hV
  let : Nonempty V := ⟨⟨⟨u, hu⟩, huV⟩⟩
  let Q := openOver k P V
  let : Nonempty Q.left := inferInstanceAs (Nonempty V)
  let j := openOverι k P V ≫ openOverι k A U
  let g : Q ⟶ G.X := openOverι k P V ≫ f
  have hdense : DenseRange g.left := hf.comp V.ι.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace
    f.left.continuous
  have hd : HasDenseRationalPoints k Q := hasDenseRationalPoints_open P V
    (hasDenseRationalPoints_open A U (hasDenseRationalPoints_affineSpace k I))
  obtain ⟨q₀, _⟩ := Set.nonempty_iUnion.mp hd.nonempty
  let q := rationalPointEquiv k Q q₀
  obtain ⟨x, hx⟩ := hne
  let : Group (RingPoint k G.X k) := inferInstanceAs (Group (ringTest k k ⟶ G.X))
  let y : RingPoint k G.X k := q ≫ g
  let h : RingPoint k G.X k := x * y⁻¹
  let h₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X := (ringTestSelfIso k).inv ≫ h
  let e := Langlands.GroupScheme.SchemeAction.translationIso (ModObj.regular G.X) h₀
  have hh : toUnit (ringTest k k) ≫ h₀ = h := by
    rw [show toUnit (ringTest k k) = (ringTestSelfIso k).hom from toUnit_unique _ _]
    simp only [h₀, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have he : y ≫ e.hom = x := by
    change y ≫ Langlands.GroupScheme.SchemeAction.translation (ModObj.regular G.X) h₀ = _
    rw [Langlands.GroupScheme.SchemeAction.comp_translation]
    let h' : RingPoint k G.X k := toUnit (ringTest k k) ≫ h₀
    change h' * y = x
    rw [show h' = h from hh]
    exact inv_mul_cancel_right x y
  let F : RingPoint k Q k → RingPoint k G.X k := fun p => p ≫ (g ≫ e.hom)
  let W' := F ⁻¹' W
  have hW' : IsOpen W' := hW.preimage (continuous_affineSchemePointMap k k (g ≫ e.hom))
  have hne' : W'.Nonempty := by
    use q
    change q ≫ g ≫ e.hom ∈ W
    rw [← Category.assoc, show q ≫ g = y from rfl, he]
    exact hx
  let J : RingPoint k Q k → RingPoint k A k := fun p => p ≫ j
  let : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion (V.ι ≫ U.ι))
  have hJo : IsOpenMap J := by
    have h := isOpenEmbedding_schemePointMap k k j
    change @IsOpenEmbedding _ _ (schemePointTopology k Q k) (schemePointTopology k A k) J at h
    rw [schemePointTopology_eq_affine k Q k, schemePointTopology_eq_affine k A k] at h
    exact h.isOpenMap
  have hD := dense_underlyingNormedPoint_affineSpace I (J '' W') (hJo W' hW') (hne'.image J)
  have hDW : Dense (underlyingNormedPoint Q '' W') := by
    apply (hD.preimage j.left.isOpenEmbedding.isOpenMap).mono
    intro z hz
    change j.left z ∈ underlyingNormedPoint A '' (J '' W') at hz
    obtain ⟨_, ⟨p, hp, rfl⟩, heq⟩ := hz
    have hqz : underlyingNormedPoint Q p = z := j.left.isOpenEmbedding.injective heq
    exact ⟨p, hp, hqz⟩
  let : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have hF : DenseRange (g ≫ e.hom).left :=
    e.hom.left.surjective.denseRange.comp hdense e.hom.left.continuous
  apply hF.dense_of_mapsTo (g ≫ e.hom).left.continuous hDW
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨F p, hp, rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
