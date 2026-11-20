import Langlands.AlgebraicGeometry.PointTopology.CompleteFieldSmoothOpenProof
import Langlands.AlgebraicGeometry.PointTopology.RationalPointGroups
import Langlands.GroupScheme.Lie.InnerAdjoint
import Langlands.GroupScheme.Lie.RegularTorusDescent
import Langlands.GroupScheme.Lie.RegularTorusSlice
import Langlands.GroupScheme.Lie.ScalarExtensionCoordinates
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Local approximation of real maximal tori by rational maximal tori -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.AlgebraicGeometry.TangentSmoothness
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

open _root_.Langlands.GroupScheme.Lie MatrixRepresentation

set_option backward.isDefEq.respectTransparency false

section Coordinates

variable (k : Type) [Field k] (n : Type)

private abbrev coeffSpace := coefficientSpace n (CommRingCat.of k)

private def coeffSpaceIso : ringTest k (MvPolynomial (ULift n) k) ≅ coeffSpace k n :=
  Over.isoMk (AffineSpace.SpecIso (ULift n) (CommRingCat.of k)).symm
    (AffineSpace.SpecIso_inv_over _)

private def coeffPointHomeomorph [TopologicalSpace k] [IsTopologicalRing k] :
    RingPoint k (coeffSpace k n) k ≃ₜ (n → k) :=
  (affineSchemePointIsoHomeomorph k k (coeffSpaceIso k n).symm).trans
    ((spectrumAlgebraPointHomeomorph k k (MvPolynomial (ULift n) k)).trans
      ((AlgPoint.polynomialPointHomeomorph (R := k) (S := k) (ULift n)).trans
        (Homeomorph.piCongrLeft (Y := fun _ : n => k) Equiv.ulift)))

private theorem coeffPointHomeomorph_apply [TopologicalSpace k] [IsTopologicalRing k]
    (q : RingPoint k (coeffSpace k n) k) (i : n) :
    coeffPointHomeomorph k n q i =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom (coefficientCoordinates q i) := by
  let e := coeffSpaceIso k n
  let q' : RingPoint k (ringTest k (MvPolynomial (ULift n) k)) k := q ≫ e.inv
  have he : affineSchemePointIsoHomeomorph k k e.symm q = q' :=
    affineSchemePointIsoHomeomorph_apply k k e.symm q
  change spectrumAlgebraPointHomeomorph k k (MvPolynomial (ULift n) k)
    (affineSchemePointIsoHomeomorph k k e.symm q) (MvPolynomial.X (ULift.up i)) = _
  rw [he]
  change (Spec.preimage q'.left).hom (MvPolynomial.X (ULift.up i)) = _
  have hq : q' ≫ e.hom = q := by
    change (q ≫ e.inv) ≫ e.hom = q
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hq, coefficientCoordinates_comp]
  change _ = (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (q'.left.appTop ((AffineSpace.SpecIso (ULift n) (CommRingCat.of k)).inv.appTop
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i))))
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  have h := (CategoryTheory.ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (Spec.preimage q'.left))
      (MvPolynomial.X (ULift.up i))).symm
  rw [Spec.map_preimage] at h
  exact (Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _).symm.trans
    (congrArg (fun a => (Scheme.ΓSpecIso (CommRingCat.of k)).hom a) h.symm)

private theorem coeffPointHomeomorph_constant [TopologicalSpace k] [IsTopologicalRing k]
    (t : n → k) : coeffPointHomeomorph k n
      (rationalPointEquiv k (coeffSpace k n) (constantCoefficientPoint t)) = t := by
  funext i
  rw [coeffPointHomeomorph_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    ((rationalPointEquiv k _ (constantCoefficientPoint t)).left.appTop
      (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i))) = t i
  rw [rationalPointEquiv_left]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (coefficientCoordinates (constantCoefficientPoint t) i) = _
  rw [constantCoefficientPoint, coefficientCoordinates_coefficientPoint]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of k)) _

end Coordinates

section Slice

variable {k : Type} [NontriviallyNormedField k] [CompleteSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [Smooth G.X.hom] {d r : ℕ} (c : FiniteCoordinates G d)

omit [CompleteSpace k] [IsAffineHom G.X.hom] [IsAffine G.X.left] [Smooth G.X.hom] in
private theorem constantPoint_eq_rationalPointEquiv (g : RationalPoint k G.X) :
    G.constantPoint g (ringTest k k) = rationalPointEquiv k G.X g := by
  apply RingPoint.ext
  change (ringTest k k).hom ≫ g.left = (rationalPointEquiv k G.X g).left
  rw [rationalPointEquiv_left]
  change Spec.algebraMap k k ≫ g.left = g.left
  simp [Spec.algebraMap]

omit [CompleteSpace k] [IsAffine G.X.left] [Smooth G.X.hom] in
private theorem coeffPointHomeomorph_sliceMap (B : Matrix (Fin d) (Fin r) k)
    (g : RingPoint k G.X k) (x : RingPoint k (coeffSpace k (Fin r)) k) :
    coeffPointHomeomorph k (Fin d) (lift g x ≫ sliceMap (adjointRepresentation c) B) =
      c.equiv (.of (CommRingCat.of k) k)
        (targetMapLinear (G.innerIso ((rationalPointEquiv k G.X).symm g)).hom k
          ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ coeffPointHomeomorph k (Fin r) x))) := by
  let S := CommAlgCat.of (CommRingCat.of k) k
  have hx := affineCoordinates_sliceMap (adjointRepresentation c) B S g x
  have hB : B.map (algebraMap k k) = B := by ext; simp
  rw [hB] at hx
  have hc : coeffPointHomeomorph k (Fin d) (lift g x ≫ sliceMap (adjointRepresentation c) B) =
      (adjointRepresentation c).affineAction S g (B *ᵥ coeffPointHomeomorph k (Fin r) x) := by
    rw [MatrixRepresentation.affineAction_apply]
    funext i
    rw [coeffPointHomeomorph_apply]
    have hx' : coeffPointHomeomorph k (Fin r) x = fun j =>
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom (coefficientCoordinates x j) := by
      funext j
      exact coeffPointHomeomorph_apply k _ x j
    rw [hx']
    exact congrFun hx i
  rw [hc, targetMapLinear_innerIso]
  have hg : G.constantPoint ((rationalPointEquiv k G.X).symm g)
      ((algSpec (CommRingCat.of k)).obj (op S)) = g :=
    (constantPoint_eq_rationalPointEquiv ((rationalPointEquiv k G.X).symm g)).trans
      (Equiv.apply_symm_apply _ _)
  change _ = c.equiv S (adjoint G k
    (G.constantPoint ((rationalPointEquiv k G.X).symm g) ((algSpec (CommRingCat.of k)).obj (op S)))
    ((c.equiv S).symm (B *ᵥ coeffPointHomeomorph k (Fin r) x)))
  rw [hg]
  simpa only [LinearEquiv.apply_symm_apply] using
    (adjointRepresentation_affineAction c S g ((c.equiv S).symm
      (B *ᵥ coeffPointHomeomorph k (Fin r) x)))

private theorem exists_regularSliceImage_open (B : Matrix (Fin d) (Fin r) k)
    (P : MvPolynomial (Fin r) k) (t : Fin r → k) (htP : MvPolynomial.eval t P ≠ 0)
    (ht : ∀ v : Fin d → k, ∃ (ξ : lieKernel G k) (s : Fin r → k),
      (adjointRepresentation c).tangentMatrix k ξ *ᵥ (B *ᵥ t) + B *ᵥ s = v)
    (U : Set (RingPoint k G.X k)) (hU : IsOpen U)
    (h1 : rationalPointEquiv k G.X (1 : RationalPoint k G.X) ∈ U) :
    ∃ W : Set (Fin d → k), IsOpen W ∧ W.Nonempty ∧ ∀ v ∈ W,
      ∃ (g : RingPoint k G.X k), g ∈ U ∧ ∃ s : Fin r → k,
        MvPolynomial.eval s P ≠ 0 ∧
        c.equiv (.of (CommRingCat.of k) k)
          (targetMapLinear (G.innerIso ((rationalPointEquiv k G.X).symm g)).hom k
            ((c.equiv (.of (CommRingCat.of k) k)).symm (B *ᵥ s))) = v := by
  let A := coeffSpace k (Fin r)
  let L := G.X ⊗ A
  let F := sliceMap (adjointRepresentation c) B
  let z := slicePoint (G := G) t
  let : IsAffine L.left := tensor_isAffine k G.X A
  let : Smooth L.hom := smooth_tensor _ _ inferInstance
    (inferInstanceAs (Smooth (AffineSpace (ULift (Fin r)) (Spec (CommRingCat.of k)) ↘ _)))
  let : LocallyOfFiniteType (coeffSpace k (Fin d)).hom :=
    inferInstanceAs (LocallyOfFiniteType (AffineSpace (ULift (Fin d)) (Spec (CommRingCat.of k)) ↘ _))
  let : LocallyOfFinitePresentation F.left := locallyOfFinitePresentation_of_comp_eq F.left (Over.w F)
  have hsm : z.left (IsLocalRing.closedPoint k) ∈ F.left.smoothLocus :=
    mem_smoothLocus_of_isTangentSurjectiveAt F.left (Over.w F) (Over.w z)
      (isTangentSurjectiveAt_sliceMap (adjointRepresentation c) B t ht)
  obtain ⟨V, hV, hzV, hVs⟩ := exists_isAffineOpen_mem_and_subset hsm
  let : IsAffine V := hV
  let Q := openOver k L V
  let j := openOverι k L V
  let f : Q ⟶ coeffSpace k (Fin d) := j ≫ F
  let : Smooth f.left := by
    change Smooth (V.ι ≫ F.left)
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_unique (fun u _ => hVs u.property)
  let W' : Set (RingPoint k Q k) := {q | (q ≫ j ≫ fst G.X A) ∈ U ∧
    MvPolynomial.eval (coeffPointHomeomorph k (Fin r) (q ≫ j ≫ snd G.X A)) P ≠ 0}
  have hW' : IsOpen W' := by
    refine (hU.preimage (continuous_affineSchemePointMap k k (j ≫ fst G.X A))).inter ?_
    apply isOpen_ne_fun _ continuous_const
    exact (MvPolynomial.continuous_eval P).comp
      ((coeffPointHomeomorph k (Fin r)).continuous.comp
        (continuous_affineSchemePointMap k k (j ≫ snd G.X A)))
  let z' := rationalPointEquiv k L z
  have hz' : Set.range z'.left ⊆ V := by
    rintro _ ⟨a, rfl⟩
    have ha : a = IsLocalRing.closedPoint k :=
      @Subsingleton.elim (PrimeSpectrum k) inferInstance _ _
    change (rationalPointEquiv k L z).left a ∈ V
    rw [rationalPointEquiv_left, ha]
    exact hzV
  let q : RingPoint k Q k := relativeOpenLift k z' V hz'
  have hq : q ≫ j = z' := relativeOpenLift_fac k z' V hz'
  have hqW : q ∈ W' := by
    constructor
    · rw [← Category.assoc, hq, ← rationalPointEquiv_natural]
      change rationalPointEquiv k G.X (lift (1 : RationalPoint k G.X)
        (constantCoefficientPoint t) ≫ fst G.X A) ∈ U
      rwa [lift_fst]
    · rw [← Category.assoc, hq, ← rationalPointEquiv_natural]
      change MvPolynomial.eval (coeffPointHomeomorph k (Fin r)
        (rationalPointEquiv k A (lift (1 : RationalPoint k G.X) (constantCoefficientPoint t) ≫
          snd G.X A))) P ≠ 0
      rwa [lift_snd, coeffPointHomeomorph_constant]
  let fvec : RingPoint k Q k → (Fin d → k) := fun q => coeffPointHomeomorph k _ (q ≫ f)
  have hfvec : IsOpenMap fvec := (coeffPointHomeomorph k (Fin d)).isOpenMap.comp
    (isOpenMap_affineSmoothPointMap k f)
  refine ⟨fvec '' W', hfvec _ hW', ⟨_, q, hqW, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  let g : RingPoint k G.X k := s ≫ j ≫ fst G.X A
  let x : RingPoint k A k := s ≫ j ≫ snd G.X A
  refine ⟨g, hs.1, coeffPointHomeomorph k (Fin r) x, hs.2, ?_⟩
  have hs' : lift g x = s ≫ j := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (Category.assoc _ _ _).symm
    · rw [lift_snd]
      exact (Category.assoc _ _ _).symm
  rw [← coeffPointHomeomorph_sliceMap c B g x, hs']
  change coeffPointHomeomorph k (Fin d) ((s ≫ j) ≫ F) = _
  rw [Category.assoc]

end Slice

private theorem finiteCoordinates_kernelFieldExtension {k K : Type} [Field k] [Field K]
    [Algebra k K] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {d : ℕ} (c : FiniteCoordinates G d) (X : lieKernel G k) :
    (c.baseChange k K).equiv (.of (CommRingCat.of K) K)
      (Additive.ofMul (kernelFieldExtension (K := K) G X)) =
      fun i => algebraMap k K (c.equiv (.of (CommRingCat.of k) k) (Additive.ofMul X) i) := by
  have h : kernelBaseChangeEquiv k K G K (kernelFieldExtension (K := K) G X) =
      lieKernelMap G (Algebra.ofId k K) X := (kernelBaseChangeEquiv k K G K).apply_symm_apply _
  rw [FiniteCoordinates.baseChange_equiv_apply, kernelBaseChangeLinearEquiv_ofMul, h]
  exact c.naturality (CommAlgCat.ofHom (Algebra.ofId k K)) (Additive.ofMul X)

private theorem exists_kernelFieldExtension_eq_of_coordinates
    {k K : Type} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {d : ℕ} (c : FiniteCoordinates G d) (v : Fin d → k)
    (Z : Additive (lieKernel ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) K))
    (hZ : (c.baseChange k K).equiv (.of (CommRingCat.of K) K) Z =
      fun i => algebraMap k K (v i)) :
    ∃ X : lieKernel G k, kernelFieldExtension (K := K) G X = Z.toMul := by
  let e := c.equiv (.of (CommRingCat.of k) k)
  let X := (e.symm v).toMul
  have hX := finiteCoordinates_kernelFieldExtension (K := K) c X
  change _ = (fun i => algebraMap k K (e (e.symm v) i)) at hX
  rw [LinearEquiv.apply_symm_apply] at hX
  exact ⟨X, Additive.ofMul.injective
    (((c.baseChange k K).equiv (.of (CommRingCat.of K) K)).injective (hX.trans hZ.symm))⟩

/-- A real maximal torus of a rational connected reductive group is conjugate to a
rational maximal torus by an element of any prescribed real identity neighborhood. -/
def RealMaximalTorusApproximationStatement : Prop :=
  ∀ (G : GroupScheme (Spec (CommRingCat.of ℚ))) [IsAffine G.X.left],
    IsConnectedReductive G →
    let G_R := (GroupScheme.baseChange (algebraBaseMap ℚ ℝ)).obj G
    letI : IsAffine G_R.X.left := ringBaseChange_isAffine ℚ ℝ G.X
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of ℝ))) (j : T.toGrp ⟶ G_R),
      IsMaximalTorus j → ∀ (U : Set (RingPoint ℝ G_R.X ℝ)), IsOpen U →
        rationalPointEquiv ℝ G_R.X (1 : RationalPoint ℝ G_R.X) ∈ U →
        ∃ g : RingPoint ℝ G_R.X ℝ, g ∈ U ∧
          ∃ (P : CommGroupScheme (Spec (CommRingCat.of ℚ))) (i : P.toGrp ⟶ G),
            IsMaximalTorus i ∧
              ∃ e : T.toGrp ≅ (GroupScheme.baseChange (algebraBaseMap ℚ ℝ)).obj P.toGrp,
                e.hom ≫ (GroupScheme.baseChange (algebraBaseMap ℚ ℝ)).map i =
                  j ≫ (G_R.innerIso ((rationalPointEquiv ℝ G_R.X).symm g)).hom

set_option maxRecDepth 1500 in
set_option maxHeartbeats 600000 in
theorem realMaximalTorusApproximation : RealMaximalTorusApproximationStatement := by
  intro G _ hG G_R T j hj U hU h1
  let : IsAffine G_R.X.left := ringBaseChange_isAffine ℚ ℝ G.X
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hGR : IsConnectedReductive G_R := connectedReductiveFieldExtensionStatement ℚ ℝ G hG
  let : Smooth G_R.X.hom := hGR.smooth
  let : IsAffineHom G_R.X.hom := hGR.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj.2.1
  let : IsAffineHom T.toGrp.X.hom := hj.2.1.isAffineHom
  let d := Module.finrank ℚ (Additive (lieKernel G ℚ))
  let c₀ : FiniteCoordinates G d := finiteCoordinates G
  let c : FiniteCoordinates G_R d := c₀.baseChange ℚ ℝ
  let B := torusCentralizerMatrix c j
  obtain ⟨p, hp, hreg⟩ := regularMaximalTorusSlice ℝ G_R T j c hGR hj
  obtain ⟨t, ht⟩ : ∃ t, MvPolynomial.eval t p ≠ 0 := by
    by_contra! hz
    exact hp (MvPolynomial.funext (q := 0) fun v => by simpa using hz v)
  obtain ⟨W, hW, hnW, hslice⟩ := exists_regularSliceImage_open c B p t ht (hreg t ht).1 U hU h1
  have hd : DenseRange (fun v : Fin d → ℚ => fun i => (v i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨v, hv⟩ := hd.exists_mem_open hW hnW
  obtain ⟨g, hg, s, hs, he⟩ := hslice _ hv
  let Y := torusSliceElement c j s
  let g₀ := (rationalPointEquiv ℝ G_R.X).symm g
  obtain ⟨X, hXY⟩ := exists_kernelFieldExtension_eq_of_coordinates c₀ v _ he
  change kernelFieldExtension (K := ℝ) G X = targetMap (G_R.innerIso g₀).hom ℝ Y at hXY
  exact ⟨g, hg, regularTorusDescent ℚ ℝ G T j hj Y
    (range_le_elementCentralizer_torusSliceElement c j hj.1 s) (hreg s hs).2 g₀ X hXY⟩

end Langlands.GroupScheme
