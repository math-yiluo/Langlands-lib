import Langlands.Representation.Aubert.General.CentralizingUnipotentHaarDeterminant
import Langlands.Analysis.Local.VectorFiltrationHaarModulusProof
import Langlands.BruhatTits.Unipotent.CompactOpenContainmentProof

/-! # Vector filtrations and Haar determinants for smooth affine groups -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme GroupScheme.Dynamic.GradedCoordinates GroupScheme.Corepresented
  GroupScheme.RelativeRoot Langlands.AlgebraicGeometry.PointTopology

/-- A finite vector filtration normalized by one ambient element, with a prescribed
product of the actual linear determinants. -/
structure VectorFiltrationDeterminantData
    (k : Type u) [Field k] [TopologicalSpace k]
    (H : Type*) [Group H] [TopologicalSpace H]
    (U : Subgroup H) (g : H) (delta : kˣ) where
  length : ℕ
  step : ℕ → Subgroup H
  dimension : ℕ → ℕ
  quotient : ∀ r, step r → Fin (dimension r) → k
  linear : ∀ r, (Fin (dimension r) → k) ≃ₗ[k] (Fin (dimension r) → k)
  zero : step 0 = U
  last : step length = ⊥
  antitone : ∀ r < length, step (r + 1) ≤ step r
  normalized : ∀ r < length, g ∈ Subgroup.normalizer (step r : Set H)
  add : ∀ r < length, ∀ x y : step r, quotient r (x * y) = quotient r x + quotient r y
  kernel : ∀ r < length, ∀ x : step r, quotient r x = 0 ↔ (x : H) ∈ step (r + 1)
  continuous : ∀ r < length, Continuous (quotient r)
  openMap : ∀ r < length, IsOpenMap (quotient r)
  surjective : ∀ r < length, Function.Surjective (quotient r)
  intertwine : ∀ r < length, ∀ x y : step r,
    (y : H) = g * x * g⁻¹ → quotient r y = linear r (quotient r x)
  determinant : ∏ r ∈ Finset.range length, LinearEquiv.det (linear r) = delta

section SmoothAffine

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] [Smooth G.X.hom]

/-- Smoothness and affineness suffice for the actual rational vector filtration.
The construction adapts Worker 1423's published graded-coordinate proof. -/
theorem exists_smoothAffineUnipotentVectorFiltration :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
      (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d) (m : rationalPoints Z),
      Nonempty (VectorFiltrationDeterminantData k (RationalPoint k G.X)
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) (m ≫ iZ.hom.hom)
        (rationalCharacterEval
          ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m)) := by
  intro _ _ _ χ Z U iZ iU hZ hU _ _ e c m
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := isAffineHom_affineCoordinates G
  have := AffineCoordinates.formallySmooth_algebra G (inferInstance : Smooth G.X.hom)
  have := AffineCoordinates.finiteType_algebra G (inferInstance : Smooth G.X.hom)
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  obtain ⟨n, dd, x, hd, -, hx, hbij⟩ := exists_aeval_bijective_cyclicTail
    (AffineCoordinates.corepresentation G) (cocharModelAction G χ) (idExponent_ne_zero (k := k)) 1
  have hg : m ≫ iZ.hom.hom ∈ (torusCentralizer χ).carrier _ :=
    mem_torusCentralizer_of_centralizer G χ hZ m
  set J := centralizerMatrix G χ hx hbij hZ m with hJdef
  have hJ : J.det =
      (rationalCharacterEval ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m :
        k) := by
    rw [rationalCharacterEval_determinantCharacter G χ hU hZ m c,
      det_differential G χ hU hd hx hbij hZ m]
  have hJ0 : J.det ≠ 0 := by
    rw [hJ]
    exact Units.ne_zero _
  have hJprod : J.det = ∏ s ∈ Finset.univ.image dd, (J.toSquareBlock dd s).det :=
    det_conjMatrix (AffineCoordinates.corepresentation G) (cocharModelAction G χ)
      (constantFamily_naturality G (m ≫ iZ.hom.hom))
      (constantFamily_fixed G _ χ (mem_torusCentralizer_of_centralizer G χ hZ m))
      idExponent_ne_zero hx hbij.2
  have hblock : ∀ s, (J.toSquareBlock dd s).det ≠ 0 := by
    intro s
    by_cases hs : s ∈ Finset.univ.image dd
    · rw [hJprod] at hJ0
      exact Finset.prod_ne_zero_iff.1 hJ0 s hs
    · have : IsEmpty {i // dd i = s} :=
        ⟨fun i => hs (Finset.mem_image.2 ⟨i.1, Finset.mem_univ _, i.2⟩)⟩
      rw [Matrix.det_isEmpty]
      exact one_ne_zero
  set N := Finset.univ.sup dd with hNdef
  have hN : ∀ i, dd i ≤ N := fun i => Finset.le_sup (Finset.mem_univ i)
  let nr : ℕ → ℕ := fun r => Fintype.card {i // dd i = r + 1}
  let eqv : ∀ r, {i // dd i = r + 1} ≃ Fin (nr r) := fun r => Fintype.equivFin _
  let M : ∀ r, Matrix (Fin (nr r)) (Fin (nr r)) k := fun r =>
    (J.toSquareBlock dd (r + 1)).reindex (eqv r) (eqv r)
  have hM : ∀ r, (M r).det = (J.toSquareBlock dd (r + 1)).det := fun r =>
    Matrix.det_reindex_self _ _
  let L : ∀ r, (Fin (nr r) → k) ≃ₗ[k] (Fin (nr r) → k) := fun r =>
    LinearMap.equivOfDetNeZero (Matrix.toLin' (M r))
      (by rw [LinearMap.det_toLin', hM]; exact hblock _)
  let F := rationalFiltration G χ
  have hF0 : ∀ r, F r ≤ F 0 := rationalFiltration_le_zero G χ
  let q : ∀ r, F r → Fin (nr r) → k := fun r p j =>
    ratCoord G χ x ⟨p.1, hF0 r p.2⟩ ((eqv r).symm j).1
  have hqmul : ∀ r, ∀ p p' : F r, q r (p * p') = q r p + q r p' := by
    intro r p p'
    funext j
    change ratCoord G χ x (⟨p.1, hF0 r p.2⟩ * ⟨p'.1, hF0 r p'.2⟩) ((eqv r).symm j).1 = _
    exact ratCoord_mul G χ hx ⟨p.1, hF0 r p.2⟩ ⟨p'.1, hF0 r p'.2⟩ p.2 p'.2 ((eqv r).symm j).2
  let v : ∀ r, (Fin (nr r) → k) → Fin n → k := fun r w i =>
    if h : dd i = r + 1 then w (eqv r ⟨i, h⟩) else 0
  have hvmem : ∀ r w, ratPoint G χ x hbij (v r w) ∈ F r := by
    intro r w
    refine (mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r)
      ⟨_, ratPoint_mem G χ hbij (v r w)⟩).2 fun i hi => ?_
    rw [ratCoord_ratPoint]
    simp only [v, show ¬ dd i = r + 1 by omega, ↓reduceDIte]
  let sec : ∀ r, (Fin (nr r) → k) → F r := fun r w => ⟨ratPoint G χ x hbij (v r w), hvmem r w⟩
  have hqsec : ∀ r w, q r (sec r w) = w := by
    intro r w
    funext j
    change ratCoord G χ x ⟨ratPoint G χ x hbij (v r w), _⟩ ((eqv r).symm j).1 = w j
    rw [ratCoord_ratPoint]
    simp only [v, ((eqv r).symm j).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]
  have hsec_cont : ∀ r, Continuous (sec r) := by
    intro r
    refine Continuous.subtype_mk ((continuous_ratPoint G χ hbij).comp ?_) _
    refine continuous_pi fun i => ?_
    by_cases h : dd i = r + 1
    · simp only [v, h, ↓reduceDIte]
      exact continuous_apply _
    · simp only [v, h, ↓reduceDIte]
      exact continuous_const
  refine ⟨⟨N, F, nr, q, L, rationalFiltration_zero G χ,
    rationalFiltration_eq_bot G χ hd hx hbij hN, fun r _ => rationalFiltration_succ_le G χ r,
    fun r _ => mem_normalizer_rationalFiltration G χ hg r, fun r _ => hqmul r, ?_, ?_,
    fun r _ => isOpenMap_of_continuous_section (q r) (hqmul r) (sec r) (hsec_cont r) (hqsec r),
    fun r _ w => ⟨sec r w, hqsec r w⟩, ?_, ?_⟩⟩
  · intro r _ p
    have h0 := (mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r)
      ⟨p.1, hF0 r p.2⟩).1 p.2
    rw [show (p.1 ∈ F (r + 1)) ↔ _ from
      mem_rationalFiltration_iff_ratCoord G χ hd hx hbij (r := r + 1) ⟨p.1, hF0 r p.2⟩]
    constructor
    · intro hq i hi
      by_cases hir : dd i = r + 1
      · have h := congrFun hq (eqv r ⟨i, hir⟩)
        simpa [q] using h
      · exact h0 i (by omega)
    · intro h
      funext j
      exact h _ (by have := ((eqv r).symm j).2; omega)
  · intro r _
    refine continuous_pi fun j => ?_
    exact (continuous_ratCoord G χ ((eqv r).symm j).1).comp
      (continuous_subtype_val.subtype_mk _)
  · intro r _ p p' hy
    funext j
    have hp' : (⟨p'.1, hF0 r p'.2⟩ : F 0) =
        ⟨m ≫ iZ.hom.hom * p.1 * (m ≫ iZ.hom.hom)⁻¹,
          conj_mem_rationalFiltration G χ hg (hF0 r p.2)⟩ := Subtype.ext hy
    change ratCoord G χ x ⟨p'.1, hF0 r p'.2⟩ ((eqv r).symm j).1 =
      Matrix.toLin' (M r) (q r p) j
    rw [hp', ratCoord_conj G χ hd hx hbij hg ⟨p.1, hF0 r p.2⟩ p.2 ((eqv r).symm j).2,
      Matrix.toLin'_apply, sum_filter_eq_sum_fin dd (r + 1)]
    rfl
  · apply Units.ext
    rw [Units.coe_prod]
    have hdetL : ∀ r, (LinearEquiv.det (L r) : k) = (J.toSquareBlock dd (r + 1)).det := by
      intro r
      rw [LinearEquiv.coe_det]
      change LinearMap.det (Matrix.toLin' (M r)) = _
      rw [LinearMap.det_toLin', hM]
    simp only [hdetL]
    rw [prod_range_det_toSquareBlock dd J hd hN, ← hJprod, hJ]

/-- One actual vector filtration of a smooth affine dynamic unipotent subgroup,
chosen from the graded-coordinate construction. -/
def smoothAffineUnipotentVectorFiltration :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
      (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d) (m : rationalPoints Z),
      VectorFiltrationDeterminantData k (RationalPoint k G.X)
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))) (m ≫ iZ.hom.hom)
        (rationalCharacterEval
          ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m) := by
  intro _ _ _ χ Z U iZ iU hZ hU _ _ d c m
  exact Classical.choice (exists_smoothAffineUnipotentVectorFiltration G χ hZ hU c m)

/-- The forward Haar modulus on a smooth affine dynamic unipotent subgroup
is the absolute value of the actual Lie determinant. -/
theorem smoothAffineUnipotentHaarDeterminant :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} {iZ : Z ⟶ G} {iU : U ⟶ G}
      (hZ : (Dynamic.centralizer χ).IsRepresentedBy iZ)
      (hU : (Dynamic.unipotent χ).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X))) (m : rationalPoints Z)
      (hm : m ≫ iZ.hom.hom ∈ Subgroup.normalizer
        ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X))),
      (HaarModulus.closedNormalizerCharacter _ hUc ⟨m ≫ iZ.hom.hom, hm⟩ : ℝ≥0) =
        MeasureTheory.distribHaarChar k
          (rationalCharacterEval
            ((Dynamic.centralizerAdjointAction hZ hU).determinantCharacter c) m) := by
  intro _ _ _ χ Z U iZ iU hZ hU _ _ d c hUc m hm
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let D := smoothAffineUnipotentVectorFiltration G χ hZ hU c m
  have hcover : ∀ x : (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)),
      ∃ K : OpenSubgroup ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _))),
        IsCompact (K : Set ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))) ∧ x ∈ K := by
    intro x
    obtain ⟨K, hK, hxK⟩ := BruhatTits.DynamicUnipotentContainment.exists_compactOpenSubgroup χ
      {x} isCompact_singleton
    exact ⟨K, hK, hxK (Set.mem_singleton x)⟩
  rw [Langlands.HaarModulus.VectorFiltration.vectorFiltrationHaarModulus k
    _ hUc hcover ⟨m ≫ iZ.hom.hom, hm⟩ D.length D.step D.zero D.last D.antitone D.normalized
    D.dimension D.quotient D.add D.kernel D.continuous D.openMap D.surjective D.linear D.intertwine]
  rw [← map_prod, D.determinant]

/-- The smooth affine Haar formula for any homomorphism whose image centralizes
the cocharacter, using its actual conjugation action. -/
theorem smoothAffineCentralizingUnipotentHaarDeterminant :
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (chi : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      {Z U : GroupScheme (Spec (CommRingCat.of k))} (iZ : Z ⟶ G) {iU : U ⟶ G}
      (hZ : SubgroupFunctor.range iZ ≤ Dynamic.centralizer chi)
      (hU : (Dynamic.unipotent chi).IsRepresentedBy iU)
      [IsAffine Z.X.left] [IsAffineHom U.X.hom]
      {d : ℕ} (c : Lie.FiniteCoordinates U d)
      (hUc : IsClosed ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X)))
      (m : rationalPoints Z),
      (HaarModulus.closedNormalizerCharacter _ hUc
        (Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m) : ℝ≥0) =
      MeasureTheory.distribHaarChar k
        (rationalCharacterEval
          ((Dynamic.centralizingUnipotentAction chi iZ hZ hU).determinantCharacter c) m) := by
  intro _ _ _ chi Z U iZ iU hZ hU _ _ d c hUc m
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let M := Dynamic.Affine.centralizerScheme chi
  let iM := Dynamic.Affine.centralizerHom chi
  have hM : (Dynamic.centralizer chi).IsRepresentedBy iM :=
    Dynamic.Affine.isRepresentedBy_centralizerHom chi
  have : IsClosedImmersion iM.hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_centralizerHom chi
  have : IsAffine M.X.left := isAffine_of_isAffineHom iM.hom.hom.left
  let f : Z ⟶ M := hM.factorHom iZ hZ
  have hf : f ≫ iM = iZ := hM.factorHom_comp iZ hZ
  have hm : rationalPoints.map f m ≫ iM.hom.hom = m ≫ iZ.hom.hom := by
    change (m ≫ f.hom.hom) ≫ iM.hom.hom = _
    rw [Category.assoc, ← Grp.comp_hom_hom, hf]
  have hmn : rationalPoints.map f m ≫ iM.hom.hom ∈
      Subgroup.normalizer ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X)) := by
    rw [hm]
    exact (Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m).property
  have h := smoothAffineUnipotentHaarDeterminant G chi hM hU c hUc
    (rationalPoints.map f m) hmn
  rw [← rationalCharacterEval_characterRestrict,
    Dynamic.characterRestrict_centralizerAdjointDeterminant_eq_centralizing
      chi iZ hZ hM hU f hf] at h
  have heq : (⟨rationalPoints.map f m ≫ iM.hom.hom, hmn⟩ :
      Subgroup.normalizer ((Dynamic.unipotent chi).carrier (Over.mk (𝟙 _)) :
        Set (RationalPoint k G.X))) =
      Dynamic.centralizingUnipotentNormalizerHom chi iZ hZ m := by
    apply Subtype.ext
    exact hm
  rw [heq] at h
  exact h

end SmoothAffine

end Langlands.Aubert.General.RationalPointFamily
