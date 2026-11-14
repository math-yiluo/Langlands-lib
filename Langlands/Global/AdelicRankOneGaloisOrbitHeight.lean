import Langlands.GroupScheme.Rational.RankOneGaloisParabolicDescent
import Langlands.Global.AdelicGaloisBorelTwisting
import Langlands.Global.AdelicRankOneOrbitHeightBound
import Langlands.Global.AdelicScalarExtensionOrbitHeight
import Langlands.Global.AdelicGaloisSubsetDescent
import Langlands.Global.AdelicMinimalParabolicLineBound
import Langlands.Global.AdelicBoundedRootProduct
import Langlands.Global.AdelicOrbitHeightCompactBounds
import Langlands.Global.AdelicLineCharacterHeight
import Langlands.Global.AdelicHeightMinimumLeviRestriction
import Langlands.Global.AdelicSpringerCentralCompactness

/-! # The rank-one orbit-height bound from a twisted split factorization over a Galois
splitting field

See the paired Markdown file for statements, provenance and proofs. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj NNReal Pointwise TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Global

namespace AdelicGroupPoints

open Langlands.GroupScheme GaloisPointComparison

variable (K : Type u) [Field K] [NumberField K] (H : GroupScheme (Spec (CommRingCat.of K)))

omit [NumberField K] in
/-- The constant point of a rational point at the base coefficient algebra is its rational
coefficient point. -/
theorem constantPoint_base_eq_rationalCoeffEquiv (m : rationalPoints H) :
    H.constantPoint m ((algSpec (CommRingCat.of K)).obj (op (CommAlgCat.of K K))) =
      rationalCoeffEquiv K H m := by
  apply Over.OverMorphism.ext
  rw [rationalCoeffEquiv_left]
  change Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ m.left = m.left
  simp

/-- On adelic points, the inner automorphism of a rational point is conjugation by the
principal image of that point. -/
theorem map_innerIso_hom (m : rationalPoints H) (y : AdelicGroupPoints K H) :
    map K H H (H.innerIso m).hom y =
      rational K H (rationalCoeffEquiv K H m) * y *
        (rational K H (rationalCoeffEquiv K H m))⁻¹ := by
  have h : H.constantPoint m ((algSpec (CommRingCat.of K)).obj
      (op (CommAlgCat.of K (Adeles K)))) =
      rational K H (rationalCoeffEquiv K H m) := by
    rw [← constantPoint_base_eq_rationalCoeffEquiv]
    exact (H.constantPoint_naturality m _).symm
  rw [map_apply, affinePointsTarget_apply, comp_innerIso_hom, h]

/-- The inverse of the principal image of the image of a rational point under a group-scheme
map is the image of the inverse principal point. -/
theorem rational_rationalCoeffEquiv_map_inv {H' : GroupScheme (Spec (CommRingCat.of K))}
    (f : H ⟶ H') (x : rationalPoints H) :
    (rational K H' (rationalCoeffEquiv K H' (rationalPoints.map f x)))⁻¹ =
      map K H H' f (rationalNormOne K H (rationalCoeffEquiv K H x)⁻¹ : AdelicGroupPoints K H) := by
  rw [rationalNormOne_val, map_inv, map_inv, rationalCoeffEquiv_map]
  exact congrArg _ (DFunLike.congr_fun (rational_naturality K H f) _)

end AdelicGroupPoints

namespace AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints GaloisPointComparison

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [NumberField F] [NumberField L] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The pullback comparison of points carries the coefficient extension of a rational point
to the rational point of the base change given by the pulled-back section. -/
theorem affinePointsBaseChangeMulEquiv_rationalCoeffEquiv (δ : rationalPoints G) :
    affinePointsBaseChangeMulEquiv F L L G
        (G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId F L)) (rationalCoeffEquiv F G δ)) =
      rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G)
        (baseChangeBasePoint (Spec.algebraMap F L) G δ) := by
  apply (affinePointsBaseChangeMulEquiv F L L G).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left, rationalCoeffEquiv_left,
    baseChangeBasePoint_fst, affinePointMap_apply]
  change Spec.map _ ≫ (rationalCoeffEquiv F G δ).left = _
  rw [rationalCoeffEquiv_left]
  rfl

/-- **Scalar extension of rational points.** The scalar-extension map on norm-one points
carries the principal image of a rational point `δ ∈ G(F)` to the principal image of its
base change `δ_L ∈ G_L(L)`. -/
theorem scalarExtensionNormOneMap_rationalNormOne (δ : rationalPoints G) :
    scalarExtensionNormOneMap F L G (rationalNormOne F G (rationalCoeffEquiv F G δ)) =
      rationalNormOne L (AffineWeil.unitBaseChange F L G)
        (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G)
          (baseChangeBasePoint (Spec.algebraMap F L) G δ)) := by
  apply Subtype.ext
  rw [scalarExtensionNormOneMap_val_eq_tensor, rationalNormOne_val, rationalNormOne_val,
    ← affinePointsBaseChangeMulEquiv_rationalCoeffEquiv]
  set q := rationalCoeffEquiv F G δ
  have h1 : G.affinePointMap (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : Adeles F →ₐ[F] L ⊗[F] Adeles F)) (rational F G q) =
      G.affinePointMap (CommAlgCat.ofHom
        ((Algebra.TensorProduct.includeLeft : L →ₐ[L] L ⊗[F] Adeles F).restrictScalars F))
        (G.affinePointMap (CommAlgCat.ofHom (Algebra.ofId F L)) q) := by
    rw [rational, ← MonoidHom.comp_apply, ← MonoidHom.comp_apply, ← affinePointMap_comp,
      ← affinePointMap_comp]
    congr 2
    ext
  rw [h1, ← affinePointsBaseChangeMulEquiv_naturality, rational, ← MonoidHom.comp_apply,
    ← affinePointMap_comp]
  congr 2
  ext

end AdelicGaloisUnit

end Langlands.Global

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k K : Type u} [Field k] [Field K] {G : GroupScheme (Spec (CommRingCat.of k))}
  {n : Type} [Fintype n] [DecidableEq n]

/-- **Line preservation after base change.** If `Φ` is exactly the stabilizer of the
coordinate line `j` under `ρ`, then every group-scheme homomorphism into the base change of
the group whose range lies in the base change of `Φ` preserves the line `j` under the
base-changed representation. -/
theorem preservesCoordinateLine_baseChange_restrict_of_range_le
    {ρ : MatrixRepresentation G n} {Φ : SubgroupFunctor G} {j : n}
    (hstab : ρ.HasExactCoordinateLineStabilizer Φ j)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    {H : GroupScheme (Spec (CommRingCat.of K))} (f : H ⟶ (GroupScheme.baseChange b).obj G)
    (hf : SubgroupFunctor.range f ≤ Φ.baseChange b) :
    ((ρ.baseChange b).restrict f).PreservesCoordinateLine j := by
  intro Z x
  have hx : x ≫ f.hom.hom ∈ (Φ.baseChange b).carrier Z :=
    hf Z (SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩)
  rw [SubgroupFunctor.mem_baseChange] at hx
  obtain ⟨c, hc⟩ := (hstab _ _).mp hx
  refine ⟨c, ?_⟩
  rw [pointMatrix_restrict, pointMatrix_baseChange]
  exact hc

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.Global.AdelicGaloisUnit

open Langlands.GroupScheme AdelicGroupPoints GaloisPointComparison RepresentationGrowth

/-- A nonnegative real whose positive power is at most `M` is at most `max M 1`. -/
theorem le_max_one_of_pow_le {x M : ℝ} {d : ℕ} (hd : d ≠ 0) (h : x ^ d ≤ M) :
    x ≤ max M 1 := by
  rcases le_or_gt x 1 with h1 | h1
  · exact h1.trans (le_max_right _ _)
  · exact ((le_self_pow₀ h1.le hd).trans h).trans (le_max_left _ _)

section Matched

variable (F L : Type u) [Field F] [NumberField F] [Field L] [NumberField L]
  [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

local instance : IsAffineHom (AffineWeil.unitBaseChange F L G).X.hom :=
  isAffineHom_of_isAffine _

omit [FiniteDimensional F L] [IsGalois F L] [IsAffineHom G.X.hom] in
/-- Right translation of a norm-one point by the inverse of a rational point `δ ∈ G(F)`
becomes, after scalar extension, right translation by the inverse of the principal image of
`δ_L`. -/
theorem scalarExtensionNormOneMap_mul_rationalNormOne_inv (g : normOneSubgroup F G)
    (δ : rationalPoints G) :
    (scalarExtensionNormOneMap F L G (g * rationalNormOne F G (rationalCoeffEquiv F G δ)⁻¹) :
        AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) *
        (rationalSection F L G (baseChangeBasePoint (Spec.algebraMap F L) G δ))⁻¹ := by
  simp only [map_mul, map_inv, scalarExtensionNormOneMap_rationalNormOne,
    Subgroup.coe_mul, Subgroup.coe_inv, rationalNormOne_val]

/-- The group identity behind the matched alternative: if `s = x a r` and
`r d⁻¹ = m⁻¹ y`, then `s d⁻¹ = (x m⁻¹) (m a m⁻¹) y`. -/
theorem mul_inv_eq_of_mul_inv_eq {Γ : Type*} [Group Γ] {s x a r d m y : Γ}
    (hs : s = x * a * r) (h : r * d⁻¹ = m⁻¹ * y) :
    s * d⁻¹ = x * m⁻¹ * (m * a * m⁻¹) * y := by
  rw [hs, mul_assoc (x * a), h]
  group

omit [NumberField F] [NumberField L] [FiniteDimensional F L] [IsGalois F L]
  [LocallyOfFiniteType G.X.hom] in
/-- If `m₀ ∈ G(L)` carries the minimal standard parabolic of `G_L` into the base change of
the minimal standard parabolic `P_F`, and `P_F` is the exact stabilizer of the coordinate
line `j` under `ρ`, then the conjugated base-changed representation `ρ_L ∘ Int(m₀)` preserves
the line `j` on the minimal standard parabolic of `G_L`. -/
theorem preservesCoordinateLine_innerIso_restrict_of_le_comap
    {TF : CommGroupScheme (Spec (CommRingCat.of F))} (iF : TF.toGrp ⟶ G)
    (νF : cocharacterLattice TF)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic iF νF ∅) j)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (m₀ : rationalPoints (AffineWeil.unitBaseChange F L G))
    (hm₀ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        ((standardParabolic iF νF ∅).baseChange (Spec.algebraMap F L)).comap
          ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) :
    (((ρ.baseChange (Spec.algebraMap F L)).restrict
      ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom).restrict
        (Standard.parabolicHom i ν ∅)).PreservesCoordinateLine j := by
  rw [MatrixRepresentation.restrict_comp]
  apply MatrixRepresentation.preservesCoordinateLine_baseChange_restrict_of_range_le hstab
  rw [SubgroupFunctor.range_comp_le_iff, (Standard.isRepresentedBy_parabolicHom i ν ∅).2,
    (standardParabolicEndpoints L _ hGL T i hi ν hν).1]
  exact hm₀

/-- **The matched alternative, with a fixed conjugator.** Let `G` have `F`-rank one with
minimal standard parabolic `P_F`, let `ρ` have `P_F` as exact stabilizer of the coordinate
line `j`, and let `m₀ ∈ G(L)` carry the minimal standard parabolic `P(ν)` of `G_L` into
`(P_F)_L`. For a compact set `C` and an upper root bound `c`, there is a constant `B` such
that every `g ∈ G(𝔸_F)¹` whose scalar extension factors as `x · i(t) · p · q` with
`x ∈ C`, norm-one `i(t)` with simple-root norms at most `c`, a norm-one minimal-parabolic
factor `p` and a rational point `q` matched in Springer's inverse-orbit sense has a rational
translate `g q₀` of orbit height at most `B`. -/
theorem exists_orbitHeight_bound_of_matched_of_conjugator
    (hG : IsConnectedReductive G) {TF : CommGroupScheme (Spec (CommRingCat.of F))}
    (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF)
    (αF : characterLattice TF) (hαF : simpleRelativeRoots iF νF = {αF})
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic iF νF ∅) j)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (m₀ : rationalPoints (AffineWeil.unitBaseChange F L G))
    (hm₀ : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        ((standardParabolic iF νF ∅).baseChange (Spec.algebraMap F L)).comap
          ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom)
    (C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))) (hC : IsCompact C)
    (c : ℝ≥0ˣ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (g : normOneSubgroup F G),
      ∀ x ∈ C, ∀ (t : AdelicGroupPoints L T.toGrp)
        (p : normOneSubgroup L (Standard.parabolicScheme i ν ∅))
        (q : rationalPoints (AffineWeil.unitBaseChange F L G)),
        (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
            x * map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p *
              rationalSection F L G q →
        map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
        (∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c) →
        ∀ J : (L ≃ₐ[F] L) → Set (characterLattice T),
          (∀ σ, J σ ⊆ simpleRelativeRoots i ν) →
          ∀ α ∈ simpleRelativeRoots i ν, J 1 = simpleRelativeRoots i ν \ {α} →
          (∀ σ : L ≃ₐ[F] L,
            SubgroupFunctor.range
                (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
                  ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) σ) =
              SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
                ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom)) →
          ∃ q₀ : RationalGroupPoints F G,
            orbitHeight F G ρ (Pi.single j 1) ((g : AdelicGroupPoints F G) * rational F G q₀) ≤
              B := by
  classical
  have hn : 0 < n := Fin.pos j
  have hvne : (Pi.single j (1 : L) : Fin n → L) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  have hv : (Pi.single j (1 : F) : Fin n → F) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  have hvL : (fun l => algebraMap F L ((Pi.single j (1 : F) : Fin n → F) l)) =
      (Pi.single j 1 : Fin n → L) := by
    funext l
    rcases eq_or_ne l j with rfl | h
    · simp
    · simp [h]
  have hline' := preservesCoordinateLine_innerIso_restrict_of_le_comap F L G iF νF ρ j hstab
    T i hGL hi ν hν m₀ hm₀
  obtain ⟨hTline, hbd⟩ :=
    PositiveRealTorus.exists_hasUniformCharacterBound_torusCoordinateLineCharacter_of_minimalStandardParabolic
      L (AffineWeil.unitBaseChange F L G) T hGL i hi ν hν _ j hline'
  obtain ⟨K, hK⟩ := hbd c
  -- the base-changed representation preserves the line on the base-changed `P_F`
  have hz : ((ρ.baseChange (Spec.algebraMap F L)).restrict
      ((GroupScheme.baseChange (Spec.algebraMap F L)).map
        (Standard.parabolicHom iF νF ∅))).PreservesCoordinateLine j :=
    MatrixRepresentation.preservesCoordinateLine_baseChange_restrict_of_range_le hstab _ _
      (range_baseChange_standardParabolicHom (L := L) iF νF ∅).le
  obtain ⟨B₁, hB₁, hcpt⟩ := exists_pos_orbitHeight_bounds_of_isCompact L
    (AffineWeil.unitBaseChange F L G) (ρ.baseChange (Spec.algebraMap F L)) hn
    (hC.mul isCompact_singleton :
      IsCompact (C * {(rationalSection F L G m₀)⁻¹}))
  have hH₀pos := (orbitHeight_pos L _ ((ρ.baseChange (Spec.algebraMap F L)).restrict
    ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) hvne 1).le
  refine ⟨max (B₁ * (((K : ℝ≥0) : ℝ) * orbitHeight L (AffineWeil.unitBaseChange F L G)
    ((ρ.baseChange (Spec.algebraMap F L)).restrict
      ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) (Pi.single j 1) 1)) 1,
    lt_max_of_lt_right one_pos, ?_⟩
  intro g x hx t p q hfac htn htc J hJ α hα hJ1 hmatch
  obtain ⟨δ, π, hπ, hδπ⟩ := exists_rational_mul_eq_of_inverse_orbit_matching hG iF hiF νF hνF
    αF hαF hGL i hi ν hν m₀ hm₀ J hJ α hJ1 hα q hmatch
  rw [SubgroupFunctor.rationalPoints_range] at hπ
  obtain ⟨π', rfl⟩ := hπ
  refine ⟨(rationalCoeffEquiv F G δ)⁻¹, ?_⟩
  rw [← rationalNormOne_val, ← Subgroup.coe_mul]
  apply le_max_one_of_pow_le (Module.finrank_pos (R := F) (M := L)).ne'
  rw [← orbitHeight_scalarExtensionNormOneMap F L G ρ hv, hvL,
    scalarExtensionNormOneMap_mul_rationalNormOne_inv]
  have hδπ' : baseChangeBasePoint (Spec.algebraMap F L) G δ * q⁻¹ =
      rationalPoints.map ((GroupScheme.baseChange (Spec.algebraMap F L)).map
        (Standard.parabolicHom iF νF ∅)) π' * m₀ := hδπ
  -- the coset relation on principal points
  have key : rationalSection F L G q *
        (rationalSection F L G (baseChangeBasePoint (Spec.algebraMap F L) G δ))⁻¹ =
      (rationalSection F L G m₀)⁻¹ *
        map L _ _ ((GroupScheme.baseChange (Spec.algebraMap F L)).map
          (Standard.parabolicHom iF νF ∅))
        (rationalNormOne L _ (rationalCoeffEquiv L _ π')⁻¹ : AdelicGroupPoints L _) := by
    rw [← AdelicGroupPoints.rational_rationalCoeffEquiv_map_inv]
    have hR := congrArg (fun m => rationalSection F L G m) hδπ'
    simp only [rationalSection, map_mul, map_inv] at hR ⊢
    rw [← mul_inv_rev, ← hR, mul_inv_rev, inv_inv]
  have hy : (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) *
        (rationalSection F L G (baseChangeBasePoint (Spec.algebraMap F L) G δ))⁻¹ =
      x * (rationalSection F L G m₀)⁻¹ *
        map L _ _ ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom
          (map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p) *
        map L _ _ ((GroupScheme.baseChange (Spec.algebraMap F L)).map
            (Standard.parabolicHom iF νF ∅))
          (rationalNormOne L _ (rationalCoeffEquiv L _ π')⁻¹ : AdelicGroupPoints L _) := by
    rw [AdelicGroupPoints.map_innerIso_hom]
    exact mul_inv_eq_of_mul_inv_eq (by rw [hfac]; simp only [mul_assoc]) key
  rw [hy, orbitHeight_mul_map_normOne L _ _ _ _ j hz]
  have h1 := (hcpt _ (Set.mul_mem_mul hx (Set.mem_singleton _))
    (map L _ _ ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom
      (map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p))
    (Pi.single j 1) hvne).1
  have hline := orbitHeight_mul_map_eq_lineCharacterNorm L _ T.toGrp i
    ((ρ.baseChange (Spec.algebraMap F L)).restrict
      ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) j hTline 1 t
  rw [one_mul] at hline
  have hKt : ((lineCharacterNorm L _ T.toGrp i
      ((ρ.baseChange (Spec.algebraMap F L)).restrict
        ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) j hTline t : ℝ≥0) : ℝ) ≤
      ((K : ℝ≥0) : ℝ) := by
    change ((PositiveRealTorus.normCharacter L T
      (((ρ.baseChange (Spec.algebraMap F L)).restrict
        ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom).torusCoordinateLineCharacter
          i j hTline) t : ℝ≥0) : ℝ) ≤ _
    exact NNReal.coe_le_coe.mpr (Units.val_le_val.mpr (hK t ⟨htn, htc⟩))
  calc _ ≤ B₁ * orbitHeight L _ (ρ.baseChange (Spec.algebraMap F L)) (Pi.single j 1)
        (map L _ _ ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom
          (map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p)) := h1
    _ = B₁ * (((lineCharacterNorm L _ T.toGrp i
          ((ρ.baseChange (Spec.algebraMap F L)).restrict
            ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) j hTline t : ℝ≥0) : ℝ) *
          orbitHeight L (AffineWeil.unitBaseChange F L G)
            ((ρ.baseChange (Spec.algebraMap F L)).restrict
              ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom) (Pi.single j 1) 1) := by
        rw [← orbitHeight_restrict, orbitHeight_mul_map_normOne L _ _ _ _ j hline', hline]
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKt hH₀pos) hB₁.le

/-- **The matched alternative.** The bound of
`exists_orbitHeight_bound_of_matched_of_conjugator` without a chosen conjugator: if no
`m₀ ∈ G(L)` carries the minimal standard parabolic of `G_L` into `(P_F)_L`, then no
factorization is matched, since a matched one produces such a conjugator. -/
theorem exists_orbitHeight_bound_of_matched
    (hG : IsConnectedReductive G) {TF : CommGroupScheme (Spec (CommRingCat.of F))}
    (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF)
    (αF : characterLattice TF) (hαF : simpleRelativeRoots iF νF = {αF})
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic iF νF ∅) j)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))) (hC : IsCompact C)
    (c : ℝ≥0ˣ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (g : normOneSubgroup F G),
      ∀ x ∈ C, ∀ (t : AdelicGroupPoints L T.toGrp)
        (p : normOneSubgroup L (Standard.parabolicScheme i ν ∅))
        (q : rationalPoints (AffineWeil.unitBaseChange F L G)),
        (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
            x * map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p *
              rationalSection F L G q →
        map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
        (∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c) →
        ∀ J : (L ≃ₐ[F] L) → Set (characterLattice T),
          (∀ σ, J σ ⊆ simpleRelativeRoots i ν) →
          ∀ α ∈ simpleRelativeRoots i ν, J 1 = simpleRelativeRoots i ν \ {α} →
          (∀ σ : L ≃ₐ[F] L,
            SubgroupFunctor.range
                (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
                  ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) σ) =
              SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
                ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom)) →
          ∃ q₀ : RationalGroupPoints F G,
            orbitHeight F G ρ (Pi.single j 1) ((g : AdelicGroupPoints F G) * rational F G q₀) ≤
              B := by
  by_cases h : ∃ m₀ : rationalPoints (AffineWeil.unitBaseChange F L G),
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        ((standardParabolic iF νF ∅).baseChange (Spec.algebraMap F L)).comap
          ((AffineWeil.unitBaseChange F L G).innerIso m₀).hom
  · obtain ⟨m₀, hm₀⟩ := h
    exact exists_orbitHeight_bound_of_matched_of_conjugator F L G hG iF hiF νF hνF αF hαF ρ j
      hstab T i hGL hi ν hν m₀ hm₀ C hC c
  · refine ⟨1, one_pos, ?_⟩
    intro g x hx t p q hfac htn htc J hJ α hα hJ1 hmatch
    obtain ⟨δ, hδ⟩ := exists_rational_minimalParabolic_le_comap_of_inverse_orbit_matching hG iF
      hiF νF hνF αF hαF hGL i hi ν hν J hJ α hJ1 hα q hmatch
    exact (h ⟨_, hδ⟩).elim

omit [FiniteDimensional F L] [IsAffineHom G.X.hom] in
open AdelicSiegelFactors in
/-- **The unmatched alternative.** For a compact set `C` and root bounds `c, d`, there is a
constant `B` such that every `g ∈ G(𝔸_F)¹` whose scalar extension factors as
`x · i(t) · p · q` with `x ∈ C`, norm-one `i(t)` and `d < |β(t)| ≤ c` for every simple root
`β` has a rational translate `g q₀` of orbit height at most `B`. -/
theorem exists_orbitHeight_bound_of_unmatched
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hmax : IsMaximalTorus i)
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G))) (hC : IsCompact C)
    (c d : ℝ≥0ˣ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (g : normOneSubgroup F G),
      ∀ x ∈ C, ∀ (t : AdelicGroupPoints L T.toGrp)
        (p : normOneSubgroup L (Standard.parabolicScheme i ν ∅))
        (q : rationalPoints (AffineWeil.unitBaseChange F L G)),
        (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
            x * map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p *
              rationalSection F L G q →
        map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) →
        (∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c) →
        (∀ β ∈ simpleRelativeRoots i ν, d < PositiveRealTorus.normCharacter L T β t) →
        ∃ q₀ : RationalGroupPoints F G,
          orbitHeight F G ρ (Pi.single j 1) ((g : AdelicGroupPoints F G) * rational F G q₀) ≤
            B := by
  classical
  have hn : 0 < n := Fin.pos j
  have hv : (Pi.single j (1 : F) : Fin n → F) ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp at hj
  obtain ⟨K, hK, hrep⟩ :=
    exists_isCompact_normOne_rational_mul_mem_emptyParabolic_rootBox_mul_compact
      L (AffineWeil.unitBaseChange F L G) T i ν hGL hi hν hmax
      (max 1 (max (c : ℝ≥0) ((d⁻¹ : ℝ≥0ˣ) : ℝ≥0))) (le_max_left _ _) C⁻¹ hC.inv
  obtain ⟨Ω, hΩ, hdesc⟩ := exists_isCompact_rational_mul_mem_of_scalarExtension F L G K hK
  obtain ⟨B₁, hB₁, hcpt⟩ := exists_pos_orbitHeight_bounds_of_isCompact F G ρ hn
    (hΩ.inv.image continuous_subtype_val)
  refine ⟨B₁ * orbitHeight F G ρ (Pi.single j 1) 1,
    mul_pos hB₁ (orbitHeight_pos F G ρ hv 1), ?_⟩
  intro g x hx t p q hfac htn htc hlow
  -- up to a rational point, the scalar extension of `g⁻¹` lies in the bounded-root product
  have hfac' : ((rationalNormOne L _ (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q) *
        scalarExtensionNormOneMap F L G g⁻¹ : normOneSubgroup L _) :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) =
      map L _ _ (Standard.parabolicHom i ν ∅) ((p⁻¹ : normOneSubgroup L _) :
          AdelicGroupPoints L (Standard.parabolicScheme i ν ∅)) *
        map L T.toGrp _ i t⁻¹ * x⁻¹ := by
    simp only [map_inv, Subgroup.coe_mul, Subgroup.coe_inv, rationalNormOne_val]
    rw [hfac]
    simp only [rationalSection]
    group
  have hmem : ((rationalNormOne L _ (rationalCoeffEquiv L (AffineWeil.unitBaseChange F L G) q) *
        scalarExtensionNormOneMap F L G g⁻¹ : normOneSubgroup L _) :
          AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)) ∈
      boundedRootParabolicProduct L (AffineWeil.unitBaseChange F L G) T i ν
        (max 1 (max (c : ℝ≥0) ((d⁻¹ : ℝ≥0ˣ) : ℝ≥0))) C⁻¹ := by
    rw [hfac']
    refine Set.mul_mem_mul (Set.mul_mem_mul ⟨_, (p⁻¹).prop, rfl⟩ ⟨t⁻¹, ⟨?_, ?_⟩, rfl⟩)
      (Set.inv_mem_inv.mpr hx)
    · rw [map_inv]
      exact inv_mem htn
    · exact inv_mem_torusCharacterBox_of_bounds F L G T i ν t htc hlow
  obtain ⟨r, hr⟩ := hrep _ hmem
  obtain ⟨q₁, hq₁⟩ := hdesc g⁻¹ ⟨r * rationalCoeffEquiv L _ q, by rwa [map_mul, mul_assoc]⟩
  refine ⟨q₁⁻¹, ?_⟩
  have hk : (g : AdelicGroupPoints F G) * rational F G q₁⁻¹ ∈
      ((↑) : normOneSubgroup F G → AdelicGroupPoints F G) '' Ω⁻¹ :=
    ⟨g * rationalNormOne F G q₁⁻¹,
      by simpa only [Set.mem_inv, mul_inv_rev, map_inv, inv_inv] using hq₁, by simp⟩
  simpa only [mul_one] using (hcpt _ hk 1 (Pi.single j 1) hv).1

/-- **The rank-one orbit-height bound from a twisted factorization with inverse-orbit
matching.** Let `G` have `F`-rank one, with minimal standard parabolic `P_F` the exact
stabilizer of the coordinate line `j` under `ρ`. Let `i : T → G_L` be a split maximal torus
of `G_L` over the Galois extension `L/F`, with generic cocharacter `ν`. Suppose the scalar
extensions of norm-one points admit Springer's §3.5 twisted factorization with inverse-orbit
matching (the body of Worker 5268's `HasTwistedOverlapMatching`, stated inline). Then the
`ρ`-orbit heights of rational translates of norm-one points are uniformly bounded. -/
theorem hasUniformNormOneRationalOrbitHeightBound_of_twistedOverlapMatching
    (hG : IsConnectedReductive G) {TF : CommGroupScheme (Spec (CommRingCat.of F))}
    (iF : TF.toGrp ⟶ G) (hiF : IsMaximalSplitTorus iF)
    (νF : cocharacterLattice TF) (hνF : IsGenericCocharacter iF νF)
    (αF : characterLattice TF) (hαF : simpleRelativeRoots iF νF = {αF})
    {n : ℕ} (ρ : MatrixRepresentation G (Fin n)) (j : Fin n)
    (hstab : ρ.HasExactCoordinateLineStabilizer (standardParabolic iF νF ∅) j)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (i : T.toGrp ⟶ AffineWeil.unitBaseChange F L G)
    (hGL : IsConnectedReductive (AffineWeil.unitBaseChange F L G))
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
    (hmax : IsMaximalTorus i)
    (hM : ∃ C : Set (AdelicGroupPoints L (AffineWeil.unitBaseChange F L G)), IsCompact C ∧
      ∃ c d : ℝ≥0ˣ, ∀ g : normOneSubgroup F G,
        ∃ x ∈ C, ∃ (t : AdelicGroupPoints L T.toGrp)
          (p : normOneSubgroup L (Standard.parabolicScheme i ν ∅))
          (q : rationalPoints (AffineWeil.unitBaseChange F L G)),
          (scalarExtensionNormOneMap F L G g : AdelicGroupPoints L _) =
              x * map L T.toGrp _ i t * map L _ _ (Standard.parabolicHom i ν ∅) p *
                rationalSection F L G q ∧
            map L T.toGrp _ i t ∈ normOneSubgroup L (AffineWeil.unitBaseChange F L G) ∧
            (∀ β ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T β t ≤ c) ∧
            ∀ α ∈ simpleRelativeRoots i ν, PositiveRealTorus.normCharacter L T α t ≤ d →
              ∃ J : (L ≃ₐ[F] L) → Set (characterLattice T),
                (∀ σ, J σ ⊆ simpleRelativeRoots i ν) ∧
                  J 1 = simpleRelativeRoots i ν \ {α} ∧
                  ∀ σ : L ≃ₐ[F] L,
                    SubgroupFunctor.range
                        (radicalGaloisHom (Standard.parabolicHom i ν (J σ⁻¹) ≫
                          ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom) σ) =
                      SubgroupFunctor.range (Standard.parabolicHom i ν (J 1) ≫
                        ((AffineWeil.unitBaseChange F L G).innerIso q⁻¹).hom)) :
    HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1) := by
  obtain ⟨C, hC, c, d, hM⟩ := hM
  obtain ⟨B₁, hB₁, h₁⟩ :=
    exists_orbitHeight_bound_of_unmatched F L G T i hGL hi ν hν hmax ρ j C hC c d
  obtain ⟨B₂, -, h₂⟩ := exists_orbitHeight_bound_of_matched F L G hG iF hiF νF hνF αF hαF ρ j
    hstab T i hGL hi ν hν C hC c
  refine ⟨max B₁ B₂, lt_max_of_lt_left hB₁, fun g => ?_⟩
  obtain ⟨x, hx, t, p, q, hfac, htn, htc, hmatch⟩ := hM g
  by_cases hlow : ∀ β ∈ simpleRelativeRoots i ν, d < PositiveRealTorus.normCharacter L T β t
  · obtain ⟨q₀, hq₀⟩ := h₁ g x hx t p q hfac htn htc hlow
    exact ⟨q₀, hq₀.trans (le_max_left _ _)⟩
  · push Not at hlow
    obtain ⟨α, hα, hαd⟩ := hlow
    obtain ⟨J, hJ, hJ1, hJm⟩ := hmatch α hα hαd
    obtain ⟨q₀, hq₀⟩ := h₂ g x hx t p q hfac htn htc J hJ α hα hJ1 hJm
    exact ⟨q₀, hq₀.trans (le_max_right _ _)⟩

end Matched

end Langlands.Global.AdelicGaloisUnit
