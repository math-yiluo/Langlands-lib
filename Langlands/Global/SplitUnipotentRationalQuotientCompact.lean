import Langlands.Global.TriangularRationalQuotientCompact
import Langlands.GroupScheme.SplitUnipotentQuotientSection
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitStatement
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps

/-!
# Compactness of `U(F) \ U(𝔸_F)` for split unipotent groups

Let `U` be an affine group scheme over a number field `F` with a split series: a finite
normal series whose successive represented fppf quotients are one-dimensional vector groups.
If split-unipotent torsors over affine schemes are trivial
(`SplitUnipotentAffineTorsorStatement`), every quotient map of the series has a scheme
section, and induction along the series gives a compact set of adelic points meeting every
rational coset. Combined with `PerfectFieldUnipotentSplitStatement` (smooth connected
unipotent groups over perfect fields are split), this gives
`UnipotentRationalQuotientCompactStatement`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Topology
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.AdelicGroupPoints

section Cover

variable {F : Type u} [Field F] [NumberField F]

/-- Some compact set of adelic points meets every rational coset: every `x ∈ G(𝔸_F)` has a
rational `y` with `y * x` in the compact set. -/
def HasCompactRationalCover (G : GroupScheme (Spec (CommRingCat.of F))) : Prop :=
  ∃ C : Set (AdelicGroupPoints F G), IsCompact C ∧
    ∀ x : AdelicGroupPoints F G, ∃ y ∈ rationalSubgroup F G, y * x ∈ C

/-- A compact set meeting every rational coset makes `G(F) \ G(𝔸_F)` compact. -/
theorem compactSpace_rationalQuotient_of_hasCompactRationalCover
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : HasCompactRationalCover G) :
    CompactSpace (RationalQuotient F G) := by
  obtain ⟨K, hK, hcover⟩ := hG
  have himage : LeftCosetSpace.mk (rationalSubgroup F G) '' K = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective _ q
    obtain ⟨y, hy, hyx⟩ := hcover x
    exact ⟨y * x, hyx, LeftCosetSpace.mk_subgroup_mul _ ⟨y, hy⟩ x⟩
  exact isCompact_univ_iff.mp (himage ▸ hK.image (LeftCosetSpace.continuous_mk _))

/-- The covering property is invariant under isomorphisms of group schemes. -/
theorem HasCompactRationalCover.of_iso {G H : GroupScheme (Spec (CommRingCat.of F))}
    (e : G ≅ H) (hH : HasCompactRationalCover H) : HasCompactRationalCover G := by
  obtain ⟨C, hC, hcover⟩ := hH
  have hinv : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
    congrArg (fun f : G ⟶ G => f.hom.hom) e.hom_inv_id
  refine ⟨H.affinePointsTarget e.inv _ '' C,
    hC.image (H.continuous_affinePointsTarget _ e.inv), fun x => ?_⟩
  obtain ⟨y, ⟨r, rfl⟩, hy⟩ := hcover (G.affinePointsTarget e.hom _ x)
  refine ⟨rational F G (H.affinePointsTarget e.inv _ r), ⟨_, rfl⟩, _, hy, ?_⟩
  rw [map_mul]
  congr 1
  change (x ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x
  rw [Category.assoc, hinv, Category.comp_id]

end Cover

section VectorGroup

variable (F : Type u) [Field F]

/-- The standard vector group is affine. -/
instance isAffine_vectorGroup (n : ℕ) :
    IsAffine (VectorGroup.groupScheme (CommRingCat.of F) n).X.left := by
  change IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) (CommRingCat.of F))))
  infer_instance

/-- The standard vector group has triangular coordinates: its coordinate functions are
additive, so the correction polynomials vanish. -/
theorem hasTriangularCoordinates_vectorGroup (n : ℕ) :
    HasTriangularCoordinates (VectorGroup.groupScheme (CommRingCat.of F) n) := by
  let t : Fin n → AffineCoordinateRing F (VectorGroup.groupScheme (CommRingCat.of F) n).X :=
    fun i => VectorGroup.coordinateSection (CommRingCat.of F) n i
  let e : AffineCoordinateRing F (VectorGroup.groupScheme (CommRingCat.of F) n).X ≃ₐ[F]
      MvPolynomial (Fin n) F :=
    spectrumCoordinateAlgEquiv F (MvPolynomial (Fin n) F)
  have he : ∀ i, e (t i) = MvPolynomial.X i := by
    intro i
    exact congrArg (fun f : CommRingCat.of (MvPolynomial (Fin n) F) ⟶ _ =>
        f.hom (MvPolynomial.X i))
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) F))).inv_hom_id
  refine ⟨n, t, 0, ?_, ?_, ?_⟩
  · have h : (MvPolynomial.aeval t :
        MvPolynomial (Fin n) F →ₐ[F] AffineCoordinateRing F _) = e.symm.toAlgHom := by
      apply MvPolynomial.algHom_ext
      intro i
      rw [MvPolynomial.aeval_X]
      exact (e.symm_apply_eq.mpr (he i).symm).symm
    rw [h]
    exact e.symm.bijective
  · intro i v hv
    simp at hv
  · intro A x y i
    simp only [Pi.zero_apply, map_zero, add_zero]
    have h := congrFun (VectorGroup.coordinates_mul x y) i
    rw [Pi.add_apply, VectorGroup.coordinates_apply, VectorGroup.coordinates_apply,
      VectorGroup.coordinates_apply] at h
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
        ((x * y).left.appTop (VectorGroup.coordinateSection (CommRingCat.of F) n i)) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
          (x.left.appTop (VectorGroup.coordinateSection (CommRingCat.of F) n i)) +
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
          (y.left.appTop (VectorGroup.coordinateSection (CommRingCat.of F) n i))
    rw [h]
    exact map_add _ _ _

variable {F} [NumberField F]

/-- `𝔾ₐⁿ(F) \ 𝔾ₐⁿ(𝔸_F)` has a compact set meeting every rational coset. -/
theorem hasCompactRationalCover_vectorGroup (n : ℕ) :
    HasCompactRationalCover (VectorGroup.groupScheme (CommRingCat.of F) n) :=
  exists_isCompact_rational_mul_mem _ (hasTriangularCoordinates_vectorGroup F n)

/-- Every vector group over `F` has a compact set meeting every rational coset. -/
theorem hasCompactRationalCover_of_isVectorGroupOfDimension
    {V : GroupScheme (Spec (CommRingCat.of F))} {n : ℕ}
    (hV : RelativeRoot.IsVectorGroupOfDimension V n) : HasCompactRationalCover V :=
  (hasCompactRationalCover_vectorGroup n).of_iso hV.iso

end VectorGroup

section Split

variable {F : Type u} [Field F] [NumberField F]

/-- **Fibration step.** Let `j : K → H` be a closed normal subgroup with fppf quotient
`q : H → V` that has a scheme section `s`. If `K` and `V` have compact sets meeting every
rational coset, so does `H`: the set `j(C_K) · s(C_V)` works. -/
theorem hasCompactRationalCover_of_section {H K V : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] (j : K ⟶ H) (q : H ⟶ V)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)
    (s : V.X ⟶ H.X) (hs : s ≫ q.hom.hom = 𝟙 V.X)
    (hK : HasCompactRationalCover K) (hV : HasCompactRationalCover V) :
    HasCompactRationalCover H := by
  obtain ⟨CK, hCK, hcK⟩ := hK
  obtain ⟨CV, hCV, hcV⟩ := hV
  refine ⟨(K.affinePointsTarget j _ '' CK) * ((fun v => v ≫ s) '' CV),
    (hCK.image (K.continuous_affinePointsTarget _ j)).mul
      (hCV.image (V.continuous_affinePointPostcomp _ s)), fun h => ?_⟩
  obtain ⟨yV, ⟨rV, rfl⟩, hyV⟩ := hcV (H.affinePointsTarget q _ h)
  set c := rational F V rV * H.affinePointsTarget q _ h with hc
  set g : AdelicGroupPoints F H := rational F H (rV ≫ s) with hg_def
  have hg : H.affinePointsTarget q _ g = rational F V rV := by
    simp only [hg_def, affinePointsTarget_apply, rational, affinePointMap_apply,
      Category.assoc, hs, Category.comp_id]
  have hcs : H.affinePointsTarget q _ (c ≫ s) = c := by
    rw [affinePointsTarget_apply, Category.assoc, hs, Category.comp_id]
  set h' : AdelicGroupPoints F H := g * h * (c ≫ s)⁻¹ with hh'_def
  have hh' : h' ≫ q.hom.hom = 1 := by
    change H.affinePointsTarget q _ h' = 1
    rw [hh'_def, map_mul, map_mul, map_inv, hg, hcs, hc, mul_inv_cancel]
  obtain ⟨k, hk⟩ : ∃ k, k ≫ j.hom.hom = h' := by
    have hmem := (mem_range_kernelι_iff q h').mpr hh'
    rw [hq] at hmem
    exact hmem
  obtain ⟨δ, ⟨rK, rfl⟩, hδ⟩ := hcK k
  refine ⟨rational F H (rK ≫ j.hom.hom) * g, mul_mem ⟨_, rfl⟩ ⟨_, rfl⟩, ?_⟩
  refine ⟨K.affinePointsTarget j _ (rational F K rK * k), ⟨_, hδ, rfl⟩, c ≫ s,
    ⟨c, hyV, rfl⟩, ?_⟩
  have hδj : K.affinePointsTarget j _ (rational F K rK) = rational F H (rK ≫ j.hom.hom) := by
    simp only [affinePointsTarget_apply, rational, affinePointMap_apply, Category.assoc]
  have hkj : K.affinePointsTarget j _ k = g * h * (c ≫ s)⁻¹ := hk
  rw [map_mul, hδj, hkj]
  group

/-- **Induction along a split series.** Under split-unipotent torsor triviality, every affine
group scheme over a number field with a split series of length `n` has a compact set of
adelic points meeting every rational coset. -/
theorem hasCompactRationalCover_of_hasSplitSeries
    (htor : SplitUnipotentAffineTorsorStatement.{u}) (n : ℕ) :
    ∀ (H : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom H.X.hom],
      RelativeRoot.HasSplitSeries n H → HasCompactRationalCover H := by
  induction n with
  | zero =>
    intro H _ hH
    refine ⟨{1}, isCompact_singleton, fun x => ⟨1, Subgroup.one_mem _, ?_⟩⟩
    have hx : x ∈ (SubgroupFunctor.range (𝟙 H)).carrier _ := ⟨x, Category.comp_id x⟩
    rw [hH, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    rw [hx, one_mul]
    exact Set.mem_singleton _
  | succ n ih =>
    intro H _ hH
    obtain ⟨K, V, j, q, hj, hKs, _, _, hq, hV, hK⟩ := hH
    have : IsAffineHom K.X.hom := HomogeneousQuotient.affine_subgroup_of_closed H K j hj
    have : IsAffineHom V.X.hom := hV.isAffineHom
    have : Smooth K.X.hom := hKs
    have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
    obtain ⟨s, hs⟩ := HomogeneousQuotient.fppf_section_of_split_unipotent_torsors H K j htor
      hj ⟨n, hK⟩ V q hq
    exact hasCompactRationalCover_of_section j q hq.2.2.2 s hs (ih K hK)
      (hasCompactRationalCover_of_isVectorGroupOfDimension hV)

end Split

/-- **Compactness for unipotent groups from splitness and torsor triviality.** If smooth
connected unipotent groups over perfect fields are split and split-unipotent torsors over
affine schemes are trivial, then `U(F) \ U(𝔸_F)` is compact for every smooth connected
unipotent affine group scheme `U` of finite type over a number field `F`. -/
theorem unipotentRationalQuotientCompact_of_split
    (hsplit : PerfectFieldUnipotentSplitStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u}) :
    UnipotentRationalQuotientCompactStatement.{u} := by
  intro F _ _ U _ _ hs hc hu
  have : Smooth U.X.hom := hs
  have : IsAffineHom U.X.hom := inferInstance
  obtain ⟨n, hn⟩ := hsplit F U hc hu
  exact compactSpace_rationalQuotient_of_hasCompactRationalCover
    (hasCompactRationalCover_of_hasSplitSeries htor n U hn)

/-- The covering form of `unipotentRationalQuotientCompact_of_split`: a compact set of adelic
points meeting every rational coset. -/
theorem exists_isCompact_rational_mul_mem_of_split
    (hsplit : PerfectFieldUnipotentSplitStatement.{u})
    (htor : SplitUnipotentAffineTorsorStatement.{u})
    (F : Type u) [Field F] [NumberField F] (U : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine U.X.left] (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left)
    (hu : IsUnipotent U) :
    HasCompactRationalCover U := by
  have : Smooth U.X.hom := hs
  have : IsAffineHom U.X.hom := inferInstance
  obtain ⟨n, hn⟩ := hsplit F U hc hu
  exact hasCompactRationalCover_of_hasSplitSeries htor n U hn

end Langlands.Global.AdelicGroupPoints
