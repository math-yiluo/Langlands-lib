import Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChartForm
import Langlands.GroupScheme.Rational.RootHeisenbergUnitaryChart
import Langlands.Geometry.Building.QuasiSplitHenselianUnitaryDepths
import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceStatement
import Langlands.Geometry.Building.AlgebraicRankOneCoordinateCalibration
import Langlands.Geometry.Building.MaximalUnramifiedBuildingExistence
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Torus.WeilRestrictionNorm
import Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RootSubgroupRepresentability
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.LocalField.ValuativeInfinite

/-! # Scheme-level unitary coordinates from coherent algebraic SU3 coordinates

Coherent algebraic SU3 coordinates `C` of a multipliable relative root `b` (with Weyl
normalization) and the upgrade of unitary charts give valued scheme-level unitary coordinates
of the root group `U_b`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
open Langlands.GroupScheme Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Building

namespace AlgebraicSU3RootCoordinates

section SplitCoroot

variable {k : Type u} [Field k]

/-- The rational point of `𝔾_m` with value `c`. -/
def gmPoint (c : kˣ) : rationalPoints (Gm (Spec (CommRingCat.of k))).toGrp :=
  (Gm.pointsEquiv (Spec (CommRingCat.of k)) (Over.mk (𝟙 _))).symm
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom c)

/-- The scalar inclusion `𝔾_m → R_{L/k} 𝔾_m` on rational points is `kˣ → Lˣ`. -/
theorem rationalUnitsEquiv_scalar_gmPoint (L : Type u) [Field L] [Algebra k L]
    [FiniteDimensional k L] (c : kˣ) :
    WeilGm.rationalUnitsEquiv k L
        (rationalPoints.map (WeilGm.scalar (CommRingCat.of k) L) (gmPoint c)) =
      Units.map (algebraMap k L).toMonoidHom c := by
  rw [WeilGm.rationalUnitsEquiv_eq_sectionUnitsEquiv]
  apply Units.ext
  change WeilGm.sectionTensorEquiv (CommRingCat.of k) L
      (WeilGm.pointsEquiv (CommRingCat.of k) L (Over.mk (𝟙 _))
        (gmPoint c ≫ (WeilGm.scalar (CommRingCat.of k) L).hom.hom) : _) = algebraMap k L c
  rw [WeilGm.scalar_points, gmPoint, MulEquiv.apply_symm_apply]
  change WeilGm.sectionTensorEquiv (CommRingCat.of k) L
      ((1 : L) ⊗ₜ ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c : k))) = _
  rw [WeilGm.sectionTensorEquiv_tmul, Algebra.algebraMap_eq_smul_one]
  congr 1
  exact (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply c

variable {S Z : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {j : Z.toGrp ⟶ G} {s : S.toGrp ⟶ Z.toGrp}
  {b : characterLattice S}
  (C : AlgebraicSU3RootCoordinates i j s b)

/-- **Split coroot points.** The coroot of base-field units lies in the image of the maximal
split torus: the composite `𝔾_m → R_{L/k} 𝔾_m → Z → G` commutes with `S` and hence factors
through it. -/
theorem exists_map_eq_corootPoint (hi : IsMaximalSplitTorus i) (hs : s ≫ j = i)
    [Mono j.hom.hom] (c : kˣ) :
    ∃ t : rationalPoints S.toGrp,
      rationalPoints.map s t = C.corootPoint (Units.map (algebraMap k C.extension).toMonoidHom c) := by
  let sc := WeilGm.scalar (CommRingCat.of k) C.extension
  let f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G := sc ≫ C.coroot ≫ j
  have hcomm : ∀ (U : Over (Spec (CommRingCat.of k)))
      (x : U ⟶ (Gm (Spec (CommRingCat.of k))).toGrp.X) (y : U ⟶ S.toGrp.X),
      Commute (x ≫ f.hom.hom) (y ≫ i.hom.hom) := by
    intro U x y
    have hx : x ≫ f.hom.hom = (x ≫ sc.hom.hom ≫ C.coroot.hom.hom) ≫ j.hom.hom := by
      simp only [f, Grp.comp_hom_hom, Category.assoc]
    have hy : y ≫ i.hom.hom = (y ≫ s.hom.hom) ≫ j.hom.hom := by
      rw [← hs, Grp.comp_hom_hom, Category.assoc]
    rw [hx, hy]
    apply (commute_iff_eq _ _).mpr
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  obtain ⟨g, hg⟩ := hi.exists_factor_of_commute isSplitTorus_gm f hcomm
  refine ⟨rationalPoints.map g (gmPoint c), ?_⟩
  apply (cancel_mono j.hom.hom).mp
  have hpt : (WeilGm.rationalUnitsEquiv k C.extension).symm
      (Units.map (algebraMap k C.extension).toMonoidHom c) =
      rationalPoints.map sc (gmPoint c) := by
    rw [MulEquiv.symm_apply_eq, rationalUnitsEquiv_scalar_gmPoint]
  have hgi := congrArg (fun φ => gmPoint c ≫ φ.hom.hom) hg
  simp only [f, Grp.comp_hom_hom] at hgi
  rw [corootPoint, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hpt]
  simp only [rationalPoints.map_apply, Category.assoc]
  rw [← hgi, ← hs, Grp.comp_hom_hom]

omit [IsAffineHom G.X.hom] in
/-- The positive character on split coroot points. -/
theorem rationalCharacterEval_extend_map (t : rationalPoints S.toGrp) :
    rationalCharacterEval C.positive.character
        (GaloisPointComparison.rationalExtend k C.extension Z.toGrp (rationalPoints.map s t)) =
      Units.map (algebraMap k C.extension).toMonoidHom
        (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm b) t) := by
  rw [GaloisPointComparison.rationalExtend_map, ← rationalCharacterEval_characterRestrict,
    C.positive.restriction, GaloisPointComparison.rationalCharacterEval_extend]

/-- **Scaling by base-field units.** For every `c ∈ kˣ` some rational point `t` of the maximal
split torus has root value `b(t) = c` and conjugates the positive coordinates by the scaling
`(u, v) ↦ (c u, c² v)`. -/
theorem exists_conj_eq_scale (hi : IsMaximalSplitTorus i) (hs : s ≫ j = i)
    [Mono j.hom.hom] (c : kˣ) :
    ∃ t : rationalPoints S.toGrp,
      rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm b) t = c ∧
      ∀ p, rationalPoints.map i t * (C.positive.equiv p : rationalPoints G) *
          (rationalPoints.map i t)⁻¹ =
        C.positive.equiv (SU3Root.Parameters.scale (algebraMap k C.extension c) p) := by
  obtain ⟨t, ht⟩ := C.exists_map_eq_corootPoint hi hs c
  have hval := C.rationalCharacterEval_extend_map t
  rw [ht, C.character_corootPoint] at hval
  have hdiag : SU3Root.diagonalRootScalar (SU3Root.fieldInvolution C.base C.extension)
      (Units.map (algebraMap k C.extension).toMonoidHom c) =
      Units.map (algebraMap k C.extension).toMonoidHom c := by
    apply Units.ext
    simp only [SU3Root.diagonalRootScalar, Units.val_mul, SU3Root.barUnit_val,
      Units.coe_map, MonoidHom.coe_coe, Units.val_inv_eq_inv_val, RingHom.toMonoidHom_eq_coe,
      SU3Root.fieldInvolution_bar]
    rw [IsScalarTower.algebraMap_apply k C.base C.extension, AlgEquiv.commutes, mul_assoc,
      mul_inv_cancel₀ (by simp), mul_one]
  rw [hdiag] at hval
  have hbt : rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm b) t = c :=
    (Units.map_injective (algebraMap k C.extension).injective hval).symm
  refine ⟨t, hbt, fun p => ?_⟩
  have hconj := C.positive.conjugation (rationalPoints.map s t) p
  have hjs : rationalPoints.map j (rationalPoints.map s t) = rationalPoints.map i t := by
    rw [← hs]
    rfl
  rw [hjs, C.rationalCharacterEval_extend_map, hbt] at hconj
  exact hconj

/-- **Scaling on a representative of the root group.** Pulled back along a representative
`jU` of `U_b`, the positive coordinates are scaled by `(u, v) ↦ (c u, c² v)` under the torus
action of a rational point with root value `c`, for every nonzero `c ∈ k`. -/
theorem exists_act_eq_scale (hi : IsMaximalSplitTorus i) (hs : s ≫ j = i)
    [Mono j.hom.hom] {U : GroupScheme (Spec (CommRingCat.of k))} (jU : U ⟶ G)
    (hjU : (RelativeRoot.subgroup i b).IsRepresentedBy jU)
    (φ : SU3Root.rationalParameters C.base C.extension → rationalPoints U)
    (hφ : ∀ p, φ p ≫ jU.hom.hom = (C.positive.equiv p : rationalPoints G))
    (c : k) (hc : c ≠ 0) :
    ∃ t : rationalPoints S.toGrp,
      (rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm b) t : k) = c ∧
      ∀ p, (RelativeRoot.subgroupAction i b jU hjU).act t (φ p) =
        φ (SU3Root.Parameters.scale (algebraMap k C.extension c) p) := by
  let : Mono jU.hom.hom := hjU.1
  obtain ⟨t, ht, hconj⟩ := C.exists_conj_eq_scale hi hs (Units.mk0 c hc)
  refine ⟨t, by rw [ht]; rfl, fun p => ?_⟩
  apply (cancel_mono jU.hom.hom).mp
  rw [RelativeRoot.subgroupAction_act_comp i b jU hjU t (φ p), hφ, hφ]
  exact hconj p

end SplitCoroot

end AlgebraicSU3RootCoordinates

set_option maxHeartbeats 400000 in
open Langlands.GroupScheme.RelativeRoot in
/-- **Valued unitary root-group coordinates from coherent algebraic SU3 coordinates.** If every
multipliable relative root of a connected reductive group has coherent algebraic SU3
coordinates with Weyl normalization (`AlgebraicSU3RootCoordinatesExistenceStatement`), and
rational homomorphisms of chart form from the unitary parameters come from actual
homomorphisms (`UnitaryChartUpgradeStatement`), then every multipliable root group over the
maximal unramified field has valued scheme-level unitary coordinates. -/
theorem multipliableRootGroupCoordinatesExistence_of_algebraicSU3
    (hc : AlgebraicSU3RootCoordinatesExistenceStatement.{u})
    (hu : UnitaryChartUpgradeStatement.{u}) :
    MultipliableRootGroupCoordinatesExistenceStatement.{u} := by
  intro F _ _ _ _ G _ B b h2b
  have hG := B.isConnectedReductive
  have hi := B.isMaximalSplitTorus
  have hS : IsSplitTorus B.S.toGrp := hi.1.1
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom B.S.toGrp.X.hom := hS.isAffineHom
  let : IsAffine B.S.toGrp.X.left := isAffine_of_isAffineHom B.S.toGrp.X.hom
  let Z := B.centralizer
  let : IsClosedImmersion Z.j.hom.hom.left := Z.isClosedSubgroup
  let : IsAffine Z.Z.X.left := isAffine_of_isAffineHom Z.j.hom.hom.left
  let : Mono Z.j.hom.hom := Z.isRepresentedBy.1
  have hq := MaximalUnramified.isQuasiSplit F hG
  have hZ : IsTorus Z.Z := isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy hq hi Z.isRepresentedBy
  have hF : HasOppositeFactorPairs B.i := by
    intro a ha g hg hg1
    exact ((rootRankOneFactorization _ G hG B.S B.i hi) a ha g hg hg1).1.exists
  have hb := mem_indivisibleRoots_of_double_mem hS hF b h2b
  obtain ⟨C, hn⟩ := hc _ G hG B.S (Z.asTorus hZ) B.i Z.j Z.s hi hZ Z.isRepresentedBy
    Z.comp_eq b hb h2b
  -- The root group, its doubled root group and a Heisenberg normal form.
  have hb0 : (b : characterLattice B.S) ≠ 0 := (mem_relativeRoots.mp b.property).1
  have h2b0 : 2 • (b : characterLattice B.S) ≠ 0 := hS.nsmul_ne_zero hb0 (by omega)
  have hhigh : ∀ n : ℕ, 3 ≤ n → n • (b : characterLattice B.S) ∉ relativeRoots B.i :=
    fun _ hn => (relativeRootSystem _ G hG B.S B.i hi).nsmul_not_mem_of_three_le b.property hn
  obtain ⟨U, jU, hjU, hjUc, -, -⟩ :=
    subgroup_has_smooth_closed_representative hS B.i (b : characterLattice B.S) hb0
  obtain ⟨U₂, j₂, hj₂, -, -, -⟩ :=
    subgroup_has_smooth_closed_representative hS B.i (2 • (b : characterLattice B.S)) h2b0
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Mono jU.hom.hom := hjU.1
  obtain ⟨D⟩ := nonempty_doubleRootCommutatorPairing hS B.i hb0 hhigh hjU hj₂
  obtain ⟨d, e, he⟩ := D.weightVectorStructure.1
  let : IsAffineHom D.V.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e, he.1⟩
  obtain ⟨m, e', he'⟩ := weightVectorCoordinatesOfNoHigherRoots hS B.i h2b0
    (hasNoHigherRoots_two_nsmul hhigh) hj₂
  let : IsAffineHom U₂.X.hom := IsVectorGroupOfDimension.isAffineHom ⟨e', he'.1⟩
  let N := heisenbergNormalForm D hS hb0 hhigh
  -- The positive coordinates as rational points of the representative `U`.
  let φe : SU3Root.rationalParameters C.base C.extension ≃* rationalPoints U :=
    C.positive.equiv.trans (hjU.pointsEquiv (Over.mk (𝟙 _))).symm
  have hφj : ∀ p, φe p ≫ jU.hom.hom = (C.positive.equiv p : rationalPoints G) := fun p =>
    hjU.pointsEquiv_symm_comp _
  have hcentral : ∀ p, φe p ≫ D.q.hom.hom = 1 ↔ p.first = 0 := by
    intro p
    rw [← mem_range_kernelι_iff D.q, D.isFppfQuotient.2.2.2]
    change φe p ≫ jU.hom.hom ∈ rootGroupPoints B.i (2 • (b : characterLattice B.S)) ↔ _
    rw [hφj, C.positive.double]
    constructor
    · rintro ⟨p', hp', hpp'⟩
      have hpp : p' = p := C.positive.equiv.injective (Subtype.ext hpp')
      rw [← hpp]
      exact hp'
    · intro hp
      exact ⟨p, hp, rfl⟩
  have hscale := fun c hc0 => C.exists_act_eq_scale hi Z.comp_eq jU hjU φe hφj c hc0
  obtain ⟨A, Bl, H, hA, hB, hform⟩ := N.exists_unitaryChartForm e e' hS hb0 hhigh he he'
    φe.toMonoidHom φe.injective φe.surjective hcentral hscale
  let : Infinite F := LocalField.infinite_of_isNonarchimedeanLocalField F
  let : Infinite (inertiaFixedField F) :=
    Infinite.of_injective _ (algebraMap F (inertiaFixedField F)).injective
  obtain ⟨ψ, hψ, hrep⟩ := hu (inertiaFixedField F) B.S G U U₂ B.i (b : characterLattice B.S)
    jU hjU j₂ hj₂ D N hS hb0 hhigh e e' he he' C.base C.extension A Bl H φe.toMonoidHom
    hA hB hform
  -- The depths at the Weyl-normalized origin.
  have hH := MaximalUnramified.valuationSubring_isHenselian F
  have hdepth := (C.coordinateOrigin_depths Z hZ B.apartment B.isOmegaCompatible hG hi
    b.property hn
    (IntegerValuation.isNormCalibrated_henselianSeparableAddValuation hH C.extension)
    (SU3Root.henselianSeparableAddValuation_quadratic_bar _ C.base C.extension
      (MaximalUnramified.valuation F) hH)).1
  refine ⟨⟨C.base, C.extension, ψ ≫ jU, hrep, C.coordinateOrigin Z hZ B.apartment hn,
    fun p => ?_⟩⟩
  have hmap : ∀ y, rationalPoints.map (ψ ≫ jU) y = rationalPoints.map ψ y ≫ jU.hom.hom := by
    intro y
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hmap, hψ, MulEquiv.coe_toMonoidHom, hφj]
  exact hdepth p

end Langlands.Geometry.Building
