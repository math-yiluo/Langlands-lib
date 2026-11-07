import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison
import Langlands.GroupScheme.Reductive.LocalSplitCorootTransport
import Langlands.GroupScheme.Reductive.LinkedRootParametrization
import Langlands.GroupScheme.Reductive.SplitPinnedOppositeFactorPairs
import Langlands.GroupScheme.Reductive.RootDatumSubgroupCoroots
import Langlands.GroupScheme.Reductive.RepresentationWeightsFibreComparison
import Langlands.GroupScheme.Rational.RootSubgroupAutomorphismRigidity
import Langlands.GroupScheme.Rational.RootSubgroupSeparation
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Torus.WeylImageFinite

/-! # Weyl normalization of opposite root groups on field fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitCell

open CoordinateRootDatum LocalSplitBigCell

/-! ### Values of root maps -/

section Ring

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}

theorem scalarPoint_add (Z : Over (Spec (CommRingCat.of R))) (c c' : Γ(Z.left, ⊤)) :
    VectorGroup.scalarPoint (CommRingCat.of R) Z (c + c') =
      VectorGroup.scalarPoint _ Z c * VectorGroup.scalarPoint _ Z c' :=
  VectorGroup.points_ext fun j => by
    rw [VectorGroup.coordinates_mul, Pi.add_apply, VectorGroup.coordinates_scalarPoint,
      VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint]

theorem rootPoint_add (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) (c c' : Γ(Z.left, ⊤)) :
    rootPoint u Z (c + c') = rootPoint u Z c * rootPoint u Z c' := by
  rw [rootPoint, scalarPoint_add, MonObj.mul_comp]
  rfl

theorem rootPoint_neg (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint u Z (-c) = (rootPoint u Z c)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootPoint_add, neg_add_cancel, rootPoint_zero]

theorem comp_eq_rootPoint (u : Ga R ⟶ G) {Z : Over (Spec (CommRingCat.of R))}
    (a : Z ⟶ (Ga R).X) : a ≫ u.hom.hom = rootPoint u Z (gaCoord a) := by
  rw [rootPoint, VectorGroup.scalarPoint_coordinate]

end Ring

/-! ### Rescalings over a field -/

section Field

variable {k : Type u} [Field k]

local notation "pt" => 𝟙_ (Over (Spec (CommRingCat.of k)))

theorem toUnit_left (Z : Over (Spec (CommRingCat.of k))) : (toUnit Z).left = Z.hom := by
  simp

theorem baseScalar_ΓSpecIso_hom (Z : Over (Spec (CommRingCat.of k)))
    (x : Γ((𝟙_ (Over (Spec (CommRingCat.of k)))).left, ⊤)) :
    baseScalar Z ((Scheme.ΓSpecIso (CommRingCat.of k)).hom x) = (toUnit Z).left.appTop x := by
  rw [toUnit_left]
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Z.hom.appTop)
    ((Scheme.ΓSpecIso (CommRingCat.of k)).hom x) = _
  rw [CommRingCat.comp_apply, Iso.hom_inv_id_apply]

/-- An endomorphism of `𝔾ₐ` over a field that is linear in the coordinate is a rescaling. -/
theorem exists_eq_scaleHom {q : Ga k ⟶ Ga k}
    (hq : RelativeRoot.IsCoordinateLinear (VectorGroup.coordinates (CommRingCat.of k) 1) q) :
    ∃ l : k, q = scaleHom l := by
  let l0 : Γ((𝟙_ (Over (Spec (CommRingCat.of k)))).left, ⊤) :=
    gaCoord (VectorGroup.scalarPoint _ pt 1 ≫ q.hom.hom)
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom l0, ?_⟩
  apply hom_ext_points
  intro Z a
  rw [comp_scaleHom, baseScalar_ΓSpecIso_hom]
  have ha : a = RelativeRoot.coordinateSmul (VectorGroup.coordinates (CommRingCat.of k) 1) Z
      (gaCoord a) (VectorGroup.scalarPoint _ Z 1) := by
    apply VectorGroup.points_ext
    intro j
    rw [RelativeRoot.coordinateSmul_coord, Subsingleton.elim j 0, Pi.smul_apply,
      VectorGroup.coordinates_scalarPoint, smul_eq_mul, mul_one]
  have h1 : VectorGroup.scalarPoint (CommRingCat.of k) Z 1 =
      toUnit Z ≫ VectorGroup.scalarPoint _ pt 1 := by
    rw [VectorGroup.scalarPoint_comp, map_one]
  have hl := hq Z (gaCoord a) (VectorGroup.scalarPoint _ Z 1)
  rw [← ha, h1, Category.assoc, VectorGroup.coordinates_comp (toUnit Z)] at hl
  apply VectorGroup.points_ext
  intro j
  rw [Subsingleton.elim j 0, VectorGroup.coordinates_scalarPoint]
  have hl0 := congrFun hl 0
  simp only [Pi.smul_apply, smul_eq_mul] at hl0
  rw [hl0, mul_comm]

/-- A rescaling by zero is not a monomorphism. -/
theorem ne_zero_of_mono_scaleHom {l : k} [Mono (scaleHom l).hom.hom] : l ≠ 0 := by
  rintro rfl
  have h : VectorGroup.scalarPoint (CommRingCat.of k) pt 1 ≫ (scaleHom (0 : k)).hom.hom =
      (1 : pt ⟶ (Ga k).X) ≫ (scaleHom (0 : k)).hom.hom := by
    rw [comp_scaleHom, map_zero, zero_mul, MonObj.one_comp]
    apply VectorGroup.points_ext
    intro j
    rw [VectorGroup.coordinates_scalarPoint, map_one]
    rfl
  have h' := congrArg (fun x => gaCoord x) ((cancel_mono _).mp h)
  simp only [gaCoord, VectorGroup.coordinates_scalarPoint, map_one, toAdd_one] at h'
  exact one_ne_zero_unit_sections h'

local instance : IsAffineHom (Ga k).X.hom := VectorGroup.isAffineHom_groupScheme _ 1

variable {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

theorem scalarPoint_comp_eq_rootPoint (x : Ga k ⟶ G) (Z : Over (Spec (CommRingCat.of k)))
    (c : Γ(Z.left, ⊤)) : VectorGroup.scalarPoint _ Z c ≫ x.hom.hom = rootPoint x Z c :=
  rfl

/-- Two equivariant parametrizations of the same root subgroup differ by a nonzero
rescaling. -/
theorem exists_eq_scaleHom_comp (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G}
    {α : characterLattice T} (hα : α ≠ 0) {x w : Ga k ⟶ G}
    (hxr : (RelativeRoot.subgroup i α).IsRepresentedBy x)
    (hwr : (RelativeRoot.subgroup i α).IsRepresentedBy w)
    (hx : VectorGroup.IsTorusEquivariant i x α) (hw : VectorGroup.IsTorusEquivariant i w α) :
    ∃ l : k, l ≠ 0 ∧ x = scaleHom l ≫ w := by
  let q := hxr.isoOfIsRepresentedBy hwr
  have hqw : q.hom ≫ w = x := hxr.isoOfIsRepresentedBy_hom_comp hwr
  have : Mono w.hom.hom := hwr.1
  have hc (Z : Over (Spec (CommRingCat.of k))) (v : Z ⟶ (Ga k).X) :
      (v ≫ q.hom.hom.hom) ≫ w.hom.hom = v ≫ x.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hqw]
  have hq : ∀ (X : Over (Spec (CommRingCat.of k))) (s : X ⟶ T.X) (v : X ⟶ (Ga k).X),
      (VectorGroup.weightAction α).act s v ≫ q.hom.hom.hom =
        (VectorGroup.weightAction α).act s (v ≫ q.hom.hom.hom) := by
    intro X s v
    apply (cancel_mono w.hom.hom).mp
    rw [hc, hx.weightAction_comp, hw.weightAction_comp, hc]
  have hlin := RelativeRoot.isCoordinateLinear_of_weightCoordinates (q := q) hT hα
    (VectorGroup.isWeightVectorCoordinates_weightAction (n := 1) α) hq
  obtain ⟨l, hl⟩ := exists_eq_scaleHom hlin
  refine ⟨l, ?_, by rw [← hl, hqw]⟩
  have : Mono (scaleHom l).hom.hom := by
    rw [← hl]
    infer_instance
  exact ne_zero_of_mono_scaleHom

/-- The rank-one relation for `(u ∘ l, v ∘ m)` is the relation for `(u, v ∘ (l m))`. -/
theorem relationOver_scaleHom {i : T.toGrp ⟶ G} {χv : cocharacterLattice T} {u v : Ga k ⟶ G}
    {l m : k} (hl : l ≠ 0) {Z : Over (Spec (CommRingCat.of k))}
    (h : RootCell.RelationOver i χv (scaleHom l ≫ u) (scaleHom m ≫ v) Z) :
    RootCell.RelationOver i χv u (scaleHom (l * m) ≫ v) Z := by
  intro a b a' b' w hw ha' hb'
  obtain ⟨L, hLv⟩ : IsUnit (baseScalar Z l) := (isUnit_iff_ne_zero.mpr hl).map (baseScalar Z)
  simp only [RootCell.crd] at hw ha' hb'
  have key := h (VectorGroup.scalarPoint _ Z (↑L⁻¹ * RootCell.crd a))
    (VectorGroup.scalarPoint _ Z (↑L * RootCell.crd b))
    (VectorGroup.scalarPoint _ Z (↑L⁻¹ * RootCell.crd a'))
    (VectorGroup.scalarPoint _ Z (↑L * RootCell.crd b')) w ?_ ?_ ?_
  · have e1 : ∀ c : Γ(Z.left, ⊤), baseScalar Z l * (↑L⁻¹ * c) = c := by
      intro c
      rw [← hLv, ← mul_assoc, Units.mul_inv, one_mul]
    have e2 : ∀ c : Γ(Z.left, ⊤), baseScalar Z m * (↑L * c) = baseScalar Z (l * m) * c := by
      intro c
      rw [hLv, map_mul, ← mul_assoc, mul_comm (baseScalar Z m)]
    simp only [RootCell.RelationAt, scalarPoint_comp_eq_rootPoint, rootPoint_scaleHom, e1, e2]
      at key
    simp only [RootCell.RelationAt, comp_eq_rootPoint, rootPoint_scaleHom]
    exact key
  · simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint]
    rw [hw, mul_mul_mul_comm, Units.inv_mul, one_mul]
  · simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint]
    rw [ha', mul_left_comm]
  · simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint]
    rw [hb', mul_left_comm]

/-! ### Opposite factor pairs of a linked pair -/

section FactorPair

variable [IsAffineHom G.X.hom] (hT : IsSplitTorus T.toGrp) {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {α : characterLattice T} (hα : α ≠ 0) {χv : cocharacterLattice T}
  {u v : Ga k ⟶ G} (hur : (RelativeRoot.subgroup i α).IsRepresentedBy u)
  (hvr : (RelativeRoot.subgroup i (-α)).IsRepresentedBy v)
  (hv : VectorGroup.IsTorusEquivariant i v (-α))
  (hrel : RootCell.RelationOver i χv u v (𝟙_ (Over (Spec (CommRingCat.of k)))))

include hT hα hur hvr hv hrel

/-- If `(p₁, v(z))` is a normalizing opposite pair of `u(X)` for a pair `(u, v)` satisfying the
rank-one relation, then `1 + X z = 0`: otherwise the relation writes `p₁ u(X) v(z)` as a torus
point times a product of opposite root points, which forces it into the torus. -/
theorem one_add_mul_eq_zero_of_isOppositeFactorPair
    {X z : Γ((𝟙_ (Over (Spec (CommRingCat.of k)))).left, ⊤)} (hx1 : rootPoint u pt X ≠ 1)
    {p₁ : pt ⟶ G.X}
    (hp : RelativeRoot.IsOppositeFactorPair i α (rootPoint u pt X) (p₁, rootPoint v pt z)) :
    1 + X * z = 0 := by
  by_contra hne
  have hfb : ∀ y : Γ((𝟙_ (Over (Spec (CommRingCat.of k)))).left, ⊤), y = 0 ∨ IsUnit y :=
    fun y => RankOneRootCellRelation.field_base (k := k) y
  obtain ⟨W, hW⟩ := (hfb (1 + X * z)).resolve_left hne
  have hR := hrel (VectorGroup.scalarPoint _ pt X) (VectorGroup.scalarPoint _ pt z)
    (VectorGroup.scalarPoint _ pt (↑W⁻¹ * X)) (VectorGroup.scalarPoint _ pt (↑W⁻¹ * z)) W
    (by simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint]; exact hW)
    (by simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint])
    (by simp only [RootCell.crd, VectorGroup.coordinates_scalarPoint])
  simp only [RootCell.RelationAt, scalarPoint_comp_eq_rootPoint] at hR
  let s : pt ⟶ T.X := (Gm.pointsEquiv _ pt).symm W ≫ (CommGroupScheme.groupHom χv).hom.hom
  have htt : (Gm.pointsEquiv _ pt).symm W ≫ (CommGroupScheme.groupHom χv).hom.hom ≫
      i.hom.hom = s ≫ i.hom.hom := (Category.assoc _ _ _).symm
  rw [htt] at hR
  have hcent : s ≫ i.hom.hom ∈ centralizerPoints i := by
    rw [← torusCentralizer_carrier_base]
    exact range_le_torusCentralizer i _ ⟨s, rfl⟩
  have hmemv : ∀ c, rootPoint v pt c ∈ (RelativeRoot.subgroup i (-α)).carrier pt := fun c => by
    rw [← hvr.2]
    exact ⟨_, rfl⟩
  have hmemu : ∀ c, rootPoint u pt c ∈ (RelativeRoot.subgroup i α).carrier pt := fun c => by
    rw [← hur.2]
    exact ⟨_, rfl⟩
  -- the product `p₁ v(z/w)` is a value of `v`
  obtain ⟨c, hc⟩ : ∃ c, rootPoint v pt c = p₁ * rootPoint v pt (↑W⁻¹ * z) := by
    let e := (hvr.pointsEquiv pt).symm
      ⟨p₁ * rootPoint v pt (↑W⁻¹ * z), Subgroup.mul_mem _ hp.1 (hmemv _)⟩
    refine ⟨gaCoord e, ?_⟩
    rw [← comp_eq_rootPoint]
    exact SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hvr _
  have hinv : (s ≫ i.hom.hom)⁻¹ = s⁻¹ ≫ i.hom.hom := (GrpObj.inv_comp s i.hom.hom).symm
  have hconj : (s ≫ i.hom.hom)⁻¹ * rootPoint v pt c * (s ≫ i.hom.hom) =
      rootPoint v pt (VectorGroup.charValue (-α) pt s⁻¹ * c) := by
    have h2 : s ≫ i.hom.hom = (s⁻¹ ≫ i.hom.hom)⁻¹ := by rw [GrpObj.inv_comp, inv_inv]
    rw [hinv, h2]
    exact hv pt s⁻¹ c
  have hn0 := hp.2.2
  let n₁ : normalizerPoints i := ⟨(s ≫ i.hom.hom)⁻¹ * (p₁ * rootPoint u pt X * rootPoint v pt z),
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (centralizerPoints_le_normalizerPoints i hcent)) hn0⟩
  have hn₁ : n₁.val = rootPoint v pt (VectorGroup.charValue (-α) pt s⁻¹ * c) *
      rootPoint u pt (↑W⁻¹ * X) := by
    rw [← hconj, hc]
    change (s ≫ i.hom.hom)⁻¹ * (p₁ * rootPoint u pt X * rootPoint v pt z) = _
    rw [mul_assoc p₁, hR]
    simp only [mul_assoc]
  have h1 := RelativeRoot.normalizer_eq_one_of_mul_opposite i hT (neg_ne_zero.mpr hα) n₁
    (hmemv _) (by rw [neg_neg]; exact hmemu _) hn₁
  have heq : p₁ * rootPoint u pt X * rootPoint v pt z = s ≫ i.hom.hom := by
    have h := congrArg Subtype.val h1
    change (s ≫ i.hom.hom)⁻¹ * (p₁ * rootPoint u pt X * rootPoint v pt z) = 1 at h
    exact (inv_mul_eq_one.mp h).symm
  have hw1 := weylAction_eq_one_of_mem_centralizerPoints i
    (n := ⟨p₁ * rootPoint u pt X * rootPoint v pt z, hn0⟩) (by
      change p₁ * rootPoint u pt X * rootPoint v pt z ∈ centralizerPoints i
      rw [heq]
      exact hcent)
  apply hp.weylAction_ne_self i hT hα (hmemu X) hx1
  change weylAction i ⟨p₁ * rootPoint u pt X * rootPoint v pt z, hn0⟩ α = α
  rw [hw1]
  rfl

omit [IsAffineHom G.X.hom] hT [Mono i.hom.hom.left] hα hur hv hrel in
theorem exists_rootPoint_eq {g : pt ⟶ G.X}
    (hg : g ∈ (RelativeRoot.subgroup i (-α)).carrier pt) : ∃ c, rootPoint v pt c = g := by
  refine ⟨gaCoord ((hvr.pointsEquiv pt).symm ⟨g, hg⟩), ?_⟩
  rw [← comp_eq_rootPoint]
  exact SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hvr _

/-- For a pair `(u, v)` satisfying the rank-one relation, `(v(-1), v(-1))` is the normalizing
opposite pair of `u(1)`, provided some normalizing opposite pair exists. -/
theorem isOppositeFactorPair_weylPoint (hαr : α ∈ relativeRoots i)
    (hfac : RelativeRoot.HasOppositeFactorPairs i) (hx1 : rootPoint u pt 1 ≠ 1) :
    RelativeRoot.IsOppositeFactorPair i α (rootPoint u pt 1)
      (rootPoint v pt (-1), rootPoint v pt (-1)) := by
  have hmemu : ∀ c, rootPoint u pt c ∈ (RelativeRoot.subgroup i α).carrier pt := fun c => by
    rw [← hur.2]
    exact ⟨_, rfl⟩
  obtain ⟨⟨p₁, p₂⟩, hp⟩ := hfac α hαr (rootPoint u pt 1) (hmemu 1) hx1
  obtain ⟨z₁, rfl⟩ := exists_rootPoint_eq hvr hp.1
  obtain ⟨z₂, rfl⟩ := exists_rootPoint_eq hvr hp.2.1
  have h₂ := one_add_mul_eq_zero_of_isOppositeFactorPair hT hα hur hvr hv hrel hx1 hp
  rw [one_mul, add_eq_zero_iff_eq_neg'] at h₂
  have hx1' : rootPoint u pt (-1) ≠ 1 := by
    rw [rootPoint_neg]
    exact inv_ne_one.mpr hx1
  have hp' : RelativeRoot.IsOppositeFactorPair i α (rootPoint u pt (-1))
      (rootPoint v pt (-z₂), rootPoint v pt (-z₁)) := by
    refine ⟨?_, ?_, ?_⟩
    · show rootPoint v pt (-z₂) ∈ _
      rw [rootPoint_neg]
      exact Subgroup.inv_mem _ hp.2.1
    · show rootPoint v pt (-z₁) ∈ _
      rw [rootPoint_neg]
      exact Subgroup.inv_mem _ hp.1
    · show rootPoint v pt (-z₂) * rootPoint u pt (-1) * rootPoint v pt (-z₁) ∈ _
      have h := Subgroup.inv_mem _ hp.2.2
      change (rootPoint v pt z₁ * rootPoint u pt 1 * rootPoint v pt z₂)⁻¹ ∈ _ at h
      simp only [mul_inv_rev, ← rootPoint_neg, ← mul_assoc] at h
      exact h
  have h₁ := one_add_mul_eq_zero_of_isOppositeFactorPair hT hα hur hvr hv hrel hx1' hp'
  rw [neg_mul_neg, one_mul, add_eq_zero_iff_eq_neg'] at h₁
  rw [h₁, h₂] at hp
  exact hp

end FactorPair

end Field

/-! ### Weyl points from normalizing points -/

section WeylPoint

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- A point normalizing the torus through the exponent automorphism of `f` is a Weyl point
for `f`. This is the converse of `IsWeylPoint.isNormalizingPoint`. -/
theorem isWeylPoint_of_isNormalizingPoint {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X} {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i n
      (splitTorus.exponentCommIso _ I f)) : IsWeylPoint i n f := by
  intro Z t
  have h' := congrArg (fun g : splitTorus (Spec (CommRingCat.of R)) I ⟶ G => t ≫ g.hom.hom) h
  simp only [Grp.comp_hom_hom] at h'
  rw [← Category.assoc, GroupScheme.comp_innerIso_hom] at h'
  rw [toUnit_comp_eq_constantPoint, h']
  rfl

end WeylPoint

/-! ### The field statement -/

section FieldStatement

variable {k : Type u} [Field k] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}

local notation "pt" => 𝟙_ (Over (Spec (CommRingCat.of k)))

/-- **Weyl normalization over a field.** For root parametrizations `u` of a root `a` and `v` of
`-a` of a split maximal torus with a reduced coordinate root datum, some nonzero rescaling of
`v` satisfies the rank-one relation with `u`, and the resulting Weyl point acts through the
reflection `s_a`. -/
theorem exists_fieldWeylNormalization {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
    (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
    (hi : IsMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hred : P.IsReduced)
    (hP : IsRootDatumOf i (fieldRealization k P)) (a : J) {u v : Ga k ⟶ G}
    (hu : IsRootParametrization i (P.root a) u)
    (hv : IsRootParametrization i (P.root (P.reflectionPerm a a)) v) :
    ∃ d : k, d ≠ 0 ∧
      (∀ Z : Over (Spec (CommRingCat.of k)),
        RootCell.RelationOver (T := splitTorus.commGroupScheme _ I) i
          (splitTorus.exponentCocharacter _ I (P.coroot a)) u (scaleHom d ≫ v) Z) ∧
      IsWeylPoint i (weylPoint u (scaleHom d ≫ v)) (P.reflection a) := by
  have := hG.smooth
  have hT : IsSplitTorus (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I).toGrp :=
    isSplitTorus_splitTorus I
  have : Mono i.hom.hom.left := hi.2.1.mono
  have hαP : (fieldRealization k P).root a =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a) :=
    fieldRealization_root k P a
  have hnegm : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I
      (P.root (P.reflectionPerm a a)) =
        -splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a) := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
      splitTorus.exponentCharacter_neg]
  have hneg : (fieldRealization k P).root (P.reflectionPerm a a) =
      -splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a) := by
    rw [fieldRealization_root, hnegm]
  set α := splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a) with hαdef
  have hα0 : α ≠ 0 := hαP ▸ (fieldRealization k P).ne_zero a
  have hαroot : α ∈ roots i := hαP ▸ (hP.2.1 ▸ Set.mem_range_self a)
  have hnegroot : -α ∈ roots i := hneg ▸ (hP.2.1 ▸ Set.mem_range_self (P.reflectionPerm a a))
  have hhigh : RelativeRoot.HasNoHigherRoots i α :=
    hαP ▸ hasNoHigherRoots_fieldRealization hred hP a
  have hhighneg : RelativeRoot.HasNoHigherRoots i (-α) :=
    hneg ▸ hasNoHigherRoots_fieldRealization hred hP (P.reflectionPerm a a)
  obtain ⟨xp, xm, hxpm, hxmm, hxp, hxm, hrel⟩ :=
    exists_monic_rootRankOneRelations hG hT i hi (fieldRealization k P) hP a
  rw [hαP] at hxp hxm
  have := hxpm
  have := hxmm
  have hxpr := hxp.represents_root hG hT hi hαroot hhigh
  have hxmr := hxm.represents_root hG hT hi hnegroot hhighneg
  have hur : (RelativeRoot.subgroup i α).IsRepresentedBy u := hu.represents
  have hvr : (RelativeRoot.subgroup i (-α)).IsRepresentedBy v := by
    have h := hv.represents
    rwa [hnegm] at h
  have hue : VectorGroup.IsTorusEquivariant i u α := fun Z t c => hu.equivariant Z t c
  have hve : VectorGroup.IsTorusEquivariant i v (-α) := by
    intro Z t c
    have h := hv.equivariant Z t c
    rwa [hnegm] at h
  obtain ⟨l, hl0, hl⟩ := exists_eq_scaleHom_comp hT hα0 hxpr hur hxp hue
  obtain ⟨m, hm0, hm⟩ := exists_eq_scaleHom_comp hT (neg_ne_zero.mpr hα0) hxmr hvr hxm hve
  have hrel' : ∀ Z : Over (Spec (CommRingCat.of k)),
      RootCell.RelationOver (T := splitTorus.commGroupScheme _ I) i
        (splitTorus.exponentCocharacter _ I (P.coroot a)) u (scaleHom (l * m) ≫ v) Z := by
    intro Z
    have h := hrel Z
    rw [hl, hm, fieldRealization_coroot] at h
    exact relationOver_scaleHom hl0 h
  refine ⟨l * m, mul_ne_zero hl0 hm0, hrel', ?_⟩
  have hv' := hv.scale (Units.mk0 (l * m) (mul_ne_zero hl0 hm0))
  rw [Units.val_mk0] at hv'
  have hv'r : (RelativeRoot.subgroup i (-α)).IsRepresentedBy (scaleHom (l * m) ≫ v) := by
    have h := hv'.represents
    rwa [hnegm] at h
  have hv'e : VectorGroup.IsTorusEquivariant i (scaleHom (l * m) ≫ v) (-α) := by
    intro Z t c
    have h := hv'.equivariant Z t c
    rwa [hnegm] at h
  have hx1 : rootPoint u pt 1 ≠ 1 := by
    intro h
    exact one_ne_zero_unit_sections
      (hu.rootPoint_injective pt (h.trans (rootPoint_zero u pt).symm))
  have hfac := hasOppositeFactorPairs_of_rootDatum hG hT i hi (fieldRealization k P) hP
  have hαr : α ∈ relativeRoots i := by
    rw [relativeRoots_eq_roots]
    exact hαroot
  have hpair := isOppositeFactorPair_weylPoint hT hα0 hur hv'r hv'e (hrel' pt) hαr hfac hx1
  have hmemu : rootPoint u pt 1 ∈ (RelativeRoot.subgroup i α).carrier pt := by
    rw [← hur.2]
    exact ⟨_, rfl⟩
  have hcs := RelativeRoot.IsOppositeFactorPair.coroot_spec
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i hT hα0 hmemu hx1 hpair
  have hpair2 := hcs.1
  have hspec := hcs.2
  have : IsClosedImmersion i.hom.hom.left := hi.2.1
  have : Finite (weylImage (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i) :=
    splitTorusWeylImageFinite k G (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) hT i
      hi.2.1
  let n : normalizerPoints (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i :=
    ⟨_, hpair.2.2⟩
  set ν := RelativeRoot.IsOppositeFactorPair.coroot
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i hT hα0 hmemu hx1 hpair
    with hνdef
  have hν2 : latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      ((fieldRealization k P).root a) ν = 2 := by
    rw [hαP]
    exact hpair2
  have hνn : ∀ χ, weylAction (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i n χ =
      χ - latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) χ ν •
        (fieldRealization k P).root a := by
    intro χ
    rw [hαP]
    exact hspec χ
  have hcor : ν = (fieldRealization k P).coroot a :=
    IsRootDatumOf.coroot_eq_of_weylAction_of_finite_weylImage
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) (i := i) hP a ν hν2 n hνn
  obtain ⟨σ, hσ⟩ := hpair.2.2
  have hσchar : ∀ m' : I → ℤ, characterAut σ (splitTorus.exponentCharacter _ I m') =
      splitTorus.exponentCharacter _ I (P.reflection a m') := by
    intro m'
    have h1 : characterAut σ (splitTorus.exponentCharacter _ I m') =
        weylAction (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i n
          (splitTorus.exponentCharacter _ I m') :=
      (weylAction_eq (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) i (n := n) hσ
        _).symm
    rw [h1]
    refine (hνn _).trans ?_
    rw [hcor, ← fieldRealization_reflection_exponentCharacter, RootPairing.reflection_apply]
    change _ = _ - (fieldRealization k P).toLinearMap _ ((fieldRealization k P).coroot a) •
      (fieldRealization k P).root a
    rw [hP.1]
  have hσeq := splitTorus.eq_exponentCommIso_symm I (P.reflection a) σ hσchar
  have hsymm : (splitTorus.exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a)).symm =
      splitTorus.exponentCommIso _ I (P.reflection a) := by
    apply Iso.ext
    change splitTorus.exponentHom _ I I (P.reflection a).symm.toLinearMap =
      splitTorus.exponentHom _ I I (P.reflection a).toLinearMap
    rw [show (P.reflection a).symm = P.reflection a from P.reflection_inv a]
  apply isWeylPoint_of_isNormalizingPoint
  have hσ' : IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i
      (weylPoint u (scaleHom (l * m) ≫ v)) σ := hσ
  rw [hσeq, hsymm] at hσ'
  exact hσ'

/-- **Weyl normalization on field fibres**: `FieldWeylNormalizationStatement` holds. Over each
field `k` with an `R`-algebra structure, the base-changed data satisfy the hypotheses of
`exists_fieldWeylNormalization`. -/
theorem fieldWeylNormalization : FieldWeylNormalizationStatement.{u} := by
  intro R _ G _ hG I _ _ i hmax J P hP a u v hu hv k _ _
  have := hG.smooth
  let : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))
  exact exists_fieldWeylNormalization (hG.isConnectedReductive_algebraMap k)
    (splitTorus.baseChangeHom (K := k) G I i)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k) hP.isReduced
    (hP.field k) a (isRootParametrization_baseChangeRoot k i _ _ hu)
    (isRootParametrization_baseChangeRoot k i _ _ hv)

end FieldStatement

end Langlands.GroupScheme.LocalSplitCell
