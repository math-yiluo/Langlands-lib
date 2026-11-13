import Langlands.Geometry.Building.SplitIntegralPinning
import Langlands.Geometry.Building.ChevalleyRootFamily
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField
import Langlands.GroupScheme.Reductive.RootPairNoncommutation
import Langlands.GroupScheme.Reductive.LocalSplitWeylFamily
import Langlands.GroupScheme.Rational.RelativeWeylCoxeterProof
import Langlands.GroupScheme.Rational.RelativeTitsMulCellReduction
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.SplitExistence.OppositeFactorPairs

/-! # Split integral pinnings from root parametrizations over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.LocalSplitCell
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace SplitIntegralPinning

variable {k : Type u} [Field k] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "pt" => Over.mk (𝟙 (Spec (CommRingCat.of k)))
variable (k I) in
/-- The coordinate split torus over `k`, as a commutative group scheme. -/
abbrev coordTorus : CommGroupScheme (Spec (CommRingCat.of k)) :=
  splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I

/-- Field elements as global functions on the base point. -/
def baseRingEquiv : k ≃+* Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv

theorem baseRingEquiv_apply (c : k) :
    baseRingEquiv c = (Scheme.ΓSpecIso (CommRingCat.of k)).inv c := rfl

/-- The rational point `w(c)` of a map `w : 𝔾ₐ ⟶ G` at a field element `c`. -/
def fieldRootPoint (w : Ga k ⟶ G) (c : k) : rationalPoints G :=
  rootPoint w pt (baseRingEquiv c)

theorem fieldRootPoint_add (w : Ga k ⟶ G) (c d : k) :
    fieldRootPoint w (c + d) = fieldRootPoint w c * fieldRootPoint w d := by
  rw [fieldRootPoint, map_add, rootPoint_add]
  rfl

theorem fieldRootPoint_zero (w : Ga k ⟶ G) : fieldRootPoint w 0 = 1 := by
  rw [fieldRootPoint, map_zero, rootPoint_zero]

theorem exponentCharacter_injective' :
    Function.Injective (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I) := by
  intro a a' h
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k] at h
  exact (splitTorus.characterLatticeEquiv k I).symm.injective h

variable (P : RootDatum J (I → ℤ) (I → ℤ))

/-- The character of the coordinate torus of a root of the coordinate datum. -/
abbrev rootChar (α : J) : characterLattice (coordTorus k I) :=
  splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α)

theorem rootChar_injective : Function.Injective (rootChar (k := k) P) :=
  exponentCharacter_injective'.comp P.root.injective

variable (w : J → (Ga k ⟶ G))

open Classical in
/-- The root family attached to root maps `w α`: at the character of a root `α` it is
`c ↦ w α (c)`, and it is constant `1` at every other character. -/
def rootFamily (a : characterLattice (coordTorus k I)) (c : k) : rationalPoints G :=
  if h : ∃ α, rootChar (k := k) P α = a then fieldRootPoint (w h.choose) c else 1

theorem rootFamily_rootChar (α : J) (c : k) :
    rootFamily P w (rootChar P α) c = fieldRootPoint (w α) c := by
  have h : ∃ β, rootChar (k := k) P β = rootChar P α := ⟨α, rfl⟩
  rw [rootFamily, dite_eq_left_of_eq_true (eq_true h), rootChar_injective P h.choose_spec]

variable {P} [IsAffineHom G.X.hom]

theorem relativeRoots_eq_range {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
    (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P)) :
    relativeRoots (T := coordTorus k I) i = Set.range (rootChar (k := k) P) := by
  rw [relativeRoots_eq_roots, ← hP.2.1]
  congr 1
  funext α
  exact CoordinateRootDatum.fieldRealization_root k P α

section Fields

variable {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))
  {w : J → (Ga k ⟶ G)} (hu : ∀ α, IsRootParametrization i (P.root α) (w α))

include hP in
theorem exists_eq_rootChar {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i) :
    ∃ α, rootChar (k := k) P α = a := by
  rw [relativeRoots_eq_range hP] at ha
  exact ha

include hP in
theorem rootFamily_add {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i)
    (c d : k) : rootFamily P w a (c + d) = rootFamily P w a c * rootFamily P w a d := by
  obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
  simp only [rootFamily_rootChar, fieldRootPoint_add]

omit [IsAffineHom G.X.hom] in
include hu in
theorem fieldRootPoint_mem (α : J) (c : k) :
    fieldRootPoint (w α) c ∈ rootGroupPoints (S := coordTorus k I) i (rootChar P α) :=
  (hu α).rootPoint_mem pt _

include hP hu in
theorem rootFamily_mem {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i) (c : k) :
    rootFamily P w a c ∈ rootGroupPoints (S := coordTorus k I) i a := by
  obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
  rw [rootFamily_rootChar]
  exact fieldRootPoint_mem hu α c

omit [IsAffineHom G.X.hom] in
include hu in
theorem exists_fieldRootPoint_eq (α : J) {g : rationalPoints G}
    (hg : g ∈ rootGroupPoints (S := coordTorus k I) i (rootChar P α)) :
    ∃ c : k, fieldRootPoint (w α) c = g := by
  have hr := (hu α).represents
  refine ⟨baseRingEquiv.symm (LocalSplitCell.gaCoord ((hr.pointsEquiv pt).symm ⟨g, hg⟩)), ?_⟩
  rw [fieldRootPoint, RingEquiv.apply_symm_apply, ← comp_eq_rootPoint]
  exact SubgroupFunctor.IsRepresentedBy.pointsEquiv_symm_comp hr _

include hP hu in
theorem rootFamily_surjective {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints (S := coordTorus k I) i a) :
    ∃ c : k, rootFamily P w a c = g := by
  obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
  simp only [rootFamily_rootChar]
  exact exists_fieldRootPoint_eq hu α hg

omit [IsAffineHom G.X.hom] in
include hu in
theorem fieldRootPoint_injective (α : J) : Function.Injective (fieldRootPoint (w α)) :=
  ((hu α).rootPoint_injective pt).comp baseRingEquiv.injective

include hP hu in
theorem rootFamily_eq_one {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i)
    {c : k} (hc : rootFamily P w a c = 1) : c = 0 := by
  obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
  rw [rootFamily_rootChar, ← fieldRootPoint_zero (w α)] at hc
  exact fieldRootPoint_injective hu α hc

theorem charValue_eq_baseRingEquiv (χ : characterLattice (coordTorus k I))
    (t : rationalPoints (coordTorus k I).toGrp) :
    VectorGroup.charValue χ pt t = baseRingEquiv (torusCharEval (coordTorus k I) χ t : k) :=
  ChevalleyRootFamily.charValue_eq_rationalCharacterEval χ t

omit [IsAffineHom G.X.hom] in
include hu in
theorem fieldRootPoint_torus_conj (α : J) (t : rationalPoints (coordTorus k I).toGrp) (c : k) :
    rationalPoints.map i t * fieldRootPoint (w α) c * (rationalPoints.map i t)⁻¹ =
      fieldRootPoint (w α) ((torusCharEval (coordTorus k I) (rootChar P α) t : k) * c) := by
  rw [rationalPoints.map_apply, fieldRootPoint, fieldRootPoint, map_mul,
    ← charValue_eq_baseRingEquiv]
  exact (hu α).equivariant pt t (baseRingEquiv c)

include hP hu in
theorem rootFamily_torus_conj {a : characterLattice (coordTorus k I)}
    (ha : a ∈ relativeRoots (T := coordTorus k I) i)
    (t : rationalPoints (coordTorus k I).toGrp) (c : k) :
    rationalPoints.map i t * rootFamily P w a c * (rationalPoints.map i t)⁻¹ =
      rootFamily P w a ((torusCharEval (coordTorus k I) a t : k) * c) := by
  obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
  simp only [rootFamily_rootChar]
  exact fieldRootPoint_torus_conj hu α t c

end Fields

/-! ### The rank-one relation on rational points -/

section RankOne

variable {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
  {χv : cocharacterLattice T} {u v : Ga k ⟶ G} {α : characterLattice T}

omit [Fintype I] [IsAffineHom G.X.hom] in
/-- A Weyl point, as a rational point. -/
theorem weylPoint_eq_rootPoints (u u' : Ga k ⟶ G) :
    (weylPoint u u' : rationalPoints G) =
      rootPoint u' pt (-1) * rootPoint u pt 1 * rootPoint u' pt (-1) := by
  rw [← constantPoint_weylPoint u u' pt]
  exact (GroupScheme.constantPoint_self G _).symm

omit [Fintype I] [IsAffineHom G.X.hom] in
theorem rootCellPt_eq_scalarPoint {Z : Over (Spec (CommRingCat.of k))} (c : Γ(Z.left, ⊤)) :
    RootCell.pt c = VectorGroup.scalarPoint (CommRingCat.of k) Z c :=
  VectorGroup.points_ext fun j => by
    rw [VectorGroup.coordinates_scalarPoint, Fin.fin_one_eq_zero j]
    exact RootCell.crd_pt c

omit [Fintype I] [IsAffineHom G.X.hom] in
/-- The rank-one relation gives `m(u(c)) = χv(c) · m(u(1))` for the normalizing products
`m(u(c)) = v(-c⁻¹) u(c) v(-c⁻¹)`, provided `v` is torus-equivariant through `-α` and
`⟨α, χv⟩ = 2`. -/
theorem weylProduct_eq (hrel : RootCell.RelationOver i χv u v pt)
    (hv : ∀ (t : pt ⟶ T.X) (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)),
      (t ≫ i.hom.hom) * rootPoint v pt c * (t ≫ i.hom.hom)⁻¹ =
        rootPoint v pt (VectorGroup.charValue (-α) pt t * c))
    (hpair : latticePairing T α χv = 2)
    (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)ˣ) :
    rootPoint v pt (-((c⁻¹ : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)ˣ) : _)) *
        rootPoint u pt c *
        rootPoint v pt (-((c⁻¹ : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)ˣ) : _)) =
      ((Gm.pointsEquiv _ pt).symm c ≫ (CommGroupScheme.groupHom χv).hom.hom ≫ i.hom.hom) *
        (rootPoint v pt (-1) * rootPoint u pt 1 * rootPoint v pt (-1)) := by
  set ci : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤) :=
    ((c⁻¹ : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) :
      Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) with hci
  have hcci : (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) * ci = 1 := Units.mul_inv c
  set t : pt ⟶ T.X := (Gm.pointsEquiv _ pt).symm c ≫ (CommGroupScheme.groupHom χv).hom.hom
  have hH : (Gm.pointsEquiv _ pt).symm c ≫ (CommGroupScheme.groupHom χv).hom.hom ≫ i.hom.hom =
      t ≫ i.hom.hom := (Category.assoc _ _ _).symm
  rw [hH]
  have hV : ∀ x y : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤),
      rootPoint v pt x * rootPoint v pt y = rootPoint v pt (x + y) :=
    fun x y => (rootPoint_add v pt x y).symm
  have hU : ∀ x y : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤),
      rootPoint u pt x * rootPoint u pt y = rootPoint u pt (x + y) :=
    fun x y => (rootPoint_add u pt x y).symm
  -- the rank-one relation at `X = c`, `Y = 1 - c⁻¹`, `w = c`
  have hR := hrel (RootCell.pt (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)))
    (RootCell.pt (1 - ci)) (RootCell.pt 1)
    (RootCell.pt (ci * (1 - ci))) c
    (by rw [RootCell.crd_pt, RootCell.crd_pt, mul_sub, mul_one, hcci]; ring)
    (by rw [RootCell.crd_pt, RootCell.crd_pt, mul_comm, hcci])
    (by rw [RootCell.crd_pt, RootCell.crd_pt])
  simp only [RootCell.RelationAt, rootCellPt_eq_scalarPoint] at hR
  change rootPoint u pt c * rootPoint v pt (1 - ci) =
    rootPoint v pt (ci * (1 - ci)) * (t ≫ i.hom.hom) * rootPoint u pt 1 at hR
  -- the torus point scales `v` by `c⁻²`
  have hval : VectorGroup.charValue (-α) pt t = ci * ci := by
    rw [RankOneRootCellRelation.charValue_eq_cu, RankOneRootCellRelation.cu_neg,
      RootPairNoncommutation.cu_cocharacter, hpair]
    simp only [hci, zpow_ofNat]
    rw [pow_two, mul_inv_rev, Units.val_mul]
  have hconj := hv t (-1)
  rw [hval, mul_neg_one] at hconj
  calc rootPoint v pt (-ci) * rootPoint u pt c * rootPoint v pt (-ci)
      = rootPoint v pt (-ci) * (rootPoint u pt c * rootPoint v pt (1 - ci)) *
          rootPoint v pt (-1) := by
        rw [mul_assoc (rootPoint v pt (-ci)) _ _, mul_assoc (rootPoint v pt (-ci)),
          mul_assoc (rootPoint u pt c), hV]
        ring_nf
    _ = rootPoint v pt (-ci) * rootPoint v pt (ci * (1 - ci)) * (t ≫ i.hom.hom) *
          rootPoint u pt 1 * rootPoint v pt (-1) := by
        rw [hR]
        group
    _ = rootPoint v pt (-(ci * ci)) * (t ≫ i.hom.hom) * rootPoint u pt 1 *
          rootPoint v pt (-1) := by
        rw [hV]
        ring_nf
    _ = (t ≫ i.hom.hom) * (rootPoint v pt (-1) * rootPoint u pt 1 * rootPoint v pt (-1)) := by
        rw [← hconj]
        group

end RankOne

omit [Fintype I] [IsAffineHom G.X.hom] in
/-- Torus points centralize the torus. -/
theorem map_mem_centralizerPoints {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (t : rationalPoints T.toGrp) :
    rationalPoints.map i t ∈ centralizerPoints i := by
  change i ≫ (G.innerIso (t ≫ i.hom.hom)).hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ i
  rw [comp_innerIso_hom_comp, SplitExistence.innerIso_hom_eq_id_of_comm, Category.id_comp]
  rfl

section RankOneField

variable [DecidableEq I]
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G} (hG : IsConnectedReductive G)
  (hi : IsMaximalTorus (T := coordTorus k I) i) (hred : P.IsReduced)
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))
  {w : J → (Ga k ⟶ G)} (hu : ∀ α, IsRootParametrization i (P.root α) (w α))

omit [IsAffineHom G.X.hom] [DecidableEq I] in
theorem rootChar_reflectionPerm_self (α : J) :
    rootChar (k := k) P (P.reflectionPerm α α) = -rootChar P α := by
  rw [rootChar, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
    splitTorus.exponentCharacter_neg]

omit [DecidableEq I] in
include hP in
theorem latticePairing_rootChar_coroot (α : J) :
    latticePairing (coordTorus k I) (rootChar P α)
      (splitTorus.exponentCocharacter _ I (P.coroot α)) = 2 := by
  have h2 := (CoordinateRootDatum.fieldRealization k P).root_coroot_two α
  rw [hP.1, CoordinateRootDatum.fieldRealization_root,
    CoordinateRootDatum.fieldRealization_coroot] at h2
  exact h2

omit [IsAffineHom G.X.hom] [DecidableEq I] in
theorem rootPoint_mem_neg {α : J} {v : Ga k ⟶ G}
    (hv : IsRootParametrization i (P.root (P.reflectionPerm α α)) v)
    (x : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    rootPoint v pt x ∈
      (RelativeRoot.subgroup (S := coordTorus k I) i (-rootChar P α)).carrier
        (Over.mk (𝟙 _)) := by
  rw [← rootChar_reflectionPerm_self]
  exact hv.rootPoint_mem pt x

omit [IsAffineHom G.X.hom] [DecidableEq I] in
theorem rootPoint_equivariant_neg {α : J} {v : Ga k ⟶ G}
    (hv : IsRootParametrization i (P.root (P.reflectionPerm α α)) v)
    (t : pt ⟶ (coordTorus k I).X) (c : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) :
    (t ≫ i.hom.hom) * rootPoint v pt c * (t ≫ i.hom.hom)⁻¹ =
      rootPoint v pt (VectorGroup.charValue (-rootChar P α) pt t * c) := by
  rw [← rootChar_reflectionPerm_self]
  exact hv.equivariant pt t c

omit [DecidableEq I] in
include hP in
theorem torusCharEval_corootPoint (α : J) (c : kˣ)
    (c' : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ)
    (hc' : (c' : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) = baseRingEquiv (c : k)) :
    torusCharEval (coordTorus k I) (rootChar P α) ((Gm.pointsEquiv _ pt).symm c' ≫
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I (P.coroot α))).hom.hom) =
      c ^ 2 := by
  apply Units.ext
  apply (baseRingEquiv (k := k)).injective
  rw [← charValue_eq_baseRingEquiv, RankOneRootCellRelation.charValue_eq_cu,
    RootPairNoncommutation.cu_cocharacter, latticePairing_rootChar_coroot hP]
  rw [zpow_ofNat, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hc']

omit [DecidableEq I] in
include hP in
theorem weylProduct_eq_of_relation {α : J} {v : Ga k ⟶ G}
    (hv : IsRootParametrization i (P.root (P.reflectionPerm α α)) v)
    (hrel : ∀ Z, RootCell.RelationOver (T := coordTorus k I) i
      (splitTorus.exponentCocharacter _ I (P.coroot α)) (w α) v Z)
    (c' : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) :
    rootPoint v pt (-((c'⁻¹ : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) : _)) *
        rootPoint (w α) pt c' *
        rootPoint v pt (-((c'⁻¹ : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ) : _)) =
      rationalPoints.map i ((Gm.pointsEquiv _ pt).symm c' ≫
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I (P.coroot α))).hom.hom) *
        (rootPoint v pt (-1) * rootPoint (w α) pt 1 * rootPoint v pt (-1)) := by
  rw [rationalPoints.map_apply, Category.assoc]
  exact weylProduct_eq (hrel pt) (rootPoint_equivariant_neg hv)
    (latticePairing_rootChar_coroot hP α) c'

include hP in
/-- The rank-one field of a pinning for the root parametrization `w α`, given a parametrization
`v` of `-α` normalized against `w α` by the rank-one relation. -/
theorem fieldRootPoint_rankOne_of_relation [Mono i.hom.hom.left] {α : J} {v : Ga k ⟶ G}
    (hv : IsRootParametrization i (P.root (P.reflectionPerm α α)) v)
    (hrel : ∀ Z, RootCell.RelationOver (T := coordTorus k I) i
      (splitTorus.exponentCocharacter _ I (P.coroot α)) (w α) v Z)
    (hW : IsWeylPoint i (weylPoint (w α) v) (P.reflection α)) (c : kˣ) :
    ∃ (p q : rationalPoints G × rationalPoints G)
      (t : rationalPoints (coordTorus k I).toGrp),
      RelativeRoot.IsOppositeFactorPair (T := coordTorus k I) i (rootChar P α)
          (fieldRootPoint (w α) c) p ∧
        RelativeRoot.IsOppositeFactorPair (T := coordTorus k I) i (rootChar P α)
          (fieldRootPoint (w α) 1) q ∧
        torusCharEval (coordTorus k I) (rootChar P α) t = c ^ 2 ∧
        p.1 * fieldRootPoint (w α) c * p.2 =
          rationalPoints.map i t * (q.1 * fieldRootPoint (w α) 1 * q.2) := by
  have hmem := rootPoint_mem_neg (P := P) (α := α) hv
  obtain ⟨c', hc'⟩ : ∃ c' : (Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤))ˣ,
      (c' : Γ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left, ⊤)) = baseRingEquiv (c : k) :=
    ⟨(c.isUnit.map (baseRingEquiv (k := k))).unit, IsUnit.unit_spec _⟩
  have key := weylProduct_eq_of_relation hP hv hrel c'
  have hN1 : rootPoint v pt (-1) * rootPoint (w α) pt 1 * rootPoint v pt (-1) ∈
      normalizerPoints (T := coordTorus k I) i := by
    rw [← weylPoint_eq_rootPoints]
    exact hW.mem_normalizerPoints
  have htN := centralizerPoints_le_normalizerPoints (T := coordTorus k I) i
    (map_mem_centralizerPoints (T := coordTorus k I) i ((Gm.pointsEquiv _ pt).symm c' ≫
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I (P.coroot α))).hom.hom))
  have h1 : fieldRootPoint (w α) 1 = rootPoint (w α) pt 1 := by
    rw [fieldRootPoint, map_one]
  have hc : fieldRootPoint (w α) c = rootPoint (w α) pt c' := by
    rw [fieldRootPoint, hc']
  refine ⟨(rootPoint v pt (-((c'⁻¹ : _ˣ) : _)), rootPoint v pt (-((c'⁻¹ : _ˣ) : _))),
    (rootPoint v pt (-1), rootPoint v pt (-1)), (Gm.pointsEquiv _ pt).symm c' ≫
      (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I (P.coroot α))).hom.hom,
    ⟨hmem _, hmem _, ?_⟩, ⟨hmem _, hmem _, ?_⟩, torusCharEval_corootPoint hP α c c' hc', ?_⟩
  · show _ * fieldRootPoint (w α) c * _ ∈ _
    rw [hc, key]
    exact Subgroup.mul_mem _ htN hN1
  · show _ * fieldRootPoint (w α) 1 * _ ∈ _
    rw [h1]
    exact hN1
  · show _ * fieldRootPoint (w α) c * _ = _ * (_ * fieldRootPoint (w α) 1 * _)
    rw [hc, h1]
    exact key

include hG hi hred hP hu in
/-- The rank-one field of a pinning for the root parametrization `w α`. -/
theorem fieldRootPoint_rankOne [Mono i.hom.hom.left] (α : J) (c : kˣ) :
    ∃ (p q : rationalPoints G × rationalPoints G)
      (t : rationalPoints (coordTorus k I).toGrp),
      RelativeRoot.IsOppositeFactorPair (T := coordTorus k I) i (rootChar P α)
          (fieldRootPoint (w α) c) p ∧
        RelativeRoot.IsOppositeFactorPair (T := coordTorus k I) i (rootChar P α)
          (fieldRootPoint (w α) 1) q ∧
        torusCharEval (coordTorus k I) (rootChar P α) t = c ^ 2 ∧
        p.1 * fieldRootPoint (w α) c * p.2 =
          rationalPoints.map i t * (q.1 * fieldRootPoint (w α) 1 * q.2) := by
  obtain ⟨d, hd, hrel, hW⟩ := exists_fieldWeylNormalization hG i hi hred hP α (hu α)
    (hu (P.reflectionPerm α α))
  have hv' := (hu (P.reflectionPerm α α)).scale (Units.mk0 d hd)
  rw [Units.val_mk0] at hv'
  exact fieldRootPoint_rankOne_of_relation hP hv' hrel hW c

end RankOneField

/-! ### Simple roots and Weyl points -/

section Weyl

variable [DecidableEq I] {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  [Mono i.hom.hom.left] (b : P.Base) {w : J → (Ga k ⟶ G)}
  (hwS : ∀ j ∈ b.support, IsWeylPoint i (weylPoint (w j) (w (P.reflectionPerm j j)))
    (P.reflection j))

/-- The simple Weyl point `w(-j)(-1) w j (1) w(-j)(-1)` of a simple root, as a normalizer
point. -/
def simpleWeylPoint (j : J) (hj : j ∈ b.support) : normalizerPoints (T := coordTorus k I) i :=
  ⟨weylPoint (w j) (w (P.reflectionPerm j j)), (hwS j hj).mem_normalizerPoints⟩

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
theorem exponentCommIso_reflection_symm (j : J) :
    (splitTorus.exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection j)).symm =
      splitTorus.exponentCommIso _ I (P.reflection j) := by
  apply Iso.ext
  change splitTorus.exponentHom _ I I (P.reflection j).symm.toLinearMap =
    splitTorus.exponentHom _ I I (P.reflection j).toLinearMap
  rw [show (P.reflection j).symm = P.reflection j from P.reflection_inv j]

omit [IsAffineHom G.X.hom] in
/-- A Weyl point acting through the reflection `s_j` acts on exponent characters by `s_j`. -/
theorem weylAction_exponentCharacter {j : J} {n : normalizerPoints (T := coordTorus k I) i}
    (hn : IsWeylPoint i n.val (P.reflection j)) (m : I → ℤ) :
    weylAction (T := coordTorus k I) i n (splitTorus.exponentCharacter _ I m) =
      splitTorus.exponentCharacter _ I (P.reflection j m) := by
  rw [weylAction_eq (T := coordTorus k I) i hn.isNormalizingPoint]
  change characterAut _ _ = _
  rw [← exponentCommIso_reflection_symm, splitTorus.characterAut_exponentCommIso_symm]

omit [IsAffineHom G.X.hom] in
include hwS in
theorem weylAction_simpleWeylPoint_rootChar (j : J) (hj : j ∈ b.support) (α : J) :
    weylAction (T := coordTorus k I) i (simpleWeylPoint b hwS j hj) (rootChar P α) =
      rootChar P (P.reflectionPerm j α) := by
  rw [rootChar, weylAction_exponentCharacter (n := simpleWeylPoint b hwS j hj) (hwS j hj), rootChar,
    RootPairing.root_reflectionPerm]

end Weyl

/-! ### Induction over the roots and linear independence of the simple roots -/

section Base

theorem rootChar_reflectionPerm (j α : J) :
    rootChar (k := k) (I := I) P (P.reflectionPerm j α) =
      splitTorus.exponentCharacter _ I (P.reflection j (P.root α)) := by
  rw [rootChar, RootPairing.root_reflectionPerm]

/-- Every root is reached from the simple roots by simple reflections. -/
theorem induction_rootChar [Finite J] [P.IsReduced] (b : P.Base)
    (Q : characterLattice (coordTorus k I) → Prop) (h1 : ∀ j ∈ b.support, Q (rootChar P j))
    (h2 : ∀ j ∈ b.support, ∀ α, Q (rootChar P α) → Q (rootChar P (P.reflectionPerm j α)))
    (α : J) : Q (rootChar P α) := by
  let := P.indexNeg
  rcases RootPairing.Base.IsPos.or_neg b α with hα | hα
  · exact hα.induction_on_reflect (p := fun x => Q (rootChar P x)) h1
      (fun x j hx hj => h2 j hj x hx)
  · have hneg : ∀ x : J, rootChar (k := k) (I := I) P (-x) = -rootChar P x := fun x =>
      rootChar_reflectionPerm_self x
    have h := hα.induction_on_reflect (p := fun x => Q (-rootChar P x)) ?_ ?_
    · simpa only [hneg, neg_neg] using h
    · intro j hj
      have := h2 j hj j (h1 j hj)
      rwa [rootChar_reflectionPerm_self] at this
    · intro x j hx hj
      have := h2 j hj (P.reflectionPerm x x) (by rwa [rootChar_reflectionPerm_self])
      rwa [rootChar_reflectionPerm, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self, map_neg, splitTorus.exponentCharacter_neg,
        ← rootChar_reflectionPerm] at this

variable {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))

include hP in
theorem rootChar_mem (α : J) : rootChar (k := k) P α ∈ relativeRoots (T := coordTorus k I) i := by
  rw [relativeRoots_eq_range hP]
  exact ⟨α, rfl⟩

/-- Evaluation of a linear form on the translation space at the coordinate cocharacters. -/
def coordEval [DecidableEq I] :
    Module.Dual ℝ (TranslationSpace (S := coordTorus k I) i) →ₗ[ℝ] (I → ℝ) :=
  LinearMap.pi fun l => LinearMap.applyₗ
    (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ]
      splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (Pi.single l 1)))

include hP in
theorem coordEval_rootForm [DecidableEq I] (α : J) :
    coordEval (i := i) (rootForm (S := coordTorus k I) i ⟨rootChar P α, rootChar_mem hP α⟩) =
      algebraMap ℤ ℝ ∘ P.root α := by
  funext l
  simp only [coordEval, LinearMap.pi_apply, LinearMap.applyₗ_apply_apply, rootForm_mk,
    eval_tmul, one_mul, rootChar, splitTorus.latticePairing_exponentCharacter_exponentCocharacter,
    Function.comp_apply]
  rw [Finset.sum_eq_single l (fun m _ hm => by simp [hm])
    (fun h => absurd (Finset.mem_univ l) h)]
  simp

include hP in
/-- The root forms of the simple roots of a base are linearly independent on the translation
space. -/
theorem linearIndependent_rootForm_simple [DecidableEq I] (b : P.Base) :
    LinearIndependent ℝ fun x : (rootChar (k := k) (I := I) P '' (b.support : Set J)) =>
      rootForm (S := coordTorus k I) i ⟨x, by
        obtain ⟨α, -, hα⟩ := x.2
        rw [← hα]
        exact rootChar_mem hP α⟩ := by
  let e : (b.support : Set J) ≃ (rootChar (k := k) (I := I) P '' (b.support : Set J)) :=
    Equiv.Set.image _ _ (rootChar_injective P)
  rw [← linearIndependent_equiv e]
  apply LinearIndependent.of_comp (coordEval (i := i))
  have h : LinearIndependent ℝ fun j : (b.support : Set J) => algebraMap ℤ ℝ ∘ P.root j :=
    linearIndependent_algebraMap_comp_iff.mpr b.linearIndepOn_root
  convert h using 1
  funext j
  exact coordEval_rootForm hP j

end Base

/-! ### Generation of the Weyl action by the simple Weyl points -/

section WeylGeneration

variable [DecidableEq I] [Fintype J] [P.IsReduced]
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G}
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))
  (b : P.Base)

omit [DecidableEq I] in
theorem exponentCharacter_add (m n : I → ℤ) :
    splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (m + n) =
      splitTorus.exponentCharacter _ I m + splitTorus.exponentCharacter _ I n := by
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k, map_add]

variable (P) in
/-- The cocharacter `2ρ^∨` of a base: the exponent cocharacter of the sum of the positive
coroots. -/
def doubleRhoCheck : cocharacterLattice (coordTorus k I) :=
  splitTorus.exponentCocharacter _ I (IntegralWeylVector.positiveRootSum P.flip b.flip)

omit [DecidableEq I] in
include hP in
theorem latticePairing_doubleRhoCheck (α : J) :
    latticePairing (coordTorus k I) (rootChar P α) (doubleRhoCheck P b) = 2 * b.height α := by
  rw [rootChar, doubleRhoCheck, ← hP.1, CoordinateRootDatum.fieldRealization_pairing]
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int α
  rw [RootPairing.Base.height_eq_sum hf, hf, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h2 : P.toLinearMap (P.root j) (IntegralWeylVector.positiveRootSum P.flip b.flip) = 2 :=
    IntegralWeylVector.pairing_positiveRootSum_simple P.flip b.flip ⟨j, hj⟩
  rw [map_zsmul, LinearMap.smul_apply, h2, smul_eq_mul, mul_comm]

omit [DecidableEq I] in
include hP in
theorem isGenericCocharacter_doubleRhoCheck :
    IsGenericCocharacter (T := coordTorus k I) i (doubleRhoCheck P b) := by
  intro β hβ
  rw [relativeRoots_eq_range hP] at hβ
  obtain ⟨α, rfl⟩ := hβ
  rw [latticePairing_doubleRhoCheck hP b α]
  have := b.height_ne_zero α
  omega

omit [DecidableEq I] in
include hP in
theorem mem_positiveRelativeRoots_doubleRhoCheck {α : J} (hα : b.IsPos α) :
    rootChar P α ∈ positiveRelativeRoots (T := coordTorus k I) i (doubleRhoCheck P b) := by
  refine ⟨rootChar_mem hP α, ?_⟩
  rw [latticePairing_doubleRhoCheck hP b α]
  have := (RootPairing.Base.isPos_iff b).1 hα
  omega

omit [DecidableEq I] in
include hP in
/-- Every simple relative root of `2ρ^∨` is the character of a simple root of the base. -/
theorem simpleRelativeRoots_doubleRhoCheck_subset :
    simpleRelativeRoots (T := coordTorus k I) i (doubleRhoCheck P b) ⊆
      rootChar (k := k) (I := I) P '' (b.support : Set J) := by
  rintro x ⟨⟨hxΦ, hxpos⟩, hxns⟩
  rw [relativeRoots_eq_range hP] at hxΦ
  obtain ⟨α, rfl⟩ := hxΦ
  rw [latticePairing_doubleRhoCheck hP b α] at hxpos
  have hα : b.IsPos α := (RootPairing.Base.isPos_iff b).2 (by omega)
  by_cases hsupp : α ∈ b.support
  · exact ⟨α, hsupp, rfl⟩
  exfalso
  obtain ⟨j, hj, hj'⟩ := hα.exists_mem_support_pos_pairingIn
  rw [P.zero_lt_pairingIn_iff'] at hj'
  have hij : α ≠ j := fun h => hsupp (h ▸ hj)
  obtain ⟨m, hm⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
  have hmh : b.height m = b.height α - 1 := by
    rw [b.height_sub hm, RootPairing.Base.height_one_of_mem_support hj]
  have hm0 := b.height_ne_zero m
  have hαh := (RootPairing.Base.isPos_iff b).1 hα
  have hmpos : b.IsPos m := (RootPairing.Base.isPos_iff b).2 (by omega)
  apply hxns
  refine ⟨rootChar P m, mem_positiveRelativeRoots_doubleRhoCheck hP b hmpos, rootChar P j,
    mem_positiveRelativeRoots_doubleRhoCheck hP b (b.isPos_of_mem_support hj), ?_⟩
  rw [rootChar, rootChar, rootChar, ← exponentCharacter_add, hm, sub_add_cancel]

end WeylGeneration

section WeylGenerationPoints

variable [DecidableEq I] [Fintype J] [P.IsReduced]
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G} [Mono i.hom.hom.left]
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))
  (b : P.Base) {w : J → (Ga k ⟶ G)} (hu : ∀ α, IsRootParametrization i (P.root α) (w α))
  (hwS : ∀ j ∈ b.support, IsWeylPoint i (weylPoint (w j) (w (P.reflectionPerm j j)))
    (P.reflection j))

omit [IsAffineHom G.X.hom] [DecidableEq I] [Fintype J] [P.IsReduced] [Mono i.hom.hom.left] in
include hu in
theorem rootPoint_one_ne_one (j : J) : rootPoint (w j) pt 1 ≠ 1 := by
  intro h
  have h' : fieldRootPoint (w j) 1 = fieldRootPoint (w j) 0 := by
    rw [fieldRootPoint_zero, fieldRootPoint, map_one]
    exact h
  exact one_ne_zero (fieldRootPoint_injective hu j h')

omit [Fintype J] [P.IsReduced] in
include hP hu in
/-- The class of a simple Weyl point is the relative reflection of its simple root. -/
theorem isRelativeReflection_simpleWeylPoint (j : J) (hj : j ∈ b.support) :
    IsRelativeReflection (T := coordTorus k I) i (rootChar P j)
      (QuotientGroup.mk (simpleWeylPoint b hwS j hj)) := by
  have hp : RelativeRoot.IsOppositeFactorPair (T := coordTorus k I) i (rootChar P j)
      (rootPoint (w j) pt 1) (rootPoint (w (P.reflectionPerm j j)) pt (-1),
        rootPoint (w (P.reflectionPerm j j)) pt (-1)) := by
    refine ⟨rootPoint_mem_neg (hu _) _, rootPoint_mem_neg (hu _) _, ?_⟩
    rw [← weylPoint_eq_rootPoints]
    exact (hwS j hj).mem_normalizerPoints
  have h := RelativeRoot.IsOppositeFactorPair.isRelativeReflection (T := coordTorus k I) i
    (isSplitTorus_splitTorus I) (rootChar_mem hP j) ((hu j).rootPoint_mem pt 1)
    (rootPoint_one_ne_one hu j) hp
  convert h using 2
  apply Subtype.ext
  exact weylPoint_eq_rootPoints _ _

include hP hu in
/-- Every normalizer point has the Weyl action of an element of the subgroup generated by the
simple Weyl points. -/
theorem exists_weylAction_eq_of_simpleWeylPoints (hG : IsConnectedReductive G)
    (hi : IsMaximalTorus (T := coordTorus k I) i) (n : normalizerPoints (T := coordTorus k I) i) :
    ∃ m ∈ Subgroup.closure (Set.range fun j : (b.support : Set J) => simpleWeylPoint b hwS j j.2),
      weylAction (T := coordTorus k I) i n = weylAction (T := coordTorus k I) i m := by
  have hT := isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I
  have hcox := relativeWeylCoxeter k G hG (coordTorus k I) i (hi.isMaximalSplitTorus hT)
    (doubleRhoCheck P b) (isGenericCocharacter_doubleRhoCheck hP b)
  let π := QuotientGroup.mk' ((centralizerPoints (T := coordTorus k I) i).subgroupOf
    (normalizerPoints (T := coordTorus k I) i))
  have htop := HasRelativeWeylCoxeterSystem.closure_simpleRelativeReflections_eq_top hcox
  have hle : simpleRelativeReflections (T := coordTorus k I) i (doubleRhoCheck P b) ⊆
      π '' Set.range fun j : (b.support : Set J) => simpleWeylPoint b hwS j j.2 := by
    rintro s ⟨x, hx, hs⟩
    obtain ⟨j, hj, rfl⟩ := simpleRelativeRoots_doubleRhoCheck_subset hP b hx
    refine ⟨simpleWeylPoint b hwS j hj, ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    exact (hcox.eq_of_isRelativeReflection_of_mem_simple hT _ hx _ _ hs
      (isRelativeReflection_simpleWeylPoint hP b hu hwS j hj)).symm
  have hmem : π n ∈ (Subgroup.closure (Set.range fun j : (b.support : Set J) =>
      simpleWeylPoint b hwS j j.2)).map π := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hle (htop ▸ Subgroup.mem_top _)
  obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.1 hmem
  refine ⟨m, hm, ?_⟩
  have hc := (relativeWeyl_eq_iff_inv_mul_mem_centralizerPoints (T := coordTorus k I) i m n).1 hmn
  have h1 := weylAction_eq_one_of_mem_centralizerPoints (T := coordTorus k I) i (n := m⁻¹ * n) hc
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

end WeylGenerationPoints

/-! ### The pinning -/

section Pinning

variable (v : Valuation k (WithZero (Multiplicative ℤ))) [DecidableEq I] [Fintype J]
  {i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G} [Mono i.hom.hom.left]
  (hG : IsConnectedReductive G) (hi : IsMaximalTorus (T := coordTorus k I) i)
  (hred : P.IsReduced)
  (hP : IsRootDatumOf (T := coordTorus k I) i (CoordinateRootDatum.fieldRealization k P))
  (b : P.Base) {w : J → (Ga k ⟶ G)} (hu : ∀ α, IsRootParametrization i (P.root α) (w α))
  (hwS : ∀ j ∈ b.support, IsWeylPoint i (weylPoint (w j) (w (P.reflectionPerm j j)))
    (P.reflection j))

omit [IsAffineHom G.X.hom] [DecidableEq I] [Fintype J] in
theorem weylProduct_rootFamily (j : J) :
    rootFamily P w (-rootChar P j) (-1) * rootFamily P w (rootChar P j) 1 *
        rootFamily P w (-rootChar P j) (-1) =
      (weylPoint (w j) (w (P.reflectionPerm j j)) : rationalPoints G) := by
  rw [← rootChar_reflectionPerm_self, rootFamily_rootChar, rootFamily_rootChar, fieldRootPoint,
    fieldRootPoint, map_neg, map_one, weylPoint_eq_rootPoints]

omit [IsAffineHom G.X.hom] [Fintype J] [Mono i.hom.hom.left] in
include hwS in
theorem rootFamily_weyl_mem (j : J) (hj : j ∈ b.support) :
    rootFamily P w (-rootChar P j) (-1) * rootFamily P w (rootChar P j) 1 *
        rootFamily P w (-rootChar P j) (-1) ∈ normalizerPoints (T := coordTorus k I) i := by
  rw [weylProduct_rootFamily]
  exact (hwS j hj).mem_normalizerPoints

/-- **Split integral pinning from root parametrizations.** Over a field `k` with a valuation
`v`, let `i` be a split maximal torus of a connected reductive group `G` with a reduced
coordinate root datum `P`, a base `b`, root parametrizations `w α` of all roots, and Weyl
points `w(-j)(-1) w j (1) w(-j)(-1)` acting by the simple reflections. A subgroup `K` with the
three integrality conditions `hK_u`, `hK_torus`, `hK_closure` gives a split integral pinning
of `i` with root family `rootFamily P w` and simple roots the characters of `b`. -/
def ofRootParametrizations (K : Subgroup (rationalPoints G))
    (hK_u : ∀ α (c : k), fieldRootPoint (w α) c ∈ K ↔ v c ≤ 1)
    (hK_torus : ∀ t : rationalPoints (coordTorus k I).toGrp,
      (∀ a ∈ relativeRoots (T := coordTorus k I) i,
        IntegerValuation.order v (torusCharEval (coordTorus k I) a t) = 0) →
      rationalPoints.map i t ∈ characterValuationKernel v G → rationalPoints.map i t ∈ K)
    (hK_closure : K ≤ Subgroup.closure
      (rationalPoints.map i '' (characterValuationKernel v (coordTorus k I).toGrp : Set _) ∪
        ⋃ α, fieldRootPoint (w α) '' {c | v c ≤ 1})) :
    SplitIntegralPinning (S := coordTorus k I) v i where
  K := K
  u := rootFamily P w
  u_add _ ha c d := rootFamily_add hP ha c d
  u_mem _ ha c := rootFamily_mem hP hu ha c
  u_surjective _ ha _ hg := rootFamily_surjective hP hu ha hg
  u_eq_one _ ha _ hc := rootFamily_eq_one hP hu ha hc
  torus_conj _ ha t c := rootFamily_torus_conj hP hu ha t c
  rankOne a ha c := by
    obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
    simp only [rootFamily_rootChar]
    exact fieldRootPoint_rankOne hG hi hred hP hu α c
  two_smul_not_mem a ha := by
    obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
    have h := hasNoHigherRoots_fieldRealization hred hP α 2 le_rfl
    rwa [CoordinateRootDatum.fieldRealization_root] at h
  u_mem_K a ha c := by
    obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
    rw [rootFamily_rootChar]
    exact hK_u α c
  torus_mem_K := hK_torus
  K_le_closure := by
    refine hK_closure.trans (Subgroup.closure_mono (Set.union_subset_union_right _ ?_))
    rintro g ⟨_, ⟨α, rfl⟩, c, hc, rfl⟩
    refine Set.mem_biUnion (rootChar_mem hP α) ⟨c, hc, ?_⟩
    exact rootFamily_rootChar P w α c
  simple := rootChar P '' (b.support : Set J)
  simple_subset := by
    rintro _ ⟨α, -, rfl⟩
    exact rootChar_mem hP α
  simple_linearIndependent := linearIndependent_rootForm_simple hP b
  weyl_mem := by
    rintro _ ⟨j, hj, rfl⟩
    exact rootFamily_weyl_mem b hwS j hj
  induction Q h1 h2 a ha := by
    have := hred
    obtain ⟨α, rfl⟩ := exists_eq_rootChar hP ha
    refine induction_rootChar b Q (fun j hj => h1 _ ⟨j, hj, rfl⟩) (fun j hj β hβ => ?_) α
    have h := h2 _ ⟨j, hj, rfl⟩ (rootChar P β) (rootChar_mem hP β) hβ
    have hn : (⟨_, rootFamily_weyl_mem b hwS j hj⟩ : normalizerPoints (T := coordTorus k I) i) =
        simpleWeylPoint b hwS j hj :=
      Subtype.ext (weylProduct_rootFamily j)
    rwa [hn, weylAction_simpleWeylPoint_rootChar] at h
  weyl_generated n := by
    have := hred
    obtain ⟨m, hm, hnm⟩ := exists_weylAction_eq_of_simpleWeylPoints hP b hu hwS hG hi n
    refine ⟨m, Subgroup.closure_mono ?_ hm, hnm⟩
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    exact ⟨⟨rootChar P j, j, hj, rfl⟩, Subtype.ext (weylProduct_rootFamily j)⟩

end Pinning

end SplitIntegralPinning

end Langlands.Geometry.Building
