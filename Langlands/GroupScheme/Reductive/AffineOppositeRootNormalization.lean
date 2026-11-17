import Langlands.GroupScheme.Reductive.PointwiseRankOneNormalization
import Langlands.GroupScheme.Reductive.LocalRankOneActualWeylData

/-! # Opposite-root normalization over an arbitrary affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.AffineRootNormalization

open LocalSplitCell LocalSplitRootBaseChange
open splitTorus.RelativeCocharacterCentralizer

section Pairing

variable {I J : Type u} [Fintype I] [DecidableEq I]
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hstd : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)

include hstd

omit [DecidableEq I] in
theorem coroot_comp_root (a : J) (A : Type u) [CommRing A] :
    splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I (P.coroot a) ≫
      splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.root a) =
        (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of A))) := by
  rw [splitTorus.exponentCocharacter_comp_exponentCharacter, ← hstd,
    P.root_coroot_two]
  rfl

theorem reflectionIso_eq (a : J) (A : Type u) [CommRing A] :
    RingRootCell.reflectionIso
        (splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.root a))
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I (P.coroot a))
        (coroot_comp_root hstd a A) =
      splitTorus.exponentCommIso (Spec (CommRingCat.of A)) I (P.reflection a) := by
  have hc (m : I → ℤ) :
      (𝟙 (splitTorus.commGroupScheme (Spec (CommRingCat.of A)) I) -
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.root a) ≫
          splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I (P.coroot a)) ≫
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I m =
      splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.reflection a m) := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      splitTorus.exponentCocharacter_comp_exponentCharacter, Gm.powerHom_apply,
      Preadditive.comp_zsmul, Category.comp_id, RootPairing.reflection_apply]
    change _ = splitTorus.exponentCharacterLinear _ I
      (m - P.toLinearMap m (P.coroot a) • P.root a)
    rw [map_sub, map_smul, hstd]
    rfl
  apply Iso.ext
  apply splitTorus.hom_ext_projections _ I
  intro j
  change (𝟙 _ - _ ≫ _) ≫ splitTorus.proj _ I j =
    splitTorus.exponentHom _ I I (P.reflection a).toLinearMap ≫ splitTorus.proj _ I j
  have hs : splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (Pi.single j 1) =
      splitTorus.proj (Spec (CommRingCat.of A)) I j := by
    simp [splitTorus.exponentCharacter, Pi.single_apply]
  rw [splitTorus.exponentHom_comp_proj, ← hs]
  exact hc (Pi.single j 1)

end Pairing

variable {R : Type u} [CommRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hstd : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)
    (a : J) (ha : ∑ j, P.root a j * mu j = 0)
    (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
      P.root b = P.root a ∨ P.root b = -P.root a)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)

/-- The actual coroot cell, using its integral dot-product identity
instead of an assumption that the original ring is local. -/
def affineCorootCell : RingRootCell.CellData R :=
  cellData i mu hG hmax hP a ha hmu (P.coroot a) (by
    have htwo : ∑ j, P.root a j * P.coroot a j = 2 := by
      rw [← hstd, P.root_coroot_two]
    rw [htwo]
    norm_num) hp hm

def affineBaseChangeCell (A : Type u) [CommRing A] [Algebra R A] :
    RingRootCell.CellData A :=
  LocalRankOneCell.baseChangeCellData (torusHom I G i mu) (P.root a)
    (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))
    (rootLift i mu hp ha)
    (isRootParametrization_rootLift i mu hm _)
    (isRootParametrization_rootLift i mu hp ha)
    (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm).open_cell A

theorem exists_fieldUnitCellCoordinates (hi : IsClosedSubgroup i)
    (k : Type u) [Field k] [Algebra R k] :
    let D := affineBaseChangeCell i mu hG hmax hP hstd a ha hmu hp hm k
    ∃ d : k, d ≠ 0 ∧
      IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) D.i
        (weylPoint D.xp (scaleHom d ≫ D.xm))
        (splitTorus.exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a)) ∧
      ∃ beta : Γ(Spec (CommRingCat.of k), ⊤),
      ∃ t : RingRootCell.base k ⟶ D.T.X,
      ∃ delta : Γ(Spec (CommRingCat.of k), ⊤),
        IsUnit beta ∧ IsUnit delta ∧
          D.A 1 * weylPoint D.xp (scaleHom d ≫ D.xm) = D.cellPt beta t delta := by
  let C := groupScheme I G i mu
  let b := algebraBaseMap R k
  let D := affineBaseChangeCell i mu hG hmax hP hstd a ha hmu hp hm k
  let hC := isReductive i mu hG
  let : Smooth G.X.hom := hG.smooth
  let : Smooth C.X.hom := hC.smooth
  have hCk := hC.isConnectedReductive_baseChange b
  let : Smooth D.G.X.hom := hCk.smooth
  let : ConnectedSpace D.G.X.left := hCk.connectedSpace
  let h := splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (P.coroot a)
  have hh : h ≫ D.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of k))) :=
    coroot_comp_root hstd a k
  have hpair : latticePairing D.T D.α h = 2 := by
    change latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root a))
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of k)) I (P.coroot a)) = 2
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter,
      ← hstd, P.root_coroot_two]
  obtain ⟨d, hd, hn⟩ := exists_fieldReflection i mu hG hmax hP a ha hp hm k
  have hn' : IsNormalizingPoint D.i (weylPoint D.xp (scaleHom d ≫ D.xm))
      (RingRootCell.reflectionIso D.α h hh) := by
    have he : RingRootCell.reflectionIso D.α h hh =
        splitTorus.exponentCommIso (Spec (CommRingCat.of k)) I (P.reflection a) :=
      reflectionIso_eq hstd a k
    rw [he]
    exact hn
  have hiD : IsClosedSubgroup D.i :=
    splitTorus.isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
      (isClosedSubgroup_torusHom I G i mu hi)
  have hmaxD : IsFibrewiseMaximalTorus (T := D.T) D.i :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
      (isFibrewiseMaximalTorus i mu hmax)
  have hn2 := hn'.exists_sq_eq_of_fibrewiseMaximal
    (RingRootCell.reflectionIso_trans_self D.α h hh) (hC.baseChange b)
    (isSplitTorus_splitTorus I) hiD hmaxD
  obtain ⟨beta, t, delta, hb, hd', hf⟩ :=
    D.exists_unitFieldCellCoordinates h hh hpair _ hn' hn2
      (DynamicConnected.irreducibleSpace_of_smooth D.G)
  exact ⟨d, hd, hn, beta, t, delta, hb, hd', hf⟩

/-- Lift the chosen field normalizer while retaining its actual unit-cell
coordinates and its integral reflection. -/
def pointedEtaleUnitCellReflection (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of R)) :
    RingRootCell.PointedEtaleUnitCellData
      (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm)
      (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)) s :=
  Classical.choice <| by
  let k := (Spec (CommRingCat.of R)).residueField s
  let := LocalRankOneEtaleWeylData.residueFieldAlgebra R s
  let b := algebraBaseMap R k
  have hb : b = (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    LocalRankOneEtaleWeylData.residueFieldAlgebra_baseMap R s
  let C := groupScheme I G i mu
  let D := affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm
  let E := affineBaseChangeCell i mu hG hmax hP hstd a ha hmu hp hm k
  let σ := splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)
  obtain ⟨d, -, hn, beta, t, delta, hbeta, hdelta, hfactor⟩ :=
    exists_fieldUnitCellCoordinates i mu hG hmax hP hstd a ha hmu hp hm hi k
  let n := weylPoint E.xp (scaleHom d ≫ E.xm)
  let n' := GroupScheme.baseChangePointsEquiv b C (RingRootCell.base k) n
  let t' := GroupScheme.baseChangePointsEquiv b (splitTorus _ I) (RingRootCell.base k)
    (t ≫ (splitTorus.baseChangeIso b I).inv.hom.hom)
  let c : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
      (Over.map b).obj (RingRootCell.base k) :=
    Over.homMk (𝟙 _) (by
      change (𝟙 _ ≫ (𝟙 _ ≫ b)) = (Spec (CommRingCat.of R)).fromSpecResidueField s
      simpa only [Category.id_comp] using hb)
  let n₀ := c ≫ n'
  have hn' : IsNormalizingPoint ((GroupScheme.baseChange b).map D.i) n
      ((CommGroupScheme.baseChange b).mapIso σ) :=
    splitTorus.isNormalizingPoint_baseChange_of_coordinates D.i b (P.reflection a) hn
  have ht : PointwiseSchemeAction.IsTransporter
      ((GroupScheme.baseChange b).map (CommGroupScheme.groupHom σ.hom ≫ D.i))
      ((GroupScheme.baseChange b).map D.i) n := by
    rw [Functor.map_comp]
    exact hn'.isTransporter
  have hn₀ : PointwiseSchemeAction.IsTransporter
      (CommGroupScheme.groupHom σ.hom ≫ D.i) D.i n₀ :=
    (ht.baseChangePointsEquiv b).restrict c
  have hf : D.A 1 * n' = D.cellPt beta t' delta := by
    exact LocalRankOneCell.baseChangePointsEquiv_factorization
      (torusHom I G i mu) (P.root a)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))
      (rootLift i mu hp ha)
      (isRootParametrization_rootLift i mu hm _)
      (isRootParametrization_rootLift i mu hp ha) D.open_cell k n beta t delta hfactor
  have hf₀ : D.A 1 * n₀ = D.cellPt beta (c ≫ t') delta := by
    have hf₀ := congrArg (fun v => c ≫ v) hf
    rw [MonObj.comp_mul, D.comp_A, D.comp_cellPt] at hf₀
    exact hf₀
  let hC := isReductive i mu hG
  let : IsAffine D.G.X.left := isAffine_of_isAffineHom C.X.hom
  exact ⟨{ residueNormalizer := n₀
           lift := pointedEtaleNormalizerOfTransporter D.i σ (isSplitTorus_splitTorus I)
             hC.smooth s n₀ hn₀
           beta := beta, torus := c ≫ t', delta := delta
           unit_beta := hbeta, unit_delta := hdelta, factorization := hf₀ }⟩

variable {s : Spec (CommRingCat.of R)}
    {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
      (groupScheme I G i mu).X}
    (E : RingRootCell.AffineEtaleUnitCellData
      (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm)
      (splitTorus.exponentCommIso (Spec (CommRingCat.of R)) I (P.reflection a)) s n₀)

/-- Weyl data on the actual affine coefficient ring of a pointed chart. -/
def affineEtaleWeylData (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    RingRootCell.WeylData E.ring := by
  letI := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let D := affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm
  let b := algebraBaseMap R E.ring
  let D' := affineBaseChangeCell i mu hG hmax hP hstd a ha hmu hp hm E.ring
  let h := splitTorus.exponentCocharacter (Spec (CommRingCat.of E.ring)) I (P.coroot a)
  have hh : h ≫ D'.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of E.ring))) :=
    coroot_comp_root hstd a E.ring
  have hn : IsNormalizingPoint D'.i E.baseSection
      (RingRootCell.reflectionIso D'.α h hh) := by
    have he : RingRootCell.reflectionIso D'.α h hh =
        splitTorus.exponentCommIso (Spec (CommRingCat.of E.ring)) I (P.reflection a) :=
      reflectionIso_eq hstd a E.ring
    rw [he]
    exact splitTorus.isNormalizingPoint_coordinates_of_baseChange
      (torusHom I G i mu) b (P.reflection a) E.baseSection_isNormalizing
  let hC := isReductive i mu hG
  let : Smooth C.X.hom := hC.smooth
  have hiD : IsClosedSubgroup D'.i :=
    splitTorus.isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
      (isClosedSubgroup_torusHom I G i mu hi)
  have hmaxD : IsFibrewiseMaximalTorus (T := D'.T) D'.i :=
    splitTorus.isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
      (isFibrewiseMaximalTorus i mu hmax)
  have hn2 := hn.exists_sq_eq_of_fibrewiseMaximal
    (RingRootCell.reflectionIso_trans_self D'.α h hh) (hC.baseChange b)
    (isSplitTorus_splitTorus I) hiD hmaxD
  let t₀ := (GroupScheme.baseChangePointsEquiv b (splitTorus _ I)
    (RingRootCell.base E.ring)).symm (E.baseComparison ≫ E.torus)
  let t := t₀ ≫ (splitTorus.baseChangeIso b I).hom.hom.hom
  have ht : GroupScheme.baseChangePointsEquiv b (splitTorus _ I)
      (RingRootCell.base E.ring) (t ≫ (splitTorus.baseChangeIso b I).inv.hom.hom) =
        E.baseComparison ≫ E.torus := by
    dsimp only [t]
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id]
    exact (GroupScheme.baseChangePointsEquiv b (splitTorus _ I)
      (RingRootCell.base E.ring)).apply_symm_apply _
  have hf : D.A 1 * (E.baseComparison ≫ E.normalizer) =
      D.cellPt E.beta (E.baseComparison ≫ E.torus) E.delta :=
    E.baseComparison_factorization
  have hfactor : D'.A 1 * E.baseSection = D'.cellPt E.beta t E.delta := by
    refine LocalRankOneCell.factorization_of_baseChangePointsEquiv
      (torusHom I G i mu) (P.root a)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))
      (rootLift i mu hp ha)
      (isRootParametrization_rootLift i mu hm _)
      (isRootParametrization_rootLift i mu hp ha) D.open_cell E.ring
      E.baseSection E.beta t E.delta ?_
    rw [ht]
    exact (congrArg (fun n => D.A 1 * n) E.baseSection_recovers).trans hf
  exact { D' with
    h := h, hh := hh, n := E.baseSection, hn := hn, hn2 := hn2
    cβ := E.beta, ct := t, cδ := E.delta
    unitβ := E.unit_beta, unitδ := E.unit_delta, decomp := hfactor }

/-- The actual pointed affine etale Weyl chart for the rank-one
centralizer, with its prescribed integral reflection. -/
def etaleRankOneChart (hi : IsClosedSubgroup i)
    (s : Spec (CommRingCat.of R)) :
    EtaleRankOneChart (torusHom I G i mu) (P.root a)
      (rootLift i mu hp ha)
      (rootLift i mu hm (by
        simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
          congrArg Neg.neg ha))
      (isRootParametrization_rootLift i mu hp ha)
      (isRootParametrization_rootLift i mu hm _)
      (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm).open_cell
      (P.reflection a) s := by
  let p := pointedEtaleUnitCellReflection i mu hG hmax hP hstd a ha hmu hp hm hi s
  let E := p.affineEtaleUnitCell
  letI := E.coefficientAlgebra
  let W := affineEtaleWeylData i mu hG hmax hP hstd a ha hmu hp hm E hi
  refine
    { ring := E.ring
      algebra := E.coefficientAlgebra
      etale := ?_
      covers := ?_
      data := W
      cell_eq := rfl
      normalizes := ?_ }
  · rw [E.coefficientAlgebra_baseMap]
    exact E.etale
  · rw [E.coefficientAlgebra_baseMap]
    refine ⟨E.residuePoint (IsLocalRing.closedPoint _), ?_⟩
    change (E.residuePoint ≫ E.projection) (IsLocalRing.closedPoint _) = s
    rw [E.residue_over, Scheme.fromSpecResidueField_apply]
  · let C := groupScheme I G i mu
    let b := algebraBaseMap R E.ring
    let : IsAffineHom ((GroupScheme.baseChange b).obj C).X.hom :=
      inferInstanceAs (IsAffineHom (Limits.pullback.snd C.X.hom b))
    let : IsAffine W.G.X.left :=
      isAffine_of_isAffineHom ((GroupScheme.baseChange b).obj C).X.hom
    change IsNormalizingPoint W.i
      (scalarWeylPoint W.xp W.xm (W.betaUnit : E.ring))
      (splitTorus.exponentCommIso (Spec E.ring) I (P.reflection a))
    rw [W.scalarWeylPoint_betaUnit]
    have he : RingRootCell.reflectionIso W.α W.h W.hh =
        splitTorus.exponentCommIso (Spec E.ring) I (P.reflection a) :=
      reflectionIso_eq hstd a E.ring
    rw [← he]
    exact W.normalizedWeylPoint_isNormalizing

include hG hmax hP ha hmu hstd hp hm in
/-- Pointwise charts give one global unit rescaling in the original
ambient group. No locality assumption on the base ring is used. -/
theorem exists_unit_weylNormalization_of_pairing (hi : IsClosedSubgroup i) :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint xp (scaleHom (d : R) ≫ xm))
      (P.reflection a) := by
  obtain ⟨d, hn⟩ := exists_unit_weylNormalization_of_charts
    (torusHom I G i mu) (P.root a)
    (rootLift i mu hp ha)
    (rootLift i mu hm (by
      simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_zero] using
        congrArg Neg.neg ha))
    (isRootParametrization_rootLift i mu hp ha)
    (isRootParametrization_rootLift i mu hm _)
    (affineCorootCell i mu hG hmax hP hstd a ha hmu hp hm).open_cell
    (P.reflection a)
    (etaleRankOneChart i mu hG hmax hP hstd a ha hmu hp hm hi)
  refine ⟨d, isWeylPoint_of_isNormalizingPoint ?_⟩
  have h := hn.isNormalizingPoint.comp (inclusion I G i mu)
  rw [torusHom_comp] at h
  change IsNormalizingPoint (T := splitTorus.commGroupScheme _ I) i
    (weylPoint (rootLift i mu hp ha) (scaleHom (d : R) ≫ rootLift i mu hm _) ≫
      (inclusion I G i mu).hom.hom) _ at h
  rw [← weylPoint_comp, rootLift_comp, Category.assoc, rootLift_comp] at h
  exact h

end Langlands.GroupScheme.AffineRootNormalization

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    {xp xm : Ga R ⟶ G}
    (hp : IsRootParametrization i (P.root a) xp)
    (hm : IsRootParametrization i (-P.root a) xm)

include hG hi hmax hP hp hm in
/-- Every actual opposite root pair over an arbitrary affine base
admits one global unit rescaling realizing its integral reflection. -/
theorem exists_unit_weylNormalization_affine :
    ∃ d : Rˣ, IsWeylPoint i (weylPoint xp (scaleHom (d : R) ≫ xm))
      (P.reflection a) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let : IsEmpty (Spec (CommRingCat.of R)) :=
      inferInstanceAs (IsEmpty (PrimeSpectrum R))
    refine ⟨1, ?_⟩
    intro Z t
    let : IsEmpty Z.left := Function.isEmpty Z.hom
    apply Over.OverMorphism.ext
    exact isInitialOfIsEmpty.hom_ext _ _
  · obtain ⟨m, hm'⟩ := Ideal.exists_maximal R
    let := hm'
    let k := R ⧸ m
    let : Field k := Ideal.Quotient.field m
    have hstd : ∀ v w, P.toLinearMap v w = ∑ j, v j * w j :=
      hP.pairing k
    have : Finite J := hP.finite
    have := hP.isReduced
    obtain ⟨mu, ha, hmu⟩ := LocalRootGroup.exists_kernel_exponent P k a
    exact AffineRootNormalization.exists_unit_weylNormalization_of_pairing
      i mu hG hmax hP hstd a ha hmu hp hm hi

/-- A chosen normalized opposite pair on an arbitrary affine base,
retaining its actual original-base unit. -/
def normalizedAffineOppositePair : NormalizedOppositePair i xp xm (P.reflection a) where
  scalar := (exists_unit_weylNormalization_affine hG i hi hmax hP a hp hm).choose
  normalizes :=
    (exists_unit_weylNormalization_affine hG i hi hmax hP a hp hm).choose_spec

end Langlands.GroupScheme.LocalSplitCell
