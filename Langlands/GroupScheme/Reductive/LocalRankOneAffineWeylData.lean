import Langlands.GroupScheme.Reductive.LocalRankOneAffineEtaleUnitCell

/-! # Actual ring Weyl data on affine etale neighbourhoods -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

namespace RingRootCell.AffineEtaleUnitCellData

variable {R : Type u} [CommRing R] {D : CellData R}
  {σ : D.T ≅ D.T} {s : Spec (CommRingCat.of R)}
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶ D.G.X}
  (E : AffineEtaleUnitCellData D σ s n₀)

/-- The coefficient algebra induced by the actual affine projection. -/
abbrev coefficientAlgebra : Algebra R E.ring :=
  (Spec.preimage E.projection).hom.toAlgebra

/-- The algebra-induced base map is the given etale projection. -/
theorem coefficientAlgebra_baseMap :
    letI := E.coefficientAlgebra
    algebraBaseMap R E.ring = E.projection :=
  Spec.map_preimage _

/-- The identity comparison of the coefficient base with the affine test. -/
def baseComparison :
    letI := E.coefficientAlgebra
    (Over.map (algebraBaseMap R E.ring)).obj (base E.ring) ⟶
      Over.mk E.projection := by
  letI := E.coefficientAlgebra
  exact Over.homMk (𝟙 _) (by
    change 𝟙 _ ≫ E.projection = 𝟙 _ ≫ algebraBaseMap R E.ring
    rw [E.coefficientAlgebra_baseMap]
    simp only [Category.id_comp])

/-- The normalizer as an actual section of the coefficient-ring pullback. -/
def baseSection :
    letI := E.coefficientAlgebra
    base E.ring ⟶ ((GroupScheme.baseChange
      (algebraBaseMap R E.ring)).obj D.G).X := by
  letI := E.coefficientAlgebra
  exact (GroupScheme.baseChangePointsEquiv
    (algebraBaseMap R E.ring) D.G (base E.ring)).symm
      (E.baseComparison ≫ E.normalizer)

/-- The actual section recovers the supplied original-base normalizer. -/
theorem baseSection_recovers :
    letI := E.coefficientAlgebra
    GroupScheme.baseChangePointsEquiv
      (algebraBaseMap R E.ring) D.G (base E.ring) E.baseSection =
        E.baseComparison ≫ E.normalizer := by
  let := E.coefficientAlgebra
  exact (GroupScheme.baseChangePointsEquiv
    (algebraBaseMap R E.ring) D.G (base E.ring)).apply_symm_apply _

/-- The coefficient-ring section retains the actual prescribed torus action. -/
theorem baseSection_isNormalizing :
    letI := E.coefficientAlgebra
    IsNormalizingPoint
      ((GroupScheme.baseChange (algebraBaseMap R E.ring)).map D.i)
      E.baseSection
      ((CommGroupScheme.baseChange (algebraBaseMap R E.ring)).mapIso σ) := by
  let := E.coefficientAlgebra
  have ht := E.isTransporter.baseChange (algebraBaseMap R E.ring)
    E.baseComparison E.baseSection E.baseSection_recovers
  rw [Functor.map_comp] at ht
  exact isNormalizingPoint_of_isTransporter ht

/-- The identity affine comparison retains both scalar coordinates exactly. -/
theorem baseComparison_factorization :
    letI := E.coefficientAlgebra
    D.A 1 * (E.baseComparison ≫ E.normalizer) =
      D.cellPt E.beta (E.baseComparison ≫ E.torus) E.delta := by
  let := E.coefficientAlgebra
  have hf := congrArg (fun v => E.baseComparison ≫ v) E.factorization
  have hc (x : Γ(Spec E.ring, ⊤)) : E.baseComparison.left.appTop x = x := rfl
  simpa only [MonObj.comp_mul, D.comp_A, D.comp_cellPt, map_one, hc] using hf

end RingRootCell.AffineEtaleUnitCellData

namespace splitTorus

variable {S S' : Scheme.{u}} {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme S} (i : splitTorus S I ⟶ G) (b : S' ⟶ S)
    (e : (I → ℤ) ≃ₗ[ℤ] (I → ℤ))
    {n : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj G).X}

/-- A prescribed action on the actual pullback torus gives that same
integral action in the standard split-torus coordinates. -/
theorem isNormalizingPoint_coordinates_of_baseChange
    (hn : IsNormalizingPoint
      (T := (CommGroupScheme.baseChange b).obj (commGroupScheme S I))
      ((GroupScheme.baseChange b).map i) n
      ((CommGroupScheme.baseChange b).mapIso (exponentCommIso S I e))) :
    IsNormalizingPoint (T := commGroupScheme S' I)
      ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) n
      (exponentCommIso S' I e) := by
  have he : (baseChangeIso b I).inv ≫
      (GroupScheme.baseChange b).map (exponentIso S I e).hom =
      (exponentIso S' I e).hom ≫ (baseChangeIso b I).inv := by
    apply (cancel_mono (baseChangeIso b I).hom).mp
    rw [Category.assoc, ← exponentIso_baseChange S I b e,
      Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change ((baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map i) ≫
      (((GroupScheme.baseChange b).obj G).innerIso n).hom = _
  rw [Category.assoc, hn]
  change (baseChangeIso b I).inv ≫
      (GroupScheme.baseChange b).map (exponentIso S I e).hom ≫
        (GroupScheme.baseChange b).map i =
    (exponentIso S' I e).hom ≫ (baseChangeIso b I).inv ≫
      (GroupScheme.baseChange b).map i
  rw [← Category.assoc, he, Category.assoc]

end splitTorus

namespace LocalRankOneWeylData

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {I : Type u} [Fintype I] [DecidableEq I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

omit [DecidableEq I] in
/-- The integral pairing from the original local base gives the actual
root-coroot composite over every coefficient ring. -/
theorem coroot_comp_root_over (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (A : Type u) [CommRing A] :
    splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I (P.coroot a) ≫
        splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.root a) =
      (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of A))) := by
  rw [splitTorus.exponentCocharacter_comp_exponentCharacter,
    ← hP.pairing (IsLocalRing.ResidueField R), P.root_coroot_two]
  rfl

/-- The reflection remains the same integral exponent reflection over an
arbitrary coefficient ring, without a locality assumption on that ring. -/
theorem reflectionIso_eq_exponentCommIso_over
    (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
    (A : Type u) [CommRing A] :
    RingRootCell.reflectionIso
        (splitTorus.exponentCharacter (Spec (CommRingCat.of A)) I (P.root a))
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of A)) I (P.coroot a))
        (coroot_comp_root_over hP a A) =
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
    rw [map_sub, map_smul, hP.pairing (IsLocalRing.ResidueField R)]
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

end LocalRankOneWeylData

namespace LocalRankOneCell

open LocalSplitCell LocalSplitRootBaseChange

/-- A factorization over the original base is also a factorization of the
actual pullback point in the standard root and torus coordinates. -/
theorem factorization_of_baseChangePointsEquiv
    {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))}
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (a : I → ℤ) (xm xp : Ga R ⟶ G)
    (hm : IsRootParametrization i (-a) xm) (hp : IsRootParametrization i a xp)
    (hopen : IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left)
    (A : Type u) [CommRing A] [Algebra R A]
    {Z : Over (Spec (CommRingCat.of A))}
    (n : Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X)
    (y : Γ(Z.left, ⊤)) (t : Z ⟶ (splitTorus (Spec (CommRingCat.of A)) I).X)
    (x : Γ(Z.left, ⊤))
    (hf : rootPoint xp ((Over.map (algebraBaseMap R A)).obj Z) 1 *
        GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z n =
      rootPoint xm ((Over.map (algebraBaseMap R A)).obj Z) y *
        ((GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) ≫ i.hom.hom) *
            rootPoint xp ((Over.map (algebraBaseMap R A)).obj Z) x)) :
    (baseChangeCellData i a xm xp hm hp hopen A).A 1 * n =
      (baseChangeCellData i a xm xp hm hp hopen A).cellPt y t x := by
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
  change GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
    (rootPoint (baseChangeRoot A xp) Z 1 * n) = _
  rw [map_mul, baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_cellPt]
  exact hf

end LocalRankOneCell

namespace splitTorus.RelativeCocharacterCentralizer

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu : I → ℤ)
  (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i)
  {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P) (a : J)
  (ha : ∑ j, P.root a j * mu j = 0)
  (hmu : ∀ b : J, ∑ j, P.root b j * mu j = 0 →
    P.root b = P.root a ∨ P.root b = -P.root a)
  {xp xm : Ga R ⟶ G}
  (hp : IsRootParametrization i (P.root a) xp)
  (hm : IsRootParametrization i (-P.root a) xm)
  {s : Spec (CommRingCat.of R)}
  {n₀ : Over.mk ((Spec (CommRingCat.of R)).fromSpecResidueField s) ⟶
    (groupScheme I G i mu).X}
  (E : RingRootCell.AffineEtaleUnitCellData
    (corootCellData i mu hG hmax hP a ha hmu hp hm)
    (LocalRankOneWeylData.corootReflectionIso hP a) s n₀)

/-- Actual Weyl data on the affine etale coefficient ring, retaining the
given normalizer and exactly its global unit-cell scalar coordinates. -/
def affineEtaleWeylData (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    RingRootCell.WeylData E.ring := by
  letI := E.coefficientAlgebra
  let C := groupScheme I G i mu
  let D := corootCellData i mu hG hmax hP a ha hmu hp hm
  let b := algebraBaseMap R E.ring
  let D' := corootBaseChangeCellData i mu hG hmax hP a ha hmu hp hm E.ring
  let h := exponentCocharacter (Spec (CommRingCat.of E.ring)) I (P.coroot a)
  have hh : h ≫ D'.α = (2 : ℤ) • 𝟙 (Gm (Spec (CommRingCat.of E.ring))) :=
    LocalRankOneWeylData.coroot_comp_root_over hP a E.ring
  have hn : IsNormalizingPoint D'.i E.baseSection
      (RingRootCell.reflectionIso D'.α h hh) := by
    have hn₀ := E.baseSection_isNormalizing
    change IsNormalizingPoint _ _
      ((CommGroupScheme.baseChange b).mapIso
        (RingRootCell.reflectionIso _ _ (LocalRankOneWeylData.coroot_comp_root hP a))) at hn₀
    rw [LocalRankOneWeylData.reflectionIso_eq_exponentCommIso hP a] at hn₀
    have he : RingRootCell.reflectionIso D'.α h hh =
        exponentCommIso (Spec (CommRingCat.of E.ring)) I (P.reflection a) :=
      LocalRankOneWeylData.reflectionIso_eq_exponentCommIso_over hP a E.ring
    rw [he]
    exact isNormalizingPoint_coordinates_of_baseChange
      (torusHom I G i mu) b (P.reflection a) hn₀
  let hC := isReductive i mu hG
  let : Smooth C.X.hom := hC.smooth
  have hiD : IsClosedSubgroup D'.i :=
    isClosedSubgroup_coordinateBaseChange I C (torusHom I G i mu) b
      (isClosedSubgroup_torusHom I G i mu hi)
  have hmaxD : IsFibrewiseMaximalTorus (T := D'.T) D'.i :=
    isFibrewiseMaximalTorus_coordinateBaseChange I C (torusHom I G i mu) b
      (isFibrewiseMaximalTorus i mu hmax)
  have hn2 := hn.exists_sq_eq_of_fibrewiseMaximal
    (RingRootCell.reflectionIso_trans_self D'.α h hh) (hC.baseChange b)
    (isSplitTorus_splitTorus I) hiD hmaxD
  let t₀ := (GroupScheme.baseChangePointsEquiv b (splitTorus _ I)
    (RingRootCell.base E.ring)).symm (E.baseComparison ≫ E.torus)
  let t := t₀ ≫ (baseChangeIso b I).hom.hom.hom
  have ht : GroupScheme.baseChangePointsEquiv b (splitTorus _ I)
      (RingRootCell.base E.ring) (t ≫ (baseChangeIso b I).inv.hom.hom) =
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

/-- The Weyl-data normalizer is the actual pullback of the supplied one. -/
theorem affineEtaleWeylData_n (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    (affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).n =
      E.baseSection := rfl

/-- Packaging preserves the supplied negative-cell scalar exactly. -/
theorem affineEtaleWeylData_beta (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    (affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).cβ =
      E.beta := rfl

/-- Packaging preserves the supplied positive-cell scalar exactly. -/
theorem affineEtaleWeylData_delta (hi : IsClosedSubgroup i) :
    letI := E.coefficientAlgebra
    (affineEtaleWeylData i mu hG hmax hP a ha hmu hp hm E hi).cδ =
      E.delta := rfl

end splitTorus.RelativeCocharacterCentralizer

end Langlands.GroupScheme
