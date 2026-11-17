import Langlands.GroupScheme.Reductive.IsogenyNoConeCommutation
import Langlands.GroupScheme.Reductive.LocalSplitRankOneLaws

/-! # Square and fixed actions for powered Weyl families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Root-point equality on affine tests determines an additive-line homomorphism. -/
theorem hom_ext_affine_rootPoints {v w : Ga R ⟶ G}
    (h : ∀ (B : Type u) [CommRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x : Γ((Over.mk s).left, ⊤)), rootPoint v (Over.mk s) x = rootPoint w (Over.mk s) x) :
    v = w := by
  have he : v.hom.hom = w.hom.hom := by
    have he := h (MvPolynomial (Fin 1) R) (Ga R).X.hom (gaCoord (𝟙 (Ga R).X))
    simp only [rootPoint, gaCoord, VectorGroup.scalarPoint_coordinate] at he
    have hl := congrArg (fun q => q.left) he
    apply Over.OverMorphism.ext
    change (𝟙 (Ga R).X.left) ≫ v.hom.hom.left =
      (𝟙 (Ga R).X.left) ≫ w.hom.hom.left at hl
    exact (cancel_epi (𝟙 (Ga R).X.left)).mp hl
  apply hom_ext_points
  intro Z a
  rw [he]

/-- Any additive-line point is the scalar point of its actual coordinate. -/
theorem rootPoint_precompose_coordinate (F : Ga R ⟶ Ga R) (v : Ga R ⟶ G)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    rootPoint (F ≫ v) Z x = rootPoint v Z (gaCoord (rootPoint F Z x)) := by
  rw [rootPoint_comp]
  change rootPoint F Z x ≫ v.hom.hom =
    VectorGroup.scalarPoint (CommRingCat.of R) Z (gaCoord (rootPoint F Z x)) ≫ v.hom.hom
  rw [show VectorGroup.scalarPoint (CommRingCat.of R) Z (gaCoord (rootPoint F Z x)) =
    rootPoint F Z x from VectorGroup.scalarPoint_coordinate _ _]

/-- Commuting maps remain commuting under arbitrary separate additive-line
precomposition, including the characteristic power maps. -/
theorem PointsCommute.precompose {v w : Ga R ⟶ G} (h : PointsCommute v w)
    (F F' : Ga R ⟶ Ga R) : PointsCommute (F ≫ v) (F' ≫ w) := by
  intro B _ s x y
  rw [rootPoint_precompose_coordinate, rootPoint_precompose_coordinate]
  exact h B s _ _

variable {I J : Type u} [Fintype I]
    (P : RootDatum J (I → ℤ) (I → ℤ))

omit [Fintype I] in
/-- Commutation with both opposite root maps makes their actual Weyl
product act trivially. No parametrization assumption on the maps is used. -/
theorem wordConj_fixed_of_pointsCommute
    (v : J → (Ga R ⟶ G)) (c : J) (w : Ga R ⟶ G)
    (hc : PointsCommute (v c) w)
    (hm : PointsCommute (v (P.reflectionPerm c c)) w) :
    wordConj P v [c] w = w := by
  apply hom_ext_affine_rootPoints
  intro B _ s x
  rw [rootPoint_wordConj]
  simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  change G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s) *
      rootPoint w (Over.mk s) x *
      (G.constantPoint (weylPoint (v c) (v (P.reflectionPerm c c))) (Over.mk s))⁻¹ = _
  rw [constantPoint_weylPoint]
  have hcp : Commute (rootPoint (v c) (Over.mk s) 1) (rootPoint w (Over.mk s) x) :=
    hc B s 1 x
  have hmp : Commute (rootPoint (v (P.reflectionPerm c c)) (Over.mk s) (-1))
      (rootPoint w (Over.mk s) x) := hm B s (-1) x
  have hn := (hmp.mul_left hcp).mul_left hmp
  rw [hn.eq, mul_inv_cancel_right]

variable (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hstd : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j)

include hstd in
theorem coPairing_root_coroot_of_pairing (a c : J) :
    coPairing (P.root a) (P.coroot c) = P.pairingIn ℤ a c := by
  rw [coPairing, ← hstd, RootPairing.root_coroot_eq_pairing,
    ← P.algebraMap_pairingIn ℤ]
  simp

/-- The character-conjugation formula needed of an actual map. This
does not assert that the map represents a whole root subgroup. -/
def HasRootConjugationFormula (m : I → ℤ) (w : Ga R ⟶ G) : Prop :=
  ∀ (Z : Over (Spec (CommRingCat.of R)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (x : Γ(Z.left, ⊤)),
    (t ≫ i.hom.hom) * rootPoint w Z x * (t ≫ i.hom.hom)⁻¹ =
      rootPoint w Z
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I m) Z t * x)

include hstd in
/-- A coroot square acts on every map with the source-character formula
by the raw integer sign, without any root-parametrization premise. -/
theorem square_conj_rootPoint_of_formula
    {c a : J} {N : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X}
    (hN : N * N = cocharPoint (P.coroot c)
      (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1) ≫ i.hom.hom)
    {w : Ga R ⟶ G} (hw : HasRootConjugationFormula i (P.root a) w)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    (G.constantPoint N Z * G.constantPoint N Z) * rootPoint w Z x *
        (G.constantPoint N Z * G.constantPoint N Z)⁻¹ =
      rootPoint w Z
        (baseScalar Z (((P.pairingIn ℤ a c).negOnePow : ℤ) : R) * x) := by
  rw [← GroupScheme.constantPoint_mul, hN, ← toUnit_comp_eq_constantPoint,
    ← Category.assoc, hw]
  congr 1
  have hval := torusChar_cocharPoint (R := R) (P.root a) (P.coroot c)
    (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1)
  rw [coPairing_root_coroot_of_pairing P hstd] at hval
  unfold torusChar at hval
  rw [VectorGroup.charValue_comp, hval]
  rcases Int.even_or_odd (P.pairingIn ℤ a c) with he | ho
  · rw [he.neg_one_zpow, Int.negOnePow_even _ he]
    simp only [Units.val_one, Int.cast_one, map_one, one_mul]
  · rw [ho.neg_one_zpow, Int.negOnePow_odd _ ho]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      map_neg, map_one]

include hstd in
/-- The powered-family square step follows from the exact rank-one
laws and source-character equivariance alone. -/
theorem wordConj_square_of_rankOneLaws (v : J → (Ga R ⟶ G))
    (c a : J) (w : Ga R ⟶ G)
    (hc : RankOneLaws i (P.coroot c) (v c) (v (P.reflectionPerm c c)))
    (hw : HasRootConjugationFormula i (P.root a) w) :
    wordConj P v [c, c] w =
      scaleHom (((P.pairingIn ℤ a c).negOnePow : ℤ) : R) ≫ w := by
  have hN : rootWeylPoint P v c * rootWeylPoint P v c =
      cocharPoint (P.coroot c) (𝟙_ (Over (Spec (CommRingCat.of R)))) (-1) ≫ i.hom.hom := by
    have hs := hc.2.2.1 (𝟙_ (Over (Spec (CommRingCat.of R))))
    change ((𝟙 _ ≫ weylPoint (v c) (v (P.reflectionPerm c c))) *
      (𝟙 _ ≫ weylPoint (v c) (v (P.reflectionPerm c c)))) = _ at hs
    simpa only [Category.id_comp, rootWeylPoint] using hs
  apply hom_ext_affine_rootPoints
  intro B _ s x
  rw [rootPoint_wordConj, rootPoint_scaleHom]
  simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]
  exact square_conj_rootPoint_of_formula P i hstd hN hw (Over.mk s) x

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.PoweredWeylActions

open LocalSplitCell IsogenyNoCone

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I']
    [Finite J] [Finite J']
    {P : RootDatum J (I → ℤ) (I → ℤ)}
    {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    [P.IsReduced] [Q.IsReduced] {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    {H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom H.X.hom]
    (hH : IsReductive H)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (hi' : IsClosedSubgroup i')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') i')
    (hQ : IsFibrewiseRootDatumOf I' H i' Q)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)

include hH hi' hmax' hQ hchar in
/-- The source no-cone hypotheses force fixed conjugation after any
additive-line precompositions of the actual corresponding target roots.
The supplied equalities are the powered-family word formulas in the
isogeny application, and do not assert powered parametrization. -/
theorem wordConj_fixed_of_source_noCone
    (v : J → (Ga R ⟶ H)) (c a : J) (w : Ga R ⟶ H)
    (up um ua : Ga R ⟶ H) (Fp Fm Fa : Ga R ⟶ Ga R)
    (hp : IsRootParametrization i' (Q.root (f.indexEquiv.symm c)) up)
    (hm : IsRootParametrization i'
      (Q.root (f.indexEquiv.symm (P.reflectionPerm c c))) um)
    (ha : IsRootParametrization i' (Q.root (f.indexEquiv.symm a)) ua)
    (hvp : v c = Fp ≫ up)
    (hvm : v (P.reflectionPerm c c) = Fm ≫ um)
    (hwa : w = Fa ≫ ua)
    (hnp : P.root c ≠ -P.root a) (hcone : NoMixedRoot P c a)
    (hnm : P.root (P.reflectionPerm c c) ≠ -P.root a)
    (hconem : NoMixedRoot P (P.reflectionPerm c c) a) :
    wordConj P v [c] w = w := by
  apply wordConj_fixed_of_pointsCommute P v c w
  · rw [hvp, hwa]
    exact (pointsCommute_correspondingRoots f hH i' hi' hmax' hQ hchar hp ha
      hnp hcone).precompose Fp Fa
  · rw [hvm, hwa]
    exact (pointsCommute_correspondingRoots f hH i' hi' hmax' hQ hchar hm ha
      hnm hconem).precompose Fm Fa

end Langlands.GroupScheme.PoweredWeylActions

namespace Langlands.GroupScheme.LocalSplitCell

/-- The two exact Weyl action steps, using the coroot square and the
source-character formula or opposite-root commutation respectively.
These statements apply to powered maps without a parametrization premise. -/
def WeylSquareAndFixedActionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    (I J : Type u) [Fintype I]
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    (∀ m n, P.toLinearMap m n = ∑ j, m j * n j) →
    ∀ (v : J → (Ga R ⟶ G)) (c a : J) (w : Ga R ⟶ G),
      (RankOneLaws i (P.coroot c) (v c) (v (P.reflectionPerm c c)) →
        HasRootConjugationFormula i (P.root a) w →
        wordConj P v [c, c] w =
          scaleHom (((P.pairingIn ℤ a c).negOnePow : ℤ) : R) ≫ w) ∧
      (PointsCommute (v c) w → PointsCommute (v (P.reflectionPerm c c)) w →
        wordConj P v [c] w = w)

theorem weylSquareAndFixedAction : WeylSquareAndFixedActionStatement.{u} := by
  intro R _ G I J _ P i hstd v c a w
  exact ⟨wordConj_square_of_rankOneLaws P i hstd v c a w,
    wordConj_fixed_of_pointsCommute P v c w⟩

end Langlands.GroupScheme.LocalSplitCell
