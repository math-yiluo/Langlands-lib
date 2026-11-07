import Langlands.GroupScheme.Reductive.SplitBigCellField
import Langlands.AlgebraicGeometry.FiberwiseOpenImmersion
import Langlands.GroupScheme.Rational.RootSubgroupBaseChange
import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Reductive.IntegralWeylVectorProperties
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.SmoothProducts
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Dynamic.Functoriality

/-! # The big cell over a ring, from its residue-field fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalSplitBigCell

open LocalSplitCell RelativeRoot

/-! ### Base change of root parametrizations to a field -/

section RootBaseChange

variable {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k]

/-- Coordinates of the points of the base change of `𝔾ₐ` to a field `k`: a point over `Z`
corresponds to a point of `𝔾ₐ` over `Z` regarded over `Spec R`, with the same coordinate. -/
def gaCoordinates (Z : Over (Spec (CommRingCat.of k))) :
    (Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R k)).obj (Ga R)).X) ≃*
      Multiplicative (Fin 1 → Γ(Z.left, ⊤)) :=
  (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (Ga R) Z).trans
    (VectorGroup.coordinates (CommRingCat.of R) 1 ((Over.map (algebraBaseMap R k)).obj Z))

theorem isNaturalVectorCoordinates_gaCoordinates :
    IsNaturalVectorCoordinates (gaCoordinates (R := R) k) := by
  intro T W f v
  simp only [gaCoordinates, MulEquiv.trans_apply,
    GroupScheme.baseChangePointsEquiv_naturality]
  rfl

/-- The base change of `𝔾ₐ` from `R` to a field `k` is `𝔾ₐ` over `k`. -/
def gaIso : (GroupScheme.baseChange (algebraBaseMap R k)).obj (Ga R) ≅ Ga k :=
  vectorGroupIso (gaCoordinates (R := R) k) (isNaturalVectorCoordinates_gaCoordinates k)

theorem baseChangePointsEquiv_scalarPoint (Z : Over (Spec (CommRingCat.of k)))
    (c : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (Ga R) Z
        (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ (gaIso (R := R) k).inv.hom.hom) =
      VectorGroup.scalarPoint (CommRingCat.of R) ((Over.map (algebraBaseMap R k)).obj Z) c := by
  have h := coordinates_comp_vectorGroupIso_hom (gaCoordinates (R := R) k)
    (isNaturalVectorCoordinates_gaCoordinates k) Z
    (VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ (gaIso (R := R) k).inv.hom.hom)
  change VectorGroup.coordinates (CommRingCat.of k) 1 Z
    ((VectorGroup.scalarPoint (CommRingCat.of k) Z c ≫ (gaIso (R := R) k).inv.hom.hom) ≫
      (gaIso (R := R) k).hom.hom.hom) = _ at h
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_scalarPoint]
  change (gaCoordinates (R := R) k Z _).toAdd j = c
  rw [← h, VectorGroup.coordinates_scalarPoint]

variable {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The base change to `k` of a map `u : 𝔾ₐ ⟶ G`, with source the standard `𝔾ₐ` over `k`. -/
def baseChangeRoot (u : Ga R ⟶ G) : Ga k ⟶ (GroupScheme.baseChange (algebraBaseMap R k)).obj G :=
  (gaIso (R := R) k).inv ≫ (GroupScheme.baseChange (algebraBaseMap R k)).map u

/-- The values of the base-changed root map correspond to the values of the original map. -/
theorem baseChangePointsEquiv_rootPoint (u : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of k)))
    (c : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Z (rootPoint (baseChangeRoot k u) Z c) =
      rootPoint u ((Over.map (algebraBaseMap R k)).obj Z) c := by
  rw [rootPoint, baseChangeRoot, Grp.comp_hom_hom, ← Category.assoc,
    GroupScheme.baseChangePointsEquiv_comp, baseChangePointsEquiv_scalarPoint, rootPoint]

/-- Ordered products of base-changed root maps correspond to the original ordered products. -/
theorem baseChangePointsEquiv_orderedProduct {J : Type u} (u : J → (Ga R ⟶ G)) {r : ℕ}
    (e : Fin r → J) (Z : Over (Spec (CommRingCat.of k))) (c : Fin r → Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Z
        (orderedProduct (fun α => baseChangeRoot k (u α)) e Z c) =
      orderedProduct u e ((Over.map (algebraBaseMap R k)).obj Z) c := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    baseChangePointsEquiv_rootPoint]

variable {I : Type u} [Fintype I]

/-- The base-changed root map represents the root subgroup of the base-changed torus for the
same exponent character. -/
theorem isRepresentedBy_baseChangeRoot (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (m : I → ℤ) (u : Ga R ⟶ G)
    (hu : (subgroup (S := splitTorus.commGroupScheme _ I) i
      (splitTorus.exponentCharacter _ I m)).IsRepresentedBy u) :
    (subgroup (S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i)
      (splitTorus.exponentCharacter _ I m)).IsRepresentedBy (baseChangeRoot k u) := by
  have h := hu.baseChange (algebraBaseMap R k)
  rw [← subgroup_baseChange] at h
  have hsq : (GroupScheme.baseChange (algebraBaseMap R k)).map i ≫
      (Iso.refl ((GroupScheme.baseChange (algebraBaseMap R k)).obj G)).hom =
      CommGroupScheme.groupHom (splitTorus.commBaseChangeIso (algebraBaseMap R k) I).hom ≫
        splitTorus.baseChangeHom (K := k) G I i := by
    change _ ≫ 𝟙 _ = (splitTorus.baseChangeIso (algebraBaseMap R k) I).hom ≫
      (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv ≫ _
    rw [Category.comp_id, Iso.hom_inv_id_assoc]
  have htr := subgroup_comap_of_transport (splitTorus.commBaseChangeIso (algebraBaseMap R k) I)
    (Iso.refl _) hsq (characterLattice.baseChange (algebraBaseMap R k) _
      (splitTorus.exponentCharacter _ I m))
  have ha : characterLattice.congr (splitTorus.commBaseChangeIso (algebraBaseMap R k) I)
      (characterLattice.baseChange (algebraBaseMap R k) _ (splitTorus.exponentCharacter _ I m)) =
      splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I m := by
    rw [characterLattice.congr_apply, ← splitTorus.exponentCharacter_baseChange,
      Iso.inv_hom_id_assoc]
  rw [ha, Iso.refl_hom, SubgroupFunctor.comap_id] at htr
  rw [htr]
  refine ⟨?_, ?_⟩
  · have : Mono ((GroupScheme.baseChange (algebraBaseMap R k)).map u).hom.hom := h.1
    change Mono ((gaIso (R := R) k).inv.hom.hom ≫
      ((GroupScheme.baseChange (algebraBaseMap R k)).map u).hom.hom)
    infer_instance
  · exact (SubgroupFunctor.range_iso_comp (gaIso (R := R) k).symm _).trans h.2

/-- Torus values of the base-changed torus map correspond to torus values of the original
map. -/
theorem baseChangePointsEquiv_torus (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {Z : Over (Spec (CommRingCat.of k))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Z
        (t ≫ (splitTorus.baseChangeHom (K := k) G I i).hom.hom) =
      GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv.hom.hom) ≫ i.hom.hom := by
  rw [← GroupScheme.baseChangePointsEquiv_comp, Category.assoc, ← Grp.comp_hom_hom]
  rfl

/-- Character values on torus points correspond under base change. -/
theorem charValue_exponentCharacter_baseChange (m : I → ℤ) {Z : Over (Spec (CommRingCat.of k))}
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :
    VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) Z t =
      VectorGroup.charValue (S := splitTorus.commGroupScheme _ I)
        (splitTorus.exponentCharacter _ I m) ((Over.map (algebraBaseMap R k)).obj Z)
        (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) Z
          (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv.hom.hom)) := by
  rw [VectorGroup.charValue, VectorGroup.charValue, splitTorus.pointsEquiv_exponentCharacter,
    splitTorus.pointsEquiv_exponentCharacter]
  have h := splitTorus.pointsEquiv_baseChangeIso_hom (algebraBaseMap R k) I Z
    (t ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  rw [h]
  rfl

/-- Root parametrizations stay root parametrizations after base change to a field. -/
theorem isRootParametrization_baseChangeRoot (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (m : I → ℤ) (u : Ga R ⟶ G) (hu : IsRootParametrization i m u) :
    IsRootParametrization (splitTorus.baseChangeHom (K := k) G I i) m (baseChangeRoot k u) where
  represents := isRepresentedBy_baseChangeRoot k i m u hu.represents
  isClosedSubgroup := by
    have hc := hu.isClosedSubgroup.baseChange (algebraBaseMap R k)
    change IsClosedImmersion ((gaIso (R := R) k).inv.hom.hom.left ≫
      ((GroupScheme.baseChange (algebraBaseMap R k)).map u).hom.hom.left)
    have : IsClosedImmersion ((GroupScheme.baseChange (algebraBaseMap R k)).map u).hom.hom.left :=
      hc
    have : IsIso (gaIso (R := R) k).inv.hom.hom.left :=
      (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map (gaIso (R := R) k).inv))
    infer_instance
  equivariant Z t c := by
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G Z).injective
    rw [map_mul, map_mul, map_inv, baseChangePointsEquiv_torus, baseChangePointsEquiv_rootPoint,
      baseChangePointsEquiv_rootPoint, hu.equivariant,
      charValue_exponentCharacter_baseChange (R := R) k]

end RootBaseChange

/-! ### The cell source and its base change -/

section Cell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}

/-- The three coordinates of a point of the cell source. -/
def coordTriple {W : Over (Spec (CommRingCat.of R))} (x : W ⟶ cellObj R I m n) :
    (Fin m → Γ(W.left, ⊤)) × (W ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) ×
      (Fin n → Γ(W.left, ⊤)) :=
  (negCoord x, torusCoord x, posCoord x)

variable (R I m n) in
/-- On points, the cell source is the product of its negative, torus and positive
coordinates. -/
theorem coordTriple_bijective (W : Over (Spec (CommRingCat.of R))) :
    Function.Bijective (coordTriple (R := R) (I := I) (m := m) (n := n) (W := W)) := by
  constructor
  · intro x x' h
    simp only [coordTriple, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have e1 : x ≫ fst _ _ ≫ fst _ _ = x' ≫ fst _ _ ≫ fst _ _ :=
      (VectorGroup.coordinates _ m W).injective (Multiplicative.toAdd.injective h1)
    have e3 : x ≫ snd _ _ = x' ≫ snd _ _ :=
      (VectorGroup.coordinates _ n W).injective (Multiplicative.toAdd.injective h3)
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ e3
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simpa only [Category.assoc] using e1
    · simpa only [torusCoord, Category.assoc] using h2
  · rintro ⟨v, t, w⟩
    refine ⟨lift (lift ((VectorGroup.coordinates _ m W).symm (Multiplicative.ofAdd v)) t)
      ((VectorGroup.coordinates _ n W).symm (Multiplicative.ofAdd w)), ?_⟩
    simp only [coordTriple, negCoord, torusCoord, posCoord, lift_fst_assoc, lift_fst, lift_snd,
      MulEquiv.apply_symm_apply, toAdd_ofAdd]

variable (R I m n) (k : Type u) [Field k] [Algebra R k]

/-- The base change of the cell source to a field `k`. -/
abbrev fibreObj : Over (Spec (CommRingCat.of k)) :=
  (Over.pullback (algebraBaseMap R k)).obj (cellObj R I m n)

/-- The universal point of the cell source over its base change. -/
def fibreCounit :
    (Over.map (algebraBaseMap R k)).obj (fibreObj R I m n k) ⟶ cellObj R I m n :=
  ((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv _ _).symm (𝟙 _)

/-- The negative-root coordinates of the base-changed cell source. -/
def fibreNeg : Fin m → Γ((fibreObj R I m n k).left, ⊤) :=
  negCoord (R := R) (Z := (Over.map (algebraBaseMap R k)).obj (fibreObj R I m n k))
    (fibreCounit R I m n k)

/-- The positive-root coordinates of the base-changed cell source. -/
def fibrePos : Fin n → Γ((fibreObj R I m n k).left, ⊤) :=
  posCoord (R := R) (Z := (Over.map (algebraBaseMap R k)).obj (fibreObj R I m n k))
    (fibreCounit R I m n k)

/-- The torus coordinate of the base-changed cell source. -/
def fibreTorus : fibreObj R I m n k ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X :=
  (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) _).symm
      (torusCoord (fibreCounit R I m n k)) ≫
    (splitTorus.baseChangeIso (algebraBaseMap R k) I).hom.hom.hom

theorem homEquiv_symm_eq {Z : Over (Spec (CommRingCat.of k))} (z : Z ⟶ fibreObj R I m n k) :
    ((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv Z (cellObj R I m n)).symm z =
      (Over.map (algebraBaseMap R k)).map z ≫ fibreCounit R I m n k := by
  rw [fibreCounit, ← Adjunction.homEquiv_naturality_left_symm, Category.comp_id]

/-- The coordinates of the base-changed cell source identify its points with triples. -/
theorem fibreCoords_bijective (Z : Over (Spec (CommRingCat.of k))) :
    Function.Bijective fun z : Z ⟶ fibreObj R I m n k =>
      ((fun r => z.left.appTop (fibreNeg R I m n k r)), z ≫ fibreTorus R I m n k,
        (fun r => z.left.appTop (fibrePos R I m n k r))) := by
  let W := (Over.map (algebraBaseMap R k)).obj Z
  let g : (Z ⟶ ((GroupScheme.baseChange (algebraBaseMap R k)).obj
      (splitTorus (Spec (CommRingCat.of R)) I)).X) →
      (Z ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) :=
    fun y => y ≫ (splitTorus.baseChangeIso (algebraBaseMap R k) I).hom.hom.hom
  have hg : Function.Bijective g :=
    (isoPointsEquiv (splitTorus.baseChangeIso (algebraBaseMap R k) I) Z).bijective
  let Φ : (Fin m → Γ(W.left, ⊤)) × (W ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) ×
      (Fin n → Γ(W.left, ⊤)) →
      (Fin m → Γ(Z.left, ⊤)) × (Z ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) ×
        (Fin n → Γ(Z.left, ⊤)) :=
    Prod.map id (Prod.map
      (g ∘ (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) Z).symm) id)
  have hΦ : Function.Bijective Φ :=
    Function.Bijective.prodMap Function.bijective_id
      (Function.Bijective.prodMap (hg.comp (MulEquiv.bijective _)) Function.bijective_id)
  have hfun : (fun z : Z ⟶ fibreObj R I m n k =>
      ((fun r => z.left.appTop (fibreNeg R I m n k r)), z ≫ fibreTorus R I m n k,
        (fun r => z.left.appTop (fibrePos R I m n k r)))) =
      Φ ∘ coordTriple (R := R) (I := I) (m := m) (n := n) (W := W) ∘
        ((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv Z (cellObj R I m n)).symm := by
    funext z
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · change _ = negCoord (((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv Z
        (cellObj R I m n)).symm z)
      rw [homEquiv_symm_eq, negCoord_comp]
      rfl
    · change _ = g ((GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) Z).symm
        (torusCoord (((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv Z
          (cellObj R I m n)).symm z)))
      rw [homEquiv_symm_eq, torusCoord_comp]
      simp only [fibreTorus, g]
      rw [← Category.assoc]
      congr 1
      apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) (splitTorus _ I) Z).injective
      rw [MulEquiv.apply_symm_apply, GroupScheme.baseChangePointsEquiv_naturality,
        MulEquiv.apply_symm_apply]
    · change _ = posCoord (((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv Z
        (cellObj R I m n)).symm z)
      rw [homEquiv_symm_eq, posCoord_comp]
      rfl
  rw [hfun]
  exact hΦ.comp ((coordTriple_bijective R I m n W).comp (Equiv.bijective _))

end Cell

/-! ### The fibre of the big-cell map -/

section Fibre

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {m n : ℕ}
  (k : Type u) [Field k] [Algebra R k] {G : GroupScheme (Spec (CommRingCat.of R))} {J : Type u}

/-- The base change to `k` of the big-cell map is the big-cell formula for the base-changed
root maps and torus, in the coordinates of the base-changed cell source. -/
theorem pullback_map_cellMap (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (u : J → (Ga R ⟶ G)) (neg : Fin m → J) (pos : Fin n → J) :
    ((Over.pullback (algebraBaseMap R k)).map (cellMap i u neg pos) :
        fibreObj R I m n k ⟶ ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X) =
      orderedProduct (fun α => baseChangeRoot k (u α)) neg _ (fibreNeg R I m n k) *
        (fibreTorus R I m n k ≫ (splitTorus.baseChangeHom (K := k) G I i).hom.hom) *
        orderedProduct (fun α => baseChangeRoot k (u α)) pos _ (fibrePos R I m n k) := by
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R k) G _).injective
  rw [map_mul, map_mul, baseChangePointsEquiv_orderedProduct,
    baseChangePointsEquiv_orderedProduct, baseChangePointsEquiv_torus]
  change ((Over.mapPullbackAdj (algebraBaseMap R k)).homEquiv _ G.X).symm
    (𝟙 _ ≫ (Over.pullback (algebraBaseMap R k)).map (cellMap i u neg pos)) = _
  rw [Adjunction.homEquiv_naturality_right_symm, comp_cellMap]
  simp only [fibreTorus, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom,
    Category.comp_id, MulEquiv.apply_symm_apply]
  rfl

end Fibre

/-! ### The root datum on a field fibre -/

section RootDatum

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] (k : Type u) [Field k] [Algebra R k]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {J : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

local instance fibreAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R k)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))

theorem exponentCharacter_injective :
    Function.Injective (splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I) := by
  intro a a' h
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k] at h
  exact (splitTorus.characterLatticeEquiv k I).symm.injective h

/-- The relative roots of the base-changed torus are the exponent characters of the roots. -/
theorem relativeRoots_baseChangeHom (hP : IsFibrewiseRootDatumOf I G i P) :
    relativeRoots (T := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        (splitTorus.baseChangeHom (K := k) G I i) =
      Set.range fun α => splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) := by
  rw [relativeRoots, ← (hP.field k).2.1]
  congr 1
  funext α
  exact CoordinateRootDatum.fieldRealization_root k P α

/-- The roots of the base-changed torus have reduced rays. -/
theorem reducedRays (hP : IsFibrewiseRootDatumOf I G i P) :
    SplitBigCell.ReducedRays (S := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
      (splitTorus.baseChangeHom (K := k) G I i) := by
  have := hP.isReduced
  intro β₁ hβ₁ β₂ hβ₂ p q hp hq h
  rw [relativeRoots_baseChangeHom k hP] at hβ₁ hβ₂
  obtain ⟨α₁, rfl⟩ := hβ₁
  obtain ⟨α₂, rfl⟩ := hβ₂
  beta_reduce at h ⊢
  rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm I k,
    ← map_nsmul (splitTorus.characterLatticeEquiv k I).symm p,
    ← map_nsmul (splitTorus.characterLatticeEquiv k I).symm q] at h
  have h' : p • P.root α₁ = q • P.root α₂ :=
    (splitTorus.characterLatticeEquiv k I).symm.injective h
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (P.ne_zero α₂)
  have hdep : ¬ LinearIndependent ℤ ![P.root α₁, P.root α₂] := by
    rw [LinearIndependent.pair_iff]
    intro hli
    have := hli (p : ℤ) (-(q : ℤ)) (by rw [neg_smul, natCast_zsmul, natCast_zsmul, h',
      add_neg_cancel])
    omega
  rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) α₁ α₂ hdep with he | he
  · rw [he] at h'
    have hj' := congrFun h' j
    simp only [Pi.smul_apply, nsmul_eq_mul] at hj'
    have hpq : (p : ℤ) = q := mul_right_cancel₀ hj hj'
    exact ⟨by rw [he], by exact_mod_cast hpq⟩
  · exfalso
    rw [he] at h'
    have hj' := congrFun h' j
    simp only [Pi.smul_apply, Pi.neg_apply, nsmul_eq_mul] at hj'
    have h0 : ((p : ℤ) + q) * P.root α₂ j = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h1 | h1
    · omega
    · exact hj h1

variable [Fintype J]

/-- The cocharacter of the field big cell: the exponent cocharacter of the sum of the positive
coroots, which pairs with each root to twice its height. -/
def cellCocharacter (bs : P.Base) :
    cocharacterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) :=
  splitTorus.exponentCocharacter _ I (IntegralWeylVector.positiveRootSum P.flip bs.flip)

theorem pairing_cellCocharacter (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base) (α : J) :
    latticePairing (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
        (splitTorus.exponentCharacter _ I (P.root α)) (cellCocharacter k bs) =
      2 * bs.height α := by
  have := hP.isReduced
  rw [cellCocharacter, splitTorus.latticePairing_exponentCharacter_exponentCocharacter,
    ← hP.pairing k]
  obtain ⟨f, -, -, hf⟩ := bs.exists_root_eq_sum_int α
  rw [RootPairing.Base.height_eq_sum hf, hf, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h2 : P.toLinearMap (P.root j) (IntegralWeylVector.positiveRootSum P.flip bs.flip) = 2 :=
    IntegralWeylVector.pairing_positiveRootSum_simple P.flip bs.flip ⟨j, hj⟩
  rw [map_zsmul, LinearMap.smul_apply, h2, smul_eq_mul, mul_comm]

theorem isGenericCocharacter_cellCocharacter (hP : IsFibrewiseRootDatumOf I G i P)
    (bs : P.Base) :
    IsGenericCocharacter (splitTorus.baseChangeHom (K := k) G I i) (cellCocharacter k bs) := by
  intro β hβ
  rw [relativeRoots_baseChangeHom k hP] at hβ
  obtain ⟨α, rfl⟩ := hβ
  rw [pairing_cellCocharacter k hP bs α]
  have := bs.height_ne_zero α
  omega

theorem range_neg (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base) {m : ℕ}
    (neg : Fin m ≃ {α // ¬ bs.IsPos α}) :
    Set.range (fun r => splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I
        (P.root (neg r : J))) =
      {β | β ∈ relativeRoots (splitTorus.baseChangeHom (K := k) G I i) ∧
        latticePairing _ β (cellCocharacter k bs) < 0} := by
  ext β
  rw [Set.mem_ofPred_eq, relativeRoots_baseChangeHom k hP]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [pairing_cellCocharacter k hP]
    have h1 := (neg r).2
    rw [RootPairing.Base.isPos_iff] at h1
    have h2 := bs.height_ne_zero (neg r : J)
    omega
  · rintro ⟨⟨α, rfl⟩, h⟩
    rw [pairing_cellCocharacter k hP] at h
    refine ⟨neg.symm ⟨α, ?_⟩, ?_⟩
    · rw [RootPairing.Base.isPos_iff]
      omega
    · simp

theorem range_pos (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base) {n : ℕ}
    (pos : Fin n ≃ {α // bs.IsPos α}) :
    Set.range (fun r => splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I
        (P.root (pos r : J))) =
      {β | β ∈ relativeRoots (splitTorus.baseChangeHom (K := k) G I i) ∧
        0 < latticePairing _ β (cellCocharacter k bs)} := by
  ext β
  rw [Set.mem_ofPred_eq, relativeRoots_baseChangeHom k hP]
  constructor
  · rintro ⟨r, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [pairing_cellCocharacter k hP]
    have h1 := (pos r).2
    rw [RootPairing.Base.isPos_iff] at h1
    omega
  · rintro ⟨⟨α, rfl⟩, h⟩
    rw [pairing_cellCocharacter k hP] at h
    refine ⟨pos.symm ⟨α, ?_⟩, ?_⟩
    · rw [RootPairing.Base.isPos_iff]
      omega
    · simp

end RootDatum

/-! ### The big cell -/

section BigCell

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {J : Type u} [Fintype J] {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- **The big cell on a field fibre.** For every field `k` with an `R`-algebra structure, the
base change of the big-cell map to `k` is an open immersion. -/
theorem isOpenImmersion_fibre (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (bs : P.Base) (u : J → (Ga R ⟶ G))
    (hu : ∀ α, IsRootParametrization i (P.root α) (u α)) {m n : ℕ}
    (neg : Fin m ≃ {α // ¬ bs.IsPos α}) (pos : Fin n ≃ {α // bs.IsPos α})
    (k : Type u) [Field k] [Algebra R k] :
    IsOpenImmersion ((Over.pullback (algebraBaseMap R k)).map
      (cellMap i u (fun r => (neg r : J)) (fun r => (pos r : J)))).left := by
  have := hG.smooth
  rw [pullback_map_cellMap]
  exact SplitBigCell.isOpenImmersion_of_points
    ((GroupScheme.baseChange (algebraBaseMap R k)).obj G)
    (hG.isConnectedReductive_baseChange _) (splitTorus.commGroupScheme _ I)
    (isSplitTorus_splitTorus I) (splitTorus.baseChangeHom (K := k) G I i)
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k)
    (cellCocharacter k bs) (isGenericCocharacter_cellCocharacter k hP bs) (reducedRays k hP)
    (fun α => baseChangeRoot k (u α)) (fun r => (neg r : J)) (fun r => (pos r : J))
    (fun r => splitTorus.exponentCharacter _ I (P.root (neg r : J)))
    ((exponentCharacter_injective k).comp
      (P.root.injective.comp (Subtype.val_injective.comp neg.injective)))
    (range_neg k hP bs neg)
    (fun r => isRepresentedBy_baseChangeRoot k i _ _ (hu _).represents)
    (fun r => splitTorus.exponentCharacter _ I (P.root (pos r : J)))
    ((exponentCharacter_injective k).comp
      (P.root.injective.comp (Subtype.val_injective.comp pos.injective)))
    (range_pos k hP bs pos)
    (fun r => isRepresentedBy_baseChangeRoot k i _ _ (hu _).represents)
    (fibreObj R I m n k) (fibreNeg R I m n k) (fibreTorus R I m n k) (fibrePos R I m n k)
    (fibreCoords_bijective R I m n k)

end BigCell

end Langlands.GroupScheme.LocalSplitBigCell

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitBigCell

/-- **The big cell over a reduced local ring** (Conrad, *Reductive group schemes*,
Thm. 5.1.13, p.143, for split groups with a fibrewise root datum). The proof uses neither that
`R` is local nor that it is reduced: the big-cell map is an open immersion on every
residue-field fibre, by the big cell over a field, hence an open immersion. -/
theorem localSplitBigCell : LocalSplitBigCellStatement.{u} := by
  intro R _ _ _ G _ hG I _ i _ hmax J P hP bs u hu m n neg pos
  have := hG.smooth
  have : Fintype J := @Fintype.ofFinite J hP.finite
  have hV (d : ℕ) : Smooth (VectorGroup.groupScheme (CommRingCat.of R) d).X.hom :=
    Corepresented.smooth_groupScheme_iff.mpr inferInstance
  have : Smooth (cellObj R I m n).hom :=
    smooth_tensor _ _ (smooth_tensor _ _ (hV m) (smooth_splitTorus I)) (hV n)
  apply Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise
  intro s
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField s)
  let : Algebra R ((Spec (CommRingCat.of R)).residueField s) := φ.hom.toAlgebra
  have hb : algebraBaseMap R ((Spec (CommRingCat.of R)).residueField s) =
      (Spec (CommRingCat.of R)).fromSpecResidueField s :=
    Spec.map_preimage _
  have h := isOpenImmersion_fibre hG hmax hP bs u hu neg pos
    ((Spec (CommRingCat.of R)).residueField s)
  rw [hb] at h
  exact h

end Langlands.GroupScheme
