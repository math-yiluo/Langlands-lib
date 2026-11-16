import Langlands.GroupScheme.Reductive.LocalSplitRootDatumExistence
import Langlands.GroupScheme.Torus.LocalSplitWeylOrder
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof

/-! # Closed-fibre Weyl images embed in every algebraically closed fibre -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LocalSplitCorootTransport

variable (I : Type u) [Fintype I]

/-- The integral coordinate change on character automorphisms is injective. -/
theorem coordinateConj_injective (k : Type u) [Field k] :
    Function.Injective (coordinateConj I k) := by
  intro a b h
  apply LinearEquiv.ext
  intro χ
  apply (splitTorus.characterLatticeEquiv k I).injective
  have he := DFunLike.congr_fun h (splitTorus.characterLatticeEquiv k I χ)
  change splitTorus.characterLatticeEquiv k I
      (a ((splitTorus.characterLatticeEquiv k I).symm
        (splitTorus.characterLatticeEquiv k I χ))) =
    splitTorus.characterLatticeEquiv k I
      (b ((splitTorus.characterLatticeEquiv k I).symm
        (splitTorus.characterLatticeEquiv k I χ))) at he
  simpa only [AddEquiv.symm_apply_apply] using he

end LocalSplitCorootTransport

namespace splitTorus

variable {k : Type u} [Field k] (I : Type u) [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) [Mono i.hom.hom.left]

/-- The full normalizer action on the fixed integral coordinate lattice. -/
def coordinateWeylAction :
    normalizerPoints (T := commGroupScheme _ I) i →*
      ((I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :=
  (LocalSplitCorootTransport.coordinateConj I k).comp
    (weylAction (T := commGroupScheme _ I) i)

/-- The actual full Weyl image, expressed on the coordinate lattice. -/
def coordinateWeylImage : Subgroup ((I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :=
  (coordinateWeylAction I i).range

/-- A closed coordinate torus in an affine algebraic group has finite full
coordinate Weyl image. -/
theorem finite_coordinateWeylImage
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hi : IsClosedSubgroup i) :
    Finite (coordinateWeylImage I i) := by
  have : Finite (weylAction (T := commGroupScheme _ I) i).range :=
    finite_weylImage_standard G I i hi
  rw [coordinateWeylImage, coordinateWeylAction, MonoidHom.range_comp]
  exact Finite.of_surjective _
    ((LocalSplitCorootTransport.coordinateConj I k).subgroupMap_surjective _)

/-- The coordinate image has the cardinality of the actual normalizer modulo
centralizer quotient over the field. -/
theorem natCard_coordinateWeylImage :
    Nat.card (coordinateWeylImage I i) =
      Nat.card (relativeWeylGroup (T := commGroupScheme _ I) i) := by
  rw [coordinateWeylImage, coordinateWeylAction, MonoidHom.range_comp]
  have hmap : Nat.card
      ((weylAction (T := commGroupScheme _ I) i).range.map
        (LocalSplitCorootTransport.coordinateConj I k)) =
      Nat.card (weylAction (T := commGroupScheme _ I) i).range := by
    exact Nat.card_congr
      ((weylAction (T := commGroupScheme _ I) i).range.equivMapOfInjective
        (LocalSplitCorootTransport.coordinateConj I k)
        (LocalSplitCorootTransport.coordinateConj_injective I k)).toEquiv.symm
  rw [hmap]
  unfold relativeWeylGroup
  have hker := (isSplitTorus_splitTorus (S := Spec (CommRingCat.of k)) I).weylAction_ker
    (T := commGroupScheme (Spec (CommRingCat.of k)) I) i
  rw [← hker]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange
      (weylAction (T := commGroupScheme _ I) i)).toEquiv).symm

/-- A coordinate image element is exactly an exponent automorphism realized
by an actual normalizing point. -/
theorem mem_coordinateWeylImage_iff [DecidableEq I]
    (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    C ∈ coordinateWeylImage I i ↔
      ∃ n, IsNormalizingPoint (T := commGroupScheme _ I) i n
        (exponentCommIso (Spec (CommRingCat.of k)) I C).symm := by
  constructor
  · rintro ⟨n, hn⟩
    let σ := normalizingAut (T := commGroupScheme _ I) i n
    have hσ : σ = (exponentCommIso (Spec (CommRingCat.of k)) I C).symm := by
      apply eq_exponentCommIso_symm I C σ
      intro m
      apply (characterLatticeEquiv k I).injective
      have hm := DFunLike.congr_fun hn m
      change characterLatticeEquiv k I
        (characterAut σ ((characterLatticeEquiv k I).symm m)) = C m at hm
      simpa only [exponentCharacter_eq_characterLatticeEquiv_symm,
        AddEquiv.apply_symm_apply] using hm
    refine ⟨n.val, ?_⟩
    rw [← hσ]
    exact isNormalizingPoint_normalizingAut (T := commGroupScheme _ I) i n
  · rintro ⟨n, hn⟩
    let n' : normalizerPoints (T := commGroupScheme _ I) i := ⟨n, _, hn⟩
    refine ⟨n', ?_⟩
    change LocalSplitCorootTransport.coordinateConj I k
      (weylAction (T := commGroupScheme _ I) i n') = C
    have hσ : normalizingAut (T := commGroupScheme _ I) i n' =
        (exponentCommIso (Spec (CommRingCat.of k)) I C).symm :=
      IsNormalizingPoint.unique (T := commGroupScheme _ I) i
        (isNormalizingPoint_normalizingAut (T := commGroupScheme _ I) i n') hn
    have he : weylAction (T := commGroupScheme _ I) i n' = characterAut
        (exponentCommIso (Spec (CommRingCat.of k)) I C).symm :=
      congrArg characterAut hσ
    rw [he, LocalSplitCorootTransport.coordinateConj_characterAut]

end splitTorus

namespace LocalSplitCorootTransport

variable {R : Type u} [CommRing R] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of R)))
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- Coordinate Weyl-image membership on a field fibre is the transporter
realization predicate. -/
theorem mem_coordinateWeylImage_iff
    (k : Type u) [Field k] [Algebra R k]
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    (C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)) :
    C ∈ splitTorus.coordinateWeylImage I
        (splitTorus.baseChangeHom (K := k) G I i) ↔
      IsRealizedAt I G i C k := by
  rw [splitTorus.mem_coordinateWeylImage_iff, isRealizedAt_iff]

variable [IsLocalRing R] [IsAffineHom G.X.hom]

/-- Smoothness of the actual transporter spreads an automorphism realized
over a closed-fibre field to every algebraically closed field over the local
base. No Weyl quotient scheme is required. -/
theorem IsRealizedAt.of_closedField
    (hG : Smooth G.X.hom)
    {k : Type u} [Field k] [Algebra R k]
    (hclosed : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R)
    {C : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)}
    (h : IsRealizedAt I G i C k)
    (l : Type u) [Field l] [IsAlgClosed l] [Algebra R l] :
    IsRealizedAt I G i C l := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let d := Diagonalizable.splitIso (CommRingCat.of R) (AddEquiv.refl (I → ℤ))
  let j₁ := d.hom ≫ (splitTorus.exponentIso (Spec (CommRingCat.of R)) I C).inv ≫ i
  let j₂ := d.hom ≫ i
  obtain ⟨g, hg⟩ := h
  let A := CommAlgCat.of (CommRingCat.of R) k
  let a : (algSpec (CommRingCat.of R)).obj (Opposite.op A) ⟶
      Over.mk (algebraBaseMap R k) := Over.homMk (𝟙 _) (by simp; rfl)
  obtain ⟨y, -⟩ := (PointwiseSchemeAction.exists_relativeTransporter_factor_iff
      j₁ j₂ (a ≫ g)).mpr
    ((PointwiseSchemeAction.isTransporter_precomp_iso_iff d).mpr (hg.restrict a))
  let X := PointwiseSchemeAction.relativeTransporterScheme j₁ j₂
  have : Smooth X.hom :=
    PointwiseSchemeAction.smooth_relativeTransporterScheme j₁ j₂ hG
  have hx : X.hom (y.left (IsLocalRing.closedPoint k)) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w y]
    exact hclosed
  let b := algebraBaseMap R l
  let Y := pullback X.hom b
  let p : Y ⟶ Spec (CommRingCat.of l) := pullback.snd X.hom b
  have : Smooth p := inferInstanceAs (Smooth (pullback.snd X.hom b))
  have : Nonempty Y :=
    Langlands.AlgebraicGeometry.nonempty_pullback_of_flat_of_closedPoint
      X.hom _ hx l
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints
    (Set.univ_nonempty : (Set.univ : Set Y).Nonempty) isOpen_univ.isLocallyClosed
  let s : Spec (CommRingCat.of l) ⟶ Y := pointOfClosedPoint p c hc
  have hs : s ≫ p = 𝟙 _ := pointOfClosedPoint_comp p c hc
  let z : Over.mk b ⟶ X := Over.homMk (s ≫ pullback.fst X.hom b) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ p) ≫ b = b
    rw [hs, Category.id_comp])
  exact ⟨z ≫ PointwiseSchemeAction.relativeTransporterHom j₁ j₂,
    (PointwiseSchemeAction.isTransporter_precomp_iso_iff d).mp
      ((PointwiseSchemeAction.relativeTransporterHom_isTransporter j₁ j₂).restrict z)⟩

/-- The actual full closed-fibre Weyl image is a subgroup of the image on
every algebraically closed field over a local base. -/
theorem coordinateWeylImage_le_of_closedField
    (hG : Smooth G.X.hom)
    (k : Type u) [Field k] [Algebra R k]
    (hclosed : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R)
    (l : Type u) [Field l] [IsAlgClosed l] [Algebra R l]
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    [Mono (splitTorus.baseChangeHom (K := l) G I i).hom.hom.left] :
    splitTorus.coordinateWeylImage I (splitTorus.baseChangeHom (K := k) G I i) ≤
      splitTorus.coordinateWeylImage I (splitTorus.baseChangeHom (K := l) G I i) := by
  intro C hC
  exact (mem_coordinateWeylImage_iff I G i l C).mpr
    (((mem_coordinateWeylImage_iff I G i k C).mp hC).of_closedField
      I G i hG hclosed l)

/-- If the torus is closed on the comparison fibre, the actual full
normalizer modulo centralizer quotient on the closed fibre has no larger
order than the quotient on that algebraically closed fibre. -/
theorem natCard_relativeWeylGroup_le_of_closedField
    (hG : Smooth G.X.hom)
    (k : Type u) [Field k] [Algebra R k]
    (hclosed : algebraBaseMap R k (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint R)
    (l : Type u) [Field l] [IsAlgClosed l] [Algebra R l]
    [Mono (splitTorus.baseChangeHom (K := k) G I i).hom.hom.left]
    [Mono (splitTorus.baseChangeHom (K := l) G I i).hom.hom.left]
    (hil : IsClosedSubgroup (splitTorus.baseChangeHom (K := l) G I i)) :
    Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := k) G I i)) ≤
      Nat.card (relativeWeylGroup (T := splitTorus.commGroupScheme _ I)
        (splitTorus.baseChangeHom (K := l) G I i)) := by
  let : Smooth G.X.hom := hG
  let : IsAffineHom ((baseChange (algebraBaseMap R l)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R l)))
  let : LocallyOfFiniteType ((baseChange (algebraBaseMap R l)).obj G).X.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom (algebraBaseMap R l)))
  let : Finite (splitTorus.coordinateWeylImage I
      (splitTorus.baseChangeHom (K := l) G I i)) :=
    splitTorus.finite_coordinateWeylImage I _ hil
  rw [← splitTorus.natCard_coordinateWeylImage I,
    ← splitTorus.natCard_coordinateWeylImage I]
  exact Nat.card_le_card_of_injective
    (Subgroup.inclusion (coordinateWeylImage_le_of_closedField I G i hG k hclosed l))
    (Subgroup.inclusion_injective _)

end LocalSplitCorootTransport

end Langlands.GroupScheme
