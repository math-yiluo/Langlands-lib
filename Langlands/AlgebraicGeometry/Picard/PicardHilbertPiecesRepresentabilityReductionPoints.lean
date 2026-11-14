import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionDivisors

/-! # Picard classes of points of a family and the fppf Picard class sheaf -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist

lemma isInvertible_pullback {Y Y' : Scheme.{u}} (φ : Y' ⟶ Y) {M : Y.Modules}
    (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback φ).obj M) :=
  isInvertible_lineBundle ((LineBundle.pullback φ).obj (lineBundleOfIsInvertible M hM))

lemma pb_id_apply {Y : Scheme.{u}} (x : Group Y) : Group.pullback (𝟙 Y) x = x := by
  rw [Group.pullback_id]
  rfl

lemma pb_iso_inv_hom {Y Y' : Scheme.{u}} (e : Y ≅ Y') (x : Group Y') :
    Group.pullback e.inv (Group.pullback e.hom x) = x := by
  rw [← pb_comp_apply, e.inv_hom_id, pb_id_apply]

lemma pb_iso_hom_inv {Y Y' : Scheme.{u}} (e : Y ≅ Y') (x : Group Y) :
    Group.pullback e.hom (Group.pullback e.inv x) = x := by
  rw [← pb_comp_apply, e.hom_inv_id, pb_id_apply]

lemma pb_iso_injective {Y Y' : Scheme.{u}} (e : Y ≅ Y') :
    Function.Injective (Group.pullback e.hom) := fun a b h => by
  rw [← pb_iso_inv_hom e a, h, pb_iso_inv_hom]

/-- Every class is the class of an invertible module. -/
lemma exists_icl {Y : Scheme.{u}} (x : Group Y) :
    ∃ (N : Y.Modules) (hN : Scheme.Modules.IsInvertible N), icl N hN = x :=
  ⟨_, isInvertible_lineBundle (Group.lineBundleRepresentative Y x),
    (icl_lineBundle _ _).trans (Group.classOf_lineBundleRepresentative Y x)⟩

lemma icl_lineBundleOfIsInvertible {Y : Scheme.{u}} (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M) :
    (lineBundleOfIsInvertible M hM).classOf = icl M hM := rfl

section Points

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The fppf class of a Picard class of `T ×_S X`. -/
abbrev scl (T : Over S) (x : Group ((relativeSpace f).obj T)) :
    (RelativePicard.classSheafPresheaf f).obj (op T) :=
  (RelativePicard.toClassSheaf f).app (op T) x

lemma sheafClassOf_eq_scl (T : Over S) (L : LineBundle ((relativeSpace f).obj T)) :
    RelativePicard.sheafClassOf f T L = scl f T L.classOf := rfl

lemma map_scl {T T' : Over S} (k : T' ⟶ T) (x : Group ((relativeSpace f).obj T)) :
    (RelativePicard.classSheafPresheaf f).map k.op (scl f T x) =
      scl f T' (Group.pullback ((relativeSpace f).map k) x) := by
  rw [← Group.classOf_lineBundleRepresentative _ x, ← sheafClassOf_eq_scl,
    RelativePicard.map_sheafClassOf, Group.pullback_lineBundle_classOf]
  rfl

/-- The relative-space symmetry `T ×_S X ≅ X ×_S T`. -/
abbrev sym (T : Over S) : (relativeSpace f).obj T ≅ pullback f T.hom :=
  relativeSpaceSymmetry f T

lemma sym_hom_snd (T : Over S) :
    (sym f T).hom ≫ pullback.snd f T.hom = pullback.fst T.hom f :=
  pullbackSymmetry_hom_comp_snd _ _

lemma sym_hom_fst (T : Over S) :
    (sym f T).hom ≫ pullback.fst f T.hom = pullback.snd T.hom f :=
  pullbackSymmetry_hom_comp_fst _ _

/-- Kleiman's class criterion (`properFlatIntegralSheafClassTwist`) in Picard-group form,
transported to `X ×_S T`. -/
lemma scl_sym_eq_iff [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyIntegral f] (hε : ∃ ε : S ⟶ X, ε ≫ f = 𝟙 S) (T : Over S)
    (z z' : Group (pullback f T.hom)) :
    scl f T (Group.pullback (sym f T).hom z) = scl f T (Group.pullback (sym f T).hom z') ↔
      ∃ n : Group T.left, z = z' + Group.pullback (pullback.snd f T.hom) n := by
  have hcls := (properFlatIntegralSheafClassTwist f inferInstance inferInstance inferInstance
    inferInstance hε T).2
  let L := Group.lineBundleRepresentative _ (Group.pullback (sym f T).hom z)
  let L' := Group.lineBundleRepresentative _ (Group.pullback (sym f T).hom z')
  have hL : L.classOf = Group.pullback (sym f T).hom z :=
    Group.classOf_lineBundleRepresentative _ _
  have hL' : L'.classOf = Group.pullback (sym f T).hom z' :=
    Group.classOf_lineBundleRepresentative _ _
  have key : ∀ n : Group T.left, Group.pullback (pullback.fst T.hom f) n =
      Group.pullback (sym f T).hom (Group.pullback (pullback.snd f T.hom) n) := fun n => by
    rw [← pb_comp_apply, sym_hom_snd]
  rw [← hL, ← hL', ← sheafClassOf_eq_scl, ← sheafClassOf_eq_scl, hcls L L']
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    refine ⟨icl N hN, pb_iso_injective (sym f T) ?_⟩
    rw [map_add, ← key, ← hL, ← hL', ← icl_lineBundle L (isInvertible_lineBundle L),
      ← icl_lineBundle L' (isInvertible_lineBundle L')]
    rw [(icl_eq_iff _ _ _ (isInvertible_tensor (isInvertible_lineBundle L')
      (isInvertible_pullback _ hN))).2 ⟨e⟩]
    rw [icl_tensor _ _ (isInvertible_lineBundle L') (isInvertible_pullback _ hN),
      icl_pullback _ _ hN]
    rfl
  · rintro ⟨n, hn⟩
    obtain ⟨N, hN, rfl⟩ := exists_icl n
    refine ⟨N, hN, ?_⟩
    apply nonempty_iso_tensor_of_icl (isInvertible_lineBundle L) (isInvertible_lineBundle L')
      (isInvertible_pullback _ hN)
    rw [icl_lineBundle, icl_lineBundle, icl_pullback _ _ hN, hL, hL', hn, map_add, ← key]
    rfl

end Points

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
