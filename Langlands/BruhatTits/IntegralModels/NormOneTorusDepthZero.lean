import Langlands.BruhatTits.IntegralModels.GeneralLinearDepthZero
import Langlands.GroupScheme.IntegralModel.LocalReductivity
import Langlands.GroupScheme.Torus.WeilRestrictionNormBaseChange
import Langlands.GroupScheme.Torus.ConnectedReductive
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneAnisotropyProof
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.FieldTheory.Finite.GaloisField

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Depth-zero data for a norm-one torus over a local field

Let `F` be a nonarchimedean local field and `B` a finite free `𝒪[F]`-algebra
with `F ⊗ B ≃ E` for a finite separable field extension `E / F` and
`𝓀[F] ⊗ B ≃ k'` for a field `k'`. If the norm-one kernel of `B` is smooth
over `𝒪[F]` (for instance, when `B` splits after a faithfully flat base
change), it is an integral model of the anisotropic norm-one torus
`R¹_{E/F} G_m`. Its special fibre is the norm-one torus of `k' / 𝓀[F]`, so it
gives relative-component model data with the identity as a reductive quotient.

This is the anisotropic-torus regression example for the depth-zero layer.
`G(F)^{0+}` is the congruence subgroup, and its index in `G^0(𝒪)` is the
number of norm-one units of `k'`. That number is `(q ^ n - 1) / (q - 1)` with
`n = [k' : 𝓀[F]]`, and `q + 1` in the quadratic case.

The first part, in namespace `Langlands.GroupScheme.WeilGm`, adds general
facts about the norm-one kernel of a finite free algebra: invariance under
algebra isomorphisms, affineness, and smoothness by fpqc descent from a
splitting.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.WeilGm

section Congr

variable {A : CommRingCat.{u}} {B B' : Type u} [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A B'] [Module.Finite A B] [Module.Free A B]
  [Module.Finite A B'] [Module.Free A B']

omit [Module.Finite A B] [Module.Free A B] [Module.Finite A B'] [Module.Free A B'] in
/-- The tensor determinant norm is unchanged by an algebra isomorphism of the
first tensor factor. -/
theorem tensorNorm_congr (e : B ≃ₐ[A] B') (R : Type u) [CommRing R] [Algebra A R]
    (x : B ⊗[A] R) :
    Langlands.Algebra.tensorNorm A B' R
        (Algebra.TensorProduct.congr e AlgEquiv.refl x) =
      Langlands.Algebra.tensorNorm A B R x := by
  change Algebra.norm R (Algebra.TensorProduct.comm A B' R
      (Algebra.TensorProduct.congr e AlgEquiv.refl x)) =
    Algebra.norm R (Algebra.TensorProduct.comm A B R x)
  have h : Algebra.TensorProduct.comm A B' R (Algebra.TensorProduct.congr e AlgEquiv.refl x) =
      Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e
        (Algebra.TensorProduct.comm A B R x) := by
    induction x using TensorProduct.inductionOn with
    | tmul b r => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h]
  exact Algebra.norm_eq_of_algEquiv (R := R)
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e) _

omit [Module.Finite A B] [Module.Free A B] [Module.Finite A B'] [Module.Free A B'] in
/-- The unit norm is unchanged by an algebra isomorphism of the first factor. -/
theorem tensorNormUnits_congr (e : B ≃ₐ[A] B') (R : Type u) [CommRing R] [Algebra A R]
    (x : (B ⊗[A] R)ˣ) :
    Langlands.Algebra.tensorNormUnits A B' R (tensorUnitsEquiv e R x) =
      Langlands.Algebra.tensorNormUnits A B R x :=
  Units.ext (tensorNorm_congr e R x.val)

/-- Norm-one tensor units correspond under an algebra isomorphism of the first
factor. -/
def normOneCongrUnitsEquiv (e : B ≃ₐ[A] B') (R : Type u) [CommRing R] [Algebra A R] :
    (Langlands.Algebra.tensorNormUnits A B R).ker ≃*
      (Langlands.Algebra.tensorNormUnits A B' R).ker :=
  kernelModelEquiv _ _ (tensorUnitsEquiv e R) (MulEquiv.refl _)
    (fun x => (tensorNormUnits_congr e R x).symm)

omit [Module.Finite A B] [Module.Free A B] [Module.Finite A B'] [Module.Free A B'] in
@[simp] theorem normOneCongrUnitsEquiv_val (e : B ≃ₐ[A] B') (R : Type u) [CommRing R]
    [Algebra A R] (x : (Langlands.Algebra.tensorNormUnits A B R).ker) :
    (normOneCongrUnitsEquiv e R x).val = tensorUnitsEquiv e R x.val := rfl

/-- The first-factor transport commutes with restriction along test morphisms. -/
theorem normOneCongrUnitsEquiv_naturality (e : B ≃ₐ[A] B') {T T' : Over (Spec A)}
    (a : T' ⟶ T) (x : (Langlands.Algebra.tensorNormUnits A B ((algΓ A).obj T).unop).ker) :
    normOneCongrUnitsEquiv e _ (normOneUnitsRestrict A B a x) =
      normOneUnitsRestrict A B' a (normOneCongrUnitsEquiv e _ x) :=
  Subtype.ext (tensorUnitsEquiv_naturality e _ x.val)

/-- An `A`-algebra isomorphism `B ≃ B'` induces an isomorphism of the actual
norm-one group schemes. -/
def normOneCongrIso (e : B ≃ₐ[A] B') : normOne A B ≅ normOne A B' :=
  isoOfPointModels
    (fun T : Over (Spec A) => (Langlands.Algebra.tensorNormUnits A B' ((algΓ A).obj T).unop).ker)
    (fun a => normOneUnitsRestrict A B' a)
    (fun T => (normOnePointsEquiv A B T).trans (normOneCongrUnitsEquiv e _))
    (normOnePointsEquiv A B')
    (fun a x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, normOnePointsEquiv_naturality,
        normOneCongrUnitsEquiv_naturality])
    (fun a y => normOnePointsEquiv_naturality A B' a y)

/-- On points, `normOneCongrIso e` is the unit map of `e ⊗ id`. -/
theorem normOneCongrIso_hom_points (e : B ≃ₐ[A] B') (T : Over (Spec A))
    (x : T ⟶ (normOne A B).X) :
    normOnePointsEquiv A B' T (x ≫ (normOneCongrIso e).hom.hom.hom) =
      normOneCongrUnitsEquiv e _ (normOnePointsEquiv A B T x) :=
  isoOfPointModels_hom
    (fun T : Over (Spec A) => (Langlands.Algebra.tensorNormUnits A B' ((algΓ A).obj T).unop).ker)
    (fun a => normOneUnitsRestrict A B' a)
    (fun T => (normOnePointsEquiv A B T).trans (normOneCongrUnitsEquiv e _))
    (normOnePointsEquiv A B')
    (fun a x => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, normOnePointsEquiv_naturality,
        normOneCongrUnitsEquiv_naturality])
    (fun a y => normOnePointsEquiv_naturality A B' a y) T x

end Congr

section Coefficients

variable (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Free A B]
  {S T : Type u} [CommRing S] [Algebra A S] [CommRing T] [Algebra A T]

/-- Norm-one tensor units correspond under an isomorphism of coefficient
algebras. -/
def normOneCoeffEquiv (g : S ≃ₐ[A] T) :
    (Langlands.Algebra.tensorNormUnits A B S).ker ≃*
      (Langlands.Algebra.tensorNormUnits A B T).ker :=
  kernelModelEquiv _ _
    (Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) g).toMulEquiv)
    (Units.mapEquiv g.toMulEquiv)
    (fun x => by
      have h := Langlands.Algebra.tensorNormUnits_naturality (B := B) g.toAlgHom x
      exact h.symm)

@[simp] theorem normOneCoeffEquiv_val (g : S ≃ₐ[A] T)
    (x : (Langlands.Algebra.tensorNormUnits A B S).ker) :
    ((normOneCoeffEquiv A B g x).val : B ⊗[A] T) =
      Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[A] B) g x.val := rfl

end Coefficients

section Geometry

variable (A : CommRingCat.{u}) (B : Type u) [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Free A B]

/-- The actual norm-one kernel is affine over its base. -/
instance normOne_isAffineHom : IsAffineHom (normOne A B).X.hom := by
  have : IsAffineHom (groupScheme A B).X.hom := by
    change IsAffineHom (Spec.map _)
    infer_instance
  have : IsSeparated (Gm (Spec A)).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  have : IsClosedImmersion (kernelι (norm A B)).hom.hom.left := inferInstance
  change IsAffineHom (kernel (norm A B)).X.hom
  rw [← (kernelι (norm A B)).hom.hom.w]
  infer_instance

/-- A faithfully flat algebra gives a surjective, flat, quasi-compact map of
spectra. -/
theorem baseMap_fpqc (A' : CommRingCat.{u}) [Algebra A A'] [Module.FaithfullyFlat A A'] :
    Surjective (baseMap A A') ∧ Flat (baseMap A A') ∧ QuasiCompact (baseMap A A') := by
  have h : Flat (baseMap A A') ∧ Surjective (baseMap A A') := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap A A'))).2
    change (algebraMap A A').FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨h.2, h.1, inferInstance⟩

/-- If `B` splits as a product of copies of `A'` after a faithfully flat base
change `A → A'`, the actual norm-one kernel is smooth over `A`: its base change
is a split torus, and smoothness descends along fpqc morphisms. -/
theorem normOne_smooth_of_decomposition (A' : CommRingCat.{u}) [Algebra A A']
    [Module.FaithfullyFlat A A'] (I : Type u) [Fintype I] [DecidableEq I] [Nonempty I]
    (e : A' ⊗[A] B ≃ₐ[A'] (I → A')) :
    Smooth (normOne A B).X.hom := by
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨h1, h2, h3⟩ := baseMap_fpqc A A'
  have hK : Smooth ((GroupScheme.baseChange (baseMap A A')).obj (normOne A B)).X.hom :=
    smooth_of_over_iso ((Grp.forget _).mapIso (normOneDecompositionIso A A' B I e i₀))
      (smooth_splitTorus _)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := (normOne A B).X.hom) (g := baseMap A A') ⟨⟨h1, h2⟩, h3⟩ hK

end Geometry

end Langlands.GroupScheme.WeilGm

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme WeilGm
open scoped ValuativeRel

/-- Over finite fields, the norm-one units of `K'/K` have order
`(|K'| - 1) / (|K| - 1)`, since the unit norm map is surjective. -/
theorem card_normOneUnits_mul (K K' : Type*) [Field K] [Field K'] [Algebra K K'] [Finite K'] :
    Nat.card (Units.map (Algebra.norm K (S := K'))).ker * (Nat.card K - 1) =
      Nat.card K' - 1 := by
  have := Finite.of_injective _ (algebraMap K K').injective
  rw [← Nat.card_units K, ← Nat.card_units K']
  have h := (Units.map (Algebra.norm K (S := K'))).ker.card_mul_index
  rwa [Subgroup.index_ker,
    MonoidHom.range_eq_top_of_surjective _ (FiniteField.unitsMap_norm_surjective K K'),
    Subgroup.card_top] at h

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (B : Type u) [CommRing B] [Algebra 𝒪[F] B] [Module.Finite 𝒪[F] B] [Module.Free 𝒪[F] B]
  (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
  (eF : F ⊗[𝒪[F]] B ≃ₐ[F] E)
  (hB : Smooth (normOne (CommRingCat.of 𝒪[F]) B).X.hom)

/-- The norm-one kernel `R¹_{B/𝒪[F]} G_m` as an integral model of the
norm-one torus `R¹_{E/F} G_m`, for a finite free `𝒪[F]`-algebra `B` with
`F ⊗ B ≃ E` and smooth norm-one kernel. -/
def normOneModel : IntegralModel 𝒪[F] F (normOne (CommRingCat.of F) E) :=
  haveI := hB
  { group := normOne (CommRingCat.of 𝒪[F]) B
    genericIso := normOneAlgebraBaseChangeIso (CommRingCat.of 𝒪[F]) (CommRingCat.of F) B ≪≫
      normOneCongrIso eF }

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The norm-one model is smooth. -/
theorem normOneModel_isSmooth : (normOneModel F B E eF hB).IsSmooth := hB

variable (k' : Type u) [Field k'] [Algebra 𝓀[F] k'] (eκ : 𝓀[F] ⊗[𝒪[F]] B ≃ₐ[𝓀[F]] k')

/-- The special fibre of the norm-one model is the norm-one torus of the
residue extension `k' / 𝓀[F]`. -/
def normOneSpecialFibreIso [FiniteDimensional 𝓀[F] k'] :
    (normOneModel F B E eF hB).specialFibre ≅ normOne (CommRingCat.of 𝓀[F]) k' :=
  normOneAlgebraBaseChangeIso (CommRingCat.of 𝒪[F]) (CommRingCat.of 𝓀[F]) B ≪≫
    normOneCongrIso eκ

include eκ in
/-- The special fibre of the norm-one model is connected reductive: it is the
norm-one torus of the separable residue extension `k' / 𝓀[F]`. -/
theorem isConnectedReductive_normOneSpecialFibre :
    IsConnectedReductive (normOneModel F B E eF hB).specialFibre := by
  have : FiniteDimensional 𝓀[F] k' := Module.Finite.equiv eκ.toLinearEquiv
  exact IsConnectedReductive.of_iso (normOneSpecialFibreIso F B E eF hB k' eκ)
    (normOne_isTorus_of_finite_separable 𝓀[F] k').isConnectedReductive_of_fieldSplitting

variable [Algebra.IsSeparable F E]

/-- The norm-one model as relative-component model data whose full and neutral
models are both this model. -/
def normOneModelData :
    RelativeComponentModelData 𝒪[F] F (normOne (CommRingCat.of F) E) :=
  (normOneModel F B E eF hB).relativeComponentData_of_reductive_localField
    (normOne_isTorus_of_finite_separable F E).isConnectedReductive_of_fieldSplitting
    (isConnectedReductive_normOneSpecialFibre F B E eF hB k' eκ)

/-- The neutral model is the norm-one model. -/
theorem normOneModelData_neutral :
    (normOneModelData F B E eF hB k' eκ).neutral = normOneModel F B E eF hB := rfl

/-- The special-fibre quotient data of the norm-one model: the identity
quotient. -/
def normOneQuotientData : SpecialFibreQuotientData (normOneModelData F B E eF hB k' eκ) :=
  SpecialFibreQuotientData.identityQuotient _

/-- The identity quotient of the norm-one model is a reductive quotient. -/
theorem normOneQuotientData_isReductiveQuotient :
    (normOneQuotientData F B E eF hB k' eκ).IsReductiveQuotient :=
  SpecialFibreQuotientData.identityQuotient_isReductiveQuotient _
    (isConnectedReductive_normOneSpecialFibre F B E eF hB k' eκ)

/-- Global sections of `Spec 𝓀[F]`, as an `𝒪[F]`-algebra through the residue
map, are the residue field. -/
def residueSectionsEquiv :
    ((algΓ (CommRingCat.of 𝒪[F])).obj
      ((Over.map (IntegralModel.residueBaseMap 𝒪[F])).obj (Over.mk (𝟙 _)))).unop
        ≃ₐ[CommRingCat.of 𝒪[F]] 𝓀[F] :=
  { (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).commRingCatIsoToRingEquiv with
    commutes' := fun r => by
      change (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).hom
          ((𝟙 _ ≫ IntegralModel.residueBaseMap 𝒪[F]).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).inv r)) =
        IsLocalRing.residue 𝒪[F] r
      rw [Category.id_comp]
      change ((IntegralModel.residueBaseMap 𝒪[F]).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of 𝓀[F])).hom)
            ((Scheme.ΓSpecIso (CommRingCat.of 𝒪[F])).inv r) = _
      rw [IntegralModel.residueBaseMap, Scheme.ΓSpecIso_naturality]
      simp }

/-- Norm-one units of `B ⊗ 𝓀[F]` are the norm-one units of the residue
extension `k'`. -/
def residueNormOneEquiv :
    (Langlands.Algebra.tensorNormUnits (CommRingCat.of 𝒪[F]) B 𝓀[F]).ker ≃*
      (Units.map (Algebra.norm 𝓀[F] (S := k'))).ker :=
  WeilGm.kernelModelEquiv _ _
    (Units.mapEquiv ((Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) B 𝓀[F]).toMulEquiv.trans
      eκ.toMulEquiv))
    (MulEquiv.refl _)
    (fun x => Units.ext (by
      change Langlands.Algebra.tensorNorm (CommRingCat.of 𝒪[F]) B 𝓀[F] x.val =
        Algebra.norm 𝓀[F] (eκ (Algebra.TensorProduct.comm (CommRingCat.of 𝒪[F]) B 𝓀[F] x.val))
      rw [Algebra.norm_eq_of_algEquiv]
      rfl))

/-- The residue-field points of the special fibre of the norm-one model are
the norm-one units of the residue extension `k' / 𝓀[F]`. -/
def normOneSpecialFibrePointsEquiv :
    rationalPoints (normOneModelData F B E eF hB k' eκ).neutral.specialFibre ≃*
      (Units.map (Algebra.norm 𝓀[F] (S := k'))).ker :=
  (((GroupScheme.baseChangePointsEquiv (IntegralModel.residueBaseMap 𝒪[F])
      (normOne (CommRingCat.of 𝒪[F]) B) (Over.mk (𝟙 _))).trans
    (normOnePointsEquiv (CommRingCat.of 𝒪[F]) B _)).trans
    (normOneCoeffEquiv (CommRingCat.of 𝒪[F]) B (residueSectionsEquiv F))).trans
    (residueNormOneEquiv F B k' eκ)

/-- The index of `G(F)^{0+}` in `G^0(𝒪)` is the number of norm-one units of
the residue extension. -/
theorem normOne_index_positivePoints_subgroupOf :
    ((normOneQuotientData F B E eF hB k' eκ).positivePoints.subgroupOf
      (normOneModelData F B E eF hB k' eκ).neutral.integralPoints).index =
        Nat.card (Units.map (Algebra.norm 𝓀[F] (S := k'))).ker := by
  obtain ⟨hrad, hQ, -⟩ := normOneQuotientData_isReductiveQuotient F B E eF hB k' eκ
  rw [SpecialFibreQuotientData.localField_index_positivePoints_subgroupOf _ hrad hQ]
  change Nat.card (rationalPoints (normOneModelData F B E eF hB k' eκ).neutral.specialFibre) = _
  exact Nat.card_congr (normOneSpecialFibrePointsEquiv F B E eF hB k' eκ).toEquiv

/-- The index of `G(F)^{0+}` in `G^0(𝒪)` times `q - 1` is `q ^ n - 1`, where
`q` is the order of the residue field and `n = [k' : 𝓀[F]]`. -/
theorem normOne_index_positivePoints_subgroupOf_mul :
    ((normOneQuotientData F B E eF hB k' eκ).positivePoints.subgroupOf
      (normOneModelData F B E eF hB k' eκ).neutral.integralPoints).index *
        (Nat.card 𝓀[F] - 1) =
      Nat.card 𝓀[F] ^ Module.finrank 𝓀[F] k' - 1 := by
  have : FiniteDimensional 𝓀[F] k' := Module.Finite.equiv eκ.toLinearEquiv
  have : Finite k' := Module.finite_of_finite 𝓀[F]
  rw [normOne_index_positivePoints_subgroupOf, card_normOneUnits_mul,
    Module.natCard_eq_pow_finrank (K := 𝓀[F])]

/-- For a quadratic residue extension, the index of `G(F)^{0+}` in `G^0(𝒪)`
is `q + 1`. -/
theorem normOne_index_positivePoints_subgroupOf_of_finrank_eq_two
    (hk' : Module.finrank 𝓀[F] k' = 2) :
    ((normOneQuotientData F B E eF hB k' eκ).positivePoints.subgroupOf
      (normOneModelData F B E eF hB k' eκ).neutral.integralPoints).index =
        Nat.card 𝓀[F] + 1 := by
  have h := normOne_index_positivePoints_subgroupOf_mul F B E eF hB k' eκ
  rw [hk'] at h
  have hq : 1 < Nat.card 𝓀[F] := Finite.one_lt_card
  have h2 : 1 ≤ Nat.card 𝓀[F] ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hsq : Nat.card 𝓀[F] ^ 2 - 1 = (Nat.card 𝓀[F] + 1) * (Nat.card 𝓀[F] - 1) := by
    zify [hq.le, h2]
    ring
  rw [hsq] at h
  exact Nat.eq_of_mul_eq_mul_right (by omega) h

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The generic fibre `R¹_{E/F} G_m` of the norm-one model is anisotropic. -/
theorem normOne_isAnisotropic : IsAnisotropic (normOne (CommRingCat.of F) E) :=
  normOneAnisotropy F E ‹_›

/-- The radical points of the identity quotient of the norm-one model are
trivial. -/
theorem normOneQuotientData_radicalPoints :
    (normOneQuotientData F B E eF hB k' eκ).radicalPoints = ⊥ :=
  SpecialFibreQuotientData.identityQuotient_radicalPoints _

/-- `G(F)^{0+}` for the norm-one model is the congruence subgroup: the image of
the integral sections with trivial reduction. -/
theorem normOneQuotientData_positivePoints :
    (normOneQuotientData F B E eF hB k' eκ).positivePoints =
      (normOneModel F B E eF hB).congruenceSubgroup :=
  SpecialFibreQuotientData.identityQuotient_positivePoints _

end Langlands.BruhatTits.IntegralModels
