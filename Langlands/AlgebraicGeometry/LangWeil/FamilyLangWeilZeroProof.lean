import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilZeroStatement
import Langlands.AlgebraicGeometry.RelativeDimensionLoci
import Mathlib.FieldTheory.Perfect

/-! # The zero-dimensional uniform Lang–Weil estimate -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

private theorem injective_of_geometricallyIrreducible_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyIrreducible f] [LocallyQuasiFinite f] :
    Function.Injective f := by
  intro x₁ x₂ hx
  have hi : IsIrreducible (f ⁻¹' {f x₁}) := by
    rw [← f.range_fiberι]
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (f.fiber (f x₁))).image
        _ (f.fiberι _).continuous.continuousOn
  exact (f.isDiscrete_preimage_singleton (f x₁)).subsingleton_of_isPreirreducible
    hi.isPreirreducible (by simp) (by simpa using hx.symm)

private theorem universallyInjective_of_geometricallyIrreducible_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyIrreducible f] [LocallyQuasiFinite f] :
    UniversallyInjective f := by
  constructor
  intro X' S' i₁ i₂ f' h
  have : GeometricallyIrreducible f' :=
    MorphismProperty.of_isPullback h.flip inferInstance
  have : LocallyQuasiFinite f' :=
    MorphismProperty.of_isPullback h.flip inferInstance
  exact injective_of_geometricallyIrreducible_locallyQuasiFinite f'

/-- A geometrically irreducible locally quasi-finite morphism induces a bijection
on points valued in any perfect field. -/
theorem bijective_fieldPoints_of_geometricallyIrreducible_locallyQuasiFinite
    {X S : Scheme.{u}} (f : X ⟶ S)
    [GeometricallyIrreducible f] [LocallyQuasiFinite f]
    (K : Type u) [Field K] [PerfectField K] :
    Function.Bijective (fun x : Spec (CommRingCat.of K) ⟶ X => x ≫ f) := by
  have hf : UniversallyInjective f :=
    universallyInjective_of_geometricallyIrreducible_locallyQuasiFinite f
  have hinj : ∀ (L : Type u) [Field L],
      Function.Injective (fun x : Spec (CommRingCat.of L) ⟶ X => x ≫ f) :=
    ((tfae_universallyInjective f).out 1 2).mp hf
  have hres : Function.Injective f ∧
      ∀ x, (f.residueFieldMap x).hom.IsPurelyInseparable :=
    ((tfae_universallyInjective f).out 1 3).mp hf
  refine ⟨hinj K, ?_⟩
  intro s
  obtain ⟨x, hx⟩ := f.surjective (s (IsLocalRing.closedPoint K))
  let φ : S.residueField (f x) ⟶ CommRingCat.of K :=
    (S.residueFieldCongr hx).hom ≫ S.descResidueField (Scheme.stalkClosedPointTo s)
  let : Algebra (S.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : IsPurelyInseparable (S.residueField (f x)) (X.residueField x) :=
    hres.2 x
  obtain ⟨ψ, hψ⟩ := (IsPurelyInseparable.bijective_comp_algebraMap
    (S.residueField (f x)) (X.residueField x) K).surjective φ.hom
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x, ?_⟩
  change (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x) ≫ f = s
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc]
  have hc : f.residueFieldMap x ≫ CommRingCat.ofHom ψ = φ :=
    CommRingCat.hom_ext hψ
  erw [hc]
  simp only [φ, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
  exact Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S s

/-- Every finite-field point has exactly one lift in a geometrically irreducible
family whose fibres have pure dimension zero. -/
theorem card_fieldPointLifts_eq_one_of_pureDimension_zero
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [GeometricallyIrreducible f]
    (hdim : ∀ s, SchemeFiberGeometry.HasPureDimension (f.fiber s) 0)
    (K : Type u) [Field K] [Finite K] (s : Spec (CommRingCat.of K) ⟶ S) :
    Nat.card {x : Spec (CommRingCat.of K) ⟶ X // x ≫ f = s} = 1 := by
  have : LocallyQuasiFinite f :=
    (SchemeFiberGeometry.hasPureDimensionFibers_zero_iff_locallyQuasiFinite f).mp hdim
  have hb := bijective_fieldPoints_of_geometricallyIrreducible_locallyQuasiFinite f K
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · exact ⟨fun a b => Subtype.ext (hb.injective (a.2.trans b.2.symm))⟩
  · obtain ⟨x, hx⟩ := hb.surjective s
    exact ⟨⟨x, hx⟩⟩

/-- The uniform Lang–Weil estimate in fibre dimension zero, with constant `1`. -/
theorem familyLangWeilZero : FamilyLangWeilZeroStatement.{u} := by
  intro S X f _ _ hft _ hgi hdim
  let := hft
  let := hgi
  refine ⟨1, by norm_num, ?_⟩
  intro K _ _ s
  rw [card_fieldPointLifts_eq_one_of_pureDimension_zero f hdim K s]
  simp only [Nat.cast_one, pow_zero, sub_self, abs_zero, one_mul]
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end Langlands.AlgebraicGeometry.LangWeil
