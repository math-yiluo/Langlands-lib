import Langlands.GroupScheme.Torus.CocharacterFiniteTypeDescent
import Langlands.GroupScheme.Torus.CocharacterDetection
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # Descent through arbitrary purely inseparable extensions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace Langlands.GroupScheme.CocharacterDatum

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {Z : CommGroupScheme (Spec (CommRingCat.of k))}
    {Λ : Type u} [AddCommGroup Λ]

/-- Successive coefficient extensions compose. -/
theorem coeffMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] B) (g : B →ₐ[k] C)
    (x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra A Λ)) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  have h : (AddMonoidAlgebra.mapAlgHom Λ g).comp
      (AddMonoidAlgebra.mapAlgHom Λ f) = AddMonoidAlgebra.mapAlgHom Λ (g.comp f) := by
    apply AlgHom.ext
    intro a
    ext t
    simp
  rw [coeffMap, coeffMap, ← Lie.affineMap_comp, h]

variable [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]
    {F L : Type u} [Field F] [Field L]
    [Algebra k F] [Algebra k L] [Algebra F L] [IsScalarTower k F L]

/-- The exact multiplicative point over an algebraic extension is already
represented over a finite intermediate field. -/
theorem IsMult.exists_finiteDimensional_coeffMap_eq [Algebra.IsAlgebraic F L]
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsMult x) :
    ∃ E : IntermediateField F L, FiniteDimensional F E ∧
      ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra E Λ),
        IsMult y ∧ coeffMap (E.val.restrictScalars k) y = x := by
  classical
  obtain ⟨s, hs⟩ := (finiteType_coordinateAlgebra Z.toGrp).out
  let T : Finset L := s.biUnion fun c => ((coord x).hom c).coeff.frange
  let E : IntermediateField F L := IntermediateField.adjoin F (T : Set L)
  have hE : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin fun c _ => Algebra.IsIntegral.isIntegral c
  let f : E →ₐ[k] L := E.val.restrictScalars k
  have hgen : ∀ c ∈ s, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ f).range := by
    intro c hc
    obtain ⟨y, hy⟩ := exists_mapAlgHom_eq f Subtype.val_injective ((coord x).hom c)
      fun weight => by
        by_cases h : ((coord x).hom c).coeff weight = 0
        · rw [h]
          exact zero_mem _
        · refine (AlgHom.mem_range _).mpr ⟨⟨_, IntermediateField.subset_adjoin F _ ?_⟩, rfl⟩
          exact Finset.mem_biUnion.mpr ⟨c, hc, Finsupp.mem_frange.mpr ⟨h, weight, rfl⟩⟩
    exact ⟨y, hy⟩
  have hall : ∀ c, (coord x).hom c ∈ (AddMonoidAlgebra.mapAlgHom Λ f).range := by
    intro c
    have hc : c ∈ Algebra.adjoin (CommRingCat.of k) (s : Set (coordAlgebra Z.toGrp)) := by
      rw [hs]
      trivial
    induction hc using Algebra.adjoin_induction with
    | mem c hc => exact hgen c hc
    | algebraMap r =>
      rw [AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ (r : k)
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | mul a b _ _ ha hb =>
      rw [map_mul]
      exact mul_mem ha hb
  obtain ⟨y, hy⟩ := exists_affineMap_eq _ (mapAlgHom_injective f Subtype.val_injective) x hall
  refine ⟨E, hE, y, ?_, hy⟩
  apply IsMult.of_coeff_map f Subtype.val_injective
  change IsMult (Lie.affineMap Z.toGrp _ y)
  rwa [hy]

/-- A multiplicative point descends unchanged through every purely inseparable
field extension; the extension need not have bounded exponent. -/
theorem IsMult.exists_coeffMap_eq_of_isPurelyInseparable
    [IsPurelyInseparable F L] [IsAddTorsionFree Λ]
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsMult x) :
    ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ),
      IsMult y ∧ coeffMap (IsScalarTower.toAlgHom k F L) y = x := by
  obtain ⟨E, hE, z, hz, hzx⟩ := hx.exists_finiteDimensional_coeffMap_eq (F := F)
  let := hE
  obtain ⟨p, _⟩ := ExpChar.exists k
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap k F).injective p
  obtain ⟨y, hy, hyz⟩ := hz.exists_coeffMap_eq_of_pow_mem_range p
    (IsPurelyInseparable.exponent F E)
    (fun z => IsPurelyInseparable.exponent_def' F p z)
  refine ⟨y, hy, ?_⟩
  rw [← hzx, ← hyz, coeffMap_comp]
  rfl

/-- Coefficient extension gives an actual equivalence on multiplicative points
through any purely inseparable extension. -/
def multiplicativePointsEquivOfIsPurelyInseparable
    [IsPurelyInseparable F L] [IsAddTorsionFree Λ] :
    multiplicativePoints Z F Λ ≃* multiplicativePoints Z L Λ :=
  MulEquiv.ofBijective (multiplicativeCoeffMap (Z := Z) (Λ := Λ)
    (IsScalarTower.toAlgHom k F L)) ⟨by
      intro x y h
      apply Subtype.ext
      apply affineMap_injective
        (AddMonoidAlgebra.mapAlgHom Λ (IsScalarTower.toAlgHom k F L))
        (mapAlgHom_injective _ (algebraMap F L).injective)
      exact congrArg Subtype.val h, by
      intro x
      obtain ⟨y, hy, heq⟩ := x.property.exists_coeffMap_eq_of_isPurelyInseparable (F := F)
      exact ⟨⟨y, hy⟩, Subtype.ext heq⟩⟩

/-- Character data descend with their original weight and original point
through arbitrary purely inseparable extensions. -/
theorem IsDatum.exists_coeffMap_eq_of_isPurelyInseparable
    [IsPurelyInseparable F L] [IsAddTorsionFree Λ]
    {χ : characterLattice Z} {m : Λ}
    {x : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra L Λ)} (hx : IsDatum χ m x) :
    ∃ y : Lie.AffinePoints Z.toGrp (AddMonoidAlgebra F Λ),
      IsDatum χ m y ∧ coeffMap (IsScalarTower.toAlgHom k F L) y = x := by
  obtain ⟨y, _, hy⟩ := hx.mult.exists_coeffMap_eq_of_isPurelyInseparable (F := F)
  refine ⟨y, ?_, hy⟩
  apply IsDatum.of_coeff_map (IsScalarTower.toAlgHom k F L) (algebraMap F L).injective
  rwa [hy]

end Langlands.GroupScheme.CocharacterDatum
