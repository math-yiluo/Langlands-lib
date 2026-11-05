import Langlands.GroupScheme.IntegralModel.ArithmeticHomSpreading
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Closed extensions over enlarged finite S-integer rings -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Global Langlands.GroupScheme.Descent
open scoped NumberField CategoryTheory.MonObj

namespace Langlands.GroupScheme.IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G H : GroupScheme (Spec (CommRingCat.of K))}

/-- The generic pullback of an extending model homomorphism is closed whenever
the supplied generic homomorphism is closed. -/
theorem Hom.isClosedImmersion_generic {M : IntegralModel R K G}
    {N : IntegralModel R K H} {f : G ⟶ H} (φ : M.Hom N f)
    [IsClosedImmersion f.hom.hom.left] :
    IsClosedImmersion ((GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom).hom.hom.left := by
  have hg : (GroupScheme.baseChange (Spec.algebraMap R K)).map φ.hom =
      M.genericIso.hom ≫ f ≫ N.genericIso.inv := by
    apply (cancel_mono N.genericIso.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using φ.generic_comm
  rw [hg]
  change IsClosedImmersion (M.genericIso.hom.hom.hom.left ≫
    (f.hom.hom.left ≫ N.genericIso.inv.hom.hom.left))
  infer_instance

namespace ArithmeticSpreading

variable (F : Type u) [Field F] [NumberField F]

/-- The same model homomorphism after a canonical finite arithmetic enlargement. -/
def enlargeHom {S T : Finset (FinitePlace F)}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G}
    {N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H}
    {f : G ⟶ H} (φ : M.Hom N f) (hST : S ⊆ T) :
    (enlargeModel F M hST).Hom (enlargeModel F N hST) f :=
  φ.baseChange (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F hST))) (integerInclusion_generic F hST)

/-- An actual extension of a supplied closed generic homomorphism becomes
closed after a finite canonical arithmetic enlargement. -/
theorem exists_enlarged_closedHom (S : Finset (FinitePlace F))
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G}
    {N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H}
    {f : G ⟶ H} (φ : M.Hom N f) [IsClosedImmersion f.hom.hom.left] :
    ∃ (U : Finset (FinitePlace F)) (hSU : S ⊆ U),
      IsClosedImmersion (enlargeHom F φ hSU).hom.hom.hom.left := by
  let : IsClosedImmersion
      ((baseChange (Spec.algebraMap ((S : Set (FinitePlace F)).integer F) F)).map
        φ.hom).hom.hom.left := φ.isClosedImmersion_generic
  obtain ⟨C, hC, hc⟩ :=
    Descent.FiniteCoefficient.exists_fg_closed_baseChange (K := F) φ.hom
  obtain ⟨U, hSU, hCU⟩ := exists_integer_contains_fg_over F S C hC
  let A : Type u := (U : Set (FinitePlace F)).integer F
  let i : CommRingCat.of C ⟶ CommRingCat.of A := CommRingCat.ofHom
    { toFun := fun x => ⟨x.val, hCU x.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let b := Spec.algebraMap ((S : Set (FinitePlace F)).integer F) C
  let a := Spec.map i
  let c := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap F hSU))
  have hac : a ≫ b = c := by
    dsimp [a, b, c, i, numberFieldSIntegersMap, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let E₁ := pullbackComparison b a c hac M.group
  let E₂ := pullbackComparison b a c hac N.group
  let t := (baseChange a).map ((baseChange b).map φ.hom)
  have ht : IsClosedImmersion t.hom.hom.left :=
    IsClosedSubgroup.baseChange a hc
  have heq : (baseChange c).map φ.hom = E₁.inv ≫ t ≫ E₂.hom := by
    change (baseChange c).map φ.hom =
      E₁.inv ≫ (baseChange a).map ((baseChange b).map φ.hom) ≫
        (pullbackComparison b a c hac N.group).hom
    rw [pullbackComparison_naturality]
    simp [E₁]
  refine ⟨U, hSU, ?_⟩
  change IsClosedImmersion ((baseChange c).map φ.hom).hom.hom.left
  rw [heq]
  change IsClosedImmersion (E₁.inv.hom.hom.left ≫
    (t.hom.hom.left ≫ E₂.hom.hom.hom.left))
  let : IsClosedImmersion t.hom.hom.left := ht
  infer_instance

/-- A finite arithmetic enlargement on which the prescribed extending
homomorphism itself is closed. -/
structure EnlargedClosedHomData {S : Finset (FinitePlace F)}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G}
    {N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H}
    {f : G ⟶ H} (φ : M.Hom N f) where
  places : Finset (FinitePlace F)
  contains : S ⊆ places
  closed : IsClosedImmersion (enlargeHom F φ contains).hom.hom.hom.left

/-- Choose a finite enlargement where the same pulled-back model
homomorphism is closed. -/
def enlargedClosedHomData {S : Finset (FinitePlace F)}
    {G H : GroupScheme (Spec (CommRingCat.of F))}
    {M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G}
    {N : IntegralModel ((S : Set (FinitePlace F)).integer F) F H}
    {f : G ⟶ H} (φ : M.Hom N f) [IsClosedImmersion f.hom.hom.left] :
    EnlargedClosedHomData F φ :=
  let h := exists_enlarged_closedHom F S φ
  { places := Classical.choose h
    contains := Classical.choose (Classical.choose_spec h)
    closed := Classical.choose_spec (Classical.choose_spec h) }

end ArithmeticSpreading
end Langlands.GroupScheme.IntegralModel
