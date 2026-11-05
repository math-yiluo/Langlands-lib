import Langlands.GroupScheme.Descent.ComponentCoverLifts
import Langlands.GroupScheme.SimplyConnected.BaseIsoTransport

/-! # Compatibility of cover factorizations on field components -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

variable {K : Type u} [Field K]
variable {B : Scheme.{u}} {p : Spec (CommRingCat.of K) ⟶ B}
variable {C G H : GroupScheme (Spec (CommRingCat.of K))}
variable {π : C ⟶ G} {q : H ⟶ G} {a : C ⟶ H}

/-- Field-component uniqueness forces a factorization to respect descent data. -/
theorem Compatible.of_factorization_onFieldComponents
    {D : Datum p C} {E : Datum p G} {F : Datum p H}
    (hπ : Compatible D E π) (hq : Compatible F E q)
    (hUP : HasCentralCoverUniversalProperty π)
    (hH : IsSemisimple H) (hcentral : IsCentralIsogeny q)
    (ha : a ≫ q = π)
    {I : Type} [Finite I] {L : I → Type u} [∀ i, Field (L i)]
    (r : ∀ i, Spec (CommRingCat.of (L i)) ⟶ Overlap p)
    [IsIso (Limits.Sigma.desc r)]
    [∀ i, IsIso (r i ≫ fst p)] [∀ i, IsIso (r i ≫ snd p)] :
    Compatible D F a := by
  apply FiniteComponents.pullHom_ext r
  intro i
  let f := r i ≫ fst p
  let g := r i ≫ snd p
  let e := pullIso (r i) rfl rfl E.overlap
  have hπ' :
      (baseChange f).map π ≫ e.hom =
        (pullIso (r i) rfl rfl D.overlap).hom ≫ (baseChange g).map π := by
    have h := congrArg (pullHom (r i) rfl rfl) hπ
    simpa only [f, g, e, pullHom_comp (r i) rfl rfl rfl,
      pullHom_map, pullIso_hom] using h
  have hq' :
      (baseChange f).map q ≫ e.hom =
        (pullIso (r i) rfl rfl F.overlap).hom ≫ (baseChange g).map q := by
    have h := congrArg (pullHom (r i) rfl rfl) hq
    simpa only [f, g, e, pullHom_comp (r i) rfl rfl rfl,
      pullHom_map, pullIso_hom] using h
  have haf : (baseChange f).map a ≫ (baseChange f).map q =
      (baseChange f).map π := by rw [← Functor.map_comp, ha]
  have hag : (baseChange g).map a ≫ (baseChange g).map q =
      (baseChange g).map π := by rw [← Functor.map_comp, ha]
  obtain ⟨t, _ht, hu⟩ :=
    ((hUP.baseChange_of_isIso f).comp_iso e) _ ((baseChange g).map q)
      (hH.baseChange_of_isIso g) (hcentral.baseChange g)
  rw [pullHom_comp (r i) rfl rfl rfl, pullHom_comp (r i) rfl rfl rfl,
    pullHom_map, pullHom_map]
  apply Eq.trans (b := t)
  · apply hu
    change ((baseChange f).map a ≫
      (pullIso (r i) rfl rfl F.overlap).hom) ≫ (baseChange g).map q = _
    rw [Category.assoc, ← hq', ← Category.assoc, haf]
  · symm
    apply hu
    change ((pullIso (r i) rfl rfl D.overlap).hom ≫
      (baseChange g).map a) ≫ (baseChange g).map q = _
    rw [Category.assoc, hag, ← hπ']

end Langlands.GroupScheme.Descent
