import Langlands.GroupScheme.Reductive.AffinePinnedComparisonDescent
import Langlands.GroupScheme.Descent.DisjointComponentHoms
import Langlands.GroupScheme.Reductive.AffinePinnedLocalPinning

/-! # Pinning preservation and comparison assembly on disjoint components -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AffinePinnedModel

variable {M N : AffinePinnedModel.{u}} {T U : Scheme.{u}}
  {f : T ⟶ M.base} {g : T ⟶ N.base}

/-- A pinning equation on a refined test gives its original equation after
projection through the actual normalized pullback maps. -/
theorem rootVectorPoint_of_pullComparison
    {A : Type u} [CommRing A] [Algebra M.ring A] [Algebra N.ring A]
    (e : Comparison f g) (q : U ⟶ T)
    (a : Spec (CommRingCat.of A) ⟶ U)
    (ha : algebraBaseMap M.ring A = a ≫ (q ≫ f))
    (hb : algebraBaseMap N.ring A = a ≫ (q ≫ g))
    (s : M.basis.support) (t : N.basis.support)
    (hv : M.rootVectorPoint (q ≫ f) A a ha s ≫
        (pullComparison e q).hom.hom.hom.left =
      N.rootVectorPoint (q ≫ g) A a hb t) :
    M.rootVectorPoint f A (a ≫ q)
        (by simpa only [Category.assoc] using ha) s ≫ e.hom.hom.hom.left =
      N.rootVectorPoint g A (a ≫ q)
        (by simpa only [Category.assoc] using hb) t := by
  have heq : (pullComparison e q).hom ≫ (baseChangeCompIso g q N.group).hom =
      (baseChangeCompIso f q M.group).hom ≫ (baseChange q).map e.hom := by
    simp [pullComparison]
  have heq' := congrArg (fun k => k.hom.hom.left) heq
  change (pullComparison e q).hom.hom.hom.left ≫
    (baseChangeCompIso g q N.group).hom.hom.hom.left =
    (baseChangeCompIso f q M.group).hom.hom.hom.left ≫
      ((baseChange q).map e.hom).hom.hom.left at heq'
  have hmap : ((baseChange q).map e.hom).hom.hom.left ≫
        pullback.fst (N.groupOver g).X.hom q =
      pullback.fst (M.groupOver f).X.hom q ≫ e.hom.hom.hom.left := by
    change pullback.lift _ _ _ ≫ _ = _
    exact pullback.lift_fst _ _ _
  have hp := congrArg
    (fun k => k ≫ (baseChangeCompIso g q N.group).hom.hom.hom.left ≫
      pullback.fst (N.groupOver g).X.hom q) hv
  simp only [Category.assoc] at hp
  rw [← Category.assoc (pullComparison e q).hom.hom.hom.left, heq',
    Category.assoc, hmap] at hp
  have hm := congrArg (fun k => k ≫ e.hom.hom.hom.left)
    (M.rootVectorPoint_pull f A q a ha s)
  simp only [Category.assoc] at hm
  exact hm.symm.trans (hp.trans (N.rootVectorPoint_pull g A q a hb t))

/-- Open covering charts detect pinning preservation on local affine tests.
The chart may depend on the test. -/
theorem PreservesLocalPinning.of_openCover
    {I : Type u} {Z : I → Scheme.{u}} (q : ∀ i, Z i ⟶ T)
    (hq : ∀ i, IsOpenImmersion (q i))
    (hcover : ∀ x : T, ∃ i, x ∈ Set.range (q i))
    {e : Comparison f g}
    (he : ∀ i, PreservesLocalPinning (pullComparison e (q i))) :
    PreservesLocalPinning e := by
  intro A _ _ _ _ a ha hb
  obtain ⟨i, hi⟩ := hcover (a (IsLocalRing.closedPoint A))
  let : IsOpenImmersion (q i) := hq i
  have hrange : Set.range a ⊆ Set.range (q i) := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map a.continuous).mem_open
      (IsOpenImmersion.isOpen_range (q i)) hi
  let b := IsOpenImmersion.lift (q i) a hrange
  have hba : b ≫ q i = a := IsOpenImmersion.lift_fac (q i) a hrange
  have hma : algebraBaseMap M.ring A = b ≫ (q i ≫ f) := by
    rw [← Category.assoc, hba]
    exact ha
  have hna : algebraBaseMap N.ring A = b ≫ (q i ≫ g) := by
    rw [← Category.assoc, hba]
    exact hb
  obtain ⟨σ, hσ⟩ := he i A b hma hna
  refine ⟨σ, fun s => ?_⟩
  have h := rootVectorPoint_of_pullComparison e (q i) b hma hna s (σ s) (hσ s)
  simpa only [hba] using h

namespace Disjoint

variable {I : Type u} {Z : I → Scheme.{u}}
    (q : ∀ i, Z i ⟶ T) [IsIso (Sigma.desc q)]

/-- Actual comparisons on disjoint components assemble with the specified
direct endpoints. -/
def comparison (d : ∀ i, Comparison (q i ≫ f) (q i ≫ g)) : Comparison f g :=
  Descent.DisjointComponents.groupIso q
    (fun i => comparisonToIterated (q i) (d i))

/-- Each normalized component restriction recovers the supplied comparison. -/
@[simp] theorem pullComparison_comparison
    (d : ∀ i, Comparison (q i ≫ f) (q i ≫ g)) (i : I) :
    pullComparison (comparison q d) (q i) = d i := by
  unfold pullComparison comparison
  rw [Descent.DisjointComponents.map_groupIso]
  apply Iso.ext
  simp [comparisonToIterated]

/-- Torus-square preservation is detected on an arbitrary disjoint
decomposition, with no global constant relabelling premise. -/
theorem preservesTorus_of_components {e : Comparison f g}
    (he : ∀ i, PreservesTorus (pullComparison e (q i))) :
    PreservesTorus e := by
  choose τ hτ using he
  let σ i := splitTorus.baseChangeIso (q i) M.coordinates ≪≫ τ i ≪≫
    (splitTorus.baseChangeIso (q i) N.coordinates).symm
  let ρ := Descent.DisjointComponents.groupIso q σ
  refine ⟨ρ, ?_⟩
  apply Descent.DisjointComponents.groupHom_ext q
  intro i
  have ht := hτ i
  have hσ : (baseChange (q i)).map (M.inclusionOver f) ≫
        (baseChange (q i)).map e.hom =
      (σ i).hom ≫ (baseChange (q i)).map (N.inclusionOver g) := by
    apply (cancel_epi (splitTorus.baseChangeIso (q i) M.coordinates).inv).mp
    apply (cancel_mono (baseChangeCompIso g (q i) N.group).inv).mp
    rw [← inclusionOver_pull M f (q i), ← inclusionOver_pull N g (q i)] at ht
    simpa only [σ, pullComparison, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, BasedBorelTransport.baseChangeInclusion,
      Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using ht
  simpa only [Functor.map_comp, ← Functor.mapIso_hom, ρ,
    Descent.DisjointComponents.map_groupIso] using hσ

/-- Exact canonical-cocharacter preservation is detected on all disjoint
components. -/
theorem preservesCocharacter_of_components {e : Comparison f g}
    (he : ∀ i, PreservesCocharacter (pullComparison e (q i))) :
    PreservesCocharacter e := by
  apply Descent.DisjointComponents.groupHom_ext q
  intro i
  apply (cancel_epi (Gm.baseChangeIso (q i)).inv).mp
  change Dynamic.baseChangeCocharacter (q i) (M.cocharacterOver f ≫ e.hom) =
    Dynamic.baseChangeCocharacter (q i) (N.cocharacterOver g)
  apply (cancel_mono (baseChangeCompIso g (q i) N.group).inv).mp
  have h := he i
  change M.cocharacterOver (q i ≫ f) ≫ (pullComparison e (q i)).hom =
    N.cocharacterOver (q i ≫ g) at h
  rw [← cocharacterOver_pull M f (q i), ← cocharacterOver_pull N g (q i)] at h
  simpa only [Dynamic.baseChangeCocharacter_comp_hom, pullComparison,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc] using h

/-- Concrete local pinning is detected on arbitrary disjoint components. -/
theorem isLocallyPinned_of_components {e : Comparison f g}
    (he : ∀ i, IsLocallyPinned (pullComparison e (q i))) :
    IsLocallyPinned e :=
  ⟨preservesTorus_of_components q (fun i => (he i).1),
    preservesCocharacter_of_components q (fun i => (he i).2.1),
    PreservesLocalPinning.of_openCover q
      (fun i => Descent.DisjointComponents.component_openImmersion q i)
      (fun x => by
        obtain ⟨i, y, hy⟩ := Descent.DisjointComponents.component_covers q x
        exact ⟨i, y, hy⟩)
      (fun i => (he i).2.2)⟩

/-- Assembled component comparisons retain concrete local pinning. -/
theorem comparison_isLocallyPinned
    (d : ∀ i, Comparison (q i ≫ f) (q i ≫ g))
    (hd : ∀ i, IsLocallyPinned (d i)) : IsLocallyPinned (comparison q d) :=
  isLocallyPinned_of_components q (fun i => by
    simpa only [pullComparison_comparison] using hd i)

end Disjoint

end Langlands.GroupScheme.AffinePinnedModel
