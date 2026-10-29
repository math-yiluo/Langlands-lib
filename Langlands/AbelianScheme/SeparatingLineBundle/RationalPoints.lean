import Mathlib.AlgebraicGeometry.Group.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Rational points of group schemes over algebraically closed fields

A quasi-compact connected group scheme locally of finite type over an algebraically closed
field is irreducible, and finitely many nonempty open subsets of an irreducible scheme
locally of finite type over such a field share a rational point. In particular a smooth
proper geometrically connected group scheme over such a field is irreducible.
-/

universe u

open CategoryTheory AlgebraicGeometry Topology

noncomputable section

namespace Langlands.GroupScheme.SeparatingLineBundle

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- In an irreducible scheme locally of finite type over an algebraically closed field,
finitely many nonempty open subsets contain a common rational point. -/
theorem exists_rationalPoint_mem_of_isOpen {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    {ι : Type*} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) :
    ∃ x : Spec (CommRingCat.of K) ⟶ X,
      x ≫ p = 𝟙 _ ∧ ∀ i, x (IsLocalRing.closedPoint K) ∈ U i := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have key : ∀ s : Finset ι, IsOpen (⋂ i ∈ s, U i) ∧ (⋂ i ∈ s, U i).Nonempty := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s _ ih =>
      rw [Finset.set_biInter_insert]
      exact ⟨(hU a).inter ih.1, nonempty_preirreducible_inter (hU a) ih.1 (hne a) ih.2⟩
  obtain ⟨hVo, hVne⟩ := key Finset.univ
  simp only [Finset.mem_univ, Set.iInter_true] at hVo hVne
  obtain ⟨c, hc, hcc⟩ := nonempty_inter_closedPoints hVne hVo.isLocallyClosed
  have hcc' : IsClosed {c} := hcc
  refine ⟨pointOfClosedPoint p c hcc', pointOfClosedPoint_comp p c hcc', fun i ↦ ?_⟩
  have hx := pointOfClosedPoint_apply p c hcc' (IsLocalRing.closedPoint K)
  rw [hx]
  exact Set.mem_iInter.mp hc i

/-- A chosen rational point lying in each of finitely many nonempty open subsets of an
irreducible scheme locally of finite type over an algebraically closed field. -/
def commonRationalPoint {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    {ι : Type*} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) : Spec (CommRingCat.of K) ⟶ X :=
  (exists_rationalPoint_mem_of_isOpen p U hU hne).choose

/-- The chosen common point is a section of the structure morphism. -/
theorem commonRationalPoint_comp {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    {ι : Type*} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) : commonRationalPoint p U hU hne ≫ p = 𝟙 _ :=
  (exists_rationalPoint_mem_of_isOpen p U hU hne).choose_spec.1

/-- The image of the closed point under the chosen common point lies in each open subset. -/
theorem commonRationalPoint_mem {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    {ι : Type*} [Finite ι] (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hne : ∀ i, (U i).Nonempty) (i : ι) :
    commonRationalPoint p U hU hne (IsLocalRing.closedPoint K) ∈ U i :=
  (exists_rationalPoint_mem_of_isOpen p U hU hne).choose_spec.2 i

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory CartesianMonoidalCategory MonObj in
/-- A quasi-compact connected group scheme locally of finite type over an algebraically
closed field is irreducible. Translations by rational points permute the finitely many
irreducible components, so a closed point on two components would force every closed point
onto two components; hence the components are disjoint, so each is open, and connectedness
leaves one. -/
theorem irreducibleSpace_of_grpObj (G : Over (Spec (CommRingCat.of K))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [CompactSpace G.left] [ConnectedSpace G.left] :
    IrreducibleSpace G.left := by
  have : JacobsonSpace G.left := LocallyOfFiniteType.jacobsonSpace G.hom
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsNoetherian G.left := {}
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := G.left)
  have hdisj : ∀ Z₁ ∈ irreducibleComponents G.left, ∀ Z₂ ∈ irreducibleComponents G.left,
      Z₁ ≠ Z₂ → Disjoint Z₁ Z₂ := by
    intro Z₁ h₁ Z₂ h₂ hne
    rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
    intro hZ
    obtain ⟨y, hy, hyc⟩ := nonempty_inter_closedPoints hZ
      ((isClosed_of_mem_irreducibleComponents _ h₁).inter
        (isClosed_of_mem_irreducibleComponents _ h₂)).isLocallyClosed
    have hWo : IsOpen (⋃₀ (irreducibleComponents G.left \ {Z₁}))ᶜ := by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have hWne : (⋃₀ (irreducibleComponents G.left \ {Z₁}))ᶜ.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      have := closure_sUnion_irreducibleComponents_sdiff_singleton hfin Z₁ h₁
      rw [h, closure_empty] at this
      exact h₁.1.1.ne_empty this.symm
    obtain ⟨w, hw, hwc⟩ := nonempty_inter_closedPoints hWne hWo.isLocallyClosed
    let y' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨y, hyc⟩).2
    let w' : 𝟙_ _ ⟶ G := Over.homMk _ ((pointEquivClosedPoint G.hom).symm ⟨w, hwc⟩).2
    let α := (GrpObj.mulRight w').symm ≪≫ GrpObj.mulRight y'
    have hα : w' ≫ α.hom = y' := by
      dsimp only [Iso.trans_hom, Iso.symm_hom, α]
      rw [← Category.assoc, ← Iso.eq_comp_inv]
      simp [comp_lift_assoc]
    have hα' : α.hom.left w = y := by
      simpa [w', y', pointEquivClosedPoint] using
        congr(($hα).left (IsLocalRing.closedPoint K))
    let e : G.left ≃ₜ G.left := Scheme.homeoOfIso ((Over.forget _).mapIso α)
    have he : ∀ x, e x = α.hom.left x := fun _ ↦ rfl
    have hpre : ∀ Z ∈ irreducibleComponents G.left, e ⁻¹' Z ∈ irreducibleComponents G.left :=
      fun Z hZ ↦ preimage_mem_irreducibleComponents hZ e.isOpenEmbedding
        (by rw [e.surjective.range_eq, Set.inter_univ]; exact hZ.1.1)
    have hW : ∀ Z ∈ irreducibleComponents G.left, w ∈ Z → Z = Z₁ := by
      intro Z hZ hwZ
      by_contra hne'
      exact hw (Set.mem_sUnion_of_mem hwZ ⟨hZ, hne'⟩)
    have e₁ := hW _ (hpre Z₁ h₁) (by simp only [Set.mem_preimage, he, hα']; exact hy.1)
    have e₂ := hW _ (hpre Z₂ h₂) (by simp only [Set.mem_preimage, he, hα']; exact hy.2)
    exact hne (Set.preimage_injective.mpr e.surjective (e₁.trans e₂.symm))
  obtain ⟨x⟩ := (inferInstance : Nonempty G.left)
  have hZ := irreducibleComponent_mem_irreducibleComponents x
  have hcompl : (irreducibleComponent x)ᶜ =
      ⋃₀ (irreducibleComponents G.left \ {irreducibleComponent x}) := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · intro hu
      obtain ⟨Z, hZ', huZ⟩ := Set.mem_sUnion.mp
        (sUnion_irreducibleComponents (X := G.left) ▸ Set.mem_univ u)
      exact ⟨Z, ⟨hZ', fun h ↦ hu (h ▸ huZ)⟩, huZ⟩
    · rintro ⟨Z, ⟨hZ', hne⟩, huZ⟩ hu
      exact Set.disjoint_left.mp (hdisj _ hZ' _ hZ hne) huZ hu
  have hclopen : IsClopen (irreducibleComponent x) := by
    refine ⟨isClosed_of_mem_irreducibleComponents _ hZ, ?_⟩
    rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
    exact hfin.sdiff.isClosed_biUnion fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
  have huniv := hclopen.eq_univ ⟨x, mem_irreducibleComponent⟩
  rw [irreducibleSpace_def, Set.top_eq_univ, ← huniv]
  exact hZ.1

/-- A smooth proper geometrically connected group scheme over an algebraically closed field
is irreducible. -/
theorem irreducibleSpace_of_smooth_of_isProper (G : Grp (Over (Spec (CommRingCat.of K))))
    [Smooth G.X.hom] [IsProper G.X.hom] [GeometricallyConnected G.X.hom] :
    IrreducibleSpace G.X.left := by
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : ConnectedSpace G.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := G.X.hom)
  exact irreducibleSpace_of_grpObj G.X

end Langlands.GroupScheme.SeparatingLineBundle
