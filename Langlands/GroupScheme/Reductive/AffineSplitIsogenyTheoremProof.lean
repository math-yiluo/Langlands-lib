import Langlands.GroupScheme.Reductive.AffineSplitIsogenyTheoremStatement
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyAffineCell
import Langlands.GroupScheme.Reductive.NormalizedAffineRootFamily
import Langlands.GroupScheme.Reductive.AffineSplitRootPairLaws
import Langlands.GroupScheme.Reductive.AffineTorusRestrictionIsogenyCriterion

/-! # The Isogeny Theorem for split reductive groups over an affine base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open LocalSplitCell AffineRootDatumIsogeny

section NormalData

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (hG : IsReductive G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (hi : IsClosedSubgroup i)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  (hP : IsFibrewiseRootDatumOf I G i P)

include hG hi hmax hP in
/-- Free actual root spaces give global normalized data for any supplied descending words. -/
theorem exists_normalSimpleData_of_freeRoots (b : P.Base) (W : ∀ α, SimpleWord P b α)
    (hW : IsDescendingWords P b W)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R)) :
    ∃ u : J → (Ga R ⟶ G), IsNormalSimpleData i P b W u := by
  let u := normalizedAffineRootFamily hG i hi hmax hP b hfree
  have hu α : IsRootParametrization i (P.root α) (u α) :=
    isRootParametrization_normalizedAffineRootFamily hG i hi hmax hP b hfree α
  have hn a (ha : a ∈ b.support) :
      IsWeylPoint i (rootWeylPoint P u a) (P.reflection a) :=
    isWeylPoint_normalizedAffineRootFamily hG i hi hmax hP b hfree ha
  refine ⟨u, ⟨hG, hmax, hP, fun a _ => ⟨hu a, hu (P.reflectionPerm a a)⟩,
    hn, hW, ?_⟩⟩
  intro a ha
  have hm : IsRootParametrization i (-P.root a) (u (P.reflectionPerm a a)) := by
    simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      using hu (P.reflectionPerm a a)
  exact RankOneLaws.rankOneNormal i P u a
    (rankOneLaws_of_weylNormalization_affine hG i hi hmax hP a (hu a) hm (hn a ha))

end NormalData

/-- The unchanged affine split Isogeny Theorem, for every universe and commutative ring. -/
theorem affineSplitIsogenyTheorem : AffineSplitIsogenyTheoremStatement.{u} := by
  classical
  intro R _ G H hG hH I I' _ _ i i' J J' _ _ P Q _ _
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffineHom H.X.hom := hH.isAffineHom
  intro hi hmax hP hfree hi' hmax' hQ hfree' p f hchar
  let D := f.compatibleBases
  let b : P.Base := D.target
  let b' : Q.Base := D.source
  have hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support := by
    intro a ha
    apply (D.simple_iff (f.indexEquiv.symm a)).mpr
    simpa only [Equiv.apply_symm_apply] using ha
  have hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a) := by
    intro a
    simpa only [Equiv.apply_symm_apply] using (D.isPos_iff (f.indexEquiv.symm a)).symm
  let W : ∀ α, SimpleWord P b α := descWord P b
  have hW : IsDescendingWords P b W := isDescendingWords_descWord P b
  have hW' : IsDescendingWords Q b' (targetSimpleWords f hb W) := by
    apply isDescendingWords_targetSimpleWords f
      (fun a' => (D.simple_iff a').symm) (fun a' => (D.isPos_iff a').symm) W hW
  obtain ⟨u, hdG⟩ := exists_normalSimpleData_of_freeRoots hG i hi hmax hP b W hW hfree
  obtain ⟨u', hdH⟩ := exists_normalSimpleData_of_freeRoots hH i' hi' hmax' hQ b'
    (targetSimpleWords f hb W) hW' hfree'
  let neg := (Finite.equivFin {α : J // ¬ b.IsPos α}).symm
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨pos, hmono⟩ :=
    exists_equiv_monotone (fun α : {α : J // b.IsPos α} => b.height (α : J))
  have hC := cellCompatible_poweredWeylFamily_affine f hchar hb W u' hdH hdG
    hi hi' hpos neg pos hmono
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _
    hdG.isRootParametrization neg pos
  have := hG.smooth
  have := hG.geometricallyIrreducible
  let φ : G ⟶ H := CellGluing.glueHom hC (cellUnit R I _ _)
    (cellUnit_comp_cellMap i (weylFamily P W u) (fun k => (neg k : J))
      (fun k => (pos k : J)))
  have hcell :
      cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) ≫
        φ.hom.hom =
      cellMap (torusMap _ f ≫ i') (weylFamily P W (poweredRootFamily f hchar u'))
        (fun k => (neg k : J)) (fun k => (pos k : J)) :=
    CellGluing.cell_comp_glueHom hC (cellUnit R I _ _)
      (cellUnit_comp_cellMap i (weylFamily P W u) (fun k => (neg k : J))
        (fun k => (pos k : J)))
  have htorus : i ≫ φ = torusMap _ f ≫ i' := by
    apply Grp.hom_ext
    rw [Grp.comp_hom_hom, ← RelativeDerived.torusCellSection_comp_cellMap
      (i := i) (u := weylFamily P W u) (neg := fun k => (neg k : J))
      (pos := fun k => (pos k : J)), Category.assoc, hcell]
    exact RelativeDerived.torusCellSection_comp_cellMap
  refine ⟨φ, torusMap _ f, ?_, htorus, points_torusMap _ f⟩
  exact isIsogeny_of_split_torus_restriction_of_fibrewise_root_card_eq
    i i' hP hQ hG hH hmax hmax' φ (Additive.ofMul (torusMap _ f))
    (isIsogeny_torusMap (CommRingCat.of R) f) htorus (Nat.card_congr f.indexEquiv.symm)

end Langlands.GroupScheme
