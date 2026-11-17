import Langlands.GroupScheme.Reductive.AffineSplitIsogenyWeylConjugation
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyTargetWordLaws
import Langlands.GroupScheme.Reductive.LocalSplitTargetNegSimple

/-! # Actual powered cell relations over local coefficient rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I J : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

/-- Genuine normalized simple data satisfy the all-test rank-one laws. -/
theorem IsNormalSimpleData.rankOneLaws_of_closed
    (hd : IsNormalSimpleData i P b W u) (hi : IsClosedSubgroup i)
    (a : J) (ha : a ∈ b.support) :
    RankOneLaws i (P.coroot a) (u a) (u (P.reflectionPerm a a)) := by
  apply localSplitRootPairLaws R G hd.reductive I i hi hd.maximal J P hd.rootDatum a
    _ _ (hd.param a ha).1
  · simpa only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      using (hd.param a ha).2
  · exact hd.weyl a ha

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {I I' J J' : Type u} [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
  (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H}
  {b : P.Base} {b' : Q.Base}
  (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support)
  (W : ∀ α, SimpleWord P b α) (u' : J' → (Ga R ⟶ H))
  (hd : IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u')

include hd

omit [DecidableEq I] in
/-- The actual powered opposite pairs have the source coroot and source character
identities needed for negative-simple cell transfer. -/
theorem targetNegSimpleLaws_powered
    (hi' : IsClosedSubgroup i')
    (hPpair : ∀ m n, P.toLinearMap m n = ∑ j, m j * n j) :
    TargetNegSimpleLaws (torusMap _ f ≫ i') P b (poweredRootFamily f hchar u') := by
  constructor
  · intro a ha
    exact rankOneLaws_poweredRootFamily f hPpair
      (hd.rootDatum.pairing (IsLocalRing.ResidueField R)) hchar i' u' a
      (hd.rankOneLaws_of_closed hi' _ (hb a ha))
  · intro a ha
    have hp : IsRootParametrization i'
        (Q.root (f.indexEquiv.symm (P.reflectionPerm a a)))
        (u' (f.indexEquiv.symm (P.reflectionPerm a a))) := by
      simpa only [f.indexEquiv_symm_reflectionPerm] using
        (hd.param _ (hb a ha)).2
    exact hasRootConjugationFormula_rootMap f hchar (P.reflectionPerm a a) _ hp

/-- Every root-translation relation transfers from the genuine source cell to the
actual powered target cell. Only the source cell is required to be open. -/
theorem rootRelations_poweredWeylFamily
    {u : J → (Ga R ⟶ G)} (hdG : IsNormalSimpleData i P b W u)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) :
    RootRelations
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap (torusMap _ f ≫ i') (weylFamily P W (poweredRootFamily f hchar u'))
        (fun k => (neg k : J)) (fun k => (pos k : J)))
      (weylFamily P W u) (weylFamily P W (poweredRootFamily f hchar u')) := by
  classical
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum
    b _ hdG.isRootParametrization neg pos
  have hU := weylConjugationRelations_powered f hchar hb W u' hd hdG hi hi' hpos
  have hT := targetWordRelations_powered f hchar hi' hb W u' hd
  have hR := targetNegSimpleLaws_powered f hchar hb W u' hd hi'
    (hdG.rootDatum.pairing (IsLocalRing.ResidueField R))
  have hC := TargetWordProofs.commutatorRelations hdG hT hU pos hmono
  have hL := positiveLawRelations_of_commutatorRelations hdG.reductive hdG.maximal
    hdG.rootDatum W hdG.words.1 (fun a ha => (hdG.param a ha).1) hdG.weyl
    neg pos hmono hC
  have hS := simpleRootRelations_of_positiveLawRelations (i' := torusMap _ f ≫ i')
    hdG.reductive hdG.maximal hdG.rootDatum W (fun a ha => (hdG.param a ha).1)
    hdG.weyl neg pos hL
  have hBG a (ha : a ∈ b.support) : RankOneBruhat i P u a := by
    intro B _ s x y d hd
    exact (hdG.rankOneLaws_of_closed hi a ha).2.2.2 (Over.mk s) x y d hd
  have hN := localSplitTargetNegSimple R I J P G H i (torusMap _ f ≫ i') b W u
    (poweredRootFamily f hchar u') hdG hT hU hR hBG m n neg pos hmono
  exact rootRelations_weylFamily (hasCellFactors_cellMap hdG.reductive) W hS hN

/-- All multiplication relations of the source cell hold in the actual powered target
cell, from the original characteristic condition and genuine normalized data. -/
theorem cellCompatible_poweredWeylFamily
    {u : J → (Ga R ⟶ G)} (hdG : IsNormalSimpleData i P b W u)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hpos : ∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) :
    CellGluing.CellCompatible
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap (torusMap _ f ≫ i') (weylFamily P W (poweredRootFamily f hchar u'))
        (fun k => (neg k : J)) (fun k => (pos k : J))) := by
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have := LocalSplitBigCell.isOpenImmersion_cellMap hdG.reductive hdG.maximal hdG.rootDatum
    b _ hdG.isRootParametrization neg pos
  have : Mono (cellMap i (weylFamily P W u) (fun k => (neg k : J))
      (fun k => (pos k : J))) := Over.mono_of_mono_left _
  have hE : TorusEquivariant (torusMap _ f ≫ i') (fun a => P.root a)
      (weylFamily P W (poweredRootFamily f hchar u')) := by
    intro a Z t x
    exact hasRootConjugationFormula_poweredWeylFamily f hchar hb W u' hd a Z t x
  exact cellCompatible_of_generatorRelations hdG.reductive
    (torusRelations_of_equivariant
      (fun a Z t x => (hdG.isRootParametrization a).equivariant Z t x) hE)
    (rootRelations_poweredWeylFamily f hchar hb W u' hd hdG hi hi' hpos neg pos hmono)

end Langlands.GroupScheme.AffineRootDatumIsogeny

namespace Langlands.GroupScheme

open LocalSplitCell AffineRootDatumIsogeny

/-- Full multiplication compatibility of the actual powered cell over a local ring. -/
def PoweredLocalCellCompatibilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I I' J J' : Type u) [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
    [Finite J] [Finite J']
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    [P.IsReduced] [Q.IsReduced] (p : ℕ)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hchar : ∀ j', f.rootFactor j' ≠ 1 → (p : R) = 0)
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H),
    IsClosedSubgroup i → IsClosedSubgroup i' →
    ∀ (b : P.Base) (b' : Q.Base)
    (hb : ∀ a ∈ b.support, f.indexEquiv.symm a ∈ b'.support),
    (∀ a, b.IsPos a ↔ b'.IsPos (f.indexEquiv.symm a)) →
    ∀ (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) (u' : J' → (Ga R ⟶ H)),
    IsNormalSimpleData i P b W u →
    IsNormalSimpleData i' Q b' (targetSimpleWords f hb W) u' →
    ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
    (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
    CellGluing.CellCompatible
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap (torusMap _ f ≫ i') (weylFamily P W (poweredRootFamily f hchar u'))
        (fun k => (neg k : J)) (fun k => (pos k : J)))

/-- All generator relations have been proved before the compatibility conclusion. -/
theorem poweredLocalCellCompatibility : PoweredLocalCellCompatibilityStatement.{u} := by
  intro R _ _ I I' J J' _ _ _ _ _ _ P Q _ _ p f hchar G H _ _ i i' hi hi' b b' hb hpos
    W u u' hdG hdH m n neg pos hmono
  exact cellCompatible_poweredWeylFamily f hchar hb W u' hdH hdG hi hi' hpos neg pos hmono

end Langlands.GroupScheme
