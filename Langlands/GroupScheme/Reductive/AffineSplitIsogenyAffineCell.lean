import Langlands.GroupScheme.Reductive.AffineSplitIsogenyCellRelations
import Langlands.GroupScheme.Reductive.AffineSplitIsogenyBaseChange
import Langlands.GroupScheme.Reductive.AffineSplitWeylRelations
import Langlands.GroupScheme.Reductive.LocalSplitLocalAlgebraCellIsomorphism

/-! # Powered cell compatibility over arbitrary affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

open LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
  {v : J → (Ga R ⟶ G)} {w : J → (Ga R ⟶ H)}

/-- Scalar-extension compatibility on local coefficient rings implies compatibility
over the original arbitrary ring, by retaining all cell coordinates. -/
theorem cellCompatible_of_localBaseChange [IsAffine H.X.left]
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (hC : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A],
      CellGluing.CellCompatible
        (cellMap (splitTorus.baseChangeHom (K := A) G I i)
          (fun a => baseChangeRoot A (v a)) neg pos)
        (cellMap (splitTorus.baseChangeHom (K := A) H I i')
          (fun a => baseChangeRoot A (w a)) neg pos)) :
    CellGluing.CellCompatible (cellMap i v neg pos) (cellMap i' w neg pos) := by
  apply CellGluing.cellCompatible_of_localRingPoints
  intro A _ _ s x y c hxy
  let : Algebra R A := (Spec.preimage s).hom.toAlgebra
  have hs : 𝟙 _ ≫ algebraBaseMap R A = s :=
    (Category.id_comp _).trans (Spec.map_preimage s)
  let Z : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  have hZ : (Over.map (algebraBaseMap R A)).obj Z = Over.mk s := by
    change Over.mk (𝟙 _ ≫ algebraBaseMap R A) = Over.mk s
    rw [hs]
  let x0 := eqToHom hZ ≫ x
  let y0 := eqToHom hZ ≫ y
  let c0 := eqToHom hZ ≫ c
  have hxy0 : (x0 ≫ cellMap i v neg pos) * (y0 ≫ cellMap i v neg pos) =
      c0 ≫ cellMap i v neg pos := by
    simpa only [x0, y0, c0, MonObj.comp_mul, Category.assoc] using
      congrArg (fun q => eqToHom hZ ≫ q) hxy
  have hxyA :
      (liftCellPoint A Z x0 ≫ cellMap (splitTorus.baseChangeHom (K := A) G I i)
        (fun a => baseChangeRoot A (v a)) neg pos) *
      (liftCellPoint A Z y0 ≫ cellMap (splitTorus.baseChangeHom (K := A) G I i)
        (fun a => baseChangeRoot A (v a)) neg pos) =
      liftCellPoint A Z c0 ≫ cellMap (splitTorus.baseChangeHom (K := A) G I i)
        (fun a => baseChangeRoot A (v a)) neg pos := by
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
    rw [map_mul, baseChangePointsEquiv_cellMap_liftCellPoint,
      baseChangePointsEquiv_cellMap_liftCellPoint,
      baseChangePointsEquiv_cellMap_liftCellPoint]
    exact hxy0
  have h := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) H Z)
    (hC A Z (liftCellPoint A Z x0) (liftCellPoint A Z y0) (liftCellPoint A Z c0) hxyA)
  rw [map_mul, baseChangePointsEquiv_cellMap_liftCellPoint,
    baseChangePointsEquiv_cellMap_liftCellPoint,
    baseChangePointsEquiv_cellMap_liftCellPoint] at h
  apply (cancel_epi (eqToHom hZ)).mp
  simpa only [x0, y0, c0, MonObj.comp_mul, Category.assoc] using h

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R]
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

/-- The actual powered cell is compatible over every commutative coefficient ring. -/
theorem cellCompatible_poweredWeylFamily_affine
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
  apply cellCompatible_of_localBaseChange (fun k => (neg k : J)) (fun k => (pos k : J))
  intro A _ _ _
  let GA := (GroupScheme.baseChange (algebraBaseMap R A)).obj G
  let HA := (GroupScheme.baseChange (algebraBaseMap R A)).obj H
  let : IsAffineHom GA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let : IsAffineHom HA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  have hcharA : ∀ j', f.rootFactor j' ≠ 1 → (p : A) = 0 :=
    rootFactor_characteristic_baseChange f hchar
  have hiA : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi.baseChange (algebraBaseMap R A))
  have hiA' : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) H I' i') :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I').symm
      (hi'.baseChange (algebraBaseMap R A))
  have hRaw :
      (fun a => baseChangeRoot A (poweredRootFamily f hchar u' a)) =
        poweredRootFamily f hcharA (fun a' => baseChangeRoot A (u' a')) := by
    funext a
    exact baseChangeRoot_rootMap f hchar hcharA _ _
  have hSource :
      (fun a => baseChangeRoot A (weylFamily P W u a)) =
        weylFamily P W (fun a => baseChangeRoot A (u a)) :=
    funext (baseChangeRoot_weylFamily A P W u)
  have hTarget :
      (fun a => baseChangeRoot A (weylFamily P W (poweredRootFamily f hchar u') a)) =
        weylFamily P W (poweredRootFamily f hcharA (fun a' => baseChangeRoot A (u' a'))) := by
    funext a
    rw [baseChangeRoot_weylFamily, hRaw]
  rw [hSource, hTarget, baseChangeHom_torusMap]
  exact cellCompatible_poweredWeylFamily f hcharA hb W (fun a' => baseChangeRoot A (u' a'))
    (hd.baseChange A) (hdG.baseChange A) hiA hiA' hpos neg pos hmono

end Langlands.GroupScheme.AffineRootDatumIsogeny

namespace Langlands.GroupScheme

open LocalSplitCell AffineRootDatumIsogeny

/-- Full multiplication compatibility of the actual powered cell over an arbitrary commutative ring. -/
def PoweredAffineCellCompatibilityStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
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
theorem poweredAffineCellCompatibility : PoweredAffineCellCompatibilityStatement.{u} := by
  intro R _ I I' J J' _ _ _ _ _ _ P Q _ _ p f hchar G H _ _ i i' hi hi' b b' hb hpos
    W u u' hdG hdH m n neg pos hmono
  exact cellCompatible_poweredWeylFamily_affine f hchar hb W u' hdH hdG hi hi' hpos neg pos hmono

end Langlands.GroupScheme
