import Langlands.GroupScheme.Reductive.LocalSplitIsomorphismAssembly
import Langlands.GroupScheme.Reductive.LocalSplitRootBaseChange
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Transporting local Weyl relations to arbitrary affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace LocalSplitRootBaseChange

open LocalSplitCell

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {I : Type u} {J : Type u}
  (P : RootDatum J (I → ℤ) (I → ℤ))
  {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Constant Weyl points commute with arbitrary coefficient base change. -/
theorem baseChangePointsEquiv_constantPoint_rootWeylPoint (u : J → (Ga R ⟶ G))
    (a : J) (Z : Over (Spec (CommRingCat.of A))) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).constantPoint
          (rootWeylPoint P (fun α => baseChangeRoot A (u α)) a) Z) =
      G.constantPoint (rootWeylPoint P u a)
        ((Over.map (algebraBaseMap R A)).obj Z) := by
  rw [rootWeylPoint, rootWeylPoint, constantPoint_weylPoint, constantPoint_weylPoint,
    map_mul, map_mul, baseChangePointsEquiv_rootPoint, baseChangePointsEquiv_rootPoint]

/-- Coefficient base change commutes with conjugation by a Weyl point. -/
theorem baseChangeRoot_comp_innerIso_rootWeylPoint (u : J → (Ga R ⟶ G))
    (a : J) (w : Ga R ⟶ G) :
    baseChangeRoot A (w ≫ (G.innerIso (rootWeylPoint P u a)).hom) =
      baseChangeRoot A w ≫
        (((GroupScheme.baseChange (algebraBaseMap R A)).obj G).innerIso
          (rootWeylPoint P (fun α => baseChangeRoot A (u α)) a)).hom := by
  apply hom_ext_rootPoint
  intro Z c
  apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
  rw [baseChangePointsEquiv_rootPoint, rootPoint_comp, rootPoint_comp,
    GroupScheme.comp_innerIso_hom, GroupScheme.comp_innerIso_hom,
    map_mul, map_mul, map_inv, baseChangePointsEquiv_rootPoint,
    baseChangePointsEquiv_constantPoint_rootWeylPoint]

/-- Coefficient base change commutes with conjugation along a simple word. -/
theorem baseChangeRoot_wordConj (u : J → (Ga R ⟶ G)) (l : List J) (w : Ga R ⟶ G) :
    baseChangeRoot A (wordConj P u l w) =
      wordConj P (fun α => baseChangeRoot A (u α)) l (baseChangeRoot A w) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [wordConj, wordConj, baseChangeRoot_comp_innerIso_rootWeylPoint, ih]

/-- The entire Weyl family commutes with arbitrary coefficient base change. -/
theorem baseChangeRoot_weylFamily {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) (α : J) :
    baseChangeRoot A (weylFamily P W u α) =
      weylFamily P W (fun β => baseChangeRoot A (u β)) α :=
  baseChangeRoot_wordConj A P u (W α).word (u (W α).simple)

/-- Values of the entire Weyl family correspond under coefficient base change. -/
theorem baseChangePointsEquiv_rootPoint_weylFamily {b : P.Base}
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) (α : J)
    (Z : Over (Spec (CommRingCat.of A))) (c : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (rootPoint (weylFamily P W (fun β => baseChangeRoot A (u β)) α) Z c) =
      rootPoint (weylFamily P W u α) ((Over.map (algebraBaseMap R A)).obj Z) c := by
  rw [← baseChangeRoot_weylFamily, baseChangePointsEquiv_rootPoint]

/-- Commutators of Weyl-family values correspond under coefficient base change. -/
theorem baseChangePointsEquiv_posComm_weylFamily {b : P.Base}
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of A))) (k l : Fin n) (x y : Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (posComm (weylFamily P W (fun β => baseChangeRoot A (u β))) pos Z k l x y) =
      posComm (weylFamily P W u) pos ((Over.map (algebraBaseMap R A)).obj Z) k l x y := by
  simp only [posComm, map_mul, map_inv, baseChangePointsEquiv_rootPoint_weylFamily]

/-- Ordered products of Weyl-family values correspond under coefficient base change. -/
theorem baseChangePointsEquiv_orderedProduct_weylFamily {b : P.Base}
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of A))) (c : Fin n → Γ(Z.left, ⊤)) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (orderedProduct (weylFamily P W (fun β => baseChangeRoot A (u β))) pos Z c) =
      orderedProduct (weylFamily P W u) pos ((Over.map (algebraBaseMap R A)).obj Z) c := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    baseChangePointsEquiv_rootPoint_weylFamily]

variable {P} [Fintype I]

/-- Lift a point of the coordinate cell to the coefficient base change by
retaining all its additive and multiplicative coordinates. -/
def liftCellPoint (Z : Over (Spec (CommRingCat.of A))) {m n : ℕ}
    (x : (Over.map (algebraBaseMap R A)).obj Z ⟶ cellObj R I m n) :
    Z ⟶ cellObj A I m n :=
  mkCellPoint Z (negCoord (R := R) x)
    (splitTorus.pointsEquiv I ((Over.map (algebraBaseMap R A)).obj Z) (torusCoord x))
    (posCoord (R := R) x)

/-- The torus coordinate of the lifted cell point corresponds to the original
torus coordinate under coefficient base change. -/
theorem baseChangePointsEquiv_torusCoord_liftCellPoint
    (Z : Over (Spec (CommRingCat.of A))) {m n : ℕ}
    (x : (Over.map (algebraBaseMap R A)).obj Z ⟶ cellObj R I m n) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) (splitTorus _ I) Z
        (torusCoord (liftCellPoint A Z x) ≫
          (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom) =
      torusCoord x := by
  apply (splitTorus.pointsEquiv I ((Over.map (algebraBaseMap R A)).obj Z)).injective
  have h := splitTorus.pointsEquiv_baseChangeIso_hom (algebraBaseMap R A) I Z
    (torusCoord (liftCellPoint A Z x) ≫
      (splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id] at h
  simp only [splitTorus.baseChangePointsEquiv, MulEquiv.trans_apply] at h
  exact h.symm.trans (torusCoord_mkCellPoint Z (negCoord (R := R) x)
    (splitTorus.pointsEquiv I ((Over.map (algebraBaseMap R A)).obj Z) (torusCoord x))
    (posCoord (R := R) x))

/-- Evaluation of a cell map on the lifted point corresponds to evaluation of
the original cell map. -/
theorem baseChangePointsEquiv_cellMap_liftCellPoint
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of A)))
    (x : (Over.map (algebraBaseMap R A)).obj Z ⟶ cellObj R I m n) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (liftCellPoint A Z x ≫ cellMap (splitTorus.baseChangeHom (K := A) G I i)
          (fun α => baseChangeRoot A (u α)) neg pos) =
      x ≫ cellMap i u neg pos := by
  rw [comp_cellMap, comp_cellMap, cellPoint, cellPoint, map_mul, map_mul,
    baseChangePointsEquiv_orderedProduct, baseChangePointsEquiv_orderedProduct,
    baseChangePointsEquiv_torus, baseChangePointsEquiv_torusCoord_liftCellPoint]
  simp only [liftCellPoint, negCoord_mkCellPoint, posCoord_mkCellPoint]

/-- Evaluation of a Weyl-family cell map on the lifted point corresponds to
evaluation of the original Weyl-family cell map. -/
theorem baseChangePointsEquiv_cellMap_weylFamily_liftCellPoint
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) {b : P.Base}
    (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G))
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of A)))
    (x : (Over.map (algebraBaseMap R A)).obj Z ⟶ cellObj R I m n) :
    GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z
        (liftCellPoint A Z x ≫ cellMap (splitTorus.baseChangeHom (K := A) G I i)
          (weylFamily P W (fun α => baseChangeRoot A (u α))) neg pos) =
      x ≫ cellMap i (weylFamily P W u) neg pos := by
  have hfamily : weylFamily P W (fun α => baseChangeRoot A (u α)) =
      fun α => baseChangeRoot A (weylFamily P W u α) :=
    funext fun α => (baseChangeRoot_weylFamily A P W u α).symm
  rw [hfamily]
  exact baseChangePointsEquiv_cellMap_liftCellPoint A i (weylFamily P W u) neg pos Z x

end LocalSplitRootBaseChange

namespace AffineSplitWeylRelations

open LocalSplitCell LocalSplitRootBaseChange

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}

/-- Local commutator relations imply the same relations over an arbitrary
affine base, since every test ring is already local. -/
theorem commutatorRelations_of_local
    (h2 : LocalSplitWeylCommutatorStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    (hP : IsFibrewiseRootDatumOf I G i P) (hP' : IsFibrewiseRootDatumOf I H i' P)
    (W : ∀ α, SimpleWord P b α) (hD : IsDescendingWords P b W)
    (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
      IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a)))
    (hw' : ∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a))
    {n : ℕ} (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) :
    CommutatorRelations b W u u' (fun k => (pos k : J)) := by
  intro A _ _ _ s k l hkl x y e hxy
  let : Algebra R A := (Spec.preimage s).hom.toAlgebra
  have hs : 𝟙 _ ≫ algebraBaseMap R A = s := (Category.id_comp _).trans (Spec.map_preimage s)
  let GA := (GroupScheme.baseChange (algebraBaseMap R A)).obj G
  let HA := (GroupScheme.baseChange (algebraBaseMap R A)).obj H
  let : IsAffineHom GA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let : IsAffineHom HA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let iA' := splitTorus.baseChangeHom (K := A) H I i'
  let uA := fun α => baseChangeRoot A (u α)
  let uA' := fun α => baseChangeRoot A (u' α)
  have hiA : IsClosedSubgroup iA :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi.baseChange (algebraBaseMap R A))
  have hiA' : IsClosedSubgroup iA' :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi'.baseChange (algebraBaseMap R A))
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
  have hmaxA' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA' :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I H i' hmax'
  have huA : ∀ a ∈ b.support, IsRootParametrization iA (P.root a) (uA a) ∧
      IsRootParametrization iA (P.root (P.reflectionPerm a a)) (uA (P.reflectionPerm a a)) :=
    fun a ha => ⟨isRootParametrization_baseChangeRoot A i _ _ (hu a ha).1,
      isRootParametrization_baseChangeRoot A i _ _ (hu a ha).2⟩
  have huA' : ∀ a ∈ b.support, IsRootParametrization iA' (P.root a) (uA' a) ∧
      IsRootParametrization iA' (P.root (P.reflectionPerm a a)) (uA' (P.reflectionPerm a a)) :=
    fun a ha => ⟨isRootParametrization_baseChangeRoot A i' _ _ (hu' a ha).1,
      isRootParametrization_baseChangeRoot A i' _ _ (hu' a ha).2⟩
  have hwA : ∀ a ∈ b.support, IsWeylPoint iA (rootWeylPoint P uA a) (P.reflection a) :=
    fun a ha => isWeylPoint_baseChange A (hw a ha)
  have hwA' : ∀ a ∈ b.support, IsWeylPoint iA' (rootWeylPoint P uA' a) (P.reflection a) :=
    fun a ha => isWeylPoint_baseChange A (hw' a ha)
  have hlocal := h2 A I J GA HA (hG.baseChange _) (hH.baseChange _) iA iA'
    hiA hiA' hmaxA hmaxA' P (hP.baseChange_implicit (A := A))
    (hP'.baseChange_implicit (A := A)) b W hD uA uA' huA hwA huA' hwA' n pos hmono
  let Z : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  have hxyA :
      posComm (weylFamily P W uA) (fun k => (pos k : J)) Z k l x y =
        orderedProduct (weylFamily P W uA) (fun k => (pos k : J)) Z e := by
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
    rw [baseChangePointsEquiv_posComm_weylFamily, baseChangePointsEquiv_orderedProduct_weylFamily]
    change posComm (weylFamily P W u) (fun k => (pos k : J))
        (Over.mk (𝟙 _ ≫ algebraBaseMap R A)) k l x y =
      orderedProduct (weylFamily P W u) (fun k => (pos k : J))
        (Over.mk (𝟙 _ ≫ algebraBaseMap R A)) e
    rw [hs]
    exact hxy
  have hxyA' := hlocal A (𝟙 _) k l hkl x y e hxyA
  have h := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) H Z) hxyA'
  rw [baseChangePointsEquiv_posComm_weylFamily, baseChangePointsEquiv_orderedProduct_weylFamily] at h
  change posComm (weylFamily P W u') (fun k => (pos k : J))
      (Over.mk (𝟙 _ ≫ algebraBaseMap R A)) k l x y =
    orderedProduct (weylFamily P W u') (fun k => (pos k : J))
      (Over.mk (𝟙 _ ≫ algebraBaseMap R A)) e at h
  rw [hs] at h
  exact h

/-- Local negative-simple relations imply the same relations over an arbitrary
affine base, by lifting coordinate cell points to each local test ring. -/
theorem negSimpleRelations_of_local
    (h3 : LocalSplitWeylNegSimpleStatement.{u})
    (hG : IsReductive G) (hH : IsReductive H)
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i')
    (hP : IsFibrewiseRootDatumOf I G i P) (hP' : IsFibrewiseRootDatumOf I H i' P)
    (W : ∀ α, SimpleWord P b α) (hD : IsDescendingWords P b W)
    (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H))
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
      IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a)))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    (hu' : ∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a) ∧
      IsRootParametrization i' (P.root (P.reflectionPerm a a)) (u' (P.reflectionPerm a a)))
    (hw' : ∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) :
    NegSimpleRelations P
      (cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)))
      (cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) b u u' := by
  intro A _ _ _ s x y a ha hxy
  let : Algebra R A := (Spec.preimage s).hom.toAlgebra
  have hs : 𝟙 _ ≫ algebraBaseMap R A = s := (Category.id_comp _).trans (Spec.map_preimage s)
  let GA := (GroupScheme.baseChange (algebraBaseMap R A)).obj G
  let HA := (GroupScheme.baseChange (algebraBaseMap R A)).obj H
  let : IsAffineHom GA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let : IsAffineHom HA.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd H.X.hom (algebraBaseMap R A)))
  let : Smooth G.X.hom := hG.smooth
  let : Smooth H.X.hom := hH.smooth
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let iA' := splitTorus.baseChangeHom (K := A) H I i'
  let uA := fun α => baseChangeRoot A (u α)
  let uA' := fun α => baseChangeRoot A (u' α)
  have hiA : IsClosedSubgroup iA :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi.baseChange (algebraBaseMap R A))
  have hiA' : IsClosedSubgroup iA' :=
    IsClosedSubgroup.iso_comp (splitTorus.baseChangeIso (algebraBaseMap R A) I).symm
      (hi'.baseChange (algebraBaseMap R A))
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
  have hmaxA' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA' :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I H i' hmax'
  have huA : ∀ a ∈ b.support, IsRootParametrization iA (P.root a) (uA a) ∧
      IsRootParametrization iA (P.root (P.reflectionPerm a a)) (uA (P.reflectionPerm a a)) :=
    fun a ha => ⟨isRootParametrization_baseChangeRoot A i _ _ (hu a ha).1,
      isRootParametrization_baseChangeRoot A i _ _ (hu a ha).2⟩
  have huA' : ∀ a ∈ b.support, IsRootParametrization iA' (P.root a) (uA' a) ∧
      IsRootParametrization iA' (P.root (P.reflectionPerm a a)) (uA' (P.reflectionPerm a a)) :=
    fun a ha => ⟨isRootParametrization_baseChangeRoot A i' _ _ (hu' a ha).1,
      isRootParametrization_baseChangeRoot A i' _ _ (hu' a ha).2⟩
  have hwA : ∀ a ∈ b.support, IsWeylPoint iA (rootWeylPoint P uA a) (P.reflection a) :=
    fun a ha => isWeylPoint_baseChange A (hw a ha)
  have hwA' : ∀ a ∈ b.support, IsWeylPoint iA' (rootWeylPoint P uA' a) (P.reflection a) :=
    fun a ha => isWeylPoint_baseChange A (hw' a ha)
  have hlocal := h3 A I J GA HA (hG.baseChange _) (hH.baseChange _) iA iA'
    hiA hiA' hmaxA hmaxA' P (hP.baseChange_implicit (A := A))
    (hP'.baseChange_implicit (A := A)) b W hD uA uA' huA hwA huA' hwA' m n neg pos hmono
  let Z : Over (Spec (CommRingCat.of A)) := Over.mk (𝟙 _)
  have hZ : (Over.map (algebraBaseMap R A)).obj Z = Over.mk s := by
    change Over.mk (𝟙 _ ≫ algebraBaseMap R A) = Over.mk s
    rw [hs]
  let x0 := eqToHom hZ ≫ x
  let y0 := eqToHom hZ ≫ y
  have hxy0 :
      (x0 ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
          rootPoint (u (P.reflectionPerm a a)) ((Over.map (algebraBaseMap R A)).obj Z) (-1) =
        y0 ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) := by
    have h := congrArg (fun q => eqToHom hZ ≫ q) hxy
    rw [MonObj.comp_mul, comp_rootPoint, map_neg, map_one] at h
    exact h
  let xA := liftCellPoint A Z x0
  let yA := liftCellPoint A Z y0
  have hxyA :
      (xA ≫ cellMap iA (weylFamily P W uA) (fun k => (neg k : J)) (fun k => (pos k : J))) *
          rootPoint (uA (P.reflectionPerm a a)) Z (-1) =
        yA ≫ cellMap iA (weylFamily P W uA) (fun k => (neg k : J)) (fun k => (pos k : J)) := by
    apply (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) G Z).injective
    rw [map_mul, baseChangePointsEquiv_cellMap_weylFamily_liftCellPoint,
      baseChangePointsEquiv_cellMap_weylFamily_liftCellPoint, baseChangePointsEquiv_rootPoint]
    exact hxy0
  have hxyA' := hlocal A (𝟙 _) xA yA a ha hxyA
  have h := congrArg (GroupScheme.baseChangePointsEquiv (algebraBaseMap R A) H Z) hxyA'
  rw [map_mul, baseChangePointsEquiv_cellMap_weylFamily_liftCellPoint,
    baseChangePointsEquiv_cellMap_weylFamily_liftCellPoint, baseChangePointsEquiv_rootPoint] at h
  apply (cancel_epi (eqToHom hZ)).mp
  rw [MonObj.comp_mul, comp_rootPoint, map_neg, map_one]
  exact h

end AffineSplitWeylRelations

end Langlands.GroupScheme
