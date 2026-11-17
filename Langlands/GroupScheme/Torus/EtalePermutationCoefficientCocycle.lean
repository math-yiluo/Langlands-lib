import Langlands.GroupScheme.Torus.EtalePermutationCoefficients
import Langlands.GroupScheme.Torus.LocalCoefficientCoherence

/-! # Coherence of coefficient transitions from split charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U U' U'' V W : Scheme.{u}} {D : GroupScheme S}
  {I J K : Type u} [Finite I] [Finite J] [Finite K]

/-- A transition evaluates the target coordinates of the same original-group
morphism whose source coordinates were supplied. -/
theorem transitionUnits_coordinates (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g)
    (T : Over V) (x : T.left ⟶ D.X.left)
    (hx : x ≫ D.X.hom = (T.hom ≫ q) ≫ f) :
    transitionUnits f g e e' q q' h T (coordinates f e (T.hom ≫ q) x hx) =
      coordinates g e' (T.hom ≫ q') x
        (hx.trans (by simp only [Category.assoc, h])) := by
  unfold transitionUnits coordinates
  simp only [MulEquiv.symm_apply_apply]
  rfl

/-- Unit transitions depend only on the two induced test maps to the original
charts, allowing comparison of different common bases. -/
theorem transitionUnits_congr (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g)
    (p : W ⟶ U) (p' : W ⟶ U') (hp : p ≫ f = p' ≫ g)
    (T : Over V) (s : T.left ⟶ W)
    (hq : T.hom ≫ q = s ≫ p) (hq' : T.hom ≫ q' = s ≫ p')
    (z : I → (Γ(T.left, ⊤))ˣ) :
    transitionUnits f g e e' q q' h T z =
      transitionUnits f g e e' p p' hp (Over.mk s) z := by
  let x := (chartPointsEquiv f e (T.hom ≫ q)).symm z
  have hx : x.left ≫ D.X.hom = (T.hom ≫ q) ≫ f := Over.w x
  have hxs : x.left ≫ D.X.hom = (s ≫ p) ≫ f :=
    hx.trans (congrArg (fun a => a ≫ f) hq)
  have hz : coordinates f e (s ≫ p) x.left hxs = z := by
    exact (coordinates_congr f e hxs hx hq.symm rfl).trans
      ((chartPointsEquiv f e (T.hom ≫ q)).apply_symm_apply z)
  change coordinates g e' (T.hom ≫ q') x.left _ = _
  calc
    _ = coordinates g e' (s ≫ p') x.left
        (hxs.trans (by simp only [Category.assoc, hp])) :=
      coordinates_congr g e' _ _ hq' rfl
    _ = transitionUnits f g e e' p p' hp (Over.mk s)
        (coordinates f e (s ≫ p) x.left hxs) :=
      (transitionUnits_coordinates f g e e' p p' hp (Over.mk s) x.left hxs).symm
    _ = _ := congrArg (transitionUnits f g e e' p p' hp (Over.mk s)) hz

/-- Three original charts yield the unit-transition cocycle on every test. -/
theorem transitionUnits_comp (f : U ⟶ S) (g : U' ⟶ S) (k : U'' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (e'' : (GroupScheme.baseChange k).obj D ≅ splitTorus U'' K)
    (q : V ⟶ U) (q' : V ⟶ U') (q'' : V ⟶ U'')
    (h : q ≫ f = q' ≫ g) (h' : q' ≫ g = q'' ≫ k)
    (T : Over V) (z : I → (Γ(T.left, ⊤))ˣ) :
    transitionUnits g k e' e'' q' q'' h' T
      (transitionUnits f g e e' q q' h T z) =
      transitionUnits f k e e'' q q'' (h.trans h') T z := by
  let x := (chartPointsEquiv f e (T.hom ≫ q)).symm z
  have hx : x.left ≫ D.X.hom = (T.hom ≫ q') ≫ g :=
    (Over.w x).trans (by
      change (T.hom ≫ q) ≫ f = (T.hom ≫ q') ≫ g
      simp only [Category.assoc, h])
  exact transitionUnits_coordinates g k e' e'' q' q'' h' T x.left hx

/-- The chosen local coefficient data describe the original chart transition
on every relative unit test in each chosen open. -/
theorem LocallyPermutes.coefficientDatum_formula (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (a : (H.coefficientDatum f g e e').Index)
    (T : Over (pullback f g))
    (hT : Set.range T.hom ⊆ (H.coefficientDatum f g e e').opens a)
    (z : I → (Γ(T.left, ⊤))ˣ) (j : J) :
    transitionUnits f g e e' (pullback.fst f g) (pullback.snd f g)
      pullback.condition T z j =
      z ((H.coefficientDatum f g e e').permutation a j) := by
  classical
  exact transitionUnits_eq_on_open f g e e' _ _ _
    (H a).choose (H a).choose_spec.choose_spec.choose
    (H a).choose_spec.choose_spec.choose_spec T hT z j

/-- Pull back the overlap coefficient datum to any pair of maps with equal
composite to the original base. -/
def LocallyPermutes.coefficientDatumAlong (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g) :
    LocalCoefficientReindexing.Datum V I J :=
  (H.coefficientDatum f g e e').pullback (pullback.lift q q' h)

/-- The pulled-back coefficient datum has the same local unit formula. -/
theorem LocallyPermutes.coefficientDatumAlong_formula (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (q : V ⟶ U) (q' : V ⟶ U') (h : q ≫ f = q' ≫ g)
    (a : (H.coefficientDatumAlong f g e e' q q' h).Index)
    (T : Over V)
    (hT : Set.range T.hom ⊆ (H.coefficientDatumAlong f g e e' q q' h).opens a)
    (z : I → (Γ(T.left, ⊤))ˣ) (j : J) :
    transitionUnits f g e e' q q' h T z j =
      z ((H.coefficientDatumAlong f g e e' q q' h).permutation a j) := by
  let m : V ⟶ pullback f g := pullback.lift q q' h
  have hTm : Set.range ((Over.map m).obj T).hom ⊆
      (H.coefficientDatum f g e e').opens a := by
    rintro _ ⟨t, rfl⟩
    exact hT ⟨t, rfl⟩
  have Hm := H.coefficientDatum_formula f g e e' a ((Over.map m).obj T) hTm z j
  have hm := transitionUnits_congr f g e e' (pullback.fst f g) (pullback.snd f g)
    pullback.condition q q' h ((Over.map m).obj T) T.hom
    (by change (T.hom ≫ m) ≫ pullback.fst f g = _; simp [m, Category.assoc])
    (by change (T.hom ≫ m) ≫ pullback.snd f g = _; simp [m, Category.assoc]) z
  exact (congrFun hm j).symm.trans Hm

/-- The actual glued coefficient equivalences obey the three-chart cocycle
after pullback to any common scheme. -/
theorem coefficientEquivAlong_cocycle (f : U ⟶ S) (g : U' ⟶ S) (k : U'' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (e'' : (GroupScheme.baseChange k).obj D ≅ splitTorus U'' K)
    (H : LocallyPermutes f g e e') (H' : LocallyPermutes g k e' e'')
    (H'' : LocallyPermutes f k e e'')
    (q : V ⟶ U) (q' : V ⟶ U') (q'' : V ⟶ U'')
    (h : q ≫ f = q' ≫ g) (h' : q' ≫ g = q'' ≫ k) :
    (H.coefficientDatumAlong f g e e' q q' h).equiv.trans
        (H'.coefficientDatumAlong g k e' e'' q' q'' h').equiv =
      (H''.coefficientDatumAlong f k e e'' q q'' (h.trans h')).equiv := by
  let A := H.coefficientDatumAlong f g e e' q q' h
  let B := H'.coefficientDatumAlong g k e' e'' q' q'' h'
  let C := H''.coefficientDatumAlong f k e e'' q q'' (h.trans h')
  change A.equiv.trans B.equiv = C.equiv
  calc
    _ = (A.comp B).equiv := (A.equiv_comp B).symm
    _ = C.equiv := by
      apply (A.comp B).equiv_eq_of_unitTransform C
        (transitionUnits f k e e'' q q'' (h.trans h'))
      · intro a T hT z i
        have ha : Set.range T.hom ⊆ A.opens a.1 := fun _ ht => (hT ht).1
        have hb : Set.range T.hom ⊆ B.opens a.2 := fun _ ht => (hT ht).2
        calc
          _ = transitionUnits g k e' e'' q' q'' h' T
              (transitionUnits f g e e' q q' h T z) i :=
            (congrFun (transitionUnits_comp f g k e e' e'' q q' q'' h h' T z) i).symm
          _ = transitionUnits f g e e' q q' h T z (B.permutation a.2 i) :=
            H'.coefficientDatumAlong_formula g k e' e'' q' q'' h' a.2 T hb _ i
          _ = z (A.permutation a.1 (B.permutation a.2 i)) :=
            H.coefficientDatumAlong_formula f g e e' q q' h a.1 T ha z _
      · intro a T hT z i
        exact H''.coefficientDatumAlong_formula f k e e'' q q'' (h.trans h')
          a T hT z i

/-- A chart changed to itself acts as the identity on all unit families. -/
theorem transitionUnits_self (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (q : V ⟶ U) (T : Over V) (z : I → (Γ(T.left, ⊤))ˣ) :
    transitionUnits f f e e q q rfl T z = z := by
  change (chartPointsEquiv f e (T.hom ≫ q))
    ((chartPointsEquiv f e (T.hom ≫ q)).symm z) = z
  exact (chartPointsEquiv f e (T.hom ≫ q)).apply_symm_apply z

/-- The coefficient equivalence on a repeated chart is the identity after
restriction to the diagonal or any other repeated test map. -/
theorem coefficientEquivAlong_self (f : U ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (H : LocallyPermutes f f e e) (q : V ⟶ U) :
    (H.coefficientDatumAlong f f e e q q rfl).equiv =
      AlgEquiv.refl (R := Γ(V, ⊤)) (A₁ := I → Γ(V, ⊤)) := by
  let E : LocalCoefficientReindexing.Datum V I I :=
    { Index := PUnit
      opens := fun _ => ⊤
      covers := by simp
      permutation := fun _ => Equiv.refl I
      agree := fun _ _ _ => rfl }
  have hE : E.equiv = AlgEquiv.refl (R := Γ(V, ⊤)) (A₁ := I → Γ(V, ⊤)) := by
    ext z i
    simpa [E, LocalCoefficientReindexing.Datum.restrict] using E.equiv_restrict z i PUnit.unit
  rw [← hE]
  apply (H.coefficientDatumAlong f f e e q q rfl).equiv_eq_of_unitTransform E
    (fun _ z => z)
  · intro a T hT z i
    exact (congrFun (transitionUnits_self f e q T z) i).symm.trans
      (H.coefficientDatumAlong_formula f f e e q q rfl a T hT z i)
  · intro a T hT z i
    rfl

end Langlands.GroupScheme.EtalePermutationAtlas
