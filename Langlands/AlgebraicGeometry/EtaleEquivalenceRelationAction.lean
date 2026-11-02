import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry

/-! # Actions of étale equivalence relations

An action on `p : P → E.U` has arrow scheme `E.R ×_{E.U,s,p} P`.
The unit and associative action laws make this an étale equivalence relation,
cartesian over `E`. These are internal scheme-level constructions.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- A left action of an equivalence relation on a scheme over its object scheme.
An arrow `(x,y)` acts on a point over `y` to give a point over `x`. -/
structure Action (E : EtaleEquivalenceRelation.{u}) {P : Scheme.{u}} (p : P ⟶ E.U) where
  map : pullback E.s p ⟶ P
  over : map ≫ p = pullback.fst E.s p ≫ E.t
  unital : pullback.lift (p ≫ E.unit) (𝟙 P) (by simp) ≫ map = 𝟙 P
  associative : ∀ {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p),
    pullback.lift r (pullback.lift q v hqv ≫ map)
      (by rw [Category.assoc, over, ← Category.assoc, pullback.lift_fst]; exact hrq) ≫
        map =
      pullback.lift (E.compose r q hrq) v (by simpa using hqv) ≫ map

namespace Action

variable {E : EtaleEquivalenceRelation.{u}} {P : Scheme.{u}} {p : P ⟶ E.U}
  (A : Action E p)

/-- Apply an arrow to a compatible scheme-valued point. -/
noncomputable def act {T : Scheme.{u}} (r : T ⟶ E.R) (v : T ⟶ P)
    (h : r ≫ E.s = v ≫ p) : T ⟶ P :=
  pullback.lift r v h ≫ A.map

lemma act_congr {T : Scheme.{u}} {r q : T ⟶ E.R} {v w : T ⟶ P}
    (hr : r = q) (hv : v = w) (h : r ≫ E.s = v ≫ p)
    (h' : q ≫ E.s = w ≫ p) : A.act r v h = A.act q w h' := by
  subst q
  subst w
  rfl

@[reassoc]
lemma act_over {T : Scheme.{u}} (r : T ⟶ E.R) (v : T ⟶ P)
    (h : r ≫ E.s = v ≫ p) : A.act r v h ≫ p = r ≫ E.t := by
  rw [act, Category.assoc, A.over, ← Category.assoc, pullback.lift_fst]

lemma act_precomp {T T' : Scheme.{u}} (z : T' ⟶ T)
    (r : T ⟶ E.R) (v : T ⟶ P) (h : r ≫ E.s = v ≫ p) :
    z ≫ A.act r v h =
      A.act (z ≫ r) (z ≫ v) (by simpa only [Category.assoc] using congrArg (z ≫ ·) h) := by
  dsimp only [act]
  rw [← Category.assoc]
  apply congrArg (· ≫ A.map)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

@[simp]
lemma act_arrow {T : Scheme.{u}} (x : T ⟶ pullback E.s p) :
    A.act (x ≫ pullback.fst E.s p) (x ≫ pullback.snd E.s p)
      (by simpa only [Category.assoc] using congrArg (x ≫ ·) pullback.condition) =
        x ≫ A.map := by
  dsimp only [act]
  apply congrArg (· ≫ A.map)
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

@[simp]
lemma act_unit {T : Scheme.{u}} (v : T ⟶ P) :
    A.act (v ≫ p ≫ E.unit) v (by simp) = v := by
  have h : pullback.lift (f := E.s) (g := p) (v ≫ p ≫ E.unit) v (by simp) =
      v ≫ pullback.lift (f := E.s) (g := p) (p ≫ E.unit) (𝟙 P) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  rw [act, h, Category.assoc, A.unital, Category.comp_id]

lemma act_assoc {T : Scheme.{u}} (r q : T ⟶ E.R) (v : T ⟶ P)
    (hrq : r ≫ E.s = q ≫ E.t) (hqv : q ≫ E.s = v ≫ p) :
    A.act r (A.act q v hqv) (by rw [act_over]; exact hrq) =
      A.act (E.compose r q hrq) v (by simpa using hqv) :=
  A.associative r q v hrq hqv

/-- Acting by the inverse undoes an action. -/
lemma act_inverse {T : Scheme.{u}} (r : T ⟶ E.R) (v : T ⟶ P)
    (h : r ≫ E.s = v ≫ p) :
    A.act (r ≫ E.inverse) (A.act r v h)
      (by rw [Category.assoc, inverse_s, act_over]) = v := by
  rw [act_assoc]
  have hc : E.compose (r ≫ E.inverse) r (by simp) = v ≫ p ≫ E.unit := by
    rw [compose_inverse_left, ← Category.assoc, h, Category.assoc]
  exact (A.act_congr hc rfl _ _).trans (A.act_unit v)

/-- Reversal of an action arrow. -/
noncomputable def inverseMap : pullback E.s p ⟶ pullback E.s p :=
  pullback.lift (pullback.fst E.s p ≫ E.inverse) A.map
    (by rw [Category.assoc, inverse_s]; exact A.over.symm)

@[reassoc (attr := simp)]
lemma inverseMap_fst :
    A.inverseMap ≫ pullback.fst E.s p = pullback.fst E.s p ≫ E.inverse :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma inverseMap_snd : A.inverseMap ≫ pullback.snd E.s p = A.map :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma inverseMap_map : A.inverseMap ≫ A.map = pullback.snd E.s p := by
  change A.act (pullback.fst E.s p ≫ E.inverse) A.map _ = _
  have ha : A.act (pullback.fst E.s p) (pullback.snd E.s p) pullback.condition = A.map := by
    simp only [act, pullback.lift_fst_snd, Category.id_comp]
  simpa only [ha] using A.act_inverse (pullback.fst E.s p) (pullback.snd E.s p)
    pullback.condition

@[reassoc (attr := simp)]
lemma inverseMap_inverseMap : A.inverseMap ≫ A.inverseMap = 𝟙 (pullback E.s p) := by
  apply pullback.hom_ext <;> simp

/-- Reversal of action arrows is an involutive isomorphism. -/
noncomputable def inverseIso : pullback E.s p ≅ pullback E.s p where
  hom := A.inverseMap
  inv := A.inverseMap
  hom_inv_id := A.inverseMap_inverseMap
  inv_hom_id := A.inverseMap_inverseMap

lemma etale_snd : Etale (pullback.snd E.s p) := by
  let := E.etale_s
  infer_instance

/-- The action map is étale by reversal and base change of the original source. -/
lemma etale_map : Etale A.map := by
  let : Etale (pullback.snd E.s p) := etale_snd
  let : IsIso A.inverseMap := A.inverseIso.isIso_hom
  rw [← A.inverseMap_snd]
  infer_instance

/-- The equivalence relation on a scheme carrying an action. -/
noncomputable def relation : EtaleEquivalenceRelation.{u} where
  U := P
  R := pullback E.s p
  t := A.map
  s := pullback.snd E.s p
  mono_lift := by
    constructor
    intro T x y h
    have ht : x ≫ A.map = y ≫ A.map := by
      simpa using congrArg (· ≫ prod.fst) h
    have hs : x ≫ pullback.snd E.s p = y ≫ pullback.snd E.s p := by
      simpa using congrArg (· ≫ prod.snd) h
    apply pullback.hom_ext
    · apply E.hom_ext
      · simpa only [Category.assoc, A.over] using congrArg (· ≫ p) ht
      · simpa only [Category.assoc, pullback.condition] using congrArg (· ≫ p) hs
    · exact hs
  refl := by
    intro T v
    exact ⟨pullback.lift (v ≫ p ≫ E.unit) v (by simp), A.act_unit v,
      pullback.lift_snd _ _ _⟩
  symm := by
    intro T r
    exact ⟨r ≫ A.inverseMap, by simp, by simp⟩
  trans := by
    intro T x y hxy
    have hc : (x ≫ pullback.fst E.s p) ≫ E.s =
        (y ≫ pullback.fst E.s p) ≫ E.t := by
      calc
        (x ≫ pullback.fst E.s p) ≫ E.s =
            (x ≫ pullback.snd E.s p) ≫ p := by
          rw [Category.assoc, pullback.condition, ← Category.assoc]
        _ = (y ≫ A.map) ≫ p := by rw [hxy]
        _ = (y ≫ pullback.fst E.s p) ≫ E.t := by
          rw [Category.assoc, A.over, ← Category.assoc]
    have hy : (y ≫ pullback.fst E.s p) ≫ E.s =
        (y ≫ pullback.snd E.s p) ≫ p := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    let r := E.compose (x ≫ pullback.fst E.s p) (y ≫ pullback.fst E.s p) hc
    have hr : r ≫ E.s = (y ≫ pullback.snd E.s p) ≫ p := by
      simpa only [r, compose_s] using hy
    refine ⟨pullback.lift r (y ≫ pullback.snd E.s p) hr, ?_,
      pullback.lift_snd _ _ _⟩
    change A.act r (y ≫ pullback.snd E.s p) hr = x ≫ A.map
    calc
      A.act r (y ≫ pullback.snd E.s p) hr =
          A.act (x ≫ pullback.fst E.s p)
            (A.act (y ≫ pullback.fst E.s p) (y ≫ pullback.snd E.s p) hy)
            (by rw [act_over]; exact hc) :=
        (A.act_assoc _ _ _ hc hy).symm
      _ = A.act (x ≫ pullback.fst E.s p) (x ≫ pullback.snd E.s p)
          (by rw [Category.assoc, pullback.condition, ← Category.assoc]) :=
        A.act_congr rfl (by simpa only [A.act_arrow] using hxy.symm) _ _
      _ = x ≫ A.map := A.act_arrow x
  etale_t := A.etale_map
  etale_s := etale_snd

/-- The action relation is cartesian over the original equivalence relation. -/
lemma isCartesianHom :
    IsCartesianHom A.relation E p (pullback.fst E.s p) :=
  ⟨A.over.symm, IsPullback.of_hasPullback E.s p⟩

lemma isAffine_relation [IsAffine E.U] [IsAffine E.R] [IsAffine P] :
    IsAffine A.relation.R := by
  change IsAffine (pullback E.s p)
  infer_instance

end Action

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
