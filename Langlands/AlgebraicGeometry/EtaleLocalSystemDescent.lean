import Langlands.AlgebraicGeometry.EtaleLocalSystemBasics
import Langlands.Algebra.FiniteOrderCongruenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.EtaleNormalLocallyIrreducible
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Descent of trivializations of étale local systems -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

/-! ## Transition isomorphisms between trivializations -/

section PartTransition

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}

/-- The isomorphism in a slice category between two objects with the same source whose structure
maps are equal. -/
def overIsoOfEq {T Y : Scheme.{u}} {g h : Y ⟶ T} (w : g = h) : Over.mk g ≅ Over.mk h :=
  Over.isoMk (Iso.refl Y) (by simp [w])

@[simp] theorem overIsoOfEq_hom_left {T Y : Scheme.{u}} {g h : Y ⟶ T} (w : g = h) :
    (overIsoOfEq w).hom.left = 𝟙 Y := rfl

@[simp] theorem overIsoOfEq_inv_left {T Y : Scheme.{u}} {g h : Y ⟶ T} (w : g = h) :
    (overIsoOfEq w).inv.left = 𝟙 Y := rfl

/-- Restriction along equal morphisms, by components. -/
def congrIso {T : Scheme.{u}} {g h : T ⟶ S} (w : g = h) (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    restrict g F ≅ restrict h F :=
  NatIso.ofComponents
    (fun V => F.mapIso (overIsoOfEq (congrArg (V.unop.hom ≫ ·) w)).symm.op)
    (fun {V V'} φ => by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← F.map_comp, ← F.map_comp]
      congr 1)

@[simp] theorem congrIso_hom_app {T : Scheme.{u}} {g h : T ⟶ S} (w : g = h)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (V : (Over T)ᵒᵖ) :
    (congrIso w F).hom.app V = F.map (overIsoOfEq (congrArg (V.unop.hom ≫ ·) w)).inv.op := rfl

@[simp] theorem congrIso_inv_app {T : Scheme.{u}} {g h : T ⟶ S} (w : g = h)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) (V : (Over T)ᵒᵖ) :
    (congrIso w F).inv.app V = F.map (overIsoOfEq (congrArg (V.unop.hom ≫ ·) w)).hom.op := rfl

/-- A trivialization `ef` over `f`, pulled back along `a : W ⟶ X`: the restriction of `F` along
`a ≫ f` is constant. Defined by components. -/
def fromRestrict {X W : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (a : W ⟶ X) : restrict (a ≫ f) F ≅ constant W M :=
  NatIso.ofComponents
    (fun V => F.mapIso (overIsoOfEq (Category.assoc V.unop.hom a f)).op ≪≫
      ef.app (op ((Over.map a).obj V.unop)))
    (fun {V V'} φ => by
      have hn := ef.hom.naturality ((Over.map a).map φ.unop).op
      have key : F.map ((Over.map (a ≫ f)).op.map φ) ≫
            F.map (overIsoOfEq (Category.assoc V'.unop.hom a f)).op.hom =
          F.map (overIsoOfEq (Category.assoc V.unop.hom a f)).op.hom ≫
            (restrict f F).map ((Over.map a).map φ.unop).op := by
        change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
        rw [← F.map_comp, ← F.map_comp]
        congr 1
      change F.map _ ≫ F.map _ ≫ ef.hom.app _ = (F.map _ ≫ ef.hom.app _) ≫ _
      exact (Category.assoc _ _ _).symm.trans ((key =≫ _).trans
        ((Category.assoc _ _ _).trans ((_ ≫= hn).trans (Category.assoc _ _ _).symm))))

@[simp] theorem fromRestrict_hom_app {X W : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (a : W ⟶ X) (V : (Over W)ᵒᵖ) :
    (fromRestrict ef a).hom.app V =
      F.map (overIsoOfEq (Category.assoc V.unop.hom a f)).hom.op ≫
        ef.hom.app (op ((Over.map a).obj V.unop)) := rfl

@[simp] theorem fromRestrict_inv_app {X W : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (a : W ⟶ X) (V : (Over W)ᵒᵖ) :
    (fromRestrict ef a).inv.app V =
      ef.inv.app (op ((Over.map a).obj V.unop)) ≫
        F.map (overIsoOfEq (Category.assoc V.unop.hom a f)).inv.op := rfl

/-- `congrIso` along `rfl` is the identity. -/
theorem congrIso_rfl {T : Scheme.{u}} (g : T ⟶ S) (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    congrIso (rfl : g = g) F = Iso.refl _ := by
  refine Iso.ext (NatTrans.ext (funext fun V => ?_))
  change F.map _ = 𝟙 _
  rw [← F.map_id]
  congr 1

/-- Composing two `congrIso`s. -/
theorem congrIso_trans {T : Scheme.{u}} {g h k : T ⟶ S} (w : g = h) (w' : h = k)
    (F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    congrIso w F ≪≫ congrIso w' F = congrIso (w.trans w') F := by
  subst w w'
  rw [congrIso_rfl, Iso.trans_refl]

/-- The transition isomorphism between two trivializations `ef` over `f` and `eg` over `g`,
pulled back to a scheme `W` along `a : W ⟶ X` and `b : W ⟶ Y` with `a ≫ f = b ≫ g`. -/
def transition {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {M N : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y N)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) : constant W M ≅ constant W N :=
  (fromRestrict ef a).symm ≪≫ congrIso h F ≪≫ fromRestrict eg b

/-- The cocycle identity for transition isomorphisms. -/
theorem transition_trans {X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {k : Z ⟶ S}
    {M N P : AddCommGrpCat.{v}} (ef : restrict f F ≅ constant X M)
    (eg : restrict g F ≅ constant Y N) (ek : restrict k F ≅ constant Z P)
    (a : W ⟶ X) (b : W ⟶ Y) (c : W ⟶ Z) (h : a ≫ f = b ≫ g) (h' : b ≫ g = c ≫ k) :
    transition ef eg a b h ≪≫ transition eg ek b c h' = transition ef ek a c (h.trans h') := by
  simp only [transition, Iso.trans_assoc, Iso.self_symm_id_assoc]
  rw [← Iso.trans_assoc (congrIso h F), congrIso_trans]

/-- The transition of a trivialization with itself along one map is the identity. -/
theorem transition_self {X W : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (a : W ⟶ X) :
    transition ef ef a a rfl = Iso.refl _ := by
  rw [transition, congrIso_rfl, Iso.refl_trans, Iso.symm_self_id]

/-- Swapping the two trivializations inverts the transition. -/
theorem transition_symm {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {M N : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y N)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    (transition ef eg a b h).symm = transition eg ef b a h.symm := by
  have := transition_trans ef eg ef a b a h h.symm
  rw [transition_self] at this
  ext1
  exact Iso.inv_ext (by simpa using congrArg Iso.hom this)

/-- The constant presheaf sends the slice isomorphism `overIsoOfEq` (identity on sources) to an
identity. -/
theorem constant_map_overIsoOfEq_hom {X Y : Scheme.{u}} (M : AddCommGrpCat.{v}) {g h : Y ⟶ X}
    (w : g = h) : (constant X M).map (overIsoOfEq w).hom.op = 𝟙 _ := by
  ext s
  rfl

/-- Transport of the inverse of a trivialization along `overIsoOfEq`. -/
theorem inv_app_overIsoOfEq {X Y : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) {g h : Y ⟶ X} (w : g = h) :
    ef.inv.app (op (Over.mk h)) ≫ (restrict f F).map (overIsoOfEq w).hom.op =
      ef.inv.app (op (Over.mk g)) := by
  rw [← ef.inv.naturality, constant_map_overIsoOfEq_hom]
  exact Category.id_comp _

/-- Transport of a trivialization along `overIsoOfEq`. -/
theorem hom_app_overIsoOfEq {X Y : Scheme.{u}} {f : X ⟶ S} {M : AddCommGrpCat.{v}}
    (ef : restrict f F ≅ constant X M) {g h : Y ⟶ X} (w : g = h) :
    (restrict f F).map (overIsoOfEq w).hom.op ≫ ef.hom.app (op (Over.mk g)) =
      ef.hom.app (op (Over.mk h)) := by
  rw [ef.hom.naturality, constant_map_overIsoOfEq_hom]
  exact Category.comp_id _

theorem restrict_map_eq {T : Scheme.{u}} (g : T ⟶ S) (G : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v})
    {V V' : (Over T)ᵒᵖ} (φ : V ⟶ V') :
    (restrict g G).map φ = G.map ((Over.map g).map φ.unop).op := rfl

/-- **Naturality of transitions.** Pulling back along `k : W' ⟶ W`: on each object `V` over `W'`,
the transition along `k ≫ a`, `k ≫ b` is the transition along `a`, `b` at the image of `V` over
`W`. -/
theorem transition_comp_app {X Y W W' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {M N : AddCommGrpCat.{v}} (ef : restrict f F ≅ constant X M)
    (eg : restrict g F ≅ constant Y N) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)
    (k : W' ⟶ W) (V : (Over W')ᵒᵖ) :
    (transition ef eg (k ≫ a) (k ≫ b) (by simp [h])).hom.app V =
      (transition ef eg a b h).hom.app (op ((Over.map k).obj V.unop)) :=
  rfl

end PartTransition

/-! ## Pointwise labels of morphisms between constant sheaves -/

section PartLabel

variable {W : Scheme.{u}} {M N P : AddCommGrpCat.{v}}

/-- The value at `x` of the image under `φ` of the locally constant section `s` over `V`. -/
def evalAt (φ : constant W M ⟶ constant W N) (V : Over W) (s : LocallyConstant V.left M)
    (x : V.left) : N :=
  constantSections W N V ((φ.app (op V)).hom ((constantSections W M V).symm s)) x

theorem constantSections_symm_map {V V' : Over W} (j : V' ⟶ V) (s : LocallyConstant V.left M) :
    (constant W M).map j.op ((constantSections W M V).symm s) =
      (constantSections W M V').symm (s.comap j.left.base.hom) := by
  apply (constantSections W M V').injective
  ext x
  rw [AddEquiv.apply_symm_apply, constantSections_map]
  simp

/-- Naturality of evaluation along a morphism `j : V' ⟶ V` over `W`. -/
theorem evalAt_comap (φ : constant W M ⟶ constant W N) {V V' : Over W} (j : V' ⟶ V)
    (s : LocallyConstant V.left M) (x : V'.left) :
    evalAt φ V' (s.comap j.left.base.hom) x = evalAt φ V s (j.left x) := by
  have hn := congrArg (fun g => g.hom ((constantSections W M V).symm s)) (φ.naturality j.op)
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply] at hn
  rw [evalAt, ← constantSections_symm_map]
  erw [hn]
  rw [constantSections_map]
  rfl

/-- The *label* of a morphism of constant sheaves at a point `w`: the group homomorphism by which
`φ` acts on constant sections near `w`. -/
def label (φ : constant W M ⟶ constant W N) (w : W) : M →+ N where
  toFun m := evalAt φ (Over.mk (𝟙 W)) (LocallyConstant.const W m) w
  map_zero' := by
    have h0 : LocallyConstant.const W (0 : M) = 0 := by ext; rfl
    simp [evalAt, h0]
  map_add' m m' := by
    have h : LocallyConstant.const W (m + m') =
        LocallyConstant.const W m + LocallyConstant.const W m' := by ext; rfl
    simp [evalAt, h]

/-- On an object whose source has at most one point, `φ` acts through its label. -/
theorem evalAt_of_subsingleton (φ : constant W M ⟶ constant W N) (V : Over W)
    [Subsingleton V.left] (s : LocallyConstant V.left M) (x : V.left) :
    evalAt φ V s x = label φ (V.hom x) (s x) := by
  have hs : s = (LocallyConstant.const W (s x)).comap V.hom.base.hom := by
    ext y
    rw [Subsingleton.elim y x]
    rfl
  let i : V ⟶ Over.mk (𝟙 W) := Over.homMk V.hom (by simp)
  rw [hs]
  exact evalAt_comap φ i _ x

/-- **Evaluation formula.** `φ` acts on any section `s` over any object `V`, at a point `x`,
through its label at the image of `x`. -/
theorem evalAt_eq_label (φ : constant W M ⟶ constant W N) (V : Over W)
    (s : LocallyConstant V.left M) (x : V.left) :
    evalAt φ V s x = label φ (V.hom x) (s x) := by
  have h : Subsingleton (Spec (V.left.residueField x)) := inferInstance
  have hx : (V.left.fromSpecResidueField x) (default : Spec (V.left.residueField x)) = x :=
    V.left.fromSpecResidueField_apply x _
  let j : Over.mk (V.left.fromSpecResidueField x ≫ V.hom) ⟶ V :=
    Over.homMk (V.left.fromSpecResidueField x) rfl
  have e := evalAt_comap φ j s (default : Spec (V.left.residueField x))
  change evalAt φ _ _ _ = evalAt φ V s ((V.left.fromSpecResidueField x) _) at e
  rw [hx] at e
  rw [← e, @evalAt_of_subsingleton _ _ _ φ _ h]
  change label φ (V.hom ((V.left.fromSpecResidueField x) _)) (s ((V.left.fromSpecResidueField x) _)) = _
  rw [hx]

theorem evalAt_comp (φ : constant W M ⟶ constant W N) (ψ : constant W N ⟶ constant W P)
    (V : Over W) (s : LocallyConstant V.left M) (x : V.left) :
    evalAt (φ ≫ ψ) V s x =
      evalAt ψ V (constantSections W N V ((φ.app (op V)).hom ((constantSections W M V).symm s)))
        x := by
  simp [evalAt]

theorem label_apply (φ : constant W M ⟶ constant W N) (w : W) (m : M) :
    label φ w m = evalAt φ (Over.mk (𝟙 W)) (LocallyConstant.const W m) w := rfl

/-- Labels of a composite. -/
theorem label_comp (φ : constant W M ⟶ constant W N) (ψ : constant W N ⟶ constant W P)
    (w : W) : label (φ ≫ ψ) w = (label ψ w).comp (label φ w) := by
  ext m
  rw [label_apply, evalAt_comp, evalAt_eq_label]
  rfl

/-- The label of the identity. -/
theorem label_id (w : W) : label (𝟙 (constant W M)) w = AddMonoidHom.id M := by
  ext m
  rfl

/-- A morphism of constant sheaves is determined by its labels. -/
theorem ext_of_label {φ ψ : constant W M ⟶ constant W N} (h : ∀ w, label φ w = label ψ w) :
    φ = ψ := by
  ext V t
  apply (constantSections W N V.unop).injective
  ext x
  have e1 := evalAt_eq_label φ V.unop (constantSections W M V.unop t) x
  have e2 := evalAt_eq_label ψ V.unop (constantSections W M V.unop t) x
  simp only [evalAt, AddEquiv.symm_apply_apply] at e1 e2
  rw [e1, e2, h]

/-- Labels are locally constant in the point. -/
theorem isLocallyConstant_label (φ : constant W M ⟶ constant W N) (m : M) :
    IsLocallyConstant (fun w => label φ w m) :=
  (constantSections W N (Over.mk (𝟙 W)) ((φ.app (op (Over.mk (𝟙 W)))).hom
    ((constantSections W M (Over.mk (𝟙 W))).symm (LocallyConstant.const W m)))).isLocallyConstant

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}}

/-- Labels of transitions are compatible with pulling back along `k : W' ⟶ W`. -/
theorem label_transition_comp {X Y W' : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y N)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) (k : W' ⟶ W) (w : W') :
    label (transition ef eg (k ≫ a) (k ≫ b) (by simp [h])).hom w =
      label (transition ef eg a b h).hom (k w) := by
  ext m
  rw [label_apply]
  have := evalAt_eq_label (transition ef eg a b h).hom ((Over.map k).obj (Over.mk (𝟙 W')))
    (LocallyConstant.const W' m) w
  exact this

end PartLabel

/-! ## Gluing trivializations with trivial transitions -/

section PartGlue

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} {M : AddCommGrpCat.{v}}

/-- The morphism in `Over S` from the object `W --(a ≫ f)--> S` to `U` given by `c : W ⟶ U.left`
with `c ≫ U.hom = a ≫ f`. -/
def trivHom {X W : Scheme.{u}} (f : X ⟶ S) (a : W ⟶ X) (U : Over S) (c : W ⟶ U.left)
    (hc : c ≫ U.hom = a ≫ f) : (Over.map (a ≫ f)).obj (Over.mk (𝟙 W)) ⟶ U :=
  Over.homMk c (by simpa using hc)

/-- A section `s` of `F` over `U`, pulled back to `W` along `c` and trivialized by `ef` along
`a`. -/
def triv {X W : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M) (a : W ⟶ X)
    {U : Over S} (c : W ⟶ U.left) (hc : c ≫ U.hom = a ≫ f) (s : F.obj (op U)) :
    (constant W M).obj (op (Over.mk (𝟙 W))) :=
  ((fromRestrict ef a).hom.app (op (Over.mk (𝟙 W)))).hom ((F.map (trivHom f a U c hc).op).hom s)

/-- Transitions carry trivialized sections to trivialized sections. -/
theorem transition_hom_triv {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) {U : Over S} (c : W ⟶ U.left)
    (hc : c ≫ U.hom = a ≫ f) (s : F.obj (op U)) :
    ((transition ef eg a b h).hom.app (op (Over.mk (𝟙 W)))).hom (triv ef a c hc s) =
      triv eg b c (hc.trans h) s := by
  simp only [transition, triv, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]
  erw [Iso.hom_inv_id_app_apply]
  congr 1
  change (F.map _ ≫ F.map _).hom s = (F.map _).hom s
  rw [← F.map_comp]
  congr 2

/-- Where the transition has trivial label, the two trivializations of a section agree. -/
theorem triv_apply_eq_of_label {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) {U : Over S} (c : W ⟶ U.left)
    (hc : c ≫ U.hom = a ≫ f) (s : F.obj (op U)) (w : W)
    (hlab : label (transition ef eg a b h).hom w = AddMonoidHom.id M) :
    constantSections W M (Over.mk (𝟙 W)) (triv eg b c (hc.trans h) s) w =
      constantSections W M (Over.mk (𝟙 W)) (triv ef a c hc s) w := by
  rw [← transition_hom_triv ef eg a b h c hc s]
  have := evalAt_eq_label (transition ef eg a b h).hom (Over.mk (𝟙 W))
    (constantSections W M (Over.mk (𝟙 W)) (triv ef a c hc s)) w
  simp only [evalAt, AddEquiv.symm_apply_apply] at this
  rw [this]
  change label _ w _ = _
  rw [hlab]
  rfl

/-- Trivialized sections are compatible with pulling back along `k : W' ⟶ W`. -/
theorem triv_comp_apply {X W W' : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M)
    (a : W ⟶ X) {U : Over S} (c : W ⟶ U.left) (hc : c ≫ U.hom = a ≫ f) (s : F.obj (op U))
    (k : W' ⟶ W) (w' : W') :
    constantSections W' M (Over.mk (𝟙 W')) (triv ef (k ≫ a) (k ≫ c) (by simp [hc]) s) w' =
      constantSections W M (Over.mk (𝟙 W)) (triv ef a c hc s) (k w') := by
  let φ : (Over.map (k ≫ a)).obj (Over.mk (𝟙 W')) ⟶ (Over.map a).obj (Over.mk (𝟙 W)) :=
    Over.homMk k (by simp)
  let x := (F.map (overIsoOfEq (Category.assoc (𝟙 W) a f)).hom.op).hom
    ((F.map (trivHom f a U c hc).op).hom s)
  have hn : (ef.hom.app _).hom (((restrict f F).map φ.op).hom x) =
      ((constant X M).map φ.op).hom ((ef.hom.app _).hom x) := by
    exact congrArg (fun g => g.hom x) (ef.hom.naturality φ.op)
  have h2 := congrArg (fun t => constantSections X M ((Over.map (k ≫ a)).obj (Over.mk (𝟙 W'))) t w') hn
  erw [constantSections_map] at h2
  refine Eq.trans ?_ (h2.trans ?_)
  · change constantSections X M ((Over.map (k ≫ a)).obj (Over.mk (𝟙 W')))
      ((ef.hom.app (op ((Over.map (k ≫ a)).obj (Over.mk (𝟙 W'))))).hom _) w' = _
    congr 3
    change (F.map _ ≫ F.map _).hom s = (F.map _ ≫ F.map _ ≫ F.map _).hom s
    rw [← F.map_comp, ← F.map_comp, ← F.map_comp]
    congr 2
  · rfl

theorem transition_congr {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    {a a' : W ⟶ X} {b b' : W ⟶ Y} (ha : a = a') (hb : b = b') (h : a ≫ f = b ≫ g) :
    transition ef eg a b h = transition ef eg a' b' (ha ▸ hb ▸ h) := by
  subst ha hb
  rfl

/-- If the transition on the fibre product `X ×_S Y` has trivial labels, then so has the
transition along any pair of maps `a`, `b` with `a ≫ f = b ≫ g`. -/
theorem label_transition_eq_id {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (htriv : ∀ z, label (transition ef eg (pullback.fst f g) (pullback.snd f g)
      pullback.condition).hom z = AddMonoidHom.id M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) (w : W) :
    label (transition ef eg a b h).hom w = AddMonoidHom.id M := by
  rw [transition_congr ef eg (pullback.lift_fst a b h).symm (pullback.lift_snd a b h).symm h,
    label_transition_comp ef eg _ _ pullback.condition, htriv]

theorem triv_congr {X W : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M)
    (a : W ⟶ X) {U : Over S} {c c' : W ⟶ U.left} (hcc : c = c') (hc : c ≫ U.hom = a ≫ f)
    (s : F.obj (op U)) : triv ef a c hc s = triv ef a c' (hcc ▸ hc) s := by
  subst hcc
  rfl

/-- **Well-definedness.** Let `U` be an object over `S`, `s` a section of `F` over `U`, and
suppose the transition between `ef` and `eg` has trivial labels. If `z ∈ U ×_S X` and
`z' ∈ U ×_S Y` lie over the same point of `U`, the two trivializations of `s` take the same
value at `z` and `z'`. -/
theorem triv_pullback_eq {X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (htriv : ∀ z, label (transition ef eg (pullback.fst f g) (pullback.snd f g)
      pullback.condition).hom z = AddMonoidHom.id M)
    {U : Over S} (s : F.obj (op U)) (z : ↥(pullback U.hom f)) (z' : ↥(pullback U.hom g))
    (hzz : pullback.fst U.hom f z = pullback.fst U.hom g z') :
    constantSections _ M (Over.mk (𝟙 _))
        (triv ef (pullback.snd U.hom f) (pullback.fst U.hom f) pullback.condition s) z =
      constantSections _ M (Over.mk (𝟙 _))
        (triv eg (pullback.snd U.hom g) (pullback.fst U.hom g) pullback.condition s) z' := by
  obtain ⟨ζ, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback z z' hzz
  have hP := pullback.condition (f := pullback.fst U.hom f) (g := pullback.fst U.hom g)
  have hab : (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ≫
        pullback.snd U.hom f) ≫ f =
      (pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g) ≫ pullback.snd U.hom g) ≫ g := by
    simp only [Category.assoc, ← pullback.condition]
    rw [← Category.assoc, hP, Category.assoc]
  have e1 := triv_comp_apply ef (pullback.snd U.hom f) (pullback.fst U.hom f)
    pullback.condition s (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g)) ζ
  have e2 := triv_comp_apply eg (pullback.snd U.hom g) (pullback.fst U.hom g)
    pullback.condition s (pullback.snd (pullback.fst U.hom f) (pullback.fst U.hom g)) ζ
  have e3 := triv_apply_eq_of_label ef eg _ _ hab
    (pullback.fst (pullback.fst U.hom f) (pullback.fst U.hom g) ≫ pullback.fst U.hom f)
    (by rw [Category.assoc, pullback.condition, Category.assoc]) s ζ
    (label_transition_eq_id ef eg htriv _ _ hab ζ)
  rw [h1] at e1
  rw [h2] at e2
  rw [← e1, ← e2, ← e3, triv_congr eg _ hP]

theorem triv_congr_a {X W : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M)
    {a a' : W ⟶ X} (haa : a = a') {U : Over S} (c : W ⟶ U.left) (hc : c ≫ U.hom = a ≫ f)
    (s : F.obj (op U)) : triv ef a c hc s = triv ef a' c (haa ▸ hc) s := by
  subst haa
  rfl

theorem triv_map {X W : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M)
    (a : W ⟶ X) {U U' : Over S} (φ : U' ⟶ U) (c : W ⟶ U'.left) (hc : c ≫ U'.hom = a ≫ f)
    (s : F.obj (op U)) :
    triv ef a c hc ((F.map φ.op).hom s) =
      triv ef a (c ≫ φ.left) (by rw [Category.assoc, Over.w φ, hc]) s := by
  unfold triv
  congr 1
  change (F.map _ ≫ F.map _).hom s = (F.map _).hom s
  rw [← F.map_comp]
  congr 2

theorem triv_add {X W : Scheme.{u}} {f : X ⟶ S} (ef : restrict f F ≅ constant X M)
    (a : W ⟶ X) {U : Over S} (c : W ⟶ U.left) (hc : c ≫ U.hom = a ≫ f) (s s' : F.obj (op U)) :
    triv ef a c hc (s + s') = triv ef a c hc s + triv ef a c hc s' := by
  unfold triv
  rw [map_add]
  exact map_add _ _ _

section Glue

variable {ι : Type*} {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (e : ∀ i, restrict (f i) F ≅ constant (X i) M)
  (hcov : ∀ x : S, ∃ i y, f i y = x)

/-- A section `s` over `U`, trivialized over `U ×_S X i` by `e i`, as a locally constant
function. -/
noncomputable def trivFun (i : ι) {U : Over S} (s : F.obj (op U)) :
    LocallyConstant ↥(pullback U.hom (f i)) M :=
  constantSections _ M (Over.mk (𝟙 _))
    (triv (e i) (pullback.snd U.hom (f i)) (pullback.fst U.hom (f i)) pullback.condition s)

include hcov in
theorem exists_pullback_point {U : Over S} (y : U.left) :
    ∃ i, ∃ z : ↥(pullback U.hom (f i)), pullback.fst U.hom (f i) z = y := by
  obtain ⟨i, x, hx⟩ := hcov (U.hom y)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y x hx.symm
  exact ⟨i, z, hz⟩

/-- The glued value of a section `s` over `U` at a point `y` of `U`. -/
noncomputable def glueValue {U : Over S} (s : F.obj (op U)) (y : U.left) : M :=
  trivFun e (exists_pullback_point hcov y).choose s (exists_pullback_point hcov y).choose_spec.choose

variable {e hcov}

theorem glueValue_eq
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    {U : Over S} (s : F.obj (op U)) (i : ι) (z : ↥(pullback U.hom (f i))) :
    glueValue e hcov s (pullback.fst U.hom (f i) z) = trivFun e i s z := by
  have h := (exists_pullback_point hcov (pullback.fst U.hom (f i) z)).choose_spec.choose_spec
  exact triv_pullback_eq (e _) (e i) (htriv _ i) s _ z h

theorem isLocallyConstant_glueValue [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    {U : Over S} (s : F.obj (op U)) : IsLocallyConstant (glueValue e hcov s) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  obtain ⟨i, z, hz⟩ := exists_pullback_point (f := f) hcov y
  let N : Set ↥(pullback U.hom (f i)) := (trivFun e i s) ⁻¹' {trivFun e i s z}
  have hN : IsOpen N := (trivFun e i s).isLocallyConstant.isOpen_fiber _
  refine ⟨pullback.fst U.hom (f i) '' N, (pullback.fst U.hom (f i)).isOpenMap _ hN,
    ⟨z, rfl, hz⟩, ?_⟩
  rintro _ ⟨z', hz', rfl⟩
  rw [← hz, glueValue_eq htriv, glueValue_eq htriv]
  exact hz'

theorem glueValue_add
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    {U : Over S} (s s' : F.obj (op U)) (y : U.left) :
    glueValue e hcov (s + s') y = glueValue e hcov s y + glueValue e hcov s' y := by
  obtain ⟨i, z, rfl⟩ := exists_pullback_point (f := f) hcov y
  rw [glueValue_eq htriv, glueValue_eq htriv, glueValue_eq htriv]
  simp [trivFun, triv_add]

theorem glueValue_map
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    {U U' : Over S} (φ : U' ⟶ U) (s : F.obj (op U)) (y : U'.left) :
    glueValue e hcov ((F.map φ.op).hom s) y = glueValue e hcov s (φ.left y) := by
  obtain ⟨i, z, rfl⟩ := exists_pullback_point (f := f) hcov y
  have hw : (pullback.fst U'.hom (f i) ≫ φ.left) ≫ U.hom = pullback.snd U'.hom (f i) ≫ f i := by
    rw [Category.assoc, Over.w φ, pullback.condition]
  let k := pullback.lift (pullback.fst U'.hom (f i) ≫ φ.left) (pullback.snd U'.hom (f i)) hw
  rw [glueValue_eq htriv]
  have hk : φ.left (pullback.fst U'.hom (f i) z) = pullback.fst U.hom (f i) (k z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst]
  rw [hk, glueValue_eq htriv]
  unfold trivFun
  rw [triv_map, triv_congr_a (e i) (pullback.lift_snd _ _ hw).symm,
    triv_congr (e i) _ (pullback.lift_fst _ _ hw).symm, triv_comp_apply]
  rfl

theorem glueValue_zero
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    {U : Over S} (y : U.left) : glueValue e hcov (0 : F.obj (op U)) y = 0 := by
  have := glueValue_add (e := e) (hcov := hcov) htriv (0 : F.obj (op U)) 0 y
  simpa using this

variable (e hcov) in
/-- The glued value of sections over `U`, as an additive map to locally constant functions. -/
noncomputable def glueAddHom [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (U : Over S) : F.obj (op U) →+ LocallyConstant U.left M where
  toFun s := ⟨glueValue e hcov s, isLocallyConstant_glueValue htriv s⟩
  map_zero' := by
    ext y
    exact glueValue_zero (hcov := hcov) htriv y
  map_add' s s' := by
    ext y
    exact glueValue_add (hcov := hcov) htriv s s' y

variable (e hcov) in
/-- The glued morphism from `F` to the constant sheaf, defined pointwise. -/
noncomputable def glueHom [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M) :
    F ⟶ constant S M where
  app U := AddCommGrpCat.ofHom (X := ↑(F.obj U)) (Y := ↑((constant S M).obj U))
    ((constantSections S M U.unop).symm.toAddMonoidHom.comp (glueAddHom e hcov htriv U.unop))
  naturality {U U'} φ := by
    ext s
    apply (constantSections S M U'.unop).injective
    ext y
    exact glueValue_map (hcov := hcov) htriv φ.unop s y

variable (f) in
/-- The member `U ×_S X i` of the pulled-back cover, as an object over `S`. -/
noncomputable abbrev coverObj (U : Over S) (i : ι) : Over S :=
  (Over.map (pullback.snd U.hom (f i) ≫ f i)).obj (Over.mk (𝟙 (pullback U.hom (f i))))

variable (f) in
/-- The arrow `U ×_S X i ⟶ U` of the pulled-back cover. -/
noncomputable abbrev coverArrow (U : Over S) (i : ι) : coverObj f U i ⟶ U :=
  trivHom (f i) (pullback.snd U.hom (f i)) U (pullback.fst U.hom (f i)) pullback.condition

include hcov in
theorem ofArrows_coverArrow_mem [∀ i, Etale (f i)] (U : Over S) :
    Sieve.ofArrows (coverObj f U) (coverArrow f U) ∈ (topology S) U := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  exact (Scheme.Cover.mkOfCovers ι (fun i => pullback U.hom (f i))
    (fun i => pullback.fst U.hom (f i))
    (fun y => let ⟨i, z, hz⟩ := exists_pullback_point (f := f) hcov y; ⟨i, z, hz⟩)
    (fun i => inferInstance) : Scheme.Cover (Scheme.precoverage @Etale) U.left).mem_grothendieckTopology

include hcov in
theorem isSheafFor_coverArrow [∀ i, Etale (f i)] (hF : IsEtaleSheaf F) (U : Over S) :
    Presieve.IsSheafFor (F ⋙ forget _) (Presieve.ofArrows (coverObj f U) (coverArrow f U)) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact ((isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf _ F (forget _) hF)) _ (ofArrows_coverArrow_mem (hcov := hcov) U)

theorem glueHom_app_injective [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (hF : IsEtaleSheaf F) (U : Over S) :
    Function.Injective ((glueHom e hcov htriv).app (op U)).hom := by
  intro s s' h
  have hv : ∀ y, glueValue e hcov s y = glueValue e hcov s' y := fun y => by
    have := congrArg (fun t => constantSections S M U t y) h
    simpa [glueHom, glueAddHom] using this
  refine (isSheafFor_coverArrow (hcov := hcov) hF U).isSeparatedFor.ext ?_
  rintro Y g ⟨i⟩
  have ht : triv (e i) (pullback.snd U.hom (f i)) (pullback.fst U.hom (f i))
      pullback.condition s =
        triv (e i) (pullback.snd U.hom (f i)) (pullback.fst U.hom (f i))
          pullback.condition s' := by
    apply (constantSections _ M (Over.mk (𝟙 _))).injective
    ext z
    change trivFun e i s z = trivFun e i s' z
    rw [← glueValue_eq (hcov := hcov) htriv s i z, ← glueValue_eq (hcov := hcov) htriv s' i z, hv]
  have := congrArg ((fromRestrict (e i) (pullback.snd U.hom (f i))).inv.app
    (op (Over.mk (𝟙 _)))).hom ht
  unfold triv at this
  erw [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at this
  exact this

variable (e) in
/-- The local preimage, over the cover member `U ×_S X i`, of a section `t` of the constant
sheaf over `U`. -/
noncomputable def localPreimage (U : Over S) (t : (constant S M).obj (op U)) (i : ι) :
    F.obj (op (coverObj f U i)) :=
  ((fromRestrict (e i) (pullback.snd U.hom (f i))).inv.app (op (Over.mk (𝟙 _)))).hom
    ((constantSections _ M (Over.mk (𝟙 _))).symm
      ((constantSections S M U t).comap (pullback.fst U.hom (f i)).base.hom))

theorem glueValue_localPreimage
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (U : Over S) (t : (constant S M).obj (op U)) (i : ι) (u : ↥(pullback U.hom (f i))) :
    glueValue e hcov (localPreimage e U t i) u =
      constantSections S M U t (pullback.fst U.hom (f i) u) := by
  have hw : 𝟙 (pullback U.hom (f i)) ≫ (coverObj f U i).hom =
      pullback.snd U.hom (f i) ≫ f i := by simp
  let k := pullback.lift (𝟙 (pullback U.hom (f i))) (pullback.snd U.hom (f i)) hw
  have hkf : k ≫ pullback.fst (coverObj f U i).hom (f i) = 𝟙 _ := pullback.lift_fst _ _ _
  have hks : k ≫ pullback.snd (coverObj f U i).hom (f i) = pullback.snd U.hom (f i) :=
    pullback.lift_snd _ _ _
  have hk : pullback.fst (coverObj f U i).hom (f i) (k u) = u := by
    rw [← Scheme.Hom.comp_apply, hkf]
    rfl
  rw [← hk, glueValue_eq (hcov := hcov) htriv]
  unfold trivFun
  rw [← triv_comp_apply, triv_congr_a (e i) hks, triv_congr (e i) _ hkf]
  have h1 : trivHom (f i) (pullback.snd U.hom (f i)) (coverObj f U i) (𝟙 _)
      (hkf ▸ hks ▸ (by rw [Category.assoc, pullback.condition, ← Category.assoc])) =
        𝟙 (coverObj f U i) := by
    ext
    rfl
  unfold triv
  rw [h1, op_id, F.map_id]
  erw [Iso.inv_hom_id_app_apply]
  rw [AddEquiv.apply_symm_apply, hk]
  rfl

theorem glueHom_app_surjective [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (hF : IsEtaleSheaf F) (U : Over S) :
    Function.Surjective ((glueHom e hcov htriv).app (op U)).hom := by
  intro t
  have hsh := isSheafFor_coverArrow (hcov := hcov) hF U
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  obtain ⟨s, hs, -⟩ := hsh (fun i => localPreimage e U t i) (by
    intro i j Z gi gj hij
    apply glueHom_app_injective (hcov := hcov) htriv hF Z
    apply (constantSections S M Z).injective
    ext z
    change glueValue e hcov ((F.map gi.op).hom (localPreimage e U t i)) z =
      glueValue e hcov ((F.map gj.op).hom (localPreimage e U t j)) z
    rw [glueValue_map (hcov := hcov) htriv, glueValue_map (hcov := hcov) htriv,
      glueValue_localPreimage (hcov := hcov) htriv, glueValue_localPreimage (hcov := hcov) htriv]
    have := congrArg (fun φ => φ.left z) hij
    exact congrArg (constantSections S M U t) this)
  refine ⟨s, ?_⟩
  apply (constantSections S M U).injective
  ext y
  obtain ⟨i, u, rfl⟩ := exists_pullback_point (f := f) hcov y
  have h := hs i
  change (F.map (coverArrow f U i).op).hom s = _ at h
  change glueValue e hcov s (pullback.fst U.hom (f i) u) =
    constantSections S M U t (pullback.fst U.hom (f i) u)
  calc glueValue e hcov s (pullback.fst U.hom (f i) u)
      = glueValue e hcov ((F.map (coverArrow f U i).op).hom s) u :=
        (glueValue_map (hcov := hcov) htriv (coverArrow f U i) s u).symm
    _ = glueValue e hcov (localPreimage e U t i) u := by rw [h]
    _ = _ := glueValue_localPreimage (hcov := hcov) htriv U t i u

theorem isIso_glueHom [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (hF : IsEtaleSheaf F) : IsIso (glueHom e hcov htriv) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨glueHom_app_injective htriv hF U.unop, glueHom_app_surjective htriv hF U.unop⟩

include hcov in
/-- **Gluing.** Let `F` be an étale sheaf of abelian groups on schemes over `S`, and let
`f i : X i ⟶ S` be étale morphisms jointly covering `S`, with isomorphisms
`e i : restrict (f i) F ≅ constant (X i) M`. If all transitions on the fibre products
`X i ×_S X j` have trivial labels, then `F` is isomorphic to the constant sheaf of `M`. -/
theorem nonempty_iso_constant_of_label_eq_id [∀ i, Etale (f i)]
    (htriv : ∀ i j z, label (transition (e i) (e j) (pullback.fst (f i) (f j))
      (pullback.snd (f i) (f j)) pullback.condition).hom z = AddMonoidHom.id M)
    (hF : IsEtaleSheaf F) : Nonempty (F ≅ constant S M) := by
  have := isIso_glueHom (hcov := hcov) htriv hF
  exact ⟨asIso (glueHom e hcov htriv)⟩

end Glue

end PartGlue

/-! ## Monodromy of local systems with level structure -/

section PartMonodromy

/-- **Finite congruence sets are trivial.** Let `Φ` be a finite set of automorphisms of a finitely
generated abelian group `M`, closed under composition, all congruent to the identity modulo `n`
(with `n ≥ 3` annihilating the torsion of `M`). Assuming the finite-order congruence detection
statement, every element of `Φ` is the identity. -/
theorem eq_refl_of_finite_of_trans_mem
    (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{v})
    {M : Type v} [AddCommGroup M] [AddGroup.FG M] {n : ℕ} (hn : 3 ≤ n)
    (htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0)
    {Φ : Set (M ≃+ M)} (hfin : Φ.Finite) (hmul : ∀ a ∈ Φ, ∀ b ∈ Φ, a.trans b ∈ Φ)
    (hcong : ∀ a ∈ Φ, ∀ x, ∃ y, a x = x + n • y) {a : M ≃+ M} (ha : a ∈ Φ) :
    a = AddEquiv.refl M := by
  classical
  let p : Equiv.Perm M := a.toEquiv
  have hpow : ∀ k : ℕ, ∃ b ∈ Φ, b.toEquiv = p ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨a, ha, by simp [p]⟩
    | succ k ih =>
      obtain ⟨b, hb, hbp⟩ := ih
      refine ⟨b.trans a, hmul b hb a ha, ?_⟩
      rw [pow_succ', ← hbp]
      ext x
      rfl
  choose g hg hgp using hpow
  have hnotinj : ¬ Function.Injective g := fun hinj =>
    (Set.infinite_of_injective_forall_mem hinj hg) hfin
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, g i = g j ∧ i ≠ j := by
    by_contra h
    push Not at h
    exact hnotinj h
  have hp : p ^ (i + 1) = p ^ (j + 1) := by rw [← hgp, ← hgp, hij]
  obtain ⟨r, hr, hpr⟩ : ∃ r, 0 < r ∧ p ^ r = 1 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have e : p ^ (i + 1) * p ^ (j - i) = p ^ (i + 1) * 1 := by
        rw [← pow_add, mul_one, show i + 1 + (j - i) = j + 1 by omega, hp]
      exact ⟨j - i, by omega, mul_left_cancel e⟩
    · have e : p ^ (j + 1) * p ^ (i - j) = p ^ (j + 1) * 1 := by
        rw [← pow_add, mul_one, show j + 1 + (i - j) = i + 1 by omega, hp]
      exact ⟨i - j, by omega, mul_left_cancel e⟩
  exact hFOC M n hn htors a ⟨r, hr, hpr⟩ (hcong a ha)

section Labels

variable {W : Scheme.{u}} {M : AddCommGrpCat.{v}}

/-- The label of an automorphism of a constant sheaf, as an automorphism of the group. -/
def labelEquiv (τ : constant W M ≅ constant W M) (w : W) : M ≃+ M where
  toFun := label τ.hom w
  invFun := label τ.inv w
  left_inv m := by
    rw [← AddMonoidHom.comp_apply, ← label_comp, τ.hom_inv_id, label_id]
    rfl
  right_inv m := by
    rw [← AddMonoidHom.comp_apply, ← label_comp, τ.inv_hom_id, label_id]
    rfl
  map_add' := map_add _

@[simp] theorem labelEquiv_apply (τ : constant W M ≅ constant W M) (w : W) (m : M) :
    labelEquiv τ w m = label τ.hom w m := rfl

/-- Labels do not change under specialization. -/
theorem label_eq_of_specializes {N : AddCommGrpCat.{v}} (φ : constant W M ⟶ constant W N)
    {w w' : W} (h : w' ⤳ w) : label φ w' = label φ w := by
  ext m
  exact h.mem_open ((isLocallyConstant_label φ m).isOpen_fiber _) rfl

/-- The label of the identity-on-sources isomorphism `constantCongr` is the given isomorphism. -/
theorem label_constantCongr {N : AddCommGrpCat.{v}} (c : M ≃+ N) (w : W) :
    label (constantCongr W c).hom w = c.toAddMonoidHom := by
  ext m
  rfl

end Labels

section Cocycle

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} {M : AddCommGrpCat.{v}}

/-- Cocycle identity for labels at a point. -/
theorem label_transition_trans_apply {X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {k : Z ⟶ S} (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (ek : restrict k F ≅ constant Z M) (a : W ⟶ X) (b : W ⟶ Y) (c : W ⟶ Z)
    (h : a ≫ f = b ≫ g) (h' : b ≫ g = c ≫ k) (w : W) :
    label (transition ef ek a c (h.trans h')).hom w =
      (label (transition eg ek b c h').hom w).comp (label (transition ef eg a b h).hom w) := by
  rw [← transition_trans ef eg ek a b c h h', Iso.trans_hom, label_comp]

/-- The label of a transition along `a`, `b` at `w` is the label of the transition on the fibre
product at the induced point. -/
theorem label_transition_eq_lift {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) (w : W) :
    label (transition ef eg a b h).hom w =
      label (transition ef eg (pullback.fst f g) (pullback.snd f g) pullback.condition).hom
        (pullback.lift a b h w) := by
  rw [transition_congr ef eg (pullback.lift_fst a b h).symm (pullback.lift_snd a b h).symm h,
    label_transition_comp ef eg _ _ pullback.condition]

/-- Adjusting a trivialization by an automorphism of the group composes the transition with the
corresponding constant isomorphism. -/
theorem transition_trans_constantCongr {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {N : AddCommGrpCat.{v}} (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (c : M ≃+ N) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    transition ef (eg ≪≫ constantCongr Y c) a b h =
      transition ef eg a b h ≪≫ constantCongr W c := by
  ext V : 3
  rfl

/-- Adjusting the first trivialization by an automorphism of the group. -/
theorem constantCongr_transition {X Y W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {N : AddCommGrpCat.{v}} (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y N)
    (c : M ≃+ M) (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g) :
    transition (ef ≪≫ constantCongr X c) eg a b h =
      (constantCongr W c).symm ≪≫ transition ef eg a b h := by
  ext V : 3
  rfl

theorem label_constantCongr_inv {W : Scheme.{u}} (c : M ≃+ M) (w : W) :
    label (constantCongr W c).inv w = c.symm.toAddMonoidHom := by
  ext m
  rfl

end Cocycle

section Main

variable {T : Scheme.{u}} {F : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} {M : AddCommGrpCat.{v}}
  {ι : Type*} {V : ι → Scheme.{u}} {f : ∀ i, V i ⟶ T} [∀ i, Etale (f i)]
  (e : ∀ i, restrict (f i) F ≅ constant (V i) M)

/-- Every point of `V i ×_T V j` specializes from a point lying over a generic point `η`. -/
theorem exists_generization_over {η : T} (hη : ∀ t, η ⤳ t) (i j : ι)
    (z : ↥(pullback (f i) (f j))) :
    ∃ z', z' ⤳ z ∧ f i (pullback.fst (f i) (f j) z') = η := by
  obtain ⟨z', h1, h2⟩ :=
    (Flat.generalizingMap (pullback.fst (f i) (f j) ≫ f i)) (hη ((pullback.fst (f i) (f j) ≫ f i) z))
  exact ⟨z', h1, by rw [← Scheme.Hom.comp_apply]; exact h2⟩

/-- **Step A.** The labels on the self-overlap of a member are trivial. -/
theorem label_self_eq_id (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{v})
    [AddGroup.FG M] {n : ℕ} (hn : 3 ≤ n)
    (htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0)
    (hlevel : ∀ i j (z : ↥(pullback (f i) (f j))) (m : M), ∃ y,
      label (transition (e i) (e j) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z m = m + n • y)
    {η : T} (hη : ∀ t, η ⤳ t)
    (hsub : ∀ i (v v' : V i), f i v = η → f i v' = η → v = v') (i₀ : ι)
    (hfin : (Set.range fun z : ↥(pullback (f i₀) (f i₀)) =>
      label (transition (e i₀) (e i₀) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z).Finite)
    (z : ↥(pullback (f i₀) (f i₀))) :
    label (transition (e i₀) (e i₀) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition).hom z = AddMonoidHom.id M := by
  set τ := transition (e i₀) (e i₀) (pullback.fst (f i₀) (f i₀)) (pullback.snd (f i₀) (f i₀))
    pullback.condition with hτ
  let Φ : Set (M ≃+ M) := Set.range fun z => labelEquiv τ z
  have hΦfin : Φ.Finite := by
    refine Set.Finite.of_finite_image (hfin.subset ?_) AddEquiv.toAddMonoidHom_injective.injOn
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩
  have hmul : ∀ a ∈ Φ, ∀ b ∈ Φ, a.trans b ∈ Φ := by
    rintro _ ⟨z₁, rfl⟩ _ ⟨z₂, rfl⟩
    obtain ⟨z₁', hz₁, hz₁η⟩ := exists_generization_over hη i₀ i₀ z₁
    obtain ⟨z₂', hz₂, hz₂η⟩ := exists_generization_over hη i₀ i₀ z₂
    have hmid : pullback.snd (f i₀) (f i₀) z₁' = pullback.fst (f i₀) (f i₀) z₂' := by
      apply hsub i₀ _ _ _ hz₂η
      rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hz₁η]
    obtain ⟨ζ, hζ₁, hζ₂⟩ := Scheme.Pullback.exists_preimage_pullback z₁' z₂' hmid
    set q₁ := pullback.fst (pullback.snd (f i₀) (f i₀)) (pullback.fst (f i₀) (f i₀))
    set q₂ := pullback.snd (pullback.snd (f i₀) (f i₀)) (pullback.fst (f i₀) (f i₀))
    have hq : q₁ ≫ pullback.snd (f i₀) (f i₀) = q₂ ≫ pullback.fst (f i₀) (f i₀) :=
      pullback.condition
    have h12 : (q₁ ≫ pullback.fst (f i₀) (f i₀)) ≫ f i₀ = (q₂ ≫ pullback.fst (f i₀) (f i₀)) ≫ f i₀ := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hq, Category.assoc]
    have h23 : (q₂ ≫ pullback.fst (f i₀) (f i₀)) ≫ f i₀ =
        (q₂ ≫ pullback.snd (f i₀) (f i₀)) ≫ f i₀ := by
      rw [Category.assoc, pullback.condition, Category.assoc]
    have hc := label_transition_trans_apply (e i₀) (e i₀) (e i₀) _ _ _ h12 h23 ζ
    have l12 : label (transition (e i₀) (e i₀) _ _ h12).hom ζ = label τ.hom z₁ := by
      have hl : pullback.lift (q₁ ≫ pullback.fst (f i₀) (f i₀))
          (q₂ ≫ pullback.fst (f i₀) (f i₀)) h12 = q₁ := by
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · exact (pullback.lift_snd _ _ _).trans hq.symm
      rw [label_transition_eq_lift, hl, hζ₁]
      exact label_eq_of_specializes _ hz₁
    have l23 : label (transition (e i₀) (e i₀) _ _ h23).hom ζ = label τ.hom z₂ := by
      rw [label_transition_comp, ← label_eq_of_specializes _ hz₂, hζ₂]
    refine ⟨pullback.lift (q₁ ≫ pullback.fst (f i₀) (f i₀)) (q₂ ≫ pullback.snd (f i₀) (f i₀))
      (h12.trans h23) ζ, ?_⟩
    ext m
    have := congrArg (fun φ => φ m) hc
    simp only [AddMonoidHom.comp_apply, l12, l23] at this
    rw [labelEquiv_apply, ← label_transition_eq_lift, this]
    rfl
  have hcong : ∀ a ∈ Φ, ∀ x, ∃ y, a x = x + n • y := by
    rintro _ ⟨z, rfl⟩ x
    exact hlevel i₀ i₀ z x
  have := eq_refl_of_finite_of_trans_mem hFOC hn htors hΦfin hmul hcong ⟨z, rfl⟩
  ext m
  exact congrArg (fun a => a m) this

/-- **Step B.** The labels on the overlap of `V i₀` with any member are all equal. -/
theorem label_overlap_eq (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{v})
    [AddGroup.FG M] {n : ℕ} (hn : 3 ≤ n)
    (htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0)
    (hlevel : ∀ i j (z : ↥(pullback (f i) (f j))) (m : M), ∃ y,
      label (transition (e i) (e j) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z m = m + n • y)
    {η : T} (hη : ∀ t, η ⤳ t)
    (hsub : ∀ i (v v' : V i), f i v = η → f i v' = η → v = v') (i₀ : ι)
    (hfin : (Set.range fun z : ↥(pullback (f i₀) (f i₀)) =>
      label (transition (e i₀) (e i₀) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z).Finite)
    (i : ι) (z z' : ↥(pullback (f i₀) (f i))) :
    label (transition (e i₀) (e i) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition).hom z =
    label (transition (e i₀) (e i) (pullback.fst _ _) (pullback.snd _ _)
      pullback.condition).hom z' := by
  obtain ⟨z₁, hz₁, hz₁η⟩ := exists_generization_over hη i₀ i z
  obtain ⟨z₁', hz₁', hz₁'η⟩ := exists_generization_over hη i₀ i z'
  rw [← label_eq_of_specializes _ hz₁, ← label_eq_of_specializes _ hz₁']
  have hsnd : pullback.snd (f i₀) (f i) z₁ = pullback.snd (f i₀) (f i) z₁' := by
    apply hsub i
    · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hz₁η]
    · rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, hz₁'η]
  obtain ⟨ζ, hζ₁, hζ₂⟩ := Scheme.Pullback.exists_preimage_pullback z₁ z₁' hsnd
  set q₁ := pullback.fst (pullback.snd (f i₀) (f i)) (pullback.snd (f i₀) (f i))
  set q₂ := pullback.snd (pullback.snd (f i₀) (f i)) (pullback.snd (f i₀) (f i))
  have hq : q₁ ≫ pullback.snd (f i₀) (f i) = q₂ ≫ pullback.snd (f i₀) (f i) :=
    pullback.condition
  have h12 : (q₁ ≫ pullback.fst (f i₀) (f i)) ≫ f i₀ =
      (q₂ ≫ pullback.fst (f i₀) (f i)) ≫ f i₀ := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq, Category.assoc,
      ← pullback.condition, Category.assoc]
  have h23 : (q₂ ≫ pullback.fst (f i₀) (f i)) ≫ f i₀ =
      (q₂ ≫ pullback.snd (f i₀) (f i)) ≫ f i := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hc := label_transition_trans_apply (e i₀) (e i₀) (e i) _ _ _ h12 h23 ζ
  have l12 : label (transition (e i₀) (e i₀) _ _ h12).hom ζ = AddMonoidHom.id M := by
    rw [label_transition_eq_lift]
    exact label_self_eq_id e hFOC hn htors hlevel hη hsub i₀ hfin _
  have l23 : label (transition (e i₀) (e i) _ _ h23).hom ζ =
      label (transition (e i₀) (e i) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z₁' := by
    rw [label_transition_comp, hζ₂]
  have hl : pullback.lift (q₁ ≫ pullback.fst (f i₀) (f i)) (q₂ ≫ pullback.snd (f i₀) (f i))
      (h12.trans h23) = q₁ := by
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans hq.symm
  rw [l12, l23, AddMonoidHom.comp_id, label_transition_eq_lift, hl, hζ₁] at hc
  exact hc

/-- **Monodromy theorem.** Let `η` be a generic point of `T`, let the members of an étale cover of
`T` have at most one point over `η`, let `V i₀` meet `η`, and let the labels on `V i₀ ×_T V i₀`
take finitely many values. If all transitions are congruent to the identity modulo `n ≥ 3`
(with `n` killing the torsion of `M`), then `F` is constant, assuming the finite-order congruence
detection statement. -/
theorem nonempty_iso_constant_of_level (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{v})
    [AddGroup.FG M] {n : ℕ} (hn : 3 ≤ n)
    (htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0)
    (hlevel : ∀ i j (z : ↥(pullback (f i) (f j))) (m : M), ∃ y,
      label (transition (e i) (e j) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z m = m + n • y)
    (hcov : ∀ x : T, ∃ i y, f i y = x) (hF : IsEtaleSheaf F)
    {η : T} (hη : ∀ t, η ⤳ t)
    (hsub : ∀ i (v v' : V i), f i v = η → f i v' = η → v = v') (i₀ : ι)
    (v₀ : V i₀) (hv₀ : f i₀ v₀ = η)
    (hfin : (Set.range fun z : ↥(pullback (f i₀) (f i₀)) =>
      label (transition (e i₀) (e i₀) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z).Finite) :
    Nonempty (F ≅ constant T M) := by
  classical
  let c : ι → (M ≃+ M) := fun i =>
    if h : Nonempty ↥(pullback (f i₀) (f i)) then
      labelEquiv (transition (e i₀) (e i) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition) (Classical.choice h)
    else AddEquiv.refl M
  have hc : ∀ i (z : ↥(pullback (f i₀) (f i))),
      label (transition (e i₀) (e i) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z = (c i).toAddMonoidHom := by
    intro i z
    simp only [c, dite_eq_left (⟨z⟩ : Nonempty ↥(pullback (f i₀) (f i)))]
    ext m
    simp only [labelEquiv_apply, AddEquiv.coe_toAddMonoidHom]
    exact congrArg (fun φ => φ m)
      (label_overlap_eq e hFOC hn htors hlevel hη hsub i₀ hfin i z (Classical.choice _))
  let e' : ∀ i, restrict (f i) F ≅ constant (V i) M := fun i => e i ≪≫ constantCongr (V i) (c i).symm
  refine nonempty_iso_constant_of_label_eq_id (e := e') (hcov := hcov) ?_ hF
  intro i j z
  rw [constantCongr_transition, transition_trans_constantCongr]
  simp only [Iso.trans_hom, Iso.symm_hom, label_comp, label_constantCongr_inv, label_constantCongr]
  obtain ⟨z', hz', hz'η⟩ := exists_generization_over hη i j z
  rw [← label_eq_of_specializes _ hz']
  have hpt : f i₀ v₀ = (pullback.fst (f i) (f j) ≫ f i) z' := by
    rw [hv₀, Scheme.Hom.comp_apply, hz'η]
  obtain ⟨ζ, hζ₁, hζ₂⟩ := Scheme.Pullback.exists_preimage_pullback v₀ z' hpt
  set p := pullback.snd (f i₀) (pullback.fst (f i) (f j) ≫ f i)
  have h0i : pullback.fst (f i₀) (pullback.fst (f i) (f j) ≫ f i) ≫ f i₀ =
      (p ≫ pullback.fst (f i) (f j)) ≫ f i :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  have hij : (p ≫ pullback.fst (f i) (f j)) ≫ f i = (p ≫ pullback.snd (f i) (f j)) ≫ f j := by
    rw [Category.assoc, Category.assoc]
    exact p ≫= pullback.condition
  have hcoc := label_transition_trans_apply (e i₀) (e i) (e j) _ _ _ h0i hij ζ
  rw [label_transition_comp (e i) (e j) _ _ pullback.condition, hζ₂,
    label_transition_eq_lift (e i₀) (e j), hc,
    label_transition_eq_lift (e i₀) (e i), hc] at hcoc
  ext m
  have := congrArg (fun φ => φ m) hcoc
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] at this
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddMonoidHom.id_apply,
    AddEquiv.symm_symm]
  rw [← this, AddEquiv.symm_apply_apply]

end Main

end PartMonodromy

/-! ## Refining trivializing covers over irreducible normal bases -/

section PartRefine

/-- Inside a fibre of an étale morphism there are no nontrivial specializations. -/
theorem eq_of_specializes_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] {x x' : X}
    (h : x' ⤳ x) (he : f x' = f x) : x' = x := by
  have : LocallyQuasiFinite f := Langlands.AlgebraicGeometry.locallyQuasiFinite_of_etale f
  have hd : DiscreteTopology ↥(f ⁻¹' {f x}) := (f.isDiscrete_preimage_singleton (f x)).to_subtype
  let a : ↥(f ⁻¹' {f x}) := ⟨x', he⟩
  let b : ↥(f ⁻¹' {f x}) := ⟨x, rfl⟩
  have hab : a ⤳ b := (Topology.IsInducing.subtypeVal.specializes_iff).1 h
  exact congrArg Subtype.val hab.eq

/-- An irreducible scheme étale over a scheme with generic point `η` has at most one point over
`η`. -/
theorem eq_of_apply_eq_of_etale_of_irreducible {V T : Scheme.{u}} [IrreducibleSpace V]
    (f : V ⟶ T) [Etale f] {η : T} (hη : ∀ t, η ⤳ t) {v v' : V} (hv : f v = η)
    (hv' : f v' = η) : v = v' := by
  have hξ : ∀ x : V, genericPoint V ⤳ x := genericPoint_specializes
  have hfξ : f (genericPoint V) = η := by
    have h1 : f (genericPoint V) ⤳ η := hv ▸ (hξ v).map f.continuous
    exact (h1.antisymm (hη _)).eq
  have h1 := eq_of_specializes_of_etale f (hξ v) (hfξ.trans hv.symm)
  have h2 := eq_of_specializes_of_etale f (hξ v') (hfξ.trans hv'.symm)
  exact h1.symm.trans h2

/-- If `V` is affine and maps into an affine open `U`, then `V ×_T V` is affine. -/
theorem isAffine_pullback_comp_ι {T V : Scheme.{u}} [IsAffine V] {U : T.Opens}
    (hU : IsAffineOpen U) (a : V ⟶ U.toScheme) : IsAffine (pullback (a ≫ U.ι) (a ≫ U.ι)) := by
  have : IsAffine U.toScheme := hU
  let e : pullback a a ≅ pullback (a ≫ U.ι) (a ≫ U.ι) :=
    (pullbackIsPullbackOfCompMono a a U.ι).conePointUniqueUpToIso
      (limit.isLimit (cospan (a ≫ U.ι) (a ≫ U.ι)))
  exact .of_isIso e.inv

/-- On a compact scheme, the labels of a morphism of constant sheaves with finitely generated
source group take only finitely many values. -/
theorem finite_range_label {W : Scheme.{u}} [CompactSpace W] {M N : AddCommGrpCat.{v}}
    [AddGroup.FG M] (φ : constant W M ⟶ constant W N) : (Set.range (label φ)).Finite := by
  classical
  obtain ⟨G, hG⟩ := AddGroup.FG.out (H := M)
  let ψ : W → (G → N) := fun w g => label φ w g
  have hψ : IsLocallyConstant ψ := by
    rw [IsLocallyConstant.iff_exists_open]
    intro w
    refine ⟨⋂ g : G, (fun w' => label φ w' g) ⁻¹' {label φ w g},
      isOpen_iInter_of_finite fun g => (isLocallyConstant_label φ g).isOpen_fiber _,
      Set.mem_iInter.2 fun g => rfl, fun w' hw' => funext fun g => ?_⟩
    exact Set.mem_iInter.1 hw' g
  let Λ : (M →+ N) → (G → N) := fun h g => h g
  have hΛ : Function.Injective Λ := by
    intro h₁ h₂ e
    apply AddMonoidHom.ext
    intro m
    have hm : m ∈ AddSubgroup.closure (G : Set M) := hG ▸ AddSubgroup.mem_top m
    induction hm using AddSubgroup.closure_induction with
    | mem x hx => exact congrFun e ⟨x, hx⟩
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | neg x _ hx => simp [hx]
  refine Set.Finite.of_finite_image ?_ hΛ.injOn
  convert hψ.range_finite using 1
  ext h
  simp [Λ, ψ]

section Restrict

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} {M : AddCommGrpCat.{v}}

/-- Transitions between restricted trivializations are transitions along composites. -/
theorem transition_fromRestrict {X Y X' Y' W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    (ef : restrict f F ≅ constant X M) (eg : restrict g F ≅ constant Y M)
    (a' : X' ⟶ X) (b' : Y' ⟶ Y) (a : W ⟶ X') (b : W ⟶ Y') (h : a ≫ a' ≫ f = b ≫ b' ≫ g) :
    transition (fromRestrict ef a') (fromRestrict eg b') a b h =
      transition ef eg (a ≫ a') (b ≫ b') (by simpa using h) := by
  ext V : 3
  change ((ef.inv.app _ ≫ F.map _) ≫ F.map _) ≫ F.map _ ≫ F.map _ ≫ F.map _ ≫ eg.hom.app _ =
    (ef.inv.app _ ≫ F.map _) ≫ F.map _ ≫ F.map _ ≫ eg.hom.app _
  simp only [Category.assoc]
  congr 1
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  congr 2

end Restrict

/-- **Constancy over irreducible normal bases from a level structure.** Let `T` be irreducible
with integrally closed domain stalks and `F` an étale sheaf trivialized with group `M` on an étale
cover of `T`. If all transitions are congruent to the identity modulo `n ≥ 3` (with `n` killing
the torsion of `M`), then `F` is constant, assuming the finite-order congruence detection
statement. -/
theorem nonempty_iso_constant_of_level_of_irreducible
    (hFOC : Langlands.FiniteOrderCongruenceDetectionStatement.{v})
    {T : Scheme.{u}} [IrreducibleSpace T]
    (hT : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧ IsIntegrallyClosed (T.presheaf.stalk t))
    {F : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{max u v}} (hF : IsEtaleSheaf F) {M : AddCommGrpCat.{v}}
    [AddGroup.FG M] {n : ℕ} (hn : 3 ≤ n)
    (htors : ∀ x : M, (∃ k : ℕ, 0 < k ∧ k • x = 0) → n • x = 0)
    {ι : Type*} {V : ι → Scheme.{u}} {f : ∀ i, V i ⟶ T} [∀ i, Etale (f i)]
    (hcov : ∀ x : T, ∃ i y, f i y = x) (e : ∀ i, restrict (f i) F ≅ constant (V i) M)
    (hlevel : ∀ i j (z : ↥(pullback (f i) (f j))) (m : M), ∃ y,
      label (transition (e i) (e j) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z m = m + n • y) :
    Nonempty (F ≅ constant T M) := by
  classical
  let ι' := Σ i, {W : (V i).Opens // IsAffineOpen W ∧ IsIrreducible (W : Set (V i)) ∧
    ∃ U : T.Opens, IsAffineOpen U ∧ W ≤ f i ⁻¹ᵁ U}
  let V' : ι' → Scheme.{u} := fun k => k.2.1.toScheme
  let f' : ∀ k, V' k ⟶ T := fun k => k.2.1.ι ≫ f k.1
  let e' : ∀ k, restrict (f' k) F ≅ constant (V' k) M := fun k => fromRestrict (e k.1) k.2.1.ι
  have hcov' : ∀ x : T, ∃ k y, f' k y = x := by
    intro x
    obtain ⟨i, y, rfl⟩ := hcov x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f i y)) isOpen_univ
    obtain ⟨hCirr, hCopen⟩ :=
      EtaleNormalLocallyIrreducible.isIrreducible_connectedComponent_of_etale (f i) hT y
    let O : (V i).Opens := ⟨connectedComponent y ∩ (f i ⁻¹ᵁ U : Set (V i)),
      hCopen.inter (f i ⁻¹ᵁ U).2⟩
    have hyO : y ∈ O := ⟨mem_connectedComponent, hxU⟩
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWO⟩ :=
      (V i).isBasis_affineOpens.exists_subset_of_mem_open hyO O.2
    have hWirr : IsIrreducible (W : Set (V i)) :=
      ⟨⟨y, hyW⟩, hCirr.2.open_subset W.2 (hWO.trans Set.inter_subset_left)⟩
    exact ⟨⟨i, W, hW, hWirr, U, hU, fun z hz => (hWO hz).2⟩, ⟨y, hyW⟩, rfl⟩
  have hlevel' : ∀ k k' (z : ↥(pullback (f' k) (f' k'))) (m : M), ∃ y,
      label (transition (e' k) (e' k') (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z m = m + n • y := by
    intro k k' z m
    rw [transition_fromRestrict, label_transition_eq_lift]
    exact hlevel _ _ _ m
  have hη : ∀ t, genericPoint T ⤳ t := genericPoint_specializes
  have hsub : ∀ k (v v' : V' k), f' k v = genericPoint T → f' k v' = genericPoint T → v = v' := by
    intro k v v' hv hv'
    have : IrreducibleSpace (V' k) := Subtype.irreducibleSpace k.2.2.2.1
    exact eq_of_apply_eq_of_etale_of_irreducible (f' k) hη hv hv'
  obtain ⟨k₀, v₀, hv₀⟩ := hcov' (genericPoint T)
  have hfin : (Set.range fun z : ↥(pullback (f' k₀) (f' k₀)) =>
      label (transition (e' k₀) (e' k₀) (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition).hom z).Finite := by
    obtain ⟨U, hU, hWU⟩ := k₀.2.2.2.2
    have : IsAffine (V' k₀) := k₀.2.2.1
    have hrange : Set.range (f' k₀) ⊆ Set.range U.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hWU z.2
    let a : V' k₀ ⟶ U.toScheme := IsOpenImmersion.lift U.ι (f' k₀) hrange
    have ha : f' k₀ = a ≫ U.ι := (IsOpenImmersion.lift_fac _ _ _).symm
    have : CompactSpace ↥(pullback (f' k₀) (f' k₀)) := by
      have := isAffine_pullback_comp_ι hU a
      rw [ha]
      infer_instance
    exact finite_range_label _
  exact nonempty_iso_constant_of_level e' hFOC hn htors hlevel' hcov' hF hη hsub k₀ v₀ hv₀ hfin

end PartRefine

end Langlands.AlgebraicGeometry.EtaleLocalSystem
