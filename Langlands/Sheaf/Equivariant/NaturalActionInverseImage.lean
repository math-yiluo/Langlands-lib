import Langlands.Sheaf.Equivariant.NaturalActionSheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Adjunction.Restrict
import Langlands.Sheaf.Equivariant.TwistedOver
import Mathlib.CategoryTheory.Limits.Final

/-!
# The inverse image along a natural action

Let a group `K` act naturally along a functor `Φ : E ⥤ T`. The functor
`F ↦ (V ↦ F(Φ V)^K)` from module presheaves on `T` to module presheaves on `E` has a left
adjoint, the inverse image. It is the left Kan extension along the inflation
`E × SingleObj Kᵐᵒᵖ ⥤ T` of `Φ`, which also sends the elements of `K` to the actions. Its
value at `U` is a colimit of the values `Q(V)` over the arrows `U ⟶ Φ V` of `T`, where two
such arrows are compared through the morphisms of `E` and the action of `K`. Sheafifying
gives a left adjoint to the presheaf of invariant sections of a sheaf. For continuous `Φ`,
its restriction to sheaves on `E` is left adjoint to the sheaf of invariant sections.

For a `G`-space `X`, this is Berkovich's inverse image `b^*` along `b : X → X(G)` (§1.2,
proof of Theorem 1.4.2); see `AnalyticInverseImage`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Prod

universe v u vE uE uK uR w vC uC uG

variable {T : Type u} [Category.{v} T] {E : Type uE} [Category.{vE} E]

namespace NaturalAction

section Inflation

variable {K : Type uK} [Monoid K] {Φ : E ⥤ T} (a : NaturalAction K Φ)

theorem act_one_unop (V : E) : (a.act V 1).unop = 𝟙 (Φ.obj V) := by
  rw [map_one]
  rfl

theorem act_mul_unop (V : E) (k l : K) :
    (a.act V (k * l)).unop = (a.act V k).unop ≫ (a.act V l).unop := by
  rw [map_mul]
  rfl

/-- The inflation of `Φ` along the action: the functor `E × SingleObj Kᵐᵒᵖ ⥤ T` sending
`(V, ⋆)` to `Φ V` and a morphism `(f, k)` from `(V, ⋆)` to `(W, ⋆)` to `Φ f` followed by the
action of `k` on `Φ W`. -/
def inflation : E × SingleObj Kᵐᵒᵖ ⥤ T where
  obj V := Φ.obj V.1
  map {_ W} f := Φ.map f.1 ≫ (a.act W.1 (MulOpposite.unop f.2)).unop
  map_id V := by
    change Φ.map (𝟙 V.1) ≫ (a.act V.1 (MulOpposite.unop 1)).unop = 𝟙 _
    rw [Φ.map_id, MulOpposite.unop_one, act_one_unop, Category.comp_id]
  map_comp {_ V W} f g := by
    change Φ.map (f.1 ≫ g.1) ≫ (a.act W.1 (MulOpposite.unop (f.2 ≫ g.2))).unop =
      (Φ.map f.1 ≫ (a.act V.1 (MulOpposite.unop f.2)).unop) ≫
        Φ.map g.1 ≫ (a.act W.1 (MulOpposite.unop g.2)).unop
    rw [SingleObj.comp_as_mul, MulOpposite.unop_mul, act_mul_unop, Φ.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% (a.comm g.1 (MulOpposite.unop f.2))]

@[simp]
theorem inflation_obj (V : E × SingleObj Kᵐᵒᵖ) : a.inflation.obj V = Φ.obj V.1 :=
  rfl

theorem inflation_map {V W : E × SingleObj Kᵐᵒᵖ} (f : V ⟶ W) :
    a.inflation.map f = Φ.map f.1 ≫ (a.act W.1 (MulOpposite.unop f.2)).unop :=
  rfl

/-- The inflation restricts to `Φ` on the objects `(V, ⋆)` and the morphisms `(f, 1)`. -/
def sectInflationIso : Prod.sectL E (SingleObj.star Kᵐᵒᵖ) ⋙ a.inflation ≅ Φ :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun f => by
    change (Φ.map f ≫ (a.act _ (MulOpposite.unop 1)).unop) ≫ 𝟙 _ = 𝟙 _ ≫ Φ.map f
    rw [MulOpposite.unop_one, act_one_unop, Category.comp_id, Category.comp_id,
      Category.id_comp]

/-- An element of `K`, as an endomorphism of the object of `SingleObj Kᵐᵒᵖ`. -/
abbrev starHom (k : K) : SingleObj.star Kᵐᵒᵖ ⟶ SingleObj.star Kᵐᵒᵖ :=
  MulOpposite.op k

variable (E K) in
/-- The action of `K` on the objects `(V, ⋆)` of `E × SingleObj Kᵐᵒᵖ`, by the morphisms
`(𝟙 V, k)`. -/
def sectAction : NaturalAction K (Prod.sectL E (SingleObj.star Kᵐᵒᵖ)) where
  act V :=
    { toFun := fun k => MulOpposite.op
        (𝟙 V ×ₘ starHom k)
      map_one' := rfl
      map_mul' := fun k l => by
        apply MulOpposite.unop_injective
        change _ = (𝟙 V ×ₘ starHom k) ≫
          (𝟙 V ×ₘ starHom l)
        rw [prod_comp, Category.comp_id]
        rfl }
  comm {V W} f k := by
    change (𝟙 V ×ₘ starHom k) ≫
        (f ×ₘ 𝟙 (SingleObj.star Kᵐᵒᵖ)) =
      (f ×ₘ 𝟙 (SingleObj.star Kᵐᵒᵖ)) ≫
        (𝟙 W ×ₘ starHom k)
    rw [prod_comp, prod_comp, Category.id_comp, Category.comp_id, Category.id_comp,
      Category.comp_id]

theorem sectAction_act_unop (V : E) (k : K) :
    ((sectAction E K).act V k).unop =
      (𝟙 V ×ₘ starHom k) :=
  rfl

/-- Every morphism of `E × SingleObj Kᵐᵒᵖ` is a morphism `(f, 1)` followed by the action of
an element of `K`. -/
theorem prod_hom_eq_sectL_map_comp {V W : E}
    (f : V ⟶ W) (k : SingleObj.star Kᵐᵒᵖ ⟶ SingleObj.star Kᵐᵒᵖ) :
    (f ×ₘ k : (V, SingleObj.star Kᵐᵒᵖ) ⟶ (W, SingleObj.star Kᵐᵒᵖ)) =
      (Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map f ≫
        ((sectAction E K).act W (MulOpposite.unop k)).unop := by
  change _ = (f ×ₘ 𝟙 (SingleObj.star Kᵐᵒᵖ)) ≫ (𝟙 W ×ₘ k)
  rw [prod_comp, Category.comp_id, Category.id_comp]

/-- The inflation sends a morphism `(f, 1)` to `Φ f`. -/
theorem inflation_map_sectL {V W : E} (f : V ⟶ W) :
    a.inflation.map ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map f) = Φ.map f := by
  change Φ.map f ≫ (a.act W (MulOpposite.unop 1)).unop = _
  rw [MulOpposite.unop_one, act_one_unop, Category.comp_id]

/-- The inflation sends the action on `(V, ⋆)` to the action on `Φ V`. -/
theorem inflation_map_sectAction (V : E) (k : K) :
    a.inflation.map ((sectAction E K).act V k).unop = (a.act V k).unop := by
  change Φ.map (𝟙 V) ≫ (a.act V (MulOpposite.unop (MulOpposite.op k))).unop = _
  rw [Φ.map_id, Category.id_comp, MulOpposite.unop_op]

end Inflation

section ActIso

variable {K : Type uK} [Group K] {Φ : E ⥤ T} (a : NaturalAction K Φ)

/-- For a group `K`, the action of `k` on `Φ V` is an isomorphism. -/
@[simps]
def actIso (V : E) (k : K) : Φ.obj V ≅ Φ.obj V where
  hom := (a.act V k).unop
  inv := (a.act V k⁻¹).unop
  hom_inv_id := by rw [← act_mul_unop, mul_inv_cancel, act_one_unop]
  inv_hom_id := by rw [← act_mul_unop, inv_mul_cancel, act_one_unop]

end ActIso

section Adjunction

variable (R : Type uR) [CommRing R]

variable (E) (K : Type uK) [Group K]

/-- Pulling a presheaf on `E` back to `E × SingleObj Kᵐᵒᵖ`, where `K` acts trivially, is left
adjoint to taking the `K`-invariant sections over the objects `(V, ⋆)`. -/
def sectPullbackAdjunction :
    (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj
        (CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)).op ⊣
      (sectAction E K).invariantFunctor R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun Q P =>
        { toFun := fun φ =>
            { app := fun V => ModuleCat.ofHom (LinearMap.codRestrict _
                (φ.app (op (V.unop, SingleObj.star Kᵐᵒᵖ))).hom fun q k => by
                  have h := NatTrans.naturality_apply φ
                    ((sectAction E K).act V.unop k).unop.op q
                  refine h.symm.trans ?_
                  change (φ.app (op (V.unop, SingleObj.star Kᵐᵒᵖ))).hom
                    ((Q.map (𝟙 V.unop).op).hom q) = _
                  rw [op_id, Q.map_id]
                  rfl)
              naturality := fun V W f => by
                ext q
                apply Subtype.ext
                exact NatTrans.naturality_apply φ
                  ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map f.unop).op q }
          invFun := fun ψ =>
            { app := fun V => ψ.app (op V.unop.1) ≫
                ((sectAction E K).invariantPresheafι R P).app (op V.unop.1)
              naturality := fun V W g => by
                ext q
                change ((ψ.app (op W.unop.1)).hom ((Q.map g.unop.1.op).hom q)).1 =
                  (P.map g).hom ((ψ.app (op V.unop.1)).hom q).1
                have h1 : ((ψ.app (op W.unop.1)).hom ((Q.map g.unop.1.op).hom q)).1 =
                    (P.map ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map g.unop.1).op).hom
                      ((ψ.app (op V.unop.1)).hom q).1 :=
                  congrArg Subtype.val (NatTrans.naturality_apply ψ g.unop.1.op q)
                refine h1.trans ?_
                have hg : P.map g = P.map ((sectAction E K).act V.unop.1
                    (MulOpposite.unop g.unop.2)).unop.op ≫
                    P.map ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map g.unop.1).op := by
                  rw [← P.map_comp, ← op_comp, ← prod_hom_eq_sectL_map_comp]
                  rfl
                have hs := ((ψ.app (op V.unop.1)).hom q).2 (MulOpposite.unop g.unop.2)
                rw [hg]
                exact congrArg (fun t => (P.map ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map
                  g.unop.1).op).hom t) hs.symm }
          left_inv := fun φ => by
            ext V q
            rfl
          right_inv := fun ψ => by
            ext V q
            rfl }
      homEquiv_naturality_left_symm := fun f ψ => by
        ext V q
        rfl
      homEquiv_naturality_right := fun φ g => by
        ext V q
        rfl }

variable {E K} {Φ : E ⥤ T} (a : NaturalAction K Φ)

/-- The invariant sections of a presheaf `F` on `T`, as an invariant presheaf on
`E × SingleObj Kᵐᵒᵖ` along the inflation, are the invariant sections along `Φ`. -/
theorem invariants_inflation_eq (F : Tᵒᵖ ⥤ ModuleCat.{w} R) (V : E) :
    (actionRepresentation (a.inflation.op ⋙ F) ((sectAction E K).act V)).invariants =
      (actionRepresentation F (a.act V)).invariants := by
  ext s
  change (∀ k, (F.map (a.inflation.map ((sectAction E K).act V k).unop).op).hom s = s) ↔
    ∀ k, (F.map (a.act V k).unop.op).hom s = s
  simp only [inflation_map_sectAction]
  exact Iff.rfl

/-- Taking invariant sections along `Φ` factors through the restriction to
`E × SingleObj Kᵐᵒᵖ` along the inflation. -/
def inflationInvariantIso :
    (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj a.inflation.op ⋙
        (sectAction E K).invariantFunctor R ≅ a.invariantFunctor R :=
  NatIso.ofComponents
    (fun F => NatIso.ofComponents
      (fun V => (LinearEquiv.ofEq _ _ (a.invariants_inflation_eq R F V.unop)).toModuleIso)
      fun f => by
        ext s
        apply Subtype.ext
        change (F.map (a.inflation.map ((Prod.sectL E (SingleObj.star Kᵐᵒᵖ)).map f.unop)).op).hom
          s.1 = (F.map (Φ.map f.unop).op).hom s.1
        rw [inflation_map_sectL]
        rfl)
    fun φ => by
      ext V s
      rfl

end Adjunction

section InverseImage

variable {K : Type uK} [Group K] {Φ : E ⥤ T} (a : NaturalAction K Φ)
variable (R : Type uR) [CommRing R]
variable [∀ F : (E × SingleObj Kᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{w} R, a.inflation.op.HasLeftKanExtension F]

/-- The inverse image of module presheaves on `E` to module presheaves on `T`: the left Kan
extension along the inflation of the pullback to `E × SingleObj Kᵐᵒᵖ` with trivial
action. -/
def inverseImagePresheafFunctor : (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ (Tᵒᵖ ⥤ ModuleCat.{w} R) :=
  (Functor.whiskeringLeft _ _ (ModuleCat.{w} R)).obj
      (CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)).op ⋙
    Functor.lan (H := ModuleCat.{w} R) a.inflation.op

/-- The inverse image is left adjoint to the presheaf of invariant sections. -/
def inverseImagePresheafAdjunction :
    a.inverseImagePresheafFunctor R ⊣ a.invariantFunctor R :=
  ((sectPullbackAdjunction E R K).comp
    (a.inflation.op.lanAdjunction (ModuleCat.{w} R))).ofNatIsoRight (a.inflationInvariantIso R)

/-- The value of the inverse image at `U` is the colimit of the values `Q(V)` over the
comma category of arrows `U ⟶ Φ V` along the inflation. -/
def inverseImagePresheafObjIsoColimit (Q : Eᵒᵖ ⥤ ModuleCat.{w} R)
    [a.inflation.op.HasPointwiseLeftKanExtension
      ((CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)).op ⋙ Q)] (U : T) :
    ((a.inverseImagePresheafFunctor R).obj Q).obj (op U) ≅
      colimit (CostructuredArrow.proj a.inflation.op (op U) ⋙
        (CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)).op ⋙ Q) :=
  a.inflation.op.leftKanExtensionObjIsoColimit
    ((CategoryTheory.Prod.fst E (SingleObj Kᵐᵒᵖ)).op ⋙ Q) (op U)

variable (J : GrothendieckTopology T) [HasSheafify J (ModuleCat.{w} R)]

/-- The inverse image of module presheaves on `E` to module sheaves on `T`: the
sheafification of the inverse image presheaf. -/
def inverseImageFunctor : (Eᵒᵖ ⥤ ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  a.inverseImagePresheafFunctor R ⋙ presheafToSheaf J (ModuleCat.{w} R)

/-- The inverse image to sheaves is left adjoint to the presheaf of invariant sections. -/
def inverseImageAdjunction : a.inverseImageFunctor R J ⊣ a.sheafInvariantFunctor R J :=
  (a.inverseImagePresheafAdjunction R).comp (sheafificationAdjunction J (ModuleCat.{w} R))

variable (JE : GrothendieckTopology E) [Φ.IsContinuous JE J]

/-- The inverse image of module sheaves on `E` to module sheaves on `T`. -/
def sheafInverseImageFunctor : Sheaf JE (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R) :=
  sheafToPresheaf JE (ModuleCat.{w} R) ⋙ a.inverseImageFunctor R J

/-- For continuous `Φ`, the inverse image of sheaves is left adjoint to the sheaf of invariant
sections. -/
def sheafInverseImageAdjunction :
    a.sheafInverseImageFunctor R J JE ⊣ a.sheafInvariantSheafFunctor R J JE :=
  (a.inverseImageAdjunction R J).restrictFullyFaithful
    (iC := sheafToPresheaf JE (ModuleCat.{w} R)) (iD := 𝟭 _)
    (fullyFaithfulSheafToPresheaf JE (ModuleCat.{w} R)) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (a.sheafInvariantSheafFunctorCompIso R J JE).symm)

end InverseImage

section Untwisted

/-! ### Untwisted arrows

Suppose that `Φ` is the composite of a functor `Ψ : E ⥤ P.Over ⊤ X` with the inclusion into
the twisted category, and that the action of `k` has twist `k⁻¹`. Then the comma category of
the arrows `U ⟶ Φ V` along the inflation is equivalent to the comma category of the arrows
`U ⟶ Ψ V` over `X`, so the inverse image is computed by the colimit over untwisted arrows. -/

variable {C : Type uC} [Category.{vC} C] {P : MorphismProperty C} {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X} {Ψ : E ⥤ P.Over ⊤ X}
variable (a : NaturalAction G (Ψ ⋙ TwistedOver.ι P ρ))

/-- If the action of `k` has twist `k⁻¹`, the image under the inflation of a morphism
`(f, k)` has twist `k⁻¹`. -/
theorem twist_inflation_map (htw : ∀ V k, TwistedOver.Hom.twist (a.act V k).unop = k⁻¹)
    {V W : E × SingleObj Gᵐᵒᵖ} (f : V ⟶ W) :
    TwistedOver.Hom.twist (a.inflation.map f) = (MulOpposite.unop f.2)⁻¹ := by
  rw [inflation_map, TwistedOver.comp_twist, htw, Functor.comp_map, TwistedOver.ι_map_twist,
    mul_one]

/-- The comparison functor from the comma category of arrows `U ⟶ Ψ V` over `X` to the comma
category of arrows `U ⟶ Φ V` along the inflation: `(V, h) ↦ ((V, ⋆), h)`. -/
@[simps]
def untwistedArrowsFunctor (U : P.Over ⊤ X) :
    CostructuredArrow Ψ.op (op U) ⥤
      CostructuredArrow a.inflation.op (op ((TwistedOver.ι P ρ).obj U)) where
  obj Y := CostructuredArrow.mk (Y := op (Y.left.unop, SingleObj.star Gᵐᵒᵖ))
    ((TwistedOver.ι P ρ).map Y.hom.unop).op
  map {Y Y'} g := CostructuredArrow.homMk
    ((Prod.sectL E (SingleObj.star Gᵐᵒᵖ)).map g.left.unop).op (by
      apply Quiver.Hom.unop_inj
      change (TwistedOver.ι P ρ).map Y'.hom.unop ≫
          a.inflation.map ((Prod.sectL E (SingleObj.star Gᵐᵒᵖ)).map g.left.unop) =
        (TwistedOver.ι P ρ).map Y.hom.unop
      rw [inflation_map_sectL]
      change (TwistedOver.ι P ρ).map Y'.hom.unop ≫
          (TwistedOver.ι P ρ).map (Ψ.map g.left.unop) = _
      rw [← Functor.map_comp]
      exact congrArg (fun h => (TwistedOver.ι P ρ).map h.unop) (CostructuredArrow.w g))
  map_id Y := CostructuredArrow.hom_ext _ _ (by
    apply Quiver.Hom.unop_inj
    exact (Prod.sectL E (SingleObj.star Gᵐᵒᵖ)).map_id _)
  map_comp f g := CostructuredArrow.hom_ext _ _ (by
    apply Quiver.Hom.unop_inj
    exact (Prod.sectL E (SingleObj.star Gᵐᵒᵖ)).map_comp _ _)

theorem untwistedArrowsFunctor_faithful (U : P.Over ⊤ X) :
    (a.untwistedArrowsFunctor U).Faithful where
  map_injective {_ _} g g' h := CostructuredArrow.hom_ext _ _ (by
    have := congrArg (fun φ => φ.left.unop.1) h
    exact Quiver.Hom.unop_inj this)

variable (htw : ∀ V k, TwistedOver.Hom.twist (a.act V k).unop = k⁻¹)

include htw in
theorem untwistedArrowsFunctor_full (U : P.Over ⊤ X) : (a.untwistedArrowsFunctor U).Full where
  map_surjective {Y Y'} φ := by
    have hw := congrArg Quiver.Hom.unop (CostructuredArrow.w φ)
    change (TwistedOver.ι P ρ).map Y'.hom.unop ≫ a.inflation.map φ.left.unop =
      (TwistedOver.ι P ρ).map Y.hom.unop at hw
    have h2 : φ.left.unop.2 = 𝟙 _ := by
      have ht : (MulOpposite.unop φ.left.unop.2)⁻¹ = 1 :=
        (a.twist_inflation_map htw φ.left.unop).symm.trans
          ((mul_one _).symm.trans (congrArg TwistedOver.Hom.twist hw))
      apply MulOpposite.unop_injective
      exact inv_eq_one.mp ht
    have hp : a.inflation.map φ.left.unop =
        (TwistedOver.ι P ρ).map (Ψ.map φ.left.unop.1) := by
      rw [inflation_map, h2]
      exact (congrArg _ (a.act_one_unop _)).trans (Category.comp_id _)
    refine ⟨CostructuredArrow.homMk φ.left.unop.1.op ?_, ?_⟩
    · apply Quiver.Hom.unop_inj
      apply (TwistedOver.ι P ρ).map_injective
      refine ((TwistedOver.ι P ρ).map_comp Y'.hom.unop (Ψ.map φ.left.unop.1)).trans ?_
      refine Eq.trans ?_ hw
      exact congrArg (fun x => (TwistedOver.ι P ρ).map Y'.hom.unop ≫ x) hp.symm
    · exact CostructuredArrow.hom_ext _ _
        (Quiver.Hom.unop_inj (CategoryTheory.Prod.hom_ext rfl h2.symm))

include htw in
theorem untwistedArrowsFunctor_essSurj (U : P.Over ⊤ X) :
    (a.untwistedArrowsFunctor U).EssSurj where
  mem_essImage Z := by
    obtain ⟨h₀, hh₀⟩ := TwistedOver.exists_ι_map_of_twist_eq_one (P := P) (ρ := ρ) (U := U)
      (V := Ψ.obj Z.left.unop.1)
      (Z.hom.unop ≫ (a.act Z.left.unop.1 (TwistedOver.Hom.twist Z.hom.unop)).unop)
      ((congrArg (· * TwistedOver.Hom.twist Z.hom.unop) (htw _ _)).trans (inv_mul_cancel _))
    exact ⟨CostructuredArrow.mk (Y := op Z.left.unop.1) h₀.op,
      ⟨CostructuredArrow.isoMk
        ((sectAction E G).actIso Z.left.unop.1 (TwistedOver.Hom.twist Z.hom.unop)).op (by
          apply Quiver.Hom.unop_inj
          have h1 := a.inflation_map_sectAction Z.left.unop.1 (TwistedOver.Hom.twist Z.hom.unop)
          exact (congrArg (fun x => Z.hom.unop ≫ x) h1).trans hh₀.symm)⟩⟩

include htw in
/-- If the action of `k` has twist `k⁻¹`, the comparison functor from untwisted arrows is an
equivalence. -/
theorem untwistedArrowsFunctor_isEquivalence (U : P.Over ⊤ X) :
    (a.untwistedArrowsFunctor U).IsEquivalence where
  faithful := a.untwistedArrowsFunctor_faithful U
  full := a.untwistedArrowsFunctor_full htw U
  essSurj := a.untwistedArrowsFunctor_essSurj htw U

variable (R : Type uR) [CommRing R]
variable [∀ F : (E × SingleObj Gᵐᵒᵖ)ᵒᵖ ⥤ ModuleCat.{w} R, a.inflation.op.HasLeftKanExtension F]

/-- If the action of `k` has twist `k⁻¹`, the value of the inverse image at an object `U` of
`P.Over ⊤ X` is the colimit of the values `Q(V)` over the comma category of arrows `U ⟶ Ψ V`
over `X`. -/
def inverseImagePresheafObjIsoUntwistedColimit (Q : Eᵒᵖ ⥤ ModuleCat.{w} R)
    [a.inflation.op.HasPointwiseLeftKanExtension
      ((CategoryTheory.Prod.fst E (SingleObj Gᵐᵒᵖ)).op ⋙ Q)]
    (U : P.Over ⊤ X) [HasColimit (CostructuredArrow.proj Ψ.op (op U) ⋙ Q)] :
    ((a.inverseImagePresheafFunctor R).obj Q).obj (op ((TwistedOver.ι P ρ).obj U)) ≅
      colimit (CostructuredArrow.proj Ψ.op (op U) ⋙ Q) :=
  haveI := a.untwistedArrowsFunctor_isEquivalence htw U
  a.inverseImagePresheafObjIsoColimit R Q _ ≪≫
    (Functor.Final.colimitIso (a.untwistedArrowsFunctor U) _).symm

end Untwisted

end NaturalAction

end Langlands.Sheaf.Equivariant
