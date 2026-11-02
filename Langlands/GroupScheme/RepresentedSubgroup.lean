import Langlands.GroupScheme.SubgroupFunctor

/-! # Points of representing group schemes, and homomorphisms between them -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S} {F : SubgroupFunctor G} {i : H ⟶ G}

namespace IsRepresentedBy

/-- The points of `H` over `T`, mapped to `G` along `i`, as points of `F`. -/
def pointsHom (hi : F.IsRepresentedBy i) (T : Over S) : (T ⟶ H.X) →* F.carrier T where
  toFun x := ⟨x ≫ i.hom.hom, by rw [← hi.2]; exact ⟨x, rfl⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' x y := Subtype.ext (MonObj.mul_comp x y _)

/-- If `i : H ⟶ G` represents `F`, then the points of `H` over `T` are the points of `F`. -/
def pointsEquiv (hi : F.IsRepresentedBy i) (T : Over S) : (T ⟶ H.X) ≃* F.carrier T :=
  MulEquiv.ofBijective (pointsHom hi T)
    ⟨fun x y h => hi.1.right_cancellation x y (congrArg Subtype.val h), fun x => by
      have hx : (x : T ⟶ G.X) ∈ (range i).carrier T := by rw [hi.2]; exact x.2
      obtain ⟨y, hy⟩ := hx
      exact ⟨y, Subtype.ext hy⟩⟩

@[simp] theorem pointsEquiv_apply_coe (hi : F.IsRepresentedBy i) {T : Over S} (x : T ⟶ H.X) :
    (hi.pointsEquiv T x : T ⟶ G.X) = x ≫ i.hom.hom :=
  rfl

theorem pointsEquiv_symm_comp (hi : F.IsRepresentedBy i) {T : Over S} (x : F.carrier T) :
    (hi.pointsEquiv T).symm x ≫ i.hom.hom = x :=
  congrArg Subtype.val ((hi.pointsEquiv T).apply_symm_apply x)

theorem pointsEquiv_comp (hi : F.IsRepresentedBy i) {T T' : Over S} (a : T' ⟶ T)
    (x : T ⟶ H.X) :
    hi.pointsEquiv T' (a ≫ x) = ⟨a ≫ (hi.pointsEquiv T x : T ⟶ G.X), F.comp_mem a (hi.pointsEquiv T x).2⟩ :=
  Subtype.ext (Category.assoc _ _ _)

variable {G' H' : GroupScheme S} {K : SubgroupFunctor G'} {j : H' ⟶ G'}

/-- A family of homomorphisms between the points of two represented subgroup functors, natural
in the test scheme, as a natural transformation of the group-valued point functors of the
representing group schemes. -/
def pointsNatTrans (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (φ : ∀ T : Over S, F.carrier T →* K.carrier T)
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : F.carrier T),
      (φ T' ⟨a ≫ (x : T ⟶ G.X), F.comp_mem a x.2⟩ : T' ⟶ G'.X) = a ≫ (φ T x : T ⟶ G'.X)) :
    yonedaGrp.obj H ⟶ yonedaGrp.obj H' where
  app T := GrpCat.ofHom (((hj.pointsEquiv T.unop).symm.toMonoidHom.comp (φ T.unop)).comp
    (hi.pointsEquiv T.unop).toMonoidHom)
  naturality {T T'} a := by
    have key : ∀ y : T.unop ⟶ H.X,
        (hj.pointsEquiv T'.unop).symm (φ T'.unop (hi.pointsEquiv T'.unop (a.unop ≫ y))) =
          a.unop ≫ (hj.pointsEquiv T.unop).symm (φ T.unop (hi.pointsEquiv T.unop y)) := by
      intro y
      apply (hj.pointsEquiv T'.unop).injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply, pointsEquiv_comp, pointsEquiv_comp, MulEquiv.apply_symm_apply]
      exact hφ a.unop _
    ext x
    exact key x

/-- The homomorphism of group schemes `H ⟶ H'` induced by a natural family of homomorphisms
between the points of the represented subgroup functors. -/
def lift (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (φ : ∀ T : Over S, F.carrier T →* K.carrier T)
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : F.carrier T),
      (φ T' ⟨a ≫ (x : T ⟶ G.X), F.comp_mem a x.2⟩ : T' ⟶ G'.X) = a ≫ (φ T x : T ⟶ G'.X)) :
    H ⟶ H' :=
  yonedaGrpFullyFaithful.preimage (pointsNatTrans hi hj φ hφ)

/-- On points, `lift` is the given family of homomorphisms. -/
theorem pointsEquiv_lift (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (φ : ∀ T : Over S, F.carrier T →* K.carrier T)
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : F.carrier T),
      (φ T' ⟨a ≫ (x : T ⟶ G.X), F.comp_mem a x.2⟩ : T' ⟶ G'.X) = a ≫ (φ T x : T ⟶ G'.X))
    {T : Over S} (x : T ⟶ H.X) :
    hj.pointsEquiv T (x ≫ (lift hi hj φ hφ).hom.hom) = φ T (hi.pointsEquiv T x) := by
  have h := congrArg (fun α : yonedaGrp.obj H ⟶ yonedaGrp.obj H' => (α.app (op T)).hom x)
    (yonedaGrpFullyFaithful.map_preimage (pointsNatTrans hi hj φ hφ))
  change x ≫ (lift hi hj φ hφ).hom.hom =
    (hj.pointsEquiv T).symm (φ T (hi.pointsEquiv T x)) at h
  rw [h, MulEquiv.apply_symm_apply]

theorem lift_comp (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (φ : ∀ T : Over S, F.carrier T →* K.carrier T)
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : F.carrier T),
      (φ T' ⟨a ≫ (x : T ⟶ G.X), F.comp_mem a x.2⟩ : T' ⟶ G'.X) = a ≫ (φ T x : T ⟶ G'.X))
    {T : Over S} (x : T ⟶ H.X) :
    (x ≫ (lift hi hj φ hφ).hom.hom) ≫ j.hom.hom = (φ T (hi.pointsEquiv T x) : T ⟶ G'.X) :=
  congrArg Subtype.val (pointsEquiv_lift hi hj φ hφ x)

/-- Two homomorphisms into a representing group scheme are equal when they agree after the
inclusion. -/
theorem hom_ext {H'' : GroupScheme S} (hj : K.IsRepresentedBy j) {f f' : H'' ⟶ H'}
    (h : f ≫ j = f' ≫ j) : f = f' := by
  have hm : Mono j.hom.hom := hj.1
  apply (Grp.forget (Over S)).map_injective
  apply hm.right_cancellation
  have h' := congrArg (Grp.forget (Over S)).map h
  rw [Functor.map_comp, Functor.map_comp] at h'
  exact h'

/-- A homomorphism `f : H ⟶ G'` that acts on points as `φ` is `lift` followed by `j`. -/
theorem lift_comp_eq (hi : F.IsRepresentedBy i) (hj : K.IsRepresentedBy j)
    (φ : ∀ T : Over S, F.carrier T →* K.carrier T)
    (hφ : ∀ {T T' : Over S} (a : T' ⟶ T) (x : F.carrier T),
      (φ T' ⟨a ≫ (x : T ⟶ G.X), F.comp_mem a x.2⟩ : T' ⟶ G'.X) = a ≫ (φ T x : T ⟶ G'.X))
    {f : H ⟶ G'}
    (hf : ∀ (T : Over S) (x : T ⟶ H.X), x ≫ f.hom.hom = (φ T (hi.pointsEquiv T x) : T ⟶ G'.X)) :
    lift hi hj φ hφ ≫ j = f := by
  apply (Grp.forget (Over S)).map_injective
  rw [Functor.map_comp]
  have h := lift_comp hi hj φ hφ (𝟙 H.X)
  rw [← hf, Category.id_comp, Category.id_comp] at h
  exact h

/-- Two group schemes representing the same subgroup functor are isomorphic, compatibly with the
inclusions. -/
def isoOfIsRepresentedBy (hi : F.IsRepresentedBy i) {H₂ : GroupScheme S} {i₂ : H₂ ⟶ G}
    (hi₂ : F.IsRepresentedBy i₂) : H ≅ H₂ where
  hom := lift hi hi₂ (fun _ => MonoidHom.id _) (fun _ _ => rfl)
  inv := lift hi₂ hi (fun _ => MonoidHom.id _) (fun _ _ => rfl)
  hom_inv_id := by
    apply hom_ext hi
    rw [Category.assoc, lift_comp_eq hi₂ hi _ (fun _ _ => rfl) (f := i₂) (fun _ _ => rfl),
      lift_comp_eq hi hi₂ _ (fun _ _ => rfl) (f := i) (fun _ _ => rfl), Category.id_comp]
  inv_hom_id := by
    apply hom_ext hi₂
    rw [Category.assoc, lift_comp_eq hi hi₂ _ (fun _ _ => rfl) (f := i) (fun _ _ => rfl),
      lift_comp_eq hi₂ hi _ (fun _ _ => rfl) (f := i₂) (fun _ _ => rfl), Category.id_comp]

theorem isoOfIsRepresentedBy_hom_comp (hi : F.IsRepresentedBy i) {H₂ : GroupScheme S}
    {i₂ : H₂ ⟶ G} (hi₂ : F.IsRepresentedBy i₂) : (isoOfIsRepresentedBy hi hi₂).hom ≫ i₂ = i :=
  lift_comp_eq hi hi₂ _ (fun _ _ => rfl) (fun _ _ => rfl)

end IsRepresentedBy

end Langlands.GroupScheme.SubgroupFunctor
