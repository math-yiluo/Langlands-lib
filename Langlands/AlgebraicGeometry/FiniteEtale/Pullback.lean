import Langlands.AlgebraicGeometry.FiniteEtale.Definitions

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

section PullbackFunctor

variable {S S' S'' : Scheme.{u}}

/-- Pullback of actual finite étale covers along an arbitrary morphism of schemes: an object
`Y → S` goes to the second projection `Y ×_S S' → S'`, and a morphism `k : Y ⟶ Z` goes to
`pullback.lift (pullback.fst ≫ k) pullback.snd`, i.e. `(y, s') ↦ (k y, s')`. This is
Mathlib's slice pullback `Over.pullback f` restricted to finite étale objects
(`pullbackFunctor_comp_inclusion`). -/
def pullbackFunctor (f : S' ⟶ S) : Cover S ⥤ Cover S' where
  obj Y := ⟨Over.mk (pullback.snd Y.obj.hom f),
    (inferInstance : IsFinite (pullback.snd Y.obj.hom f)),
    (inferInstance : Etale (pullback.snd Y.obj.hom f))⟩
  map {Y Z} k := ObjectProperty.homMk (Over.homMk
    (pullback.lift (pullback.fst Y.obj.hom f ≫ k.hom.left) (pullback.snd Y.obj.hom f)
      (by rw [Category.assoc, Over.w k.hom, pullback.condition]))
    (pullback.lift_snd _ _ _))
  map_id Y := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp
  map_comp k l := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp

variable (f : S' ⟶ S)

/-- Forgetting finite étaleness gives exactly Mathlib's pullback of objects over `S`. -/
theorem pullbackFunctor_comp_inclusion :
    pullbackFunctor f ⋙ inclusion S' = inclusion S ⋙ Over.pullback f := rfl

theorem pullbackFunctor_obj_obj (Y : Cover S) :
    ((pullbackFunctor f).obj Y).obj = Over.mk (pullback.snd Y.obj.hom f) := rfl

@[simp]
theorem pullbackFunctor_obj_left (Y : Cover S) :
    ((pullbackFunctor f).obj Y).obj.left = pullback Y.obj.hom f := rfl

@[simp]
theorem pullbackFunctor_obj_hom (Y : Cover S) :
    ((pullbackFunctor f).obj Y).obj.hom = pullback.snd Y.obj.hom f := rfl

theorem pullbackFunctor_map_hom_left {Y Z : Cover S} (k : Y ⟶ Z) :
    ((pullbackFunctor f).map k).hom.left =
      pullback.lift (pullback.fst Y.obj.hom f ≫ k.hom.left) (pullback.snd Y.obj.hom f)
        (by rw [Category.assoc, Over.w k.hom, pullback.condition]) := rfl

@[reassoc (attr := simp)]
theorem pullbackFunctor_map_hom_left_fst {Y Z : Cover S} (k : Y ⟶ Z) :
    ((pullbackFunctor f).map k).hom.left ≫ pullback.fst Z.obj.hom f =
      pullback.fst Y.obj.hom f ≫ k.hom.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackFunctor_map_hom_left_snd {Y Z : Cover S} (k : Y ⟶ Z) :
    ((pullbackFunctor f).map k).hom.left ≫ pullback.snd Z.obj.hom f =
      pullback.snd Y.obj.hom f :=
  pullback.lift_snd _ _ _

variable (S) in
/-- Pullback along an identity is the identity, via the first projection. -/
def pullbackIdIso : pullbackFunctor (𝟙 S) ≅ 𝟭 (Cover S) :=
  NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ (Over.isoMk
      { hom := pullback.fst Y.obj.hom (𝟙 S)
        inv := pullback.lift (𝟙 _) Y.obj.hom (by simp)
        hom_inv_id := by apply pullback.hom_ext <;> simp [pullback.condition]
        inv_hom_id := by simp }
      (by simp [pullback.condition])))
    (by
      intro Y Z k
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact pullbackFunctor_map_hom_left_fst (𝟙 S) k)

@[simp]
theorem pullbackIdIso_hom_app_hom_left (Y : Cover S) :
    ((pullbackIdIso S).hom.app Y).hom.left = pullback.fst Y.obj.hom (𝟙 S) := rfl

@[simp]
theorem pullbackIdIso_inv_app_hom_left (Y : Cover S) :
    ((pullbackIdIso S).inv.app Y).hom.left = pullback.lift (𝟙 _) Y.obj.hom (by simp) := rfl

/-- Pulling back along `g ≫ f` agrees with pulling back along `f` and then along `g`,
via the canonical pasting isomorphism of pullback squares. -/
def pullbackCompIso (g : S'' ⟶ S') :
    pullbackFunctor (g ≫ f) ≅ pullbackFunctor f ⋙ pullbackFunctor g :=
  NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ (Over.isoMk
      (pullbackLeftPullbackSndIso Y.obj.hom f g).symm (by simp)))
    (by
      intro Y Z k
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      dsimp
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [pullbackFunctor_map_hom_left]
        · simp [pullbackFunctor_map_hom_left]
      · simp [pullbackFunctor_map_hom_left])

@[simp]
theorem pullbackCompIso_hom_app_hom_left (g : S'' ⟶ S') (Y : Cover S) :
    ((pullbackCompIso f g).hom.app Y).hom.left =
      (pullbackLeftPullbackSndIso Y.obj.hom f g).inv := rfl

/-- The comparison from the iterated pullback is the map `(y, z) ↦ (y, z)` determined by
the two first projections and the last second projection. -/
theorem pullbackCompIso_inv_app_hom_left (g : S'' ⟶ S') (Y : Cover S) :
    ((pullbackCompIso f g).inv.app Y).hom.left =
      pullback.lift (pullback.fst (pullback.snd Y.obj.hom f) g ≫ pullback.fst Y.obj.hom f)
        (pullback.snd (pullback.snd Y.obj.hom f) g)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
          Category.assoc]) := by
  apply pullback.hom_ext <;> simp [pullbackCompIso]

end PullbackFunctor

section Fibers

variable {S S' S'' : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The universal property of the pullback identifies lifts of `s` to `Y` with lifts of
`t` to the pulled-back cover, whenever `t ≫ f = s`. -/
def pullbackFiberEquiv (f : S' ⟶ S) (t : Spec (.of Ω) ⟶ S') (s : Spec (.of Ω) ⟶ S)
    (h : t ≫ f = s) (Y : Cover S) :
    Fiber s Y ≃ Fiber t ((pullbackFunctor f).obj Y) where
  toFun x := Over.homMk (pullback.lift x.left t (by rw [h]; exact Over.w x))
    (pullback.lift_snd _ _ _)
  invFun y := Over.homMk (y.left ≫ pullback.fst Y.obj.hom f) (by
    have hy : y.left ≫ pullback.snd Y.obj.hom f = t := Over.w y
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy]
    exact h)
  left_inv x := by
    apply Over.OverMorphism.ext
    simp
  right_inv y := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp
    · simpa using (Over.w y).symm

variable (f : S' ⟶ S) (t : Spec (.of Ω) ⟶ S') (s : Spec (.of Ω) ⟶ S) (h : t ≫ f = s)

/-- A lift `x` of `s` goes to the morphism `pullback.lift x t` into the fibre product. -/
theorem pullbackFiberEquiv_apply_left (Y : Cover S) (x : Fiber s Y) :
    (pullbackFiberEquiv f t s h Y x).left =
      pullback.lift x.left t (by rw [h]; exact Over.w x) := rfl

@[reassoc (attr := simp)]
theorem pullbackFiberEquiv_apply_left_fst (Y : Cover S) (x : Fiber s Y) :
    (pullbackFiberEquiv f t s h Y x).left ≫ pullback.fst Y.obj.hom f = x.left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackFiberEquiv_apply_left_snd (Y : Cover S) (x : Fiber s Y) :
    (pullbackFiberEquiv f t s h Y x).left ≫ pullback.snd Y.obj.hom f = t :=
  pullback.lift_snd _ _ _

/-- The image of a lift is the unique morphism to the pullback with projections `x` and `t`. -/
theorem pullbackFiberEquiv_apply_left_eq (Y : Cover S) (x : Fiber s Y)
    (z : Spec (.of Ω) ⟶ pullback Y.obj.hom f)
    (hz₁ : z ≫ pullback.fst Y.obj.hom f = x.left) (hz₂ : z ≫ pullback.snd Y.obj.hom f = t) :
    (pullbackFiberEquiv f t s h Y x).left = z := by
  apply pullback.hom_ext
  · rw [pullbackFiberEquiv_apply_left_fst, hz₁]
  · rw [pullbackFiberEquiv_apply_left_snd, hz₂]

@[simp]
theorem pullbackFiberEquiv_symm_apply_left (Y : Cover S)
    (y : Fiber t ((pullbackFunctor f).obj Y)) :
    ((pullbackFiberEquiv f t s h Y).symm y).left = y.left ≫ pullback.fst Y.obj.hom f := rfl

include f h in
/-- Finiteness of the fibres over `t` of all covers of `S'` gives finiteness of the fibres over
`s` of all covers of `S`. -/
theorem pullbackFiberFinite (ht : ∀ Y : Cover S', Finite (Fiber t Y)) :
    ∀ Y : Cover S, Finite (Fiber s Y) :=
  fun Y => @Finite.of_equiv _ _ (ht _) (pullbackFiberEquiv f t s h Y).symm

/-- The geometric point functor at `s` is the pullback followed by the point functor at `t`. -/
def pointFunctorPullbackIso : pointFunctor s ≅ pullbackFunctor f ⋙ pointFunctor t :=
  NatIso.ofComponents (fun Y => (pullbackFiberEquiv f t s h Y).toIso) (by
    intro Y Z g
    ext x
    change pullbackFiberEquiv f t s h Z (x ≫ g.hom) =
      pullbackFiberEquiv f t s h Y x ≫ ((pullbackFunctor f).map g).hom
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp)

@[simp]
theorem pointFunctorPullbackIso_hom_app (Y : Cover S) (x : Fiber s Y) :
    (pointFunctorPullbackIso f t s h).hom.app Y x = pullbackFiberEquiv f t s h Y x := rfl

@[simp]
theorem pointFunctorPullbackIso_inv_app (Y : Cover S)
    (y : Fiber t ((pullbackFunctor f).obj Y)) :
    (pointFunctorPullbackIso f t s h).inv.app Y y = (pullbackFiberEquiv f t s h Y).symm y := rfl

variable (hs : ∀ Y : Cover S, Finite (Fiber s Y)) (ht : ∀ Y : Cover S', Finite (Fiber t Y))

/-- The finite geometric fibre functor at `s` is the pullback followed by the finite geometric
fibre functor at `t`. Its components are the bijections `pullbackFiberEquiv`. -/
def fiberFunctorPullbackIso : fiberFunctor s hs ≅ pullbackFunctor f ⋙ fiberFunctor t ht :=
  NatIso.ofComponents
    (fun Y => ObjectProperty.isoMk _ ((pointFunctorPullbackIso f t s h).app Y))
    (by
      intro Y Z g
      apply ObjectProperty.hom_ext
      exact (pointFunctorPullbackIso f t s h).hom.naturality g)

@[simp]
theorem fiberFunctorPullbackIso_hom_app (Y : Cover S) (x : Fiber s Y) :
    (fiberFunctorPullbackIso f t s h hs ht).hom.app Y x = pullbackFiberEquiv f t s h Y x := rfl

@[simp]
theorem fiberFunctorPullbackIso_inv_app (Y : Cover S)
    (y : Fiber t ((pullbackFunctor f).obj Y)) :
    (fiberFunctorPullbackIso f t s h hs ht).inv.app Y y =
      (pullbackFiberEquiv f t s h Y).symm y := rfl

/-- Forgetting finite-set packaging recovers the point-functor comparison. -/
theorem fiberFunctorPullbackIso_comp_incl :
    Functor.isoWhiskerRight (fiberFunctorPullbackIso f t s h hs ht) FintypeCat.incl =
      pointFunctorPullbackIso f t s h := by
  ext Y x
  rfl

/-- Identity coherence: along `𝟙 S`, the fibre bijection followed by the identity comparison
returns the original lift. -/
theorem pullbackFiberEquiv_id_left {t : Spec (.of Ω) ⟶ S} (h : t ≫ 𝟙 S = t) (Y : Cover S)
    (x : Fiber t Y) :
    (pullbackFiberEquiv (𝟙 S) t t h Y x).left ≫ ((pullbackIdIso S).hom.app Y).hom.left =
      x.left := by
  simp

/-- Composition coherence: iterated fibre bijections followed by the composition comparison
give the fibre bijection along the composite. -/
theorem pullbackFiberEquiv_comp_left (g : S'' ⟶ S') (u : Spec (.of Ω) ⟶ S'')
    (hg : u ≫ g = t) (hgf : u ≫ g ≫ f = s) (Y : Cover S) (x : Fiber s Y) :
    (pullbackFiberEquiv g u t hg _ (pullbackFiberEquiv f t s h Y x)).left ≫
        ((pullbackCompIso f g).inv.app Y).hom.left =
      (pullbackFiberEquiv (g ≫ f) u s hgf Y x).left := by
  symm
  apply pullbackFiberEquiv_apply_left_eq
  · rw [pullbackCompIso_inv_app_hom_left, Category.assoc, pullback.lift_fst]
    exact (pullbackFiberEquiv_apply_left_fst_assoc g u t hg _ _ _).trans
      (pullbackFiberEquiv_apply_left_fst f t s h Y x)
  · rw [pullbackCompIso_inv_app_hom_left, Category.assoc, pullback.lift_snd]
    exact pullbackFiberEquiv_apply_left_snd g u t hg _ _

end Fibers

section FundamentalGroup

variable {S S' S'' : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- Natural automorphisms of an actual finite geometric fibre functor are determined by their
action on all fibres. -/
theorem fundamentalGroup_ext {s : Spec (.of Ω) ⟶ S} {hs : ∀ Y : Cover S, Finite (Fiber s Y)}
    {σ τ : FundamentalGroup s hs} (H : ∀ (Y : Cover S) (x : Fiber s Y), σ • x = τ • x) :
    σ = τ := by
  apply Iso.ext
  ext Y x
  exact H Y x

variable (f : S' ⟶ S) (t : Spec (.of Ω) ⟶ S') (s : Spec (.of Ω) ⟶ S) (h : t ≫ f = s)
  (ht : ∀ Y : Cover S', Finite (Fiber t Y)) (hs : ∀ Y : Cover S, Finite (Fiber s Y))

/-- The homomorphism `π₁(S', t) → π₁(S, s)` induced by `f`: whisker an automorphism of the
fibre functor at `t` by pullback, then conjugate by `fiberFunctorPullbackIso`. -/
def fundamentalGroupMap : FundamentalGroup t ht →* FundamentalGroup s hs :=
  (fiberFunctorPullbackIso f t s h hs ht).symm.conjAut.toMonoidHom.comp
    (((Functor.whiskeringLeft _ _ FintypeCat.{u}).obj (pullbackFunctor f)).mapAut
      (fiberFunctor t ht))

theorem fundamentalGroupMap_apply (σ : FundamentalGroup t ht) :
    fundamentalGroupMap f t s h ht hs σ =
      fiberFunctorPullbackIso f t s h hs ht ≪≫ Functor.isoWhiskerLeft (pullbackFunctor f) σ ≪≫
        (fiberFunctorPullbackIso f t s h hs ht).symm := by
  ext Y x
  rfl

/-- Evaluation formula: transport a point of the fibre at `s` to the pulled-back fibre at `t`,
apply `σ`, and transport back. -/
theorem fundamentalGroupMap_smul (σ : FundamentalGroup t ht) (Y : Cover S) (x : Fiber s Y) :
    fundamentalGroupMap f t s h ht hs σ • x =
      (pullbackFiberEquiv f t s h Y).symm (σ • pullbackFiberEquiv f t s h Y x) := rfl

/-- The fibre bijection is equivariant for the induced homomorphism. -/
theorem pullbackFiberEquiv_smul (σ : FundamentalGroup t ht) (Y : Cover S) (x : Fiber s Y) :
    pullbackFiberEquiv f t s h Y (fundamentalGroupMap f t s h ht hs σ • x) =
      σ • pullbackFiberEquiv f t s h Y x := by
  rw [fundamentalGroupMap_smul, Equiv.apply_symm_apply]

theorem fundamentalGroupMap_smul_left (σ : FundamentalGroup t ht) (Y : Cover S)
    (x : Fiber s Y) :
    (fundamentalGroupMap f t s h ht hs σ • x).left =
      (σ • pullbackFiberEquiv f t s h Y x).left ≫ pullback.fst Y.obj.hom f := rfl

/-- Characterization by compatible morphisms: if `φ : Y' ⟶ Y` lies over `f` and carries
`y ∈ Fiber t Y'` to `x ∈ Fiber s Y`, then it carries `σ • y` to the induced action on `x`. -/
theorem fundamentalGroupMap_smul_left_of_comp (σ : FundamentalGroup t ht) {Y : Cover S}
    (x : Fiber s Y) {Y' : Cover S'} (y : Fiber t Y') (φ : Y'.obj.left ⟶ Y.obj.left)
    (hφ : φ ≫ Y.obj.hom = Y'.obj.hom ≫ f) (hy : y.left ≫ φ = x.left) :
    (fundamentalGroupMap f t s h ht hs σ • x).left = (σ • y).left ≫ φ := by
  let ψ : Y' ⟶ (pullbackFunctor f).obj Y :=
    ObjectProperty.homMk (Over.homMk (pullback.lift φ Y'.obj.hom hφ) (pullback.lift_snd _ _ _))
  have hx : pullbackFiberEquiv f t s h Y x = y ≫ ψ.hom := by
    apply Over.OverMorphism.ext
    apply pullbackFiberEquiv_apply_left_eq
    · simp [ψ, hy]
    · simp [ψ]
  rw [fundamentalGroupMap_smul_left, hx, smul_naturality]
  simp [ψ]

/-- Identity law, with the point equation `t ≫ 𝟙 S = t` explicit. -/
theorem fundamentalGroupMap_id (t : Spec (.of Ω) ⟶ S) (h : t ≫ 𝟙 S = t)
    (ht : ∀ Y : Cover S, Finite (Fiber t Y)) :
    fundamentalGroupMap (𝟙 S) t t h ht ht = MonoidHom.id _ := by
  ext σ : 1
  apply fundamentalGroup_ext
  intro Y x
  apply Over.OverMorphism.ext
  rw [fundamentalGroupMap_smul_left_of_comp (𝟙 S) t t h ht ht σ x x (𝟙 _) (by simp) (by simp)]
  simp

/-- Composition law, with the point equations `u ≫ g = t`, `t ≫ f = s` and
`u ≫ g ≫ f = s` explicit. -/
theorem fundamentalGroupMap_comp (g : S'' ⟶ S') (u : Spec (.of Ω) ⟶ S'') (hg : u ≫ g = t)
    (hgf : u ≫ g ≫ f = s) (hu : ∀ Y : Cover S'', Finite (Fiber u Y)) :
    fundamentalGroupMap (g ≫ f) u s hgf hu hs =
      (fundamentalGroupMap f t s h ht hs).comp (fundamentalGroupMap g u t hg hu ht) := by
  ext σ : 1
  apply fundamentalGroup_ext
  intro Y x
  apply Over.OverMorphism.ext
  rw [fundamentalGroupMap_smul_left_of_comp (g ≫ f) u s hgf hu hs σ x
    (pullbackFiberEquiv g u t hg _ (pullbackFiberEquiv f t s h Y x))
    (pullback.fst (pullback.snd Y.obj.hom f) g ≫ pullback.fst Y.obj.hom f)
    (by
      simp only [pullbackFunctor_obj_hom]
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc])
    ((pullbackFiberEquiv_apply_left_fst_assoc g u t hg _ _ _).trans
      (pullbackFiberEquiv_apply_left_fst f t s h Y x))]
  rw [MonoidHom.comp_apply, fundamentalGroupMap_smul_left, fundamentalGroupMap_smul_left,
    Category.assoc]
  rfl

open scoped PreGaloisCategory in
/-- The induced homomorphism is continuous for the evaluation topologies. -/
theorem continuous_fundamentalGroupMap : Continuous (fundamentalGroupMap f t s h ht hs) := by
  rw [Topology.IsInducing.continuous_iff
    (PreGaloisCategory.autEmbedding_isClosedEmbedding _).isInducing, continuous_pi_iff]
  intro Y
  let e := (fiberFunctorPullbackIso f t s h hs ht).app Y
  have key : (fun σ => PreGaloisCategory.autEmbedding (fiberFunctor s hs)
      (fundamentalGroupMap f t s h ht hs σ) Y) =
      (fun τ : Aut ((fiberFunctor t ht).obj ((pullbackFunctor f).obj Y)) => e ≪≫ τ ≪≫ e.symm) ∘ (fun p => p ((pullbackFunctor f).obj Y)) ∘
        PreGaloisCategory.autEmbedding (fiberFunctor t ht) := by
    funext σ
    apply Iso.ext
    rfl
  simp only [Function.comp_apply]
  rw [key]
  exact continuous_of_discreteTopology.comp ((continuous_apply _).comp continuous_induced_dom)

/-- The induced continuous homomorphism of fundamental groups. -/
def fundamentalGroupContinuousMap : FundamentalGroup t ht →ₜ* FundamentalGroup s hs where
  toMonoidHom := fundamentalGroupMap f t s h ht hs
  continuous_toFun := continuous_fundamentalGroupMap f t s h ht hs

@[simp]
theorem fundamentalGroupContinuousMap_apply (σ : FundamentalGroup t ht) :
    fundamentalGroupContinuousMap f t s h ht hs σ = fundamentalGroupMap f t s h ht hs σ := rfl

end FundamentalGroup

end Langlands.AlgebraicGeometry.FiniteEtale
