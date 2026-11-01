import Langlands.Cohomology.HyperextAbutmentNaturality
import Langlands.Cohomology.HyperextDegenerationIso

/-!
# Equivariance of the hyperext edge map and of the degeneration isomorphism

Let `Γ` be a group acting by automorphisms on an object `K` of the derived category of an
abelian category `C` (`ρ : Γ →* Aut K`) and on an object `W` of `C` (`σ : Γ →* Aut W`).

* `homAction ρ σ` is the induced action of `Γ` by additive automorphisms on any group of
  morphisms `X ⟶ Y` of a preadditive category, `γ • f = (ρ γ)⁻¹ ≫ f ≫ σ γ`.
* `abutmentAction ρ σ n` is the action on the abutment `Hom(K, W₀⟦n⟧)`, with `W₀` the object `W`
  placed in degree `0`, and `cohomologyHomAction ρ σ n` the action on `Hom(H^{-n} K, W)`, through
  the automorphisms `H^{-n}(ρ γ)` of `H^{-n} K`.
* The edge map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` intertwines the two actions
  (`edgeMap_abutmentAction`), so the degeneration isomorphism `degenerationAddEquiv` of
  `Langlands.Cohomology.HyperextDegenerationIso` and its inverse do as well. It therefore
  restricts to an additive isomorphism of the subgroups of fixed points
  (`degenerationFixedAddEquiv`, and `smoothDegenerationFixedAddEquiv` for smooth
  representations).
* The action on the abutment preserves every step of the abutment filtration
  (`abutmentAction_mem_filtration`).

The degeneration isomorphisms take Worker 3's proposition `HyperextDegenerationStatement` as the
explicit hypothesis `h`; this module does not prove it.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextAbutment

universe w' w v u uΓ uA uB

section Hom

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Conjugation by isomorphisms `α : X ≅ X'` and `β : Y ≅ Y'`, `f ↦ α⁻¹ ≫ f ≫ β`, as an additive
isomorphism `(X ⟶ Y) ≃+ (X' ⟶ Y')`. -/
def homAddEquiv {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := α.homCongr β
  map_add' f g := by
    simp only [Equiv.toFun_as_coe, Iso.homCongr_apply, Preadditive.add_comp,
      Preadditive.comp_add]

@[simp]
lemma homAddEquiv_apply {X X' Y Y' : C} (α : X ≅ X') (β : Y ≅ Y') (f : X ⟶ Y) :
    homAddEquiv α β f = α.inv ≫ f ≫ β.hom :=
  rfl

variable {Γ : Type uΓ} [Group Γ]

/-- The action of `Γ` by additive automorphisms on `X ⟶ Y` induced by actions `ρ` on `X` and `σ`
on `Y` by automorphisms: `γ` sends `f` to `(ρ γ)⁻¹ ≫ f ≫ σ γ`. -/
def homAction {X Y : C} (ρ : Γ →* Aut X) (σ : Γ →* Aut Y) : Γ →* AddMonoid.End (X ⟶ Y) where
  toFun γ := (homAddEquiv (ρ γ) (σ γ)).toAddMonoidHom
  map_one' := by
    ext f
    have h₁ : (ρ 1).inv = 𝟙 X := by rw [map_one]; rfl
    have h₂ : (σ 1).hom = 𝟙 Y := by rw [map_one]; rfl
    change (ρ 1).inv ≫ f ≫ (σ 1).hom = f
    rw [h₁, h₂]
    exact (Category.id_comp _).trans (Category.comp_id _)
  map_mul' γ δ := by
    ext f
    have h₁ : (ρ (γ * δ)).inv = (ρ γ).inv ≫ (ρ δ).inv := by rw [map_mul]; rfl
    have h₂ : (σ (γ * δ)).hom = (σ δ).hom ≫ (σ γ).hom := by rw [map_mul]; rfl
    change (ρ (γ * δ)).inv ≫ f ≫ (σ (γ * δ)).hom =
      (ρ γ).inv ≫ ((ρ δ).inv ≫ f ≫ (σ δ).hom) ≫ (σ γ).hom
    rw [h₁, h₂]
    simp only [Category.assoc]

lemma homAction_apply {X Y : C} (ρ : Γ →* Aut X) (σ : Γ →* Aut Y) (γ : Γ) (f : X ⟶ Y) :
    homAction ρ σ γ f = (ρ γ).inv ≫ f ≫ (σ γ).hom :=
  rfl

end Hom

section Fixed

variable {Γ : Type uΓ} [Group Γ]

/-- The subgroup of elements of `A` fixed by every element of `Γ`, for an action `a` of `Γ` on
`A` by additive automorphisms. -/
def fixedAddSubgroup {A : Type uA} [AddGroup A] (a : Γ →* AddMonoid.End A) : AddSubgroup A where
  carrier := {x | ∀ γ, a γ x = x}
  add_mem' {x y} hx hy γ := by
    simp only [Set.mem_ofPred_eq] at hx hy
    rw [map_add, hx γ, hy γ]
  zero_mem' γ := map_zero (a γ)
  neg_mem' {x} hx γ := by
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_neg, hx γ]

lemma mem_fixedAddSubgroup_iff {A : Type uA} [AddGroup A] (a : Γ →* AddMonoid.End A) (x : A) :
    x ∈ fixedAddSubgroup a ↔ ∀ γ, a γ x = x :=
  Iff.rfl

/-- An additive isomorphism `e : A ≃+ B` intertwining actions `a` on `A` and `b` on `B`
restricts to an additive isomorphism between the subgroups of fixed points. -/
def fixedAddEquiv {A : Type uA} {B : Type uB} [AddGroup A] [AddGroup B] (a : Γ →* AddMonoid.End A)
    (b : Γ →* AddMonoid.End B) (e : A ≃+ B) (he : ∀ γ x, e (a γ x) = b γ (e x)) :
    fixedAddSubgroup a ≃+ fixedAddSubgroup b where
  toFun x := ⟨e x, fun γ => by rw [← he, x.2 γ]⟩
  invFun y := ⟨e.symm y, fun γ => by
    apply e.injective
    rw [he, e.apply_symm_apply, y.2 γ]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_add' x y := Subtype.ext (map_add e (x : A) (y : A))

@[simp]
lemma coe_fixedAddEquiv_apply {A : Type uA} {B : Type uB} [AddGroup A] [AddGroup B]
    (a : Γ →* AddMonoid.End A) (b : Γ →* AddMonoid.End B) (e : A ≃+ B) (he : ∀ γ x, e (a γ x) = b γ (e x))
    (x : fixedAddSubgroup a) : (fixedAddEquiv a b e he x : B) = e x :=
  rfl

end Fixed

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {Γ : Type uΓ} [Group Γ]

open DerivedCategory

/-- The action of `Γ` on the abutment `Hom(K, W₀⟦n⟧)` induced by actions `ρ` on `K` and `σ` on `W`
by automorphisms, where `W₀` is `W` placed in degree `0`: `γ` sends `f` to
`(ρ γ)⁻¹ ≫ f ≫ (σ γ)₀⟦n⟧`. -/
def abutmentAction {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) :
    Γ →* AddMonoid.End (ShiftedHom K ((singleFunctor C 0).obj W) n) :=
  homAction ρ (((singleFunctor C 0 ⋙ shiftFunctor (DerivedCategory C) n).mapAut W).comp σ)

/-- The action of `Γ` on `Hom(H^{-n} K, W)` induced by actions `ρ` on `K` and `σ` on `W` by
automorphisms: `γ` sends `g` to `H^{-n}((ρ γ)⁻¹) ≫ g ≫ σ γ`. -/
def cohomologyHomAction {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) : Γ →* AddMonoid.End ((homologyFunctor C (-n)).obj K ⟶ W) :=
  homAction (((homologyFunctor C (-n)).mapAut K).comp ρ) σ

lemma abutmentAction_apply {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K) (σ : Γ →* Aut W)
    (n : ℤ) (γ : Γ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    abutmentAction ρ σ n γ f =
      postcomp K ((singleFunctor C 0).map (σ γ).hom) n (precomp (ρ γ).inv _ n f) :=
  (Category.assoc _ _ _).symm

lemma cohomologyHomAction_apply {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    cohomologyHomAction ρ σ n γ g = (homologyFunctor C (-n)).map (ρ γ).inv ≫ g ≫ (σ γ).hom :=
  rfl

/-- The edge map `Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` intertwines `abutmentAction` and
`cohomologyHomAction`. -/
lemma edgeMap_abutmentAction {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap K W n (abutmentAction ρ σ n γ f) =
      cohomologyHomAction ρ σ n γ (HyperextDegeneration.edgeMap K W n f) := by
  rw [abutmentAction_apply, edgeMap_postcomp, precomp_apply, edgeMap_comp,
    cohomologyHomAction_apply, Category.assoc]

/-- `edgeMap_abutmentAction` as an equality of additive maps. -/
lemma edgeMapAddMonoidHom_comp_abutmentAction {K : DerivedCategory C} {W : C}
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (n : ℤ) (γ : Γ) :
    (edgeMapAddMonoidHom K W n).comp (abutmentAction ρ σ n γ) =
      (cohomologyHomAction ρ σ n γ).comp (edgeMapAddMonoidHom K W n) := by
  ext f
  exact edgeMap_abutmentAction ρ σ n γ f

section TStructure

variable (t : Triangulated.TStructure (DerivedCategory C))

/-- The action of `Γ` on the abutment preserves each step `F^p` of the abutment filtration. -/
lemma abutmentAction_mem_filtration {K : DerivedCategory C} {W : C} (ρ : Γ →* Aut K)
    (σ : Γ →* Aut W) {n p : ℤ} (γ : Γ) {f : ShiftedHom K ((singleFunctor C 0).obj W) n}
    (hf : f ∈ filtration t K ((singleFunctor C 0).obj W) n p) :
    abutmentAction ρ σ n γ f ∈ filtration t K ((singleFunctor C 0).obj W) n p := by
  rw [abutmentAction_apply]
  exact postcomp_mem_filtration _ (precomp_mem_filtration _ hf)

end TStructure

variable [HasExt.{w'} C]

/-- The degeneration isomorphism `Hom(K, W₀⟦n⟧) ≃+ Hom(H^{-n} K, W)` intertwines
`abutmentAction` and `cohomologyHomAction`. -/
lemma degenerationAddEquiv_abutmentAction (h : HyperextDegenerationStatement.{w, w'} C)
    {K : DerivedCategory C} (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    {W : C} (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (γ : Γ) (f : ShiftedHom K ((singleFunctor C 0).obj W) n) :
    degenerationAddEquiv h K b hK W hW n (abutmentAction ρ σ n γ f) =
      cohomologyHomAction ρ σ n γ (degenerationAddEquiv h K b hK W hW n f) :=
  edgeMap_abutmentAction ρ σ n γ f

/-- The inverse of the degeneration isomorphism intertwines `cohomologyHomAction` and
`abutmentAction`. -/
lemma degenerationAddEquiv_symm_cohomologyHomAction (h : HyperextDegenerationStatement.{w, w'} C)
    {K : DerivedCategory C} (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    {W : C} (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (γ : Γ) (g : (homologyFunctor C (-n)).obj K ⟶ W) :
    (degenerationAddEquiv h K b hK W hW n).symm (cohomologyHomAction ρ σ n γ g) =
      abutmentAction ρ σ n γ ((degenerationAddEquiv h K b hK W hW n).symm g) := by
  apply (degenerationAddEquiv h K b hK W hW n).injective
  rw [AddEquiv.apply_symm_apply, degenerationAddEquiv_abutmentAction, AddEquiv.apply_symm_apply]

/-- The degeneration isomorphism restricted to fixed points: the `Γ`-fixed elements of the
abutment `Hom(K, W₀⟦n⟧)` correspond to the `Γ`-fixed elements of `Hom(H^{-n} K, W)`. -/
def degenerationFixedAddEquiv (h : HyperextDegenerationStatement.{w, w'} C)
    {K : DerivedCategory C} (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    {W : C} (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    fixedAddSubgroup (abutmentAction ρ σ n) ≃+ fixedAddSubgroup (cohomologyHomAction ρ σ n) :=
  fixedAddEquiv _ _ (degenerationAddEquiv h K b hK W hW n)
    (degenerationAddEquiv_abutmentAction h b hK hW n ρ σ)

@[simp]
lemma coe_degenerationFixedAddEquiv_apply (h : HyperextDegenerationStatement.{w, w'} C)
    {K : DerivedCategory C} (b : ℤ) (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor C i).obj K))
    {W : C} (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{w'} ((homologyFunctor C k).obj K) W i)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (f : fixedAddSubgroup (abutmentAction ρ σ n)) :
    (degenerationFixedAddEquiv h b hK hW n ρ σ f : (homologyFunctor C (-n)).obj K ⟶ W) =
      HyperextDegeneration.edgeMap K W n f :=
  rfl

end Derived

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [HasDerivedCategory.{w} (SmoothRep.{u, u, u} R G)]
  [HasExt.{w'} (SmoothRep.{u, u, u} R G)] {Γ : Type uΓ} [Group Γ]

open DerivedCategory

/-- For smooth representations, `smoothDegenerationAddEquiv` intertwines `abutmentAction` and
`cohomologyHomAction`. -/
lemma smoothDegenerationAddEquiv_abutmentAction
    (h : HyperextDegenerationStatement.{w, w'} (SmoothRep.{u, u, u} R G))
    {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) (γ : Γ)
    (f : ShiftedHom K ((singleFunctor _ 0).obj W) n) :
    smoothDegenerationAddEquiv R G h K b hK W hW n (abutmentAction ρ σ n γ f) =
      cohomologyHomAction ρ σ n γ (smoothDegenerationAddEquiv R G h K b hK W hW n f) :=
  edgeMap_abutmentAction ρ σ n γ f

/-- For smooth representations, `smoothDegenerationAddEquiv` restricted to `Γ`-fixed points, with
the `Ext` hypothesis stated with the smooth Ext groups. -/
def smoothDegenerationFixedAddEquiv
    (h : HyperextDegenerationStatement.{w, w'} (SmoothRep.{u, u, u} R G))
    {K : DerivedCategory (SmoothRep.{u, u, u} R G)} (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((homologyFunctor _ i).obj K)) {W : SmoothRep.{u, u, u} R G}
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton ((SmoothExt.ext R G ((homologyFunctor _ k).obj K) i).obj W)) (n : ℤ)
    (ρ : Γ →* Aut K) (σ : Γ →* Aut W) :
    fixedAddSubgroup (abutmentAction ρ σ n) ≃+ fixedAddSubgroup (cohomologyHomAction ρ σ n) :=
  fixedAddEquiv _ _ (smoothDegenerationAddEquiv R G h K b hK W hW n)
    (smoothDegenerationAddEquiv_abutmentAction R G h b hK hW n ρ σ)

end Smooth

end HyperextAbutment

end Langlands.Cohomology
