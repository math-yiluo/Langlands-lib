import Langlands.GroupScheme.CorepresentedPoints
import Langlands.GroupScheme.CorepresentedLinearEmbedding
import Langlands.GroupScheme.Rational.Characters

/-! # Comultiplication, antipode and classifying maps of corepresented group functors -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Corepresented

open LinearEmbedding (comul)

variable {R : CommRingCat.{u}}

/-! ### Tensor products of algebras -/

section Tensor

/-- The tensor product of two commutative algebras, as an object of `CommAlgCat R`. -/
abbrev tensorObj (A B : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (A ⊗[R] B)

/-- The left inclusion `a ↦ a ⊗ 1`. -/
abbrev inl (A B : CommAlgCat.{u} R) : A ⟶ tensorObj A B :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeLeft

/-- The right inclusion `b ↦ 1 ⊗ b`. -/
abbrev inr (A B : CommAlgCat.{u} R) : B ⟶ tensorObj A B :=
  CommAlgCat.ofHom Algebra.TensorProduct.includeRight

/-- The map out of a tensor product given by two algebra maps, `a ⊗ b ↦ f a * g b`. -/
abbrev tensorLift {A B C : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ C) : tensorObj A B ⟶ C :=
  CommAlgCat.ofHom (Algebra.TensorProduct.productMap f.hom g.hom)

@[simp] theorem inl_apply {A B : CommAlgCat.{u} R} (a : A) :
    (inl A B).hom a = a ⊗ₜ[R] (1 : B) :=
  rfl

@[simp] theorem inr_apply {A B : CommAlgCat.{u} R} (b : B) :
    (inr A B).hom b = (1 : A) ⊗ₜ[R] b :=
  rfl

@[simp] theorem tensorLift_tmul {A B C : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ C) (a : A)
    (b : B) : (tensorLift f g).hom (a ⊗ₜ[R] b) = f.hom a * g.hom b :=
  rfl

@[simp] theorem inl_tensorLift {A B C : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ C) :
    inl A B ≫ tensorLift f g = f := by
  ext a
  exact Algebra.TensorProduct.productMap_left_apply f.hom g.hom a

@[simp] theorem inr_tensorLift {A B C : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ C) :
    inr A B ≫ tensorLift f g = g := by
  ext b
  exact Algebra.TensorProduct.productMap_right_apply f.hom g.hom b

theorem tensorLift_comp {A B C D : CommAlgCat.{u} R} (f : A ⟶ C) (g : B ⟶ C) (h : C ⟶ D) :
    tensorLift f g ≫ h = tensorLift (f ≫ h) (g ≫ h) := by
  apply CommAlgCat.hom_ext
  apply Algebra.TensorProduct.ext'
  intro a b
  change h.hom (f.hom a * g.hom b) = h.hom (f.hom a) * h.hom (g.hom b)
  exact map_mul h.hom _ _

end Tensor

/-! ### Comultiplication and antipode -/

variable {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- The corepresentation as an application of the functor on morphisms. -/
theorem homEquiv_comp' {C D : CommAlgCat.{u} R} (f : B ⟶ C) (g : C ⟶ D) :
    e.homEquiv (f ≫ g) = F.map g (e.homEquiv f) :=
  e.homEquiv_comp g f

/-- The antipode `B ⟶ B`: it classifies the inverse of the universal point. -/
def antipode : B ⟶ B :=
  e.homEquiv.symm (e.homEquiv (𝟙 B))⁻¹

/-- Products of points are classified by the comultiplication followed by the two classifying
maps. -/
theorem homEquiv_symm_mul {C : CommAlgCat.{u} R} (x y : F.obj C) :
    e.homEquiv.symm (x * y) = comul e ≫ tensorLift (e.homEquiv.symm x) (e.homEquiv.symm y) :=
  LinearEmbedding.cls_mul e x y

/-- Inverses of points are classified by the antipode followed by the classifying map. -/
theorem homEquiv_symm_inv {C : CommAlgCat.{u} R} (x : F.obj C) :
    e.homEquiv.symm x⁻¹ = antipode e ≫ e.homEquiv.symm x := by
  apply e.homEquiv.injective
  rw [Equiv.apply_symm_apply, homEquiv_comp', antipode, Equiv.apply_symm_apply, map_inv,
    ← homEquiv_comp', Category.id_comp, Equiv.apply_symm_apply]

@[simp] theorem homEquiv_comul :
    e.homEquiv (comul e) = e.homEquiv (inl B B) * e.homEquiv (inr B B) :=
  Equiv.apply_symm_apply _ _

@[simp] theorem homEquiv_antipode : e.homEquiv (antipode e) = (e.homEquiv (𝟙 B))⁻¹ :=
  Equiv.apply_symm_apply _ _

/-! ### Classifying maps of natural homomorphisms -/

variable {G : CommAlgCat.{u} R ⥤ GrpCat.{u}} {C : CommAlgCat.{u} R}
  (d : (G ⋙ forget GrpCat).CorepresentableBy C) (α : F ⟶ G)

/-- The algebra map `C ⟶ B` classifying the image of the universal point under `α`. -/
def classify : C ⟶ B :=
  d.homEquiv.symm (α.app B (e.homEquiv (𝟙 B)))

/-- A natural homomorphism acts on classified points by precomposition with its classifying
map. -/
theorem app_homEquiv {S : CommAlgCat.{u} R} (f : B ⟶ S) :
    α.app S (e.homEquiv f) = d.homEquiv (classify e d α ≫ f) := by
  rw [homEquiv_comp', classify, Equiv.apply_symm_apply]
  have h := ConcreteCategory.congr_hom (α.naturality f) (e.homEquiv (𝟙 B))
  change α.app S (F.map f (e.homEquiv (𝟙 B))) = G.map f (α.app B (e.homEquiv (𝟙 B))) at h
  rw [← h, ← homEquiv_comp', Category.id_comp]

/-- The classifying map intertwines the comultiplications. -/
theorem classify_comul :
    classify e d α ≫ comul e =
      comul d ≫ tensorLift (classify e d α ≫ inl B B) (classify e d α ≫ inr B B) := by
  have h := homEquiv_symm_mul d (d.homEquiv (classify e d α ≫ inl B B))
    (d.homEquiv (classify e d α ≫ inr B B))
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  apply d.homEquiv.injective
  rw [Equiv.apply_symm_apply, ← app_homEquiv, homEquiv_comul, map_mul, app_homEquiv,
    app_homEquiv]

/-- The classifying map intertwines the antipodes. -/
theorem classify_antipode :
    classify e d α ≫ antipode e = antipode d ≫ classify e d α := by
  have h := homEquiv_symm_inv d (d.homEquiv (classify e d α))
  rw [Equiv.symm_apply_apply] at h
  rw [← h]
  apply d.homEquiv.injective
  rw [Equiv.apply_symm_apply, ← app_homEquiv, homEquiv_antipode, map_inv, classify,
    Equiv.apply_symm_apply]

/-! ### Homomorphisms of corepresented group schemes -/

section GroupSchemeMaps

variable {K : CommAlgCat.{u} R ⥤ GrpCat.{u}} {D : CommAlgCat.{u} R}
  (c : (K ⋙ forget GrpCat).CorepresentableBy D)

/-- Two homomorphisms out of a corepresented group scheme agree when they agree on all affine
points. -/
theorem hom_ext_affinePoints {φ₁ φ₂ : groupScheme F e ⟶ groupScheme G d}
    (h : ∀ (S : CommAlgCat.{u} R) (f : (algSpec R).obj (op S) ⟶ (groupScheme F e).X),
      affinePointsEquiv G d S (f ≫ φ₁.hom.hom) = affinePointsEquiv G d S (f ≫ φ₂.hom.hom)) :
    φ₁ = φ₂ := by
  apply Grp.hom_ext
  have h' := (affinePointsEquiv G d B).injective (h B (𝟙 _))
  have key : ∀ {X Y : Over (Spec R)} (f g : X ⟶ Y), 𝟙 X ≫ f = 𝟙 X ≫ g → f = g :=
    fun f g hfg => by simpa using hfg
  exact key _ _ h'

/-- The natural homomorphism of point functors induced by a homomorphism of corepresented group
schemes, read off on affine points. -/
def pointsTrans (φ : groupScheme F e ⟶ groupScheme G d) : F ⟶ G where
  app S := GrpCat.ofHom
    { toFun := fun x => affinePointsEquiv G d S ((affinePointsEquiv F e S).symm x ≫ φ.hom.hom)
      map_one' := by
        rw [map_one, MonObj.one_comp, map_one]
      map_mul' := fun x y => by
        rw [map_mul, MonObj.mul_comp, map_mul] }
  naturality S S' g := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change affinePointsEquiv G d S' ((affinePointsEquiv F e S').symm (F.map g x) ≫ φ.hom.hom) =
      G.map g (affinePointsEquiv G d S ((affinePointsEquiv F e S).symm x ≫ φ.hom.hom))
    have hx : (affinePointsEquiv F e S').symm (F.map g x) =
        (algSpec R).map g.op ≫ (affinePointsEquiv F e S).symm x := by
      apply (affinePointsEquiv F e S').injective
      rw [MulEquiv.apply_symm_apply, affinePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    rw [hx, Category.assoc, affinePointsEquiv_naturality]

theorem pointsTrans_app (φ : groupScheme F e ⟶ groupScheme G d) {S : CommAlgCat.{u} R}
    (x : F.obj S) :
    (pointsTrans e d φ).app S x =
      affinePointsEquiv G d S ((affinePointsEquiv F e S).symm x ≫ φ.hom.hom) :=
  rfl

/-- Every homomorphism of corepresented group schemes is induced by its point transformation. -/
theorem groupSchemeMap_pointsTrans (φ : groupScheme F e ⟶ groupScheme G d) :
    groupSchemeMap e d (pointsTrans e d φ) = φ := by
  apply hom_ext_affinePoints
  intro S f
  rw [groupSchemeMap_affinePoints, pointsTrans_app, MulEquiv.symm_apply_apply]

/-- Induced homomorphisms compose like the natural transformations. -/
theorem groupSchemeMap_comp (α : F ⟶ G) (β : G ⟶ K) :
    groupSchemeMap e d α ≫ groupSchemeMap d c β = groupSchemeMap e c (α ≫ β) := by
  apply hom_ext_affinePoints
  intro S f
  rw [Grp.comp_hom_hom]
  change affinePointsEquiv K c S ((f ≫ (groupSchemeMap e d α).hom.hom) ≫
    (groupSchemeMap d c β).hom.hom) = _
  rw [groupSchemeMap_affinePoints, groupSchemeMap_affinePoints, groupSchemeMap_affinePoints]
  rfl

/-- The scheme map of an induced homomorphism is the spectrum of its classifying map. -/
theorem groupSchemeMap_hom_left (α : F ⟶ G) :
    (groupSchemeMap e d α).hom.hom.left =
      Spec.map (CommRingCat.ofHom (classify e d α).hom.toRingHom) :=
  groupSchemeMap_hom e d α

end GroupSchemeMaps

/-! ### Centrality -/

section Centrality

theorem commute_of_mulEquiv {M N : Type*} [Mul M] [Mul N] (f : M ≃* N) {a b : M}
    (h : Commute (f a) (f b)) : Commute a b := by
  simpa using h.map f.symm

/-- An induced homomorphism is central when its values commute with all points of the target
over every test algebra. -/
theorem isCentral_groupSchemeMap (α : F ⟶ G)
    (h : ∀ (S : CommAlgCat.{u} R) (x : F.obj S) (y : G.obj S), Commute (α.app S x) y) :
    IsCentral (groupSchemeMap e d α) := by
  intro T x T' a y
  rw [← Category.assoc]
  apply commute_of_mulEquiv (pointsEquiv G d T')
  rw [groupSchemeMap_points]
  exact h _ _ _

/-- The point transformation of a central homomorphism has central values. -/
theorem IsCentral.commute_pointsTrans {φ : groupScheme F e ⟶ groupScheme G d}
    (hφ : IsCentral φ) (S : CommAlgCat.{u} R) (x : F.obj S) (y : G.obj S) :
    Commute ((pointsTrans e d φ).app S x) y := by
  have h := commute_of_mem_center (hφ _ ((affinePointsEquiv F e S).symm x))
    ((affinePointsEquiv G d S).symm y)
  have h' := h.map (affinePointsEquiv G d S)
  rwa [MulEquiv.apply_symm_apply] at h'

end Centrality

end Langlands.GroupScheme.Corepresented

namespace Langlands.GroupScheme

/-- Postcomposition with an isomorphism preserves centrality. -/
theorem IsCentral.comp_iso {S : Scheme.{u}} {H G G' : GroupScheme S} {i : H ⟶ G}
    (hi : IsCentral i) (e : G ≅ G') : IsCentral (i ≫ e.hom) := by
  intro T x T' a y
  have h := (hi T x T' a (y ≫ e.inv.hom.hom)).map (isoPointsEquiv e T')
  simp only [isoPointsEquiv_apply, Category.assoc] at h
  have hy : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 _ := by
    rw [← Grp.comp_hom_hom, e.inv_hom_id, Grp.id_hom_hom]
  rw [hy, Category.comp_id] at h
  rw [Grp.comp_hom_hom]
  simpa only [Category.assoc] using h

end Langlands.GroupScheme
