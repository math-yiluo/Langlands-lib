import Langlands.GroupScheme.Dynamic.CoactionContracting
import Langlands.GroupScheme.Dynamic.AffineChart
import Langlands.GroupScheme.Dynamic.BaseChange

/-! # Points of the base change of a corepresented group, in tensor coordinates

Let `G = Spec B` be a corepresented affine group over a field `k` and `Ω` a field extension of
`k`. A point of `G_Ω` over an `Ω`-algebra `A` is classified by the `Ω`-algebra map
`Ω ⊗[k] B → A` built from its underlying `k`-point `B → A`. In particular every such point is
pulled back from the universal point over `Ω ⊗[k] B`. For a homomorphism `π : G_Ω ⟶ H` to an
affine `Ω`-group, the functions on `H` therefore pull back to `Ω ⊗[k] B` compatibly with all
points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}

section Points

variable (Ω : Type u) [Field Ω] [Algebra k Ω]

variable (k) in
/-- The morphism `Spec Ω ⟶ Spec k`. -/
abbrev scalarMap : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k Ω))

variable (A : Type u) [CommRing A] [Algebra k A] [Algebra Ω A] [IsScalarTower k Ω A]

/-- `Spec A` as a scheme over `Spec Ω`. -/
abbrev testOver : Over (Spec (CommRingCat.of Ω)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Ω A)))

theorem specMap_algebraMap_comp_scalarMap :
    Spec.map (CommRingCat.ofHom (algebraMap Ω A)) ≫ scalarMap k Ω =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `Spec A` over `Spec k`, compared with `Spec A` over `Spec Ω` regarded over `Spec k`. -/
def testOverHom :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
      (Over.map (scalarMap k Ω)).obj (testOver Ω A) :=
  Over.homMk (𝟙 _) (by
    rw [Category.id_comp]
    exact specMap_algebraMap_comp_scalarMap (k := k) Ω A)

/-- The inverse comparison of `testOverHom`. -/
def testOverInv :
    (Over.map (scalarMap k Ω)).obj (testOver Ω A) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) :=
  Over.homMk (𝟙 _) (by
    rw [Category.id_comp]
    exact (specMap_algebraMap_comp_scalarMap (k := k) Ω A).symm)

theorem testOverHom_comp_testOverInv :
    testOverHom (k := k) Ω A ≫ testOverInv (k := k) Ω A = 𝟙 _ :=
  Over.OverMorphism.ext (Category.id_comp _)

variable (F e) in
/-- The base change `G_Ω` of `G = Spec B`. -/
abbrev baseChangeGroup : GroupScheme (Spec (CommRingCat.of Ω)) :=
  (GroupScheme.baseChange (scalarMap k Ω)).obj (groupScheme F e)

variable {Ω A}

/-- The `k`-point of `G` underlying a point of `G_Ω` over `Spec A`. -/
def basePoint (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶ (groupScheme F e).X :=
  testOverHom Ω A ≫ baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A) z

variable (F e) in
/-- The point of `G` over `Spec A` classified by a `k`-algebra map `B → A`. -/
def ofAlgHom {A' : Type u} [CommRing A'] [Algebra k A'] (φ : B →ₐ[k] A') :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A'))) ⟶ (groupScheme F e).X :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext φ.commutes)

theorem pointAlgHom_ofAlgHom {A' : Type u} [CommRing A'] [Algebra k A'] (φ : B →ₐ[k] A') :
    pointAlgHom (ofAlgHom F e φ) = φ := by
  ext b
  rw [pointAlgHom_apply]
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))) b = φ b
  rw [Spec.preimage_map]
  rfl

theorem ofAlgHom_pointAlgHom {A' : Type u} [CommRing A'] [Algebra k A']
    (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A'))) ⟶ (groupScheme F e).X) :
    ofAlgHom F e (pointAlgHom x) = x := by
  apply hom_ext_of_pointRing
  ext b
  exact congrArg (fun φ : B →ₐ[k] A' => φ b) (pointAlgHom_ofAlgHom (pointAlgHom x))

variable (F e Ω A) in
/-- The point of `G_Ω` over `Spec A` obtained by base change from the `k`-point classified by
`φ : B → A`. -/
def bcPoint (φ : B →ₐ[k] A) : testOver Ω A ⟶ (baseChangeGroup F e Ω).X :=
  (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A)).symm
    (testOverInv Ω A ≫ ofAlgHom F e φ)

theorem basePoint_bcPoint (φ : B →ₐ[k] A) : basePoint (bcPoint F e Ω A φ) = ofAlgHom F e φ := by
  rw [basePoint, bcPoint, MulEquiv.apply_symm_apply, ← Category.assoc,
    testOverHom_comp_testOverInv, Category.id_comp]

theorem pointAlgHom_basePoint_bcPoint (φ : B →ₐ[k] A) :
    pointAlgHom (basePoint (bcPoint F e Ω A φ)) = φ := by
  rw [basePoint_bcPoint, pointAlgHom_ofAlgHom]

/-- The `Ω`-algebra map `Ω ⊗[k] B → A` classifying a point of `G_Ω` over `Spec A`. -/
def classifying (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) : Ω ⊗[k] B →ₐ[Ω] A :=
  Algebra.TensorProduct.lift (Algebra.ofId Ω A) (pointAlgHom (basePoint z))
    fun _ _ => Commute.all _ _

/-- The morphism `Spec A ⟶ Spec (Ω ⊗[k] B)` over `Spec Ω` given by `classifying z`. -/
def classifyingHom (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) :
    testOver Ω A ⟶ testOver Ω (Ω ⊗[k] B) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (classifying z).toRingHom)) (by
    change _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext (classifying z).commutes)

variable (F e Ω) in
/-- The universal point of `G_Ω` over `Spec (Ω ⊗[k] B)`. -/
def univPoint : testOver Ω (Ω ⊗[k] B) ⟶ (baseChangeGroup F e Ω).X :=
  bcPoint F e Ω (Ω ⊗[k] B) Algebra.TensorProduct.includeRight

/-- Every point of `G_Ω` is pulled back from the universal point. -/
theorem classifyingHom_comp_univPoint (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) :
    classifyingHom z ≫ univPoint F e Ω = z := by
  apply (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A)).injective
  rw [baseChangePointsEquiv_naturality, univPoint, bcPoint, MulEquiv.apply_symm_apply]
  apply Over.OverMorphism.ext
  have h : (basePoint z).left =
      (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A) z).left := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  rw [← h, ← specMap_pointRing (basePoint z)]
  change Spec.map (CommRingCat.ofHom (classifying z).toRingHom) ≫ 𝟙 _ ≫
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom)) = _
  rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext b
  change classifying z (1 ⊗ₜ b) = pointRing (basePoint z) b
  rw [classifying, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end Points

section Comparison

variable {Ω : Type u} [Field Ω] [Algebra k Ω] {H : GroupScheme (Spec (CommRingCat.of Ω))}
  [IsAffine H.X.left]

variable (π : baseChangeGroup F e Ω ⟶ H)

/-- The pullback of functions on `H` along `π : G_Ω ⟶ H`, in the tensor coordinates
`Ω ⊗[k] B`. -/
def comparisonMap : Γ(H.X.left, ⊤) ⟶ CommRingCat.of (Ω ⊗[k] B) :=
  Dynamic.AffineChart.pointRing (univPoint F e Ω ≫ π.hom.hom)

variable {A : Type u} [CommRing A] [Algebra k A] [Algebra Ω A] [IsScalarTower k Ω A]

/-- The image under `π` of a point of `G_Ω` is classified by `comparisonMap π` followed by the
classifying map of the point. -/
theorem pointRing_comp_eq (z : testOver Ω A ⟶ (baseChangeGroup F e Ω).X) :
    Dynamic.AffineChart.pointRing (z ≫ π.hom.hom) =
      comparisonMap π ≫ CommRingCat.ofHom (classifying z).toRingHom := by
  conv_lhs => rw [← classifyingHom_comp_univPoint z, Category.assoc,
    Dynamic.AffineChart.pointRing_comp]
  rw [comparisonMap]
  congr 1
  exact Spec.preimage_map _

end Comparison

end Corepresented

end Langlands.GroupScheme
