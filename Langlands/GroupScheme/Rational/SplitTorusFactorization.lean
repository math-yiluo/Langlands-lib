import Langlands.GroupScheme.Rational.SplitTorusImage
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Factorizations of split tori through maximal and central split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-! ### Product homomorphisms -/

section Product

variable {S : Scheme.{u}} {A B M : GroupScheme S}

variable (a : A ⟶ M) (b : B ⟶ M)
  (hab : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X), Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))

/-- On points, the product homomorphism is `(x, y) ↦ a(x) * b(y)`. -/
def prodPoints (T : Over S) : (T ⟶ (A ⊗ B).X) →* (T ⟶ M.X) where
  toFun p := ((productPointsEquiv A B T p).1 ≫ a.hom.hom) *
    ((productPointsEquiv A B T p).2 ≫ b.hom.hom)
  map_one' := by
    rw [map_one, Prod.fst_one, Prod.snd_one, MonObj.one_comp, MonObj.one_comp, mul_one]
  map_mul' p q := by
    rw [map_mul, Prod.fst_mul, Prod.snd_mul, MonObj.mul_comp, MonObj.mul_comp]
    exact (hab T _ _).mul_mul_mul_comm _ _

theorem prodPoints_naturality {T T' : Over S} (f : T' ⟶ T) (p : T ⟶ (A ⊗ B).X) :
    prodPoints a b hab T' (f ≫ p) = f ≫ prodPoints a b hab T p := by
  change ((productPointsEquiv A B _ (f ≫ p)).1 ≫ a.hom.hom) *
      ((productPointsEquiv A B _ (f ≫ p)).2 ≫ b.hom.hom) =
    f ≫ (((productPointsEquiv A B _ p).1 ≫ a.hom.hom) *
      ((productPointsEquiv A B _ p).2 ≫ b.hom.hom))
  rw [productPointsEquiv_naturality, MonObj.comp_mul, Category.assoc, Category.assoc]

/-- The product homomorphism `A × B ⟶ M`, `(x, y) ↦ a(x) * b(y)`, of two homomorphisms whose
values commute. -/
def prodHom : A ⊗ B ⟶ M :=
  homOfPoints (prodPoints a b hab) (prodPoints_naturality a b hab)

theorem comp_prodHom (T : Over S) (p : T ⟶ (A ⊗ B).X) :
    p ≫ (prodHom a b hab).hom.hom =
      ((productPointsEquiv A B T p).1 ≫ a.hom.hom) *
        ((productPointsEquiv A B T p).2 ≫ b.hom.hom) :=
  comp_homOfPoints (prodPoints a b hab) (prodPoints_naturality a b hab) T p

variable (A B)

/-- On points, the first inclusion is `x ↦ (x, 1)`. -/
def inlPoints (T : Over S) : (T ⟶ A.X) →* (T ⟶ (A ⊗ B).X) :=
  (productPointsEquiv A B T).symm.toMonoidHom.comp (MonoidHom.inl _ _)

theorem inlPoints_naturality {T T' : Over S} (f : T' ⟶ T) (x : T ⟶ A.X) :
    inlPoints A B T' (f ≫ x) = f ≫ inlPoints A B T x := by
  apply (productPointsEquiv A B _).injective
  rw [productPointsEquiv_naturality]
  simp [inlPoints, MonObj.comp_one]

/-- On points, the second inclusion is `y ↦ (1, y)`. -/
def inrPoints (T : Over S) : (T ⟶ B.X) →* (T ⟶ (A ⊗ B).X) :=
  (productPointsEquiv A B T).symm.toMonoidHom.comp (MonoidHom.inr _ _)

theorem inrPoints_naturality {T T' : Over S} (f : T' ⟶ T) (y : T ⟶ B.X) :
    inrPoints A B T' (f ≫ y) = f ≫ inrPoints A B T y := by
  apply (productPointsEquiv A B _).injective
  rw [productPointsEquiv_naturality]
  simp [inrPoints, MonObj.comp_one]

/-- The inclusion `x ↦ (x, 1)` of the first factor. -/
def prodInl : A ⟶ A ⊗ B :=
  homOfPoints (inlPoints A B) (inlPoints_naturality A B)

/-- The inclusion `y ↦ (1, y)` of the second factor. -/
def prodInr : B ⟶ A ⊗ B :=
  homOfPoints (inrPoints A B) (inrPoints_naturality A B)

variable {A B}

theorem prodInl_prodHom : prodInl A B ≫ prodHom a b hab = a := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, prodInl, comp_homOfPoints, comp_prodHom]
  simp [inlPoints, MonObj.one_comp]

theorem prodInr_prodHom : prodInr A B ≫ prodHom a b hab = b := by
  apply hom_ext_points
  intro T y
  rw [Grp.comp_hom_hom, ← Category.assoc, prodInr, comp_homOfPoints, comp_prodHom]
  simp [inrPoints, MonObj.one_comp]

/-- The product of two central homomorphisms is central. -/
theorem isCentral_prodHom (ha : IsCentral a) (hb : IsCentral b) :
    IsCentral (prodHom a b hab) := by
  intro T p
  rw [comp_prodHom]
  exact Subgroup.mul_mem _ (ha T _) (hb T _)

end Product

/-- The values of a central homomorphism commute with the values of every homomorphism. -/
theorem IsCentral.commute_values {S : Scheme.{u}} {A B M : GroupScheme S} {a : A ⟶ M}
    (ha : IsCentral a) (b : B ⟶ M) (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X) :
    Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom) :=
  commute_of_mem_center (ha T x) _

/-! ### Factorizations over a field -/

section Field

variable {k : Type u} [Field k]

/-- The image theorem for a split torus given as a group scheme (not necessarily presented as a
commutative group scheme). -/
theorem IsSplitTorus.exists_factor_isSplitSubtorus' {D : GroupScheme (Spec (CommRingCat.of k))}
    (hD : IsSplitTorus D) {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (φ : D ⟶ H) :
    ∃ (D' : CommGroupScheme (Spec (CommRingCat.of k))) (π : D ⟶ D'.toGrp)
      (i : D'.toGrp ⟶ H), IsSplitSubtorus i ∧ π ≫ i = φ ∧ (IsCentral φ → IsCentral i) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hD
  obtain ⟨D', π, i, hi, hπ, hc⟩ := IsSplitTorus.exists_factor_isSplitSubtorus
    (D := splitTorus.commGroupScheme _ I) (isSplitTorus_splitTorus I) (e.inv ≫ φ)
  refine ⟨D', e.hom ≫ π, i, hi, ?_, fun h => hc (h.comp e.inv)⟩
  rw [Category.assoc, hπ, Iso.hom_inv_id_assoc]

variable {G M : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom M.X.hom]

/-- Let `j : M ⟶ G` be a closed subgroup and `t : T ⟶ M` a homomorphism such that
`t ≫ j` is a maximal split torus of `G`. Then every central split torus of `M` factors through
`t`. -/
theorem IsCentralSplitTorus.exists_factor_of_isMaximalSplitTorus {j : M ⟶ G}
    (hjc : IsClosedSubgroup j) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {t : T.toGrp ⟶ M} (ht : IsMaximalSplitTorus (t ≫ j))
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
    (ha : IsCentralSplitTorus a) : ∃ g : A.toGrp ⟶ T.toGrp, g ≫ t = a := by
  let hab := ha.2.commute_values t
  obtain ⟨D', π, i', hi', hπ, -⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus' (ha.1.1.tensor ht.1.1) (prodHom a t hab)
  have hsub : IsSplitSubtorus (i' ≫ j) := ⟨hi'.1, hi'.2.comp hjc⟩
  have he : (prodInr A.toGrp T.toGrp ≫ π) ≫ i' = t := by
    rw [Category.assoc, hπ, prodInr_prodHom]
  have hiso : IsIso (prodInr A.toGrp T.toGrp ≫ π) :=
    ht.2 D' (i' ≫ j) hsub _ (by rw [← Category.assoc, he])
  refine ⟨(prodInl A.toGrp T.toGrp ≫ π) ≫ inv (prodInr A.toGrp T.toGrp ≫ π), ?_⟩
  rw [← he, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hπ, prodInl_prodHom]

/-- Every central homomorphism from a split torus to `M` factors through every split component
of `M`. -/
theorem IsSplitComponent.exists_factor {A : CommGroupScheme (Spec (CommRingCat.of k))}
    {iA : A.toGrp ⟶ M} (hA : IsSplitComponent iA) {B : GroupScheme (Spec (CommRingCat.of k))}
    (hB : IsSplitTorus B) {b : B ⟶ M} (hb : IsCentral b) : ∃ f : B ⟶ A.toGrp, f ≫ iA = b := by
  let hab := hb.commute_values iA
  obtain ⟨D', π, i', hi', hπ, hc⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus' (hB.tensor hA.1.1.1) (prodHom b iA hab)
  have hcent : IsCentralSplitTorus i' := ⟨hi', hc (isCentral_prodHom b iA hab hb hA.1.2)⟩
  have he : (prodInr B A.toGrp ≫ π) ≫ i' = iA := by
    rw [Category.assoc, hπ, prodInr_prodHom]
  have hiso : IsIso (prodInr B A.toGrp ≫ π) := hA.2 D' i' hcent _ he
  refine ⟨(prodInl B A.toGrp ≫ π) ≫ inv (prodInr B A.toGrp ≫ π), ?_⟩
  rw [← he, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hπ, prodInl_prodHom]

end Field

section Maximality

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {M B : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom M.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : T.toGrp ⟶ M}

/-- A split-torus map commuting with a maximal split torus factors through it. -/
theorem IsMaximalSplitTorus.exists_factor_of_commute
    (hj : IsMaximalSplitTorus j) (hB : IsSplitTorus B) (b : B ⟶ M)
    (hbj : ∀ (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ B.X) (y : U ⟶ T.X),
      Commute (x ≫ b.hom.hom) (y ≫ j.hom.hom)) :
    ∃ f : B ⟶ T.toGrp, f ≫ j = b := by
  obtain ⟨T', π, i', hi', hπ, -⟩ :=
    IsSplitTorus.exists_factor_isSplitSubtorus' (hB.tensor hj.1.1)
      (prodHom b j hbj)
  have he : (prodInr B T.toGrp ≫ π) ≫ i' = j := by
    rw [Category.assoc, hπ, prodInr_prodHom]
  have hiso : IsIso (prodInr B T.toGrp ≫ π) := hj.2 T' i' hi' _ he
  refine ⟨(prodInl B T.toGrp ≫ π) ≫ inv (prodInr B T.toGrp ≫ π), ?_⟩
  rw [← he, Category.assoc, IsIso.inv_hom_id_assoc, Category.assoc, hπ, prodInl_prodHom]

end Maximality

end Langlands.GroupScheme
