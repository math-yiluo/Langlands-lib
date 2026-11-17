import Langlands.GroupScheme.Reductive.WeilChartWeilIso
import Langlands.GroupScheme.Descent.EtaleReflection
import Langlands.GroupScheme.NormalQuotientReductiveGluing
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.RelativeLevi.GeometricFiberComparison

/-! # The descended factor group over the cover -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option maxRecDepth 4000

namespace Langlands.GroupScheme.WeilChart

open Langlands.Algebra.GraphIdempotent IdempotentPoints

variable {A A' C B : Type u} [CommRing A] [CommRing A'] [CommRing C] [CommRing B]
  [Algebra A A'] [Algebra A' C] [Algebra A B] (e : A' ⊗[A] B ≃ₐ[A'] C)

section ChartNaturality

variable [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C] in
theorem diagMap_resBHom {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) (c : C) :
    diagMap e (structB X') (chartPush (resBHom χ) g) c =
      (resBHom (A := A) χ).hom (diagMap e (structB X) g c) := by
  obtain ⟨x, rfl⟩ := e.surjective c
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [diagMap_tmul, diagMap_tmul, map_mul]
    congr 1
    exact (χ.hom.commutes b).symm
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- The map of chart objects induced by a map of `B`-algebras, compatible with chart maps. -/
def chartObjMap {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) :
    chartObj e (structB X) g ⟶ chartObj e (structB X') (chartPush (resBHom χ) g) :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of C))
    (X := chartObj e (structB X) g) (Y := chartObj e (structB X') (chartPush (resBHom χ) g))
    (@AlgHom.mk (CommRingCat.of C) (chartObj e (structB X) g)
      (chartObj e (structB X') (chartPush (resBHom χ) g)) _ _ _
      (CommAlgCat.algebra (chartObj e (structB X) g))
      (CommAlgCat.algebra (chartObj e (structB X') (chartPush (resBHom χ) g)))
      (resBHom (A := A) χ).hom.toRingHom
      (fun c => (diagMap_resBHom e χ g c).symm))

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C] in
theorem chartObjMap_apply {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) (x : X) :
    (chartObjMap e χ g).hom x = χ.hom x :=
  rfl

variable (B) in
/-- A map of `B`-algebras as a map of `A'`-algebras between the test objects with chart maps. -/
def resBChart {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X') (g : A' →ₐ[A] resB A X) :
    letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
    letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
    (Under.mk (𝟙 (resB A X))).right →ₐ[A'] (Under.mk (𝟙 (resB A X'))).right :=
  letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
  letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
  { (resBHom (A := A) χ).hom.toRingHom with commutes' := fun _ => rfl }

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C] in
theorem chartMu_lTensor {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) :
    (chartMu e (structB X') (chartPush (resBHom χ) g)).comp
        (letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
         letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
         Algebra.TensorProduct.lTensor (S := C) C (resBChart B χ g)) =
      (chartObjMap e χ g).hom.comp (chartMu e (structB X) g) := by
  letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
  letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
  apply Algebra.TensorProduct.ext'
  intro c x
  change chartMu e (structB X') (chartPush (resBHom χ) g) (c ⊗ₜ[A'] resBChart B χ g x) =
    (chartObjMap e χ g).hom (chartMu e (structB X) g (c ⊗ₜ[A'] x))
  rw [chartMu_apply, chartMu_apply, Algebra.TensorProduct.productMap_apply_tmul,
    Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply, AlgHom.id_apply, map_mul]
  congr 1
  exact diagMap_resBHom e χ g c

end ChartNaturality

section FactorNaturality

variable [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  [Module.FaithfullyFlat A A']
  (hinv : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
    chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b)))

omit [Algebra.Etale A' C] [Module.FaithfullyFlat A A'] in
theorem underPointsEquiv_resBHom {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) (q : G.affinePoints (resB A X)) :
    underPointsEquiv P (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
        (G.affinePointMap (resBHom χ) q) =
      H.affinePointMap (CommAlgCat.ofHom (letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
        letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
        Algebra.TensorProduct.lTensor (S := C) C (resBChart B χ g)))
        (underPointsEquiv P g (Under.mk (𝟙 (resB A X))) q) := by
  letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
  letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
  haveI := underAlgebra_isScalarTower g (Under.mk (𝟙 (resB A X)))
  haveI := underAlgebra_isScalarTower (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
  exact chartPointsEquiv_naturality P (Under.mk (𝟙 (resB A X))).right
    (Under.mk (𝟙 (resB A X'))).right (resBChart B χ g) q

variable [IsAffine G.X.left]

theorem factorChartEquiv_naturality {X X' : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ X')
    (g : A' →ₐ[A] resB A X) (y : (factorGroup e P hR hred hsimple hinv).affinePoints X) :
    factorChartEquiv e P hR hred hsimple hinv X' (chartPush (resBHom χ) g)
        ((factorGroup e P hR hred hsimple hinv).affinePointMap χ y) =
      H.affinePointMap (chartObjMap e χ g) (factorChartEquiv e P hR hred hsimple hinv X g y) := by
  have key : ∀ (Z : CommAlgCat.{u} (CommRingCat.of B)) (h : A' →ₐ[A] resB A Z)
      (z : (factorGroup e P hR hred hsimple hinv).affinePoints Z),
      factorChartEquiv e P hR hred hsimple hinv Z h z =
        H.affinePointMap (CommAlgCat.ofHom (chartMu e (structB Z) h))
          (underPointsEquiv P h (Under.mk (𝟙 (resB A Z)))
            (bPointsEquiv G Z (factorPointsEquiv e P hR hred hsimple hinv Z z : _))) :=
    fun _ _ _ => rfl
  have hb : ∀ p, bPointsEquiv G X'
      (((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ p) =
      G.affinePointMap (resBHom χ) (bPointsEquiv G X p) := by
    intro p
    rw [← (bPointsEquiv G X).symm_apply_apply p, bPointsEquiv_symm_naturality,
      MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [key, key, factorPointsEquiv_naturality, hb, underPointsEquiv_resBHom, ← MonoidHom.comp_apply,
    ← H.affinePointMap_comp, ← MonoidHom.comp_apply, ← H.affinePointMap_comp]
  have hc : CommAlgCat.ofHom (letI := underAlgebra g (Under.mk (𝟙 (resB A X)))
        letI := underAlgebra (chartPush (resBHom χ) g) (Under.mk (𝟙 (resB A X')))
        Algebra.TensorProduct.lTensor (S := C) C (resBChart B χ g)) ≫
      CommAlgCat.ofHom (chartMu e (structB X') (chartPush (resBHom χ) g)) =
      CommAlgCat.ofHom (chartMu e (structB X) g) ≫ chartObjMap e χ g :=
    CommAlgCat.hom_ext (chartMu_lTensor e χ g)
  rw [hc]

section Cover

variable [Algebra B C] (hBC : ∀ b : B, algebraMap B C b = e ((1 : A') ⊗ₜ[A] b))

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  [Module.FaithfullyFlat A A'] [Algebra B C] in
theorem e_one_tmul_algebraMap (a : A) :
    e ((1 : A') ⊗ₜ[A] algebraMap A B a) = algebraMap A' C (algebraMap A A' a) := by
  rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← AlgEquiv.commutes e,
    Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

variable (B) in
/-- A `C`-algebra regarded as a `B`-algebra. -/
abbrev coverB (Y : CommAlgCat.{u} (CommRingCat.of C)) : CommAlgCat.{u} (CommRingCat.of B) :=
  letI : Algebra B Y := Algebra.compHom Y (algebraMap B C)
  CommAlgCat.of (CommRingCat.of B) Y

include hBC in
/-- The chart map `A' → C → Y` of a `C`-algebra `Y`. -/
def coverChart (Y : CommAlgCat.{u} (CommRingCat.of C)) : A' →ₐ[A] resB A (coverB B Y) :=
  { (algebraMap C Y).comp (algebraMap A' C) with
    commutes' := fun a => by
      change algebraMap C Y (algebraMap A' C (algebraMap A A' a)) =
        algebraMap C Y (algebraMap B C (algebraMap A B a))
      rw [hBC, e_one_tmul_algebraMap] }

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  [Module.FaithfullyFlat A A'] in
theorem coverChart_apply (Y : CommAlgCat.{u} (CommRingCat.of C)) (a : A') :
    coverChart e hBC Y a = algebraMap C Y (algebraMap A' C a) :=
  rfl

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  [Module.FaithfullyFlat A A'] in
theorem diagMap_cover (Y : CommAlgCat.{u} (CommRingCat.of C)) (c : C) :
    diagMap e (structB (coverB B Y)) (coverChart e hBC Y) c = (algebraMap C Y c : Y) := by
  obtain ⟨x, rfl⟩ := e.surjective c
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [diagMap_tmul, descentEquiv_tmul e a b, Algebra.smul_def, map_mul, ← hBC]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The identity of `Y`, from its chart object to `Y`, for a chart map inducing the given
`C`-algebra structure. -/
def chartObjToY (Y : CommAlgCat.{u} (CommRingCat.of C)) (g : A' →ₐ[A] resB A (coverB B Y))
    (hg : ∀ c, diagMap e (structB (coverB B Y)) g c = (algebraMap C Y c : Y)) :
    chartObj e (structB (coverB B Y)) g ⟶ Y :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of C))
    (X := chartObj e (structB (coverB B Y)) g) (Y := Y)
    (@AlgHom.mk (CommRingCat.of C) (chartObj e (structB (coverB B Y)) g) Y _ _ _
      (CommAlgCat.algebra _) (CommAlgCat.algebra Y) (RingHom.id Y) (fun c => hg c))

omit [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  [Module.FaithfullyFlat A A'] in
theorem chartObjToY_apply (Y : CommAlgCat.{u} (CommRingCat.of C))
    (g : A' →ₐ[A] resB A (coverB B Y))
    (hg : ∀ c, diagMap e (structB (coverB B Y)) g c = (algebraMap C Y c : Y)) (x : Y) :
    (chartObjToY e Y g hg).hom x = x :=
  rfl

omit [Algebra B C] in
theorem factorChartEquiv_congr (X : CommAlgCat.{u} (CommRingCat.of B))
    (Z : CommAlgCat.{u} (CommRingCat.of C)) {g₁ g₂ : A' →ₐ[A] resB A X} (h : g₁ = g₂)
    (κ₁ : chartObj e (structB X) g₁ ⟶ Z) (κ₂ : chartObj e (structB X) g₂ ⟶ Z)
    (hκ : ∀ x : X, κ₁.hom x = κ₂.hom x)
    (y : (factorGroup e P hR hred hsimple hinv).affinePoints X) :
    H.affinePointMap κ₁ (factorChartEquiv e P hR hred hsimple hinv X g₁ y) =
      H.affinePointMap κ₂ (factorChartEquiv e P hR hred hsimple hinv X g₂ y) := by
  subst h
  have : κ₁ = κ₂ := CommAlgCat.hom_ext (DFunLike.ext _ _ hκ)
  rw [this]

/-- The points of `G'` over a `C`-algebra `Y`, regarded as a `B`-algebra, are the points of
`H` over `Y`. -/
def coverEquivB (Y : CommAlgCat.{u} (CommRingCat.of C)) :
    (factorGroup e P hR hred hsimple hinv).affinePoints (coverB B Y) ≃* H.affinePoints Y :=
  (factorChartEquiv e P hR hred hsimple hinv (coverB B Y) (coverChart e hBC Y)).trans
    (MulEquiv.ofBijective
      (H.affinePointMap (chartObjToY e Y (coverChart e hBC Y) (diagMap_cover e hBC Y)))
      (affinePointMap_bijective H _ Function.bijective_id))

theorem coverEquivB_apply (Y : CommAlgCat.{u} (CommRingCat.of C))
    (y : (factorGroup e P hR hred hsimple hinv).affinePoints (coverB B Y)) :
    coverEquivB e P hR hred hsimple hinv hBC Y y =
      H.affinePointMap (chartObjToY e Y (coverChart e hBC Y) (diagMap_cover e hBC Y))
        (factorChartEquiv e P hR hred hsimple hinv (coverB B Y) (coverChart e hBC Y) y) :=
  rfl

variable (B) in
/-- A map of `C`-algebras, as a map of `B`-algebras. -/
def coverBMap {Y Y' : CommAlgCat.{u} (CommRingCat.of C)} (χ : Y ⟶ Y') :
    coverB B Y ⟶ coverB B Y' :=
  letI : Algebra B Y := Algebra.compHom Y (algebraMap B C)
  letI : Algebra B Y' := Algebra.compHom Y' (algebraMap B C)
  CommAlgCat.ofHom (X := Y) (Y := Y')
    { χ.hom.toRingHom with commutes' := fun b => χ.hom.commutes (algebraMap B C b) }

theorem coverEquivB_naturality {Y Y' : CommAlgCat.{u} (CommRingCat.of C)} (χ : Y ⟶ Y')
    (y : (factorGroup e P hR hred hsimple hinv).affinePoints (coverB B Y)) :
    coverEquivB e P hR hred hsimple hinv hBC Y'
        ((factorGroup e P hR hred hsimple hinv).affinePointMap (coverBMap B χ) y) =
      H.affinePointMap χ (coverEquivB e P hR hred hsimple hinv hBC Y y) := by
  have hg : coverChart e hBC Y' = chartPush (resBHom (coverBMap B χ)) (coverChart e hBC Y) := by
    apply AlgHom.ext
    intro a
    exact (χ.hom.commutes (algebraMap A' C a)).symm
  have hg' : ∀ c, diagMap e (structB (coverB B Y'))
      (chartPush (resBHom (coverBMap B χ)) (coverChart e hBC Y)) c = (algebraMap C Y' c : Y') := by
    intro c
    rw [diagMap_resBHom, diagMap_cover]
    exact χ.hom.commutes c
  have h1 := factorChartEquiv_congr e P hR hred hsimple hinv (coverB B Y') Y' hg
    (chartObjToY e Y' (coverChart e hBC Y') (diagMap_cover e hBC Y'))
    (chartObjToY e Y' _ hg') (fun _ => rfl)
    ((factorGroup e P hR hred hsimple hinv).affinePointMap (coverBMap B χ) y)
  rw [coverEquivB_apply, coverEquivB_apply, h1, factorChartEquiv_naturality, ← MonoidHom.comp_apply, ← H.affinePointMap_comp,
    ← MonoidHom.comp_apply, ← H.affinePointMap_comp]
  rfl

/-- Points of `G'_C` over a `C`-algebra are points of `G'` over it as a `B`-algebra. -/
def coverPointsEquiv (Y : CommAlgCat.{u} (CommRingCat.of C)) :
    ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
        (factorGroup e P hR hred hsimple hinv)).affinePoints Y ≃*
      (factorGroup e P hR hred hsimple hinv).affinePoints (coverB B Y) :=
  letI : Algebra B Y := Algebra.compHom Y (algebraMap B C)
  haveI : IsScalarTower B C Y := IsScalarTower.of_algebraMap_eq' rfl
  (affinePointsBaseChangeMulEquiv B C Y (factorGroup e P hR hred hsimple hinv)).symm

theorem coverPointsEquiv_naturality {Y Y' : CommAlgCat.{u} (CommRingCat.of C)} (χ : Y ⟶ Y')
    (z : ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
      (factorGroup e P hR hred hsimple hinv)).affinePoints Y) :
    coverPointsEquiv e P hR hred hsimple hinv Y'
        (((GroupScheme.baseChange (Spec.algebraMap B C)).obj
          (factorGroup e P hR hred hsimple hinv)).affinePointMap χ z) =
      (factorGroup e P hR hred hsimple hinv).affinePointMap (coverBMap B χ)
        (coverPointsEquiv e P hR hred hsimple hinv Y z) := by
  letI : Algebra B Y := Algebra.compHom Y (algebraMap B C)
  haveI : IsScalarTower B C Y := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra B Y' := Algebra.compHom Y' (algebraMap B C)
  haveI : IsScalarTower B C Y' := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨p, rfl⟩ := (coverPointsEquiv e P hR hred hsimple hinv Y).symm.surjective z
  rw [MulEquiv.apply_symm_apply]
  apply (coverPointsEquiv e P hR hred hsimple hinv Y').symm.injective
  rw [MulEquiv.symm_apply_apply]
  exact affinePointsBaseChangeMulEquiv_naturality (R := B) (S := C) (A := Y) (A' := Y')
    (factorGroup e P hR hred hsimple hinv) χ.hom p

/-- The total point comparison `G'_C(Y) ≃* H(Y)`. -/
def coverTotalEquiv (Y : CommAlgCat.{u} (CommRingCat.of C)) :
    ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
        (factorGroup e P hR hred hsimple hinv)).affinePoints Y ≃* H.affinePoints Y :=
  (coverPointsEquiv e P hR hred hsimple hinv Y).trans (coverEquivB e P hR hred hsimple hinv hBC Y)

theorem coverTotalEquiv_naturality {Y Y' : CommAlgCat.{u} (CommRingCat.of C)} (χ : Y ⟶ Y')
    (z : ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
      (factorGroup e P hR hred hsimple hinv)).affinePoints Y) :
    coverTotalEquiv e P hR hred hsimple hinv hBC Y'
        (((GroupScheme.baseChange (Spec.algebraMap B C)).obj
          (factorGroup e P hR hred hsimple hinv)).affinePointMap χ z) =
      H.affinePointMap χ (coverTotalEquiv e P hR hred hsimple hinv hBC Y z) := by
  simp only [coverTotalEquiv, MulEquiv.trans_apply]
  rw [coverPointsEquiv_naturality, coverEquivB_naturality]

/-- The natural isomorphism of point functors `G'_C ≅ H`. -/
def coverNatIso : ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
      (factorGroup e P hR hred hsimple hinv)).affinePointFunctor ≅ H.affinePointFunctor where
  hom :=
    { app := fun Y => GrpCat.ofHom (coverTotalEquiv e P hR hred hsimple hinv hBC Y).toMonoidHom
      naturality := fun Y Y' χ => by
        refine GrpCat.ext fun z => ?_
        exact coverTotalEquiv_naturality e P hR hred hsimple hinv hBC χ z }
  inv :=
    { app := fun Y =>
        GrpCat.ofHom (coverTotalEquiv e P hR hred hsimple hinv hBC Y).symm.toMonoidHom
      naturality := fun Y Y' χ => by
        refine GrpCat.ext fun h => ?_
        change (coverTotalEquiv e P hR hred hsimple hinv hBC Y').symm (H.affinePointMap χ h) =
          ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
            (factorGroup e P hR hred hsimple hinv)).affinePointMap χ
            ((coverTotalEquiv e P hR hred hsimple hinv hBC Y).symm h)
        apply (coverTotalEquiv e P hR hred hsimple hinv hBC Y').injective
        rw [MulEquiv.apply_symm_apply, coverTotalEquiv_naturality, MulEquiv.apply_symm_apply] }
  hom_inv_id := by
    refine NatTrans.ext (funext fun Y => GrpCat.ext fun z => ?_)
    exact (coverTotalEquiv e P hR hred hsimple hinv hBC Y).symm_apply_apply z
  inv_hom_id := by
    refine NatTrans.ext (funext fun Y => GrpCat.ext fun h => ?_)
    exact (coverTotalEquiv e P hR hred hsimple hinv hBC Y).apply_symm_apply h

theorem isAffine_coverBaseChange :
    IsAffine ((GroupScheme.baseChange (Spec.algebraMap B C)).obj
      (factorGroup e P hR hred hsimple hinv)).X.left := by
  haveI := factorGroup_isAffine e P hR hred hsimple hinv
  change IsAffine (pullback (factorGroup e P hR hred hsimple hinv).X.hom (Spec.algebraMap B C))
  infer_instance

/-- **Over the cover, the descended factor group is `H`.** -/
def coverIso : (GroupScheme.baseChange (Spec.algebraMap B C)).obj
    (factorGroup e P hR hred hsimple hinv) ≅ H :=
  haveI := isAffine_coverBaseChange e P hR hred hsimple hinv
  AffinePointComparison.iso (coverNatIso e P hR hred hsimple hinv hBC)

variable [Etale (Spec.algebraMap B C)] [Surjective (Spec.algebraMap B C)]

include hBC in
/-- The descended factor group is reductive. -/
theorem factorGroup_isReductive : IsReductive (factorGroup e P hR hred hsimple hinv) :=
  IsReductive.of_baseChange_of_etale (Spec.algebraMap B C)
    (IsReductive.of_iso (coverIso e P hR hred hsimple hinv hBC) hred)

omit [Etale (Spec.algebraMap B C)] in
include hBC in
/-- The geometric fibres of the descended factor group are almost simple. -/
theorem factorGroup_isAlmostSimple (t : Spec (CommRingCat.of B)) :
    IsAlmostSimple (geometricFiber (factorGroup e P hR hred hsimple hinv) t) := by
  obtain ⟨s, rfl⟩ := (Spec.algebraMap B C).surjective t
  let b := Spec.algebraMap B C
  let k := (Spec (CommRingCat.of B)).residueField (b s)
  let K := (Spec (CommRingCat.of C)).residueField s
  letI : Algebra k K := (b.residueFieldMap s).hom.toAlgebra
  letI : Algebra (AlgebraicClosure k) (AlgebraicClosure K) :=
    (algebraicClosureEmbedding k K).toRingHom.toAlgebra
  have h1 : IsAlmostSimple (geometricFiber ((GroupScheme.baseChange b).obj
      (factorGroup e P hR hred hsimple hinv)) s) :=
    (hsimple s).of_iso ((GroupScheme.baseChange (geometricPoint _ s)).mapIso
      (coverIso e P hR hred hsimple hinv hBC))
  have h2 := h1.of_iso ((RelativeLevi.geometricFiberBaseChangeIso b s).app
    (factorGroup e P hR hred hsimple hinv))
  exact IsAlmostSimple.of_fieldExtension (k := AlgebraicClosure k) (K := AlgebraicClosure K) h2

end Cover

end FactorNaturality

end Langlands.GroupScheme.WeilChart
