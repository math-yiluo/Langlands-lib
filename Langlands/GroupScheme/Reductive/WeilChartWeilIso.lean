import Langlands.GroupScheme.Reductive.WeilChartFactorChart

/-! # The original group as the Weil restriction of the descended factor group -/

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
  [Algebra A A'] [Algebra A' C] [Algebra A B]

section Base

variable (B) in
/-- `B ⊗[A] T` as a `B`-algebra. -/
abbrev baseTensor (T : CommAlgCat.{u} (CommRingCat.of A)) : CommAlgCat.{u} (CommRingCat.of B) :=
  CommAlgCat.of (CommRingCat.of B) (B ⊗[A] T)

variable (B) in
/-- The inclusion `T → B ⊗[A] T`, `t ↦ 1 ⊗ t`. -/
def inclT (T : CommAlgCat.{u} (CommRingCat.of A)) : T ⟶ resB A (baseTensor B T) :=
  ConcreteCategory.ofHom (C := CommAlgCat.{u} (CommRingCat.of A)) (X := T)
    (Y := resB A (baseTensor B T))
    (@AlgHom.mk (CommRingCat.of A) T (resB A (baseTensor B T)) _ _ _
      (CommAlgCat.algebra T) (CommAlgCat.algebra (resB A (baseTensor B T)))
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T)).toRingHom
      (fun a => by
        change (1 : B) ⊗ₜ[A] algebraMap A T a = algebraMap A B a ⊗ₜ[A] (1 : T)
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := T) a).symm))

theorem inclT_apply (T : CommAlgCat.{u} (CommRingCat.of A)) (t : T) :
    (inclT B T).hom t = ((1 : B) ⊗ₜ[A] t : B ⊗[A] T) :=
  rfl

/-- The map `B ⊗[A] T → B ⊗[A] T₁` of `B`-algebras induced by `χ : T ⟶ T₁`. -/
def baseTensorMap {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    baseTensor B T ⟶ baseTensor B T₁ :=
  CommAlgCat.ofHom (Algebra.TensorProduct.lTensor (S := B) B χ.hom)

theorem inclT_comp_baseTensorMap {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁) :
    inclT B T ≫ resBHom (baseTensorMap (B := B) χ) = χ ≫ inclT B T₁ := by
  refine CommAlgCat.hom_ext (DFunLike.ext _ _ fun t => ?_)
  change Algebra.TensorProduct.lTensor (S := B) B χ.hom ((1 : B) ⊗ₜ[A] t) = (1 : B) ⊗ₜ[A] χ.hom t
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- The chart map `χ ∘ f` for a map of test algebras `χ`. It is a separate definition so that
the algebra structures are taken from the objects. -/
def chartPush {T₀ T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T₀ ⟶ T₁) (f : A' →ₐ[A] T₀) :
    A' →ₐ[A] T₁ :=
  χ.hom.comp f

theorem chartPush_apply {T₀ T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T₀ ⟶ T₁)
    (f : A' →ₐ[A] T₀) (a : A') : chartPush χ f a = χ.hom (f a) :=
  rfl

end Base

section Bijective

/-- A ring map `C ⊗[A'] T → B ⊗[A] T` with `e (a ⊗ b) ⊗ t ↦ b ⊗ a t` is bijective. -/
theorem bijective_of_tmul {T : Type u} [CommRing T] [Algebra A T] [Algebra A' T]
    [IsScalarTower A A' T] (e : A' ⊗[A] B ≃ₐ[A'] C) (κ : C ⊗[A'] T →+* B ⊗[A] T)
    (hκ : ∀ (a : A') (b : B) (t : T),
      κ (e (a ⊗ₜ[A] b) ⊗ₜ[A'] t) = b ⊗ₜ[A] (algebraMap A' T a * t)) :
    Function.Bijective κ := by
  letI : Algebra A (C ⊗[A'] T) := Algebra.compHom _ (algebraMap A A')
  let fB : B →ₐ[A] C ⊗[A'] T :=
    { (Algebra.TensorProduct.includeLeftRingHom (R := A') (A := C) (B := T)).comp
        ((e : A' ⊗[A] B →+* C).comp
          (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B)).toRingHom) with
      commutes' := fun a => by
        change e ((1 : A') ⊗ₜ[A] algebraMap A B a) ⊗ₜ[A'] (1 : T) =
          algebraMap A' (C ⊗[A'] T) (algebraMap A A' a)
        rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.algebraMap_apply]
        congr 1
        rw [← AlgEquiv.commutes e (algebraMap A A' a), Algebra.TensorProduct.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply] }
  let gT : T →ₐ[A] C ⊗[A'] T :=
    { (Algebra.TensorProduct.includeRight (R := A') (A := C) (B := T)).toRingHom with
      commutes' := fun a => by
        change (1 : C) ⊗ₜ[A'] algebraMap A T a = algebraMap A' (C ⊗[A'] T) (algebraMap A A' a)
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul,
          ← IsScalarTower.algebraMap_apply] }
  let lam : B ⊗[A] T →ₐ[A] C ⊗[A'] T := Algebra.TensorProduct.productMap fB gT
  have hlam : ∀ (b : B) (t : T), lam (b ⊗ₜ[A] t) = e ((1 : A') ⊗ₜ[A] b) ⊗ₜ[A'] t := by
    intro b t
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    change e ((1 : A') ⊗ₜ[A] b) ⊗ₜ[A'] (1 : T) * ((1 : C) ⊗ₜ[A'] t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h1 : ∀ x, κ (lam x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b t => rw [hlam, hκ, map_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h2 : ∀ x, lam (κ x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c t =>
      obtain ⟨y, rfl⟩ := e.surjective c
      induction y using TensorProduct.inductionOn with
      | tmul a b =>
        rw [hκ, hlam, ← Algebra.smul_def, ← TensorProduct.smul_tmul, descentEquiv_tmul e a b]
      | add y y' hy hy' => rw [map_add, TensorProduct.add_tmul, map_add, map_add, hy, hy']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact ⟨fun x y hxy => by rw [← h2 x, ← h2 y, hxy], fun y => ⟨lam y, h1 y⟩⟩

/-- Points over a bijective map of algebras correspond bijectively. -/
theorem affinePointMap_bijective {R : CommRingCat.{u}} (K : GroupScheme (Spec R))
    {X Y : CommAlgCat.{u} R} (κ : X ⟶ Y) (hκ : Function.Bijective κ.hom) :
    Function.Bijective (K.affinePointMap κ) := by
  let κe : X ≅ Y := CommAlgCat.isoMk (AlgEquiv.ofBijective κ.hom hκ)
  have hhom : κe.hom = κ := CommAlgCat.hom_ext rfl
  rw [← hhom]
  refine ⟨fun x y hxy => ?_, fun y => ⟨K.affinePointMap κe.inv y, ?_⟩⟩
  · have h := congrArg (K.affinePointMap κe.inv) hxy
    rwa [← MonoidHom.comp_apply, ← K.affinePointMap_comp, ← MonoidHom.comp_apply,
      ← K.affinePointMap_comp, Iso.hom_inv_id, K.affinePointMap_id] at h
  · rw [← MonoidHom.comp_apply, ← K.affinePointMap_comp, Iso.inv_hom_id, K.affinePointMap_id,
      MonoidHom.id_apply]

end Bijective

section Weil

variable (e : A' ⊗[A] B ≃ₐ[A'] C)
  [Module.Finite A' C] [Module.Projective A' C] [Algebra.Etale A' C]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  {H : GroupScheme (Spec (CommRingCat.of C))} [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom]
  (P : (GroupScheme.baseChange (Spec.algebraMap A A')).obj G ≅ AffineWeil.groupScheme A' C H)
  (hR : WeilFactorIdempotentRigidityStatement.{u})
  (hred : IsReductive H) (hsimple : ∀ s, IsAlmostSimple (geometricFiber H s))
  [Module.FaithfullyFlat A A']
  (hinv : ∀ (T : CommAlgCat.{u} (CommRingCat.of A)) (f₁ f₂ : A' →ₐ[A] T) (b : B),
    chartAlgEquiv P hR hred hsimple f₁ f₂ (coeffTmul f₂ 1 (e (1 ⊗ₜ[A] b))) =
      coeffTmul f₁ 1 (e (1 ⊗ₜ[A] b)))

theorem factorEndApp_idem (X : CommAlgCat.{u} (CommRingCat.of B))
    (p : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :
    factorEndApp e P hR hred hsimple hinv X (factorEndApp e P hR hred hsimple hinv X p) =
      factorEndApp e P hR hred hsimple hinv X p := by
  simp only [factorEndApp_apply, MulEquiv.apply_symm_apply, descProj_idem]

theorem factorEndApp_naturality {X Y : CommAlgCat.{u} (CommRingCat.of B)} (χ : X ⟶ Y)
    (p : ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePoints X) :
    ((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ
        (factorEndApp e P hR hred hsimple hinv X p) =
      factorEndApp e P hR hred hsimple hinv Y
        (((GroupScheme.baseChange (Spec.algebraMap A B)).obj G).affinePointMap χ p) := by
  obtain ⟨q, rfl⟩ := (bPointsEquiv G X).symm.surjective p
  simp only [factorEndApp_apply, MulEquiv.apply_symm_apply, bPointsEquiv_symm_naturality,
    descProj_map]
  rw [resBHom_comp_structB]

variable [IsAffine G.X.left]

/-- The point map `G(T) → G'(B ⊗[A] T)`: extend coefficients to `B ⊗[A] T` and project to the
diagonal factor. -/
def pointsMap (T : CommAlgCat.{u} (CommRingCat.of A)) :
    G.affinePoints T →* (factorGroup e P hR hred hsimple hinv).affinePoints (baseTensor B T) :=
  (factorPointsEquiv e P hR hred hsimple hinv (baseTensor B T)).symm.toMonoidHom.comp
    ((((factorEndApp e P hR hred hsimple hinv (baseTensor B T)).comp
        (bPointsEquiv G (baseTensor B T)).symm.toMonoidHom).comp
          (G.affinePointMap (inclT B T))).codRestrict
      (fixedPoints e P hR hred hsimple hinv (baseTensor B T))
      fun _ => factorEndApp_idem e P hR hred hsimple hinv _ _)

theorem factorPointsEquiv_pointsMap (T : CommAlgCat.{u} (CommRingCat.of A))
    (q : G.affinePoints T) :
    (factorPointsEquiv e P hR hred hsimple hinv (baseTensor B T)
        (pointsMap e P hR hred hsimple hinv T q) : _) =
      factorEndApp e P hR hred hsimple hinv (baseTensor B T)
        ((bPointsEquiv G (baseTensor B T)).symm (G.affinePointMap (inclT B T) q)) := by
  rw [pointsMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rfl

theorem pointsMap_naturality {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (q : G.affinePoints T) :
    pointsMap e P hR hred hsimple hinv T₁ (G.affinePointMap χ q) =
      (factorGroup e P hR hred hsimple hinv).affinePointMap (baseTensorMap χ)
        (pointsMap e P hR hred hsimple hinv T q) := by
  apply (factorPointsEquiv e P hR hred hsimple hinv (baseTensor B T₁)).injective
  apply Subtype.ext
  rw [factorPointsEquiv_naturality, factorPointsEquiv_pointsMap, factorPointsEquiv_pointsMap,
    factorEndApp_naturality, bPointsEquiv_symm_naturality, ← MonoidHom.comp_apply,
    ← G.affinePointMap_comp, ← MonoidHom.comp_apply, ← G.affinePointMap_comp,
    inclT_comp_baseTensorMap]

/-- The fixed points of the factor endomorphism of `G_B` are the points of `G` fixed by the
descended projection. -/
def fixedEqLocusEquiv (X : CommAlgCat.{u} (CommRingCat.of B)) :
    fixedPoints e P hR hred hsimple hinv X ≃*
      MonoidHom.eqLocus (descProj e P hR hred hsimple hinv (structB X)) (MonoidHom.id _) where
  toFun p := ⟨bPointsEquiv G X p.1, by
    have h : factorEndApp e P hR hred hsimple hinv X p.1 = p.1 := p.2
    rw [factorEndApp_apply, MulEquiv.symm_apply_eq] at h
    exact h⟩
  invFun q := ⟨(bPointsEquiv G X).symm q.1, by
    change factorEndApp e P hR hred hsimple hinv X _ = _
    rw [factorEndApp_apply, MulEquiv.apply_symm_apply]
    exact congrArg _ q.2⟩
  left_inv p := Subtype.ext ((bPointsEquiv G X).symm_apply_apply p.1)
  right_inv q := Subtype.ext ((bPointsEquiv G X).apply_symm_apply q.1)
  map_mul' p p' := Subtype.ext (map_mul (bPointsEquiv G X) p.1 p'.1)

omit [IsAffine G.X.left] in
theorem descProj_eqLocus_eq {T : CommAlgCat.{u} (CommRingCat.of A)} (φ : B →ₐ[A] T)
    (g : A' →ₐ[A] T) :
    MonoidHom.eqLocus (descProj e P hR hred hsimple hinv φ) (MonoidHom.id _) =
      MonoidHom.eqLocus (diagProj e P φ g) (MonoidHom.id _) := by
  congr 1
  exact MonoidHom.ext fun x => descProj_eq_diagProj e P hR hred hsimple hinv φ g x

/-- The chart description of the points of `G'` over a `B`-algebra with a chart map. -/
def factorChartEquiv (X : CommAlgCat.{u} (CommRingCat.of B)) (g : A' →ₐ[A] resB A X) :
    (factorGroup e P hR hred hsimple hinv).affinePoints X ≃*
      H.affinePoints (chartObj e (structB X) g) :=
  (factorPointsEquiv e P hR hred hsimple hinv X).trans <|
    (fixedEqLocusEquiv e P hR hred hsimple hinv X).trans <|
      (MulEquiv.subgroupCongr (descProj_eqLocus_eq e P hR hred hsimple hinv (structB X) g)).trans
        (chartFixedEquiv e P (structB X) g)

theorem factorChartEquiv_pointsMap (T : CommAlgCat.{u} (CommRingCat.of A)) (f : A' →ₐ[A] T)
    (q : G.affinePoints T) :
    factorChartEquiv e P hR hred hsimple hinv (baseTensor B T) (chartPush (inclT B T) f)
        (pointsMap e P hR hred hsimple hinv T q) =
      H.affinePointMap (CommAlgCat.ofHom
          (chartMu e (structB (baseTensor B T)) (chartPush (inclT B T) f)))
        (underPointsEquiv P (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
          (G.affinePointMap (inclT B T) q)) := by
  have hx : (bPointsEquiv G (baseTensor B T))
      (factorPointsEquiv e P hR hred hsimple hinv (baseTensor B T)
        (pointsMap e P hR hred hsimple hinv T q) : _) =
      diagProj e P (structB (baseTensor B T)) (chartPush (inclT B T) f)
        (G.affinePointMap (inclT B T) q) := by
    rw [factorPointsEquiv_pointsMap, factorEndApp_apply, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply, descProj_eq_diagProj e P hR hred hsimple hinv _
        (chartPush (inclT B T) f)]
  have h := chartFixedEquiv_diagProj e P (structB (baseTensor B T)) (chartPush (inclT B T) f)
    (G.affinePointMap (inclT B T) q) (diagProj_idem e P _ _ _)
  rw [factorChartEquiv, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, ← h]
  congr 1
  exact Subtype.ext hx

variable (B) in
/-- The inclusion `T → B ⊗[A] T` as a map of `A'`-algebras, for a chart map of `T`. -/
def inclChart {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T) :
    letI := underAlgebra f (Under.mk (𝟙 T))
    letI := underAlgebra (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
    (Under.mk (𝟙 T)).right →ₐ[A'] (Under.mk (𝟙 (resB A (baseTensor B T)))).right :=
  letI := underAlgebra f (Under.mk (𝟙 T))
  letI := underAlgebra (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
  { (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := T)).toRingHom with
    commutes' := fun _ => rfl }

omit [Algebra.Etale A' C] [Module.FaithfullyFlat A A'] [IsAffine G.X.left] in
theorem underPointsEquiv_inclT {T : CommAlgCat.{u} (CommRingCat.of A)} (f : A' →ₐ[A] T)
    (q : G.affinePoints T) :
    underPointsEquiv P (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
        (G.affinePointMap (inclT B T) q) =
      H.affinePointMap (CommAlgCat.ofHom (letI := underAlgebra f (Under.mk (𝟙 T))
        letI := underAlgebra (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
        Algebra.TensorProduct.lTensor (S := C) C (inclChart B f)))
        (underPointsEquiv P f (Under.mk (𝟙 T)) q) := by
  letI := underAlgebra f (Under.mk (𝟙 T))
  letI := underAlgebra (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
  haveI := underAlgebra_isScalarTower f (Under.mk (𝟙 T))
  haveI := underAlgebra_isScalarTower (chartPush (inclT B T) f)
    (Under.mk (𝟙 (resB A (baseTensor B T))))
  exact chartPointsEquiv_naturality P (Under.mk (𝟙 T)).right
    (Under.mk (𝟙 (resB A (baseTensor B T)))).right (inclChart B f) q

/-- **Chart case**: over a test algebra with a chart map, the point map is bijective. -/
theorem pointsMap_bijective_of_chart (T : CommAlgCat.{u} (CommRingCat.of A)) (f : A' →ₐ[A] T) :
    Function.Bijective (pointsMap e P hR hred hsimple hinv T) := by
  letI := underAlgebra f (Under.mk (𝟙 T))
  letI := underAlgebra (chartPush (inclT B T) f) (Under.mk (𝟙 (resB A (baseTensor B T))))
  haveI := underAlgebra_isScalarTower f (Under.mk (𝟙 T))
  let κ := (chartMu e (structB (baseTensor B T)) (chartPush (inclT B T) f)).comp
    (Algebra.TensorProduct.lTensor (S := C) C (inclChart B f))
  have hκ : Function.Bijective κ := by
    refine bijective_of_tmul (T := (Under.mk (𝟙 T)).right) e κ.toRingHom ?_
    intro a b t
    change graphMul (chartRho e (structB (baseTensor B T)) (chartPush (inclT B T) f))
      (e (a ⊗ₜ[A] b) ⊗ₜ[A'] ((1 : B) ⊗ₜ[A] t)) = _
    rw [Algebra.TensorProduct.productMap_apply_tmul, AlgHom.id_apply]
    have h1 : chartRho e (structB (baseTensor B T)) (chartPush (inclT B T) f) (e (a ⊗ₜ[A] b)) =
        (show (Under.mk (𝟙 (resB A (baseTensor B T)))).right from
          chartPush (inclT B T) f a * structB (A := A) (baseTensor B T) b) :=
      diagMap_tmul e (structB (baseTensor B T)) (chartPush (inclT B T) f) a b
    rw [h1]
    change ((1 : B) ⊗ₜ[A] f a) * (b ⊗ₜ[A] (1 : T)) * ((1 : B) ⊗ₜ[A] (show T from t)) =
      b ⊗ₜ[A] (f a * (show T from t))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hH := affinePointMap_bijective H (CommAlgCat.ofHom κ) hκ
  have hcomp : ∀ q : G.affinePoints T,
      factorChartEquiv e P hR hred hsimple hinv (baseTensor B T) (chartPush (inclT B T) f)
          (pointsMap e P hR hred hsimple hinv T q) =
        H.affinePointMap (CommAlgCat.ofHom κ) (underPointsEquiv P f (Under.mk (𝟙 T)) q) := by
    intro q
    rw [factorChartEquiv_pointsMap, underPointsEquiv_inclT, ← MonoidHom.comp_apply,
      ← H.affinePointMap_comp]
    rfl
  have hb : Function.Bijective
      (factorChartEquiv e P hR hred hsimple hinv (baseTensor B T) (chartPush (inclT B T) f) ∘
        pointsMap e P hR hred hsimple hinv T) := by
    have heq : (factorChartEquiv e P hR hred hsimple hinv (baseTensor B T)
          (chartPush (inclT B T) f) ∘ pointsMap e P hR hred hsimple hinv T) =
        (H.affinePointMap (CommAlgCat.ofHom κ)) ∘ (underPointsEquiv P f (Under.mk (𝟙 T))) :=
      funext hcomp
    rw [heq]
    exact hH.comp (MulEquiv.bijective _)
  exact (Function.Bijective.of_comp_iff' (MulEquiv.bijective _) _).1 hb

variable [Module.Finite A B] [Module.Projective A B]
  [IsAffine (factorGroup e P hR hred hsimple hinv).X.left]
  [LocallyOfFiniteType (factorGroup e P hR hred hsimple hinv).X.hom]

/-- The point map `G(T) → R_{B/A}(G')(T)`. -/
def weilMap (T : CommAlgCat.{u} (CommRingCat.of A)) :
    G.affinePoints T →*
      (AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePoints T :=
  (AffineWeil.pointsEquiv A B (factorGroup e P hR hred hsimple hinv) T).symm.toMonoidHom.comp
    (pointsMap e P hR hred hsimple hinv T)

theorem pointsEquiv_weilMap (T : CommAlgCat.{u} (CommRingCat.of A)) (q : G.affinePoints T) :
    AffineWeil.pointsEquiv A B (factorGroup e P hR hred hsimple hinv) T
        (weilMap e P hR hred hsimple hinv T q) = pointsMap e P hR hred hsimple hinv T q :=
  MulEquiv.apply_symm_apply _ _

theorem weilMap_naturality {T T₁ : CommAlgCat.{u} (CommRingCat.of A)} (χ : T ⟶ T₁)
    (q : G.affinePoints T) :
    weilMap e P hR hred hsimple hinv T₁ (G.affinePointMap χ q) =
      (AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePointMap χ
        (weilMap e P hR hred hsimple hinv T q) := by
  apply (AffineWeil.pointsEquiv A B (factorGroup e P hR hred hsimple hinv) T₁).injective
  rw [pointsEquiv_weilMap, pointsMap_naturality]
  have h := AffineWeil.pointsEquiv_naturality A B (factorGroup e P hR hred hsimple hinv) χ.hom
    (weilMap e P hR hred hsimple hinv T q)
  rw [pointsEquiv_weilMap] at h
  exact h.symm

theorem weilMap_bijective_of_chart (T : CommAlgCat.{u} (CommRingCat.of A)) (f : A' →ₐ[A] T) :
    Function.Bijective (weilMap e P hR hred hsimple hinv T) :=
  (MulEquiv.bijective (AffineWeil.pointsEquiv A B (factorGroup e P hR hred hsimple hinv) T).symm).comp
    (pointsMap_bijective_of_chart e P hR hred hsimple hinv T f)

theorem weilMap_injective (T : CommAlgCat.{u} (CommRingCat.of A)) :
    Function.Injective (weilMap e P hR hred hsimple hinv T) := by
  intro q₁ q₂ h
  apply AffinePointDescent.affinePointMap_injective G (extι A' T) (extι_faithfullyFlat T)
  apply (weilMap_bijective_of_chart e P hR hred hsimple hinv (extT A' T) (extChart T)).1
  rw [weilMap_naturality, weilMap_naturality, h]

theorem weilMap_surjective (T : CommAlgCat.{u} (CommRingCat.of A)) :
    Function.Surjective (weilMap e P hR hred hsimple hinv T) := by
  intro y
  obtain ⟨x', hx'⟩ := (weilMap_bijective_of_chart e P hR hred hsimple hinv (extT A' T)
    (extChart T)).2
    ((AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePointMap
      (extι A' T) y)
  obtain ⟨x, hx⟩ := AffinePointDescent.exists_affinePointMap_eq G (extι A' T)
    (extι_faithfullyFlat T) x' (fun Z a b hab => by
      apply weilMap_injective e P hR hred hsimple hinv Z
      rw [weilMap_naturality, weilMap_naturality, hx', ← MonoidHom.comp_apply,
        ← GroupScheme.affinePointMap_comp, hab, GroupScheme.affinePointMap_comp,
        MonoidHom.comp_apply])
  refine ⟨x, AffinePointDescent.affinePointMap_injective _ (extι A' T) (extι_faithfullyFlat T) ?_⟩
  rw [← weilMap_naturality, hx, hx']

/-- The point maps `G(T) ≃* R_{B/A}(G')(T)`. -/
def weilEquiv (T : CommAlgCat.{u} (CommRingCat.of A)) :
    G.affinePoints T ≃*
      (AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePoints T :=
  MulEquiv.ofBijective (weilMap e P hR hred hsimple hinv T)
    ⟨weilMap_injective e P hR hred hsimple hinv T, weilMap_surjective e P hR hred hsimple hinv T⟩

/-- The natural isomorphism of point functors `G ≅ R_{B/A}(G')`. -/
def weilIsoNat : G.affinePointFunctor ≅
    (AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePointFunctor where
  hom :=
    { app := fun T => GrpCat.ofHom (weilMap e P hR hred hsimple hinv T)
      naturality := fun T T₁ χ => by
        refine GrpCat.ext fun q => ?_
        exact weilMap_naturality e P hR hred hsimple hinv χ q }
  inv :=
    { app := fun T => GrpCat.ofHom (weilEquiv e P hR hred hsimple hinv T).symm.toMonoidHom
      naturality := fun T T₁ χ => by
        refine GrpCat.ext fun y => ?_
        change (weilEquiv e P hR hred hsimple hinv T₁).symm
            ((AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv)).affinePointMap
              χ y) =
          G.affinePointMap χ ((weilEquiv e P hR hred hsimple hinv T).symm y)
        apply (weilEquiv e P hR hred hsimple hinv T₁).injective
        rw [MulEquiv.apply_symm_apply]
        change _ = weilMap e P hR hred hsimple hinv T₁ _
        rw [weilMap_naturality]
        congr 1
        exact ((weilEquiv e P hR hred hsimple hinv T).apply_symm_apply y).symm }
  hom_inv_id := by
    refine NatTrans.ext (funext fun T => GrpCat.ext fun q => ?_)
    exact (weilEquiv e P hR hred hsimple hinv T).symm_apply_apply q
  inv_hom_id := by
    refine NatTrans.ext (funext fun T => GrpCat.ext fun y => ?_)
    exact (weilEquiv e P hR hred hsimple hinv T).apply_symm_apply y

/-- **The original group is the Weil restriction of the descended factor group.** -/
def weilIso : G ≅ AffineWeil.groupScheme A B (factorGroup e P hR hred hsimple hinv) :=
  AffinePointComparison.iso (weilIsoNat e P hR hred hsimple hinv)

end Weil

end Langlands.GroupScheme.WeilChart
