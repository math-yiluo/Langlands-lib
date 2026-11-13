import Langlands.GroupScheme.LocalGroupIsoBaseChangeRecovery
import Langlands.GroupScheme.Descent.GaloisHom

/-!
# Base-changed isomorphisms from local isomorphisms over a cover

Let `b : S ⟶ B` be a morphism of schemes and let `e` be a local isomorphism between group
schemes `G₁` and `G₂` over `B`, defined over the cover `S`. Evaluating `e` at the canonical
cover point of every scheme over `S` gives an isomorphism of the base changes of `G₁` and
`G₂` to `S`. If `e` is unchanged by translating cover points along an endomorphism `a` of
`S` over `B`, this isomorphism is compatible with the descent identification along `a`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LocalGroupIso

variable {B S : Scheme.{u}} (b : S ⟶ B) {G₁ G₂ : GroupScheme B}
  (e : LocalGroupIso G₁ G₂ (Over.mk b))

/-- The endomorphism of the cover given by an endomorphism `a` of `S` over `B`. -/
def coverMap (a : S ⟶ S) (ha : a ≫ b = b) : Over.mk b ⟶ Over.mk b :=
  Over.homMk a ha

theorem testPoint_descent (a : S ⟶ S) (ha : a ≫ b = b) (T : Over S) :
    (descentTestIso b a ha T).hom ≫ baseChangeTestPoint (U := Over.mk b) ((Over.map a).obj T) =
      baseChangeTestPoint (U := Over.mk b) T ≫ coverMap b a ha :=
  Over.OverMorphism.ext (Category.id_comp _)

/-- Translating cover points along `a` does not change the local isomorphisms. -/
def IsInvariant (a : S ⟶ S) (ha : a ≫ b = b) : Prop :=
  ∀ {Z : Over B} (c : Z ⟶ Over.mk b) (y : Z ⟶ G₁.X),
    e.toFun (c ≫ coverMap b a ha) y = e.toFun c y

variable {b e}

theorem comp_comp_hom {A A' A'' : GroupScheme S} (f : A ⟶ A') (g : A' ⟶ A'')
    {T : Over S} (x : T ⟶ A.X) : x ≫ (f ≫ g).hom.hom = (x ≫ f.hom.hom) ≫ g.hom.hom := by
  rw [Grp.comp_hom_hom, Category.assoc]

/-- The translated side of the compatibility square, on points. -/
theorem compatible_left (a : S ⟶ S) (ha : a ≫ b = b) (T : Over S)
    (x : T ⟶ ((Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G₁)).X) :
    baseChangePointsEquiv b G₂ T
        ((x ≫ ((Over.pullback a).mapGrp.map e.toBaseChangeIso.hom).hom.hom) ≫
          (descentBaseChangeIso b a ha G₂).hom.hom.hom) =
      (descentTestIso b a ha T).hom ≫
        e.toFun (baseChangeTestPoint (U := Over.mk b) ((Over.map a).obj T))
          (baseChangePointsEquiv b G₁ _ (baseChangePointsEquiv a _ T x)) := by
  rw [baseChangePointsEquiv_descent, baseChangePointsEquiv_comp]
  erw [e.toBaseChangeIso_hom_points]
  rfl

/-- The descent-identification side of the compatibility square, on points. -/
theorem compatible_right (a : S ⟶ S) (ha : a ≫ b = b) (T : Over S)
    (x : T ⟶ ((Over.pullback a).mapGrp.obj ((Over.pullback b).mapGrp.obj G₁)).X) :
    baseChangePointsEquiv b G₂ T
        ((x ≫ (descentBaseChangeIso b a ha G₁).hom.hom.hom) ≫ e.toBaseChangeIso.hom.hom.hom) =
      e.toFun (baseChangeTestPoint (U := Over.mk b) T)
        ((descentTestIso b a ha T).hom ≫
          baseChangePointsEquiv b G₁ _ (baseChangePointsEquiv a _ T x)) := by
  erw [e.toBaseChangeIso_hom_points]
  simp only [Over.mk_hom]
  rw [baseChangePointsEquiv_descent]

/-- Invariant local isomorphisms give a base-changed isomorphism compatible with the
descent identification along `a`. -/
theorem baseIso_compatible (a : S ⟶ S) (ha : a ≫ b = b) (he : e.IsInvariant b a ha) :
    (Over.pullback a).mapGrp.map e.toBaseChangeIso.hom ≫ (descentBaseChangeIso b a ha G₂).hom =
      (descentBaseChangeIso b a ha G₁).hom ≫ e.toBaseChangeIso.hom := by
  apply hom_ext_points
  intro T x
  apply (baseChangePointsEquiv b G₂ T).injective
  rw [comp_comp_hom, comp_comp_hom, compatible_left, compatible_right, ← e.naturality,
    testPoint_descent, he]

omit e in
/-- A homomorphism over `B` whose base change is `e.toBaseChangeIso` agrees with `e` on every
test scheme with a cover point. -/
theorem comp_eq_of_baseChange (e : LocalGroupIso G₁ G₂ (Over.mk b)) (f : G₁ ⟶ G₂)
    (hf : (Over.pullback b).mapGrp.map f = e.toBaseChangeIso.hom)
    {Z : Over B} (c : Z ⟶ Over.mk b) (y : Z ⟶ G₁.X) :
    y ≫ f.hom.hom = e.toFun c y := by
  let T : Over S := Over.mk c.left
  let i : (Over.map b).obj T ≅ Z :=
    Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact (Over.w c).symm)
  have hi : i.hom ≫ c = baseChangeTestPoint (U := Over.mk b) T := Over.OverMorphism.ext (Category.id_comp _)
  apply (cancel_epi i.hom).mp
  have h1 := baseChangePointsEquiv_comp b f T ((baseChangePointsEquiv b G₁ T).symm (i.hom ≫ y))
  rw [MulEquiv.apply_symm_apply, hf] at h1
  erw [e.toBaseChangeIso_hom_points] at h1
  simp only [Over.mk_hom] at h1
  rw [MulEquiv.apply_symm_apply, ← hi, e.naturality, Category.assoc] at h1
  exact h1.symm

section Galois

variable {K M : Type u} [Field K] [Field M] [Algebra K M] [IsGalois K M]
  {H₁ H₂ : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom H₁.X.hom]
  [IsAffineHom H₂.X.hom]

/-- The isomorphism over `Spec K` descended from local isomorphisms over `Spec M` that are
invariant under every automorphism of `M` over `K`. -/
def galoisDescendIso (e : LocalGroupIso H₁ H₂ (Over.mk (algebraBaseMap K M)))
    (he : ∀ σ : M ≃ₐ[K] M,
      e.IsInvariant (algebraBaseMap K M) (galoisBaseMap K M σ) (galoisBaseMap_over K M σ)) :
    H₁ ≅ H₂ :=
  Descent.GaloisHom.iso e.toBaseChangeIso.hom
    (fun σ => baseIso_compatible (galoisBaseMap K M σ) (galoisBaseMap_over K M σ) (he σ))

/-- On every test scheme with a point of `Spec M`, the descended isomorphism is the local
isomorphism at that point. -/
theorem comp_galoisDescendIso_hom (e : LocalGroupIso H₁ H₂ (Over.mk (algebraBaseMap K M)))
    (he : ∀ σ : M ≃ₐ[K] M,
      e.IsInvariant (algebraBaseMap K M) (galoisBaseMap K M σ) (galoisBaseMap_over K M σ))
    {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ Over.mk (algebraBaseMap K M))
    (y : Z ⟶ H₁.X) :
    y ≫ (galoisDescendIso e he).hom.hom.hom = e.toFun c y :=
  comp_eq_of_baseChange e _ (Descent.GaloisHom.baseChange_iso_hom _ _) c y

end Galois

end Langlands.GroupScheme.LocalGroupIso
