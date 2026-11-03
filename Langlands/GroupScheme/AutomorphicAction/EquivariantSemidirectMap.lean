import Langlands.GroupScheme.AutomorphicAction.SemidirectMaps

/-! # Semidirect maps induced by an equivariant homomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {B : Scheme.{u}} {K H G : GroupScheme B}
    (c : AutomorphicAction K H) (a : AutomorphicAction K G) (f : H ⟶ G)
    (heq : ∀ (T : Over B) (k : T ⟶ K.X) (h : T ⟶ H.X),
      c.act k h ≫ f.hom.hom = a.act k (h ≫ f.hom.hom))

/-- An equivariant homomorphism, together with the identity on the acting
group, gives a natural homomorphism of semidirect point groups. -/
def semidirectMapPoints : c.semidirectPoints ⟶ a.semidirectPoints where
  app T := GrpCat.ofHom (SemidirectProduct.map
    ((pointsMap f).app T).hom (MonoidHom.id _) (by
      intro k
      apply MonoidHom.ext
      intro h
      exact heq T.unop k h))
  naturality {T V} q := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext
    · change (q.unop ≫ x.left) ≫ f.hom.hom =
        q.unop ≫ x.left ≫ f.hom.hom
      exact Category.assoc _ _ _
    · rfl

/-- The actual homomorphism of semidirect group schemes induced by an
equivariant homomorphism of normal factors. -/
def semidirectMap : c.semidirectProduct ⟶ a.semidirectProduct :=
  yonedaGrpFullyFaithful.preimage
    (c.semidirectPointsIso.hom ≫ semidirectMapPoints c a f heq ≫
      a.semidirectPointsIso.inv)

/-- On all tests, the induced map applies `f` to the normal coordinate and
leaves the acting coordinate unchanged. -/
theorem semidirectMap_points {T : Over B} (x : T ⟶ c.semidirectProduct.X) :
    a.semidirectPointsEquiv T (x ≫ (semidirectMap c a f heq).hom.hom) =
      ⟨(c.semidirectPointsEquiv T x).left ≫ f.hom.hom,
        (c.semidirectPointsEquiv T x).right⟩ := by
  have hn : pointsMap (semidirectMap c a f heq) ≫ a.semidirectPointsIso.hom =
      c.semidirectPointsIso.hom ≫ semidirectMapPoints c a f heq := by
    calc
      _ = (c.semidirectPointsIso.hom ≫ semidirectMapPoints c a f heq ≫
          a.semidirectPointsIso.inv) ≫ a.semidirectPointsIso.hom :=
        congrArg (fun m => m ≫ a.semidirectPointsIso.hom)
          (yonedaGrpFullyFaithful.map_preimage _)
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun m => (m.app (op T)).hom x) hn

@[simp]
theorem semidirectMap_hom :
    (semidirectMap c a f heq).hom.hom = f.hom.hom ⊗ₘ 𝟙 K.X := by
  apply (a.semidirectPointsEquiv c.semidirectProduct.X).injective
  have hp := semidirectMap_points c a f heq (𝟙 c.semidirectProduct.X)
  rw [Category.id_comp] at hp
  rw [hp]
  apply SemidirectProduct.ext
  · change (𝟙 _ ≫ fst H.X K.X) ≫ f.hom.hom =
      (f.hom.hom ⊗ₘ 𝟙 K.X) ≫ fst G.X K.X
    simp only [Category.id_comp, tensorHom_fst]
  · change 𝟙 _ ≫ snd H.X K.X =
      (f.hom.hom ⊗ₘ 𝟙 K.X) ≫ snd G.X K.X
    simp only [Category.id_comp, tensorHom_snd, Category.comp_id]

end Langlands.GroupScheme.AutomorphicAction
