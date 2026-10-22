import Langlands.AlgebraicGeometry.RelativeDerivations

/-!
# Precomposition of relative derivations

Relative derivations on the source of a scheme morphism induce derivations
on its target, with values in the actual pushforward module sheaf.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Langlands.Scheme.RelativeDerivation

variable {X Y Z S : AlgebraicGeometry.Scheme.{u}}

/-- Precompose a relative derivation with the section maps of a scheme morphism. -/
def precomp (g : X ⟶ Y) (f : Y ⟶ S) {M : X.Modules}
    (d : RelativeDerivation (g ≫ f) M) :
    RelativeDerivation f ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj M) where
  d {U} := d.d.comp (g.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d (g.app U.unop (a * b)) =
      g.app U.unop a • d.d (g.app U.unop b) +
        g.app U.unop b • d.d (g.app U.unop a)
    rw [map_mul, d.d_mul]
  d_map {U V} i a := by
    change d.d (g.app V.unop (Y.presheaf.map i a)) =
      M.presheaf.map ((Opens.map g.base).map i.unop).op (d.d (g.app U.unop a))
    change d.app _ (g.app _ (Y.presheaf.map i a)) =
      M.presheaf.map ((Opens.map g.base).map i.unop).op (d.app _ (g.app _ a))
    rw [← app_restrict]
    exact congrArg (d.app _) (ConcreteCategory.congr_hom (g.naturality i) a)
  d_app {U} a := d.d_app (X := U) a

@[simp]
lemma precomp_app (g : X ⟶ Y) (f : Y ⟶ S) {M : X.Modules}
    (d : RelativeDerivation (g ≫ f) M) (U : Y.Opens) (a : Γ(Y, U)) :
    (precomp g f d).app U a = d.app (g ⁻¹ᵁ U) (g.app U a) := rfl

/-- Precomposition for a morphism over a fixed base, with its commuting triangle
given as an equality of scheme morphisms. -/
def precompOver (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S}
    (h : g ≫ fY = fX) {M : X.Modules} (d : RelativeDerivation fX M) :
    RelativeDerivation fY ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj M) :=
  precomp g fY (h.symm ▸ d)

@[simp]
lemma precompOver_app (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S}
    (h : g ≫ fY = fX) {M : X.Modules} (d : RelativeDerivation fX M)
    (U : Y.Opens) (a : Γ(Y, U)) :
    (precompOver g h d).app U a = d.app (g ⁻¹ᵁ U) (g.app U a) := by
  subst fX
  rfl

lemma precompOver_postcomp (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S}
    (h : g ≫ fY = fX) {M N : X.Modules} (d : RelativeDerivation fX M) (α : M ⟶ N) :
    precompOver g h (postcomp d α) =
      postcomp (precompOver g h d) ((AlgebraicGeometry.Scheme.Modules.pushforward g).map α) := by
  subst fX
  ext U a
  rfl

/-- Identity precomposition, after the canonical pushforward identification. -/
@[simp]
lemma precompOver_id (f : X ⟶ S) {M : X.Modules} (d : RelativeDerivation f M) :
    postcomp (precompOver (𝟙 X) (Category.id_comp f) d)
      ((AlgebraicGeometry.Scheme.Modules.pushforwardId X).hom.app M) = d := by
  ext U a
  change (postcomp (precompOver (𝟙 X) (Category.id_comp f) d)
    ((AlgebraicGeometry.Scheme.Modules.pushforwardId X).hom.app M)).app U.unop a = d.app U.unop a
  simp only [postcomp_app, precompOver_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardId_hom_app_app,
    AlgebraicGeometry.Scheme.Hom.id_app]
  rfl

/-- Successive precomposition agrees with composite precomposition using the
actual pushforward composition isomorphism. -/
lemma precompOver_comp (h : X ⟶ Y) (k : Y ⟶ Z)
    {fX : X ⟶ S} {fY : Y ⟶ S} {fZ : Z ⟶ S}
    (wh : h ≫ fY = fX) (wk : k ≫ fZ = fY)
    {M : X.Modules} (d : RelativeDerivation fX M) :
    postcomp (precompOver k wk (precompOver h wh d))
      ((AlgebraicGeometry.Scheme.Modules.pushforwardComp h k).hom.app M) =
    precompOver (h ≫ k) (by rw [Category.assoc, wk, wh]) d := by
  ext U a
  change (postcomp (precompOver k wk (precompOver h wh d))
    ((AlgebraicGeometry.Scheme.Modules.pushforwardComp h k).hom.app M)).app U.unop a =
    (precompOver (h ≫ k) _ d).app U.unop a
  simp only [postcomp_app, precompOver_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardComp_hom_app_app,
    AlgebraicGeometry.Scheme.Hom.comp_app, CommRingCat.comp_apply]
  rfl

end Langlands.Scheme.RelativeDerivation
