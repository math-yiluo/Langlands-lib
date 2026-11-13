import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.PositiveRealTorusLog
import Langlands.Global.RelativeRootChamber
import Langlands.GroupScheme.Rational.SplitTorusVectorCocycle

/-! # Rational normalizer points acting on adelic torus points -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Points over the base are the rational coefficient points: precompose with the
identification of the affine self-test scheme with the base. -/
def basePointEquiv :
    (Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) ≃* RationalGroupPoints F G where
  toFun n := (Lie.affineSelfTestIso (CommRingCat.of F)).hom ≫ n
  invFun q := (Lie.affineSelfTestIso (CommRingCat.of F)).inv ≫ q
  left_inv n := by simp
  right_inv q := by simp
  map_mul' n m := MonObj.comp_mul _ n m

omit [NumberField F] in
theorem basePointEquiv_apply (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    basePointEquiv n = (Lie.affineSelfTestIso (CommRingCat.of F)).hom ≫ n :=
  rfl

omit [NumberField F] in
/-- The base-point identification commutes with group-scheme homomorphisms. -/
theorem basePointEquiv_comp {H : GroupScheme (Spec (CommRingCat.of F))} (f : H ⟶ G)
    (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ H.X) :
    basePointEquiv (n ≫ f.hom.hom) =
      H.affinePointsTarget f (CommAlgCat.of F F) (basePointEquiv n) := by
  rw [basePointEquiv_apply, basePointEquiv_apply, affinePointsTarget_apply, Category.assoc]

/-- The principal adelic point of a base point is its constant point on the adelic test
scheme. -/
theorem rational_basePointEquiv (n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) :
    rational F G (basePointEquiv n) =
      G.constantPoint n
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
  change (algSpec (CommRingCat.of F)).map _ ≫ (Lie.affineSelfTestIso _).hom ≫ n =
    Over.homMk _ _ ≫ n
  rw [← Category.assoc]
  congr 1

variable {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- **Moving a torus point past a normalizing rational point.** If `n` normalizes
`i : T → G` through `σ`, then `i(t) n = n i(σ⁻¹ t)` for every adelic torus point `t`. -/
theorem map_mul_rational_basePointEquiv {i : T.toGrp ⟶ G}
    {n : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (t : AdelicGroupPoints F T.toGrp) :
    map F T.toGrp G i t * rational F G (basePointEquiv n) =
      rational F G (basePointEquiv n) *
        map F T.toGrp G i (map F T.toGrp T.toGrp (CommGroupScheme.groupHom σ.inv) t) := by
  set U := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  have hn : (CommGroupScheme.groupHom σ.inv ≫ i) ≫ (G.innerIso n).hom = i := by
    rw [Category.assoc, h, ← Category.assoc]
    change CommGroupScheme.groupHom (σ.inv ≫ σ.hom) ≫ i = i
    rw [Iso.inv_hom_id]
    exact Category.id_comp i
  have key := G.comp_innerIso_hom n U
    (t ≫ (CommGroupScheme.groupHom σ.inv ≫ i).hom.hom)
  rw [Category.assoc, ← Grp.comp_hom_hom, hn] at key
  rw [rational_basePointEquiv]
  simp only [map_apply, affinePointsTarget_apply]
  change t ≫ i.hom.hom * G.constantPoint n U =
    G.constantPoint n U * (t ≫ (CommGroupScheme.groupHom σ.inv ≫ i).hom.hom)
  rw [key]
  group

/-- Precomposing with an automorphism of the torus on adelic points pulls the character
back along its inverse. -/
theorem normCharacter_map_groupHom_inv (σ : T ≅ T) (χ : characterLattice T)
    (t : AdelicGroupPoints F T.toGrp) :
    PositiveRealTorus.normCharacter F T χ
        (map F T.toGrp T.toGrp (CommGroupScheme.groupHom σ.inv) t) =
      PositiveRealTorus.normCharacter F T (σ.inv ≫ χ) t :=
  (PositiveRealTorus.normCharacter_pullback F T T σ.inv χ t).symm

/-- For a normalizing rational point `n`, `i(t) n = n i(t')` where `t'` evaluates every
character `χ` as `t` evaluates the Weyl translate `n · χ`. -/
theorem exists_map_mul_rational_normalizer (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (t : AdelicGroupPoints F T.toGrp) :
    ∃ t' : AdelicGroupPoints F T.toGrp,
      map F T.toGrp G i t * rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X)) =
        rational F G (basePointEquiv (n : Over.mk _ ⟶ G.X)) * map F T.toGrp G i t' ∧
      ∀ χ : characterLattice T,
        PositiveRealTorus.normCharacter F T χ t' =
          PositiveRealTorus.normCharacter F T (weylAction i n χ) t := by
  refine ⟨map F T.toGrp T.toGrp (CommGroupScheme.groupHom (normalizingAut i n).inv) t,
    map_mul_rational_basePointEquiv (isNormalizingPoint_normalizingAut i n) t, fun χ => ?_⟩
  rw [normCharacter_map_groupHom_inv, weylAction_apply]

end Langlands.Global.AdelicGroupPoints
