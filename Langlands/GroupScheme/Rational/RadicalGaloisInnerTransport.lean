import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Galois translates and inner conjugates of subgroups

Descent transport (`radicalGaloisHom`) of a subgroup followed by an inner automorphism, and
range identities for subgroups conjugated by rational points.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section Abstract

variable {S S' : Scheme.{u}} (b : S' ⟶ S) (a : S' ⟶ S') (ha : a ≫ b = b)
  {H : GroupScheme S} {V : GroupScheme S'}

/-- Descent transport of a subgroup followed by an inner automorphism, for abstract base
maps. -/
theorem descent_comp_innerIso (f : V ⟶ (GroupScheme.baseChange b).obj H)
    (n : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj H).X) :
    (GroupScheme.baseChange a).map (f ≫ (((GroupScheme.baseChange b).obj H).innerIso n).hom) ≫
        (descentBaseChangeIso b a ha H).hom =
      ((GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha H).hom) ≫
        (((GroupScheme.baseChange b).obj H).innerIso
          (baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) n ≫
            (descentBaseChangeIso b a ha H).hom.hom.hom)).hom := by
  rw [Functor.map_comp, baseChange_innerIso_hom, Category.assoc, Category.assoc,
    innerIso_hom_comp]

/-- The same identity with the transported point given through an equation. -/
theorem descent_comp_innerIso_of_eq (f : V ⟶ (GroupScheme.baseChange b).obj H)
    (n : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj H).X)
    (m : Over.mk (𝟙 S') ⟶ ((GroupScheme.baseChange b).obj H).X)
    (hm : m = baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) n ≫
      (descentBaseChangeIso b a ha H).hom.hom.hom) :
    (GroupScheme.baseChange a).map (f ≫ (((GroupScheme.baseChange b).obj H).innerIso n).hom) ≫
        (descentBaseChangeIso b a ha H).hom =
      ((GroupScheme.baseChange a).map f ≫ (descentBaseChangeIso b a ha H).hom) ≫
        (((GroupScheme.baseChange b).obj H).innerIso m).hom := by
  subst hm
  exact descent_comp_innerIso b a ha f n

end Abstract

section GaloisInner

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of K))}

/-- The canonical Galois translate of an inner conjugate of a subgroup is the inner
conjugate of the translate by the Galois conjugate point. -/
theorem radicalGaloisHom_comp_innerIso
    (f : U ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (σ : K ≃ₐ[k] K) :
    radicalGaloisHom (f ≫ (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso
        n).hom) σ =
      radicalGaloisHom f σ ≫
        (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso
          (GaloisPointComparison.rationalConjugate k K G σ n)).hom :=
  descent_comp_innerIso_of_eq (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) f n _ (rationalConjugate_eq_baseChange_descent k K σ n)

end GaloisInner

/-- Conjugating a subgroup by one of its own rational points does not change its range. -/
theorem range_comp_innerIso_of_mem {S : Scheme.{u}} {H G : GroupScheme S} (j : H ⟶ G)
    (p : Over.mk (𝟙 S) ⟶ H.X) :
    SubgroupFunctor.range (j ≫ (G.innerIso (p ≫ j.hom.hom)).hom) =
      SubgroupFunctor.range j := by
  rw [← innerIso_hom_comp, SubgroupFunctor.range_iso_comp]

/-- If `X` is `Y` followed by conjugation by `c`, the range of `Y` is the conjugate of the range
of `P` by `m`, and `c * m = q * pt` with `pt` a point of the subgroup `P`, then the range of `X`
is the conjugate of the range of `P` by `q`. -/
theorem range_eq_of_innerIso_transport {S : Scheme.{u}} {G H H' : GroupScheme S}
    (X Y : H ⟶ G) (P : H' ⟶ G) (c m q pt : Over.mk (𝟙 S) ⟶ G.X)
    (p : Over.mk (𝟙 S) ⟶ H'.X) (hpt : pt = p ≫ P.hom.hom)
    (hX : X = Y ≫ (G.innerIso c).hom)
    (hY : SubgroupFunctor.range Y = SubgroupFunctor.range (P ≫ (G.innerIso m).hom))
    (hc : c * m = q * pt) :
    SubgroupFunctor.range X = SubgroupFunctor.range (P ≫ (G.innerIso q).hom) := by
  rw [hX, (SubgroupFunctor.range_comp_iso_eq_iff Y (P ≫ (G.innerIso m).hom)
      (G.innerIso c)).mpr hY, Category.assoc, ← innerIso_mul_hom, hc, hpt, innerIso_mul_hom,
    ← Category.assoc, ← innerIso_hom_comp, Category.assoc, SubgroupFunctor.range_iso_comp]

end Langlands.GroupScheme
